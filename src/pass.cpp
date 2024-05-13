#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Process.h"
#include <filesystem>
#include <string>
#include <cstdio>
#include <array>
#include <iostream>
#include <fstream>
#include <map>
#include "spdlog/spdlog.h"
#include "fmt/format.h"
#include "yaml-cpp/yaml.h"
using namespace llvm;

static const char *OUT_ENV = "BRANCHES_OUT";
static const char *DEBUG_ENV = "BRANCHES_DEBUG";

namespace branch_pass
{

struct InstructionDebugInfo {
    size_t line;
    size_t column;

    InstructionDebugInfo(const DebugLoc &loc)
        : line(loc->getLine()), column(loc->getColumn())
    {
    }

    YAML::Node to_node()
    {
        YAML::Node node;

        node["line"] = this->line;
        node["column"] = this->column;

        return node;
    }
};

struct FunctionDebugInfo {
    std::string function;
    size_t start_line;
    size_t end_line;

    YAML::Node to_node()
    {
        YAML::Node node;

        node["function"] = this->function;
        node["start_line"] = this->start_line;
        node["end_line"] = this->end_line;

        return node;
    }
};

struct Branch {
    InstructionDebugInfo branch;
    InstructionDebugInfo lhs;
    InstructionDebugInfo rhs;

    YAML::Node to_node()
    {
        YAML::Node node;

        auto branch = this->branch.to_node();
        auto lhs = this->lhs.to_node();
        auto rhs = this->rhs.to_node();

        node["branch"] = branch;
        node["lhs"] = lhs;
        node["rhs"] = rhs;

        return node;
    }
};

struct FunctionWithBranches {
    FunctionDebugInfo function;
    std::vector<Branch> branches;

    YAML::Node to_node()
    {
        YAML::Node node;
        std::vector<YAML::Node> ns;

        auto function = this->function.to_node();

        for (auto &&br : this->branches) {
            ns.push_back(br.to_node());
        }

        node["branches"] = ns;
        // node["function"] = function;
        
        for (auto&& it: function) {
            node[it.first] = it.second;
        }

        return node;
    }
};

struct FileBranchInformation {
    std::string file;
    std::vector<FunctionWithBranches> functions;

    YAML::Node to_node()
    {
        YAML::Node node;
        std::vector<YAML::Node> ns;

        node["file"] = this->file;
        for (auto &&fn : this->functions) {
            ns.push_back(fn.to_node());
        }
        node["functions"] = ns;

        return node;
    }
};

static std::string linkage_to_string(const GlobalValue::LinkageTypes linkage)
{
    std::array mapping = {
        "ExternalLinkage",
        "AvailableExternallyLinkage", ///< Available for inspection, not
                                      ///< emission.
        "LinkOnceAnyLinkage", ///< Keep one copy of function when linking
                              ///< (inline)
        "LinkOnceODRLinkage", ///< Same, but only replaced by something
                              ///< equivalent.
        "WeakAnyLinkage",     ///< Keep one copy of named function when linking
                              ///< (weak)
        "WeakODRLinkage", ///< Same, but only replaced by something equivalent.
        "AppendingLinkage", ///< Special purpose, only applies to global arrays
        "InternalLinkage",  ///< Rename collisions when linking (static
                            ///< functions).
        "PrivateLinkage",   ///< Like Internal, but omit from symbol table.
        "ExternalWeakLinkage", ///< ExternalWeak linkage description.
        "CommonLinkage"        ///< Tentative definitions.
    };

    if (size_t(linkage) > mapping.size()) {
        return std::string("Unknown type");
    } else {
        return mapping[size_t(linkage)];
    }
}

static std::string debug_loc_identifier(const DebugLoc &loc)
{
    if (loc) {
        auto fn = loc->getFilename().str();
        auto ln = loc.getLine();
        auto col = loc->getColumn();
        return fmt::format("{}:{}:{}", fn, ln, col);
    } else {
        return std::string("<No DebugLoc>");
    }
}

class BranchPass : public PassInfoMixin<BranchPass>
{
  private:
    std::filesystem::path output_directory_;

  public:
    BranchPass(std::string out) : output_directory_(out) {}

    PreservedAnalyses run(Module &m, ModuleAnalysisManager &mgr)
    {
        auto absolute_path = this->module_path(m);
        std::vector<FunctionWithBranches> branches;
        spdlog::debug("Running in module {} source {}", m.getName().str(),
                      absolute_path.generic_string());

        for (auto &&f : m.functions()) {
            if (this->shouldAnalyze(f)) {
                branches.push_back(this->analyzeFunction(f));
            }
        }

        if (branches.size() > 0) {
            if (!std::filesystem::exists(this->output_directory_)) {
                std::filesystem::create_directory(this->output_directory_);
            } else {

            }
            auto out_fname = this->next_available(absolute_path.filename());
            auto info = FileBranchInformation{.file = absolute_path,
                                              .functions = branches}
                            .to_node();

            auto out =
                std::ofstream(out_fname, std::ios::trunc | std::ios::out);

            out << info;
        }

        return PreservedAnalyses::all();
    }

    static bool isRequired()
    {
        return true;
    }

  private:
    std::filesystem::path next_available(const std::string &fname)
    {
        auto pid = llvm::sys::Process::getProcessId();
        std::filesystem::path next =
            this->output_directory_ / fmt::format("{}-{}.yaml", fname, pid);
        size_t idx = 0;
        while (std::filesystem::exists(next)) {
            auto new_fname = fmt::format("{}-{}-{}.yaml", fname, pid, idx);
            next = this->output_directory_ / new_fname;
            idx += 1;
        }

        return next;
    }

    // https://stackoverflow.com/questions/68962513/in-llvm-ir-pass-how-to-extract-an-absolute-path-of-the-current-module
    std::filesystem::path module_path(Module &m)
    {
        std::string relFilename =
            m.getSourceFileName(); // e.g., relFilename = ..\aaa.c
        llvm::SmallString<128> FilenameVec = StringRef(relFilename);
        llvm::SmallString<128> RealPath;
        (void)llvm::sys::fs::real_path(
            FilenameVec,
            RealPath); // e.g., RealPath = \path\to\aaa.c  <-- in Windows
        //
        return std::filesystem::path{std::string(RealPath)};
    }

    unsigned last_line(Function &f)
    {
        unsigned last = 0;

        for (auto &&bb : f) {
            auto last_inst = bb.getTerminator();

            if (last_inst) {
                auto dbg = last_inst->getDebugLoc();
                if (dbg) {
                    auto line = dbg.getLine();

                    if (line > last) {
                        last = line;
                    }
                }
            }
        }

        return last;
    }

    bool shouldAnalyze(Function &f)
    {
        return f.size() != 0;
    }

    FunctionWithBranches analyzeFunction(Function &f)
    {
        auto subprogram = f.getSubprogram();
        auto function_fn = subprogram->getFilename().str();
        std::vector<FunctionWithBranches> out;
        auto function_name = f.getName().str();
        auto start_line = subprogram->getLine();
        auto last_line = this->last_line(f);
        auto function_debug = FunctionDebugInfo{.function = function_name,
                                                .start_line = start_line,
                                                .end_line = last_line};
        std::vector<Branch> branches;

        spdlog::debug("Analyze: Function {}:{}:{} Linkage {} Blocks {}",
                      function_name, start_line, last_line,
                      linkage_to_string(f.getLinkage()), f.size());
        // auto domtree = DominatorTree(f);
        // auto loops = LoopInfo(domtree);

        for (auto &&bb : f) {
            auto terminator = bb.getTerminator();
            if (terminator) {
                auto branch = dyn_cast<BranchInst>(terminator);

                if (branch && branch->isConditional()) {
                    auto branch_dbg = branch->getDebugLoc();

                    // auto loop = loops.getLoopFor(&bb);
                    // if (loop) {
                    //     spdlog::debug("Loop: {} Guarded: {}",
                    //     loop->getName().str(), loop->isGuarded()); auto guard
                    //     = loop->getLoopGuardBranch(); if (guard)
                    //         spdlog::debug("Guard: {}",
                    //         debug_loc_identifier(guard->getDebugLoc()));
                    //     if (guard == branch) {
                    //         spdlog::debug("Loop guard detected at {}",
                    //                     debug_loc_identifier(branch_dbg));
                    //         continue;
                    //     }
                    // }

                    auto lhs = branch->getSuccessor(0);
                    auto rhs = branch->getSuccessor(1);

                    auto lhs_first_ln =
                        lhs->getFirstNonPHIOrDbgOrLifetime(true);
                    auto rhs_first_ln =
                        rhs->getFirstNonPHIOrDbgOrLifetime(true);

                    if (!lhs_first_ln || !rhs_first_ln) {
                        spdlog::debug(
                            "Skipped because either lhs or rhs no first lines");
                        continue;
                    }

                    auto lhs_dbg = lhs_first_ln->getDebugLoc();
                    auto rhs_dbg = rhs_first_ln->getDebugLoc();

                    spdlog::debug("Found a branch at {} lhs {} rhs {}",
                                  debug_loc_identifier(branch_dbg),
                                  debug_loc_identifier(lhs_dbg),
                                  debug_loc_identifier(rhs_dbg));

                    // SmallVector<BasicBlock *> v;
                    // domtree.getDescendants(&bb, v);

                    if (branch_dbg && lhs_dbg && rhs_dbg) {
                        branches.push_back(
                            Branch{.branch = InstructionDebugInfo(branch_dbg),
                                   .lhs = InstructionDebugInfo(lhs_dbg),
                                   .rhs = InstructionDebugInfo(rhs_dbg)});
                    }
                }
            }
        }

        return FunctionWithBranches{.function = function_debug,
                                    .branches = branches};
    }
};

PassPluginLibraryInfo getPlugin()
{
    return {LLVM_PLUGIN_API_VERSION, "BranchPass", LLVM_VERSION_STRING,
            [](PassBuilder &pb) {
                pb.registerPipelineEarlySimplificationEPCallback(
                    [](ModulePassManager &mp, OptimizationLevel OL) {
                        std::string out;
                        if (char *env = std::getenv(OUT_ENV)) {
                            out = env;
                        } else {
                            out = std::filesystem::current_path();
                        }

                        if (std::getenv(DEBUG_ENV)) {
                            spdlog::set_level(spdlog::level::debug);
                        } else {
                            spdlog::set_level(spdlog::level::info);
                        }

                        spdlog::info("Our output folder is {}", out);

                        mp.addPass(BranchPass(out));
                    });
            }};
}

} // namespace branch_pass

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo()
{
    return branch_pass::getPlugin();
}