// CEP:FILE: tools/cep_lint/src/main.cpp
// CEP:WHAT: Command-line entry point: option parsing, configuration resolution (flag, environment, default), lint runs, self-test runs, and exit code mapping.
// CEP:WHY: CEP&CC 50.1 defines the invocation contract (options, exit codes 0-3, environment override); main is the only place that contract is realized.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: exits 3 on usage errors, 2 on bootstrap failures, 1 on fail_on findings, 0 otherwise.
// CEP:ASSUMES: run from the repository root or with explicit paths.
// CEP:COST: argument parsing is constant; the run cost is the engine's.
// CEP:EVIDENCE: CI invokes every option path.
// CEP:SECURITY: no network; configuration paths come from the caller or environment.

#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "engine.hpp"

namespace {

// CEP:WHAT: Default configuration path.
// CEP:WHY: CEP&CC 50.1 fixes the default at .cep/cep_lint.json.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: main.
// CEP:SECURITY: none.
constexpr const char* kDefaultConfig = ".cep/cep_lint.json";

// CEP:WHAT: Default self-test manifest path.
// CEP:WHY: CEP&CC 50.1 points --self-test at tools/cep_lint/tests/manifest.json.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: main.
// CEP:SECURITY: none.
constexpr const char* kDefaultManifest = "tools/cep_lint/tests/manifest.json";

}  // namespace

// CEP:WHAT: Program entry point.
// CEP:WHY: See file header.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: exit codes per CEP&CC 50.1.
// CEP:ASSUMES: none.
// CEP:COST: see engine.
// CEP:EVIDENCE: CI.
// CEP:SECURITY: none.
int main(int argc, char** argv) {
    std::string config_path = kDefaultConfig;
    bool self_test = false;
    bool help = false;
    bool version = false;
    std::vector<std::string> paths;
    for (int index = 1; index < argc; index += 1) {
        std::string argument = argv[index];
        if (argument == "--config" || argument == "-c") {
            if (index + 1 >= argc) {
                std::cerr << "option " << argument << " requires a path" << std::endl;
                return cep_lint::ExitUsage;
            }
            index += 1;
            config_path = argv[index];
            continue;
        }
        if (argument == "--self-test" || argument == "-t") {
            self_test = true;
            continue;
        }
        if (argument == "--help" || argument == "-h") {
            help = true;
            continue;
        }
        if (argument == "--version" || argument == "-v") {
            version = true;
            continue;
        }
        if (!argument.empty() && argument[0] == '-') {
            std::cerr << "unknown option " << argument << std::endl;
            cep_lint::print_usage();
            return cep_lint::ExitUsage;
        }
        paths.push_back(argument);
    }
    const char* environment = std::getenv("CEP_LINT_CONFIG");
    if (environment != nullptr && config_path == kDefaultConfig) {
        config_path = environment;
    }
    if (help) {
        cep_lint::print_usage();
        return cep_lint::ExitOk;
    }
    cep_lint::Configuration config;
    if (!cep_lint::load_configuration(config_path, config)) {
        return cep_lint::ExitBootstrap;
    }
    if (version) {
        cep_lint::print_version(config);
        return cep_lint::ExitOk;
    }
    if (self_test) {
        const bool ok = cep_lint::run_self_test(config, kDefaultManifest);
        return ok ? cep_lint::ExitOk : cep_lint::ExitFindings;
    }
    if (paths.empty()) {
        std::cerr << "no files or directories given" << std::endl;
        cep_lint::print_usage();
        return cep_lint::ExitUsage;
    }
    return cep_lint::run_lint(config, paths);
}
