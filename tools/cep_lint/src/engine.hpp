// CEP:FILE: tools/cep_lint/src/engine.hpp
// CEP:WHAT: Lint engine: configuration loading with bootstrap error codes, sorted file discovery, rule dispatch with class scoping, deterministic finding output, and the version banner.
// CEP:WHY: CEP&CC 50.1 defines invocation, exit codes, and determinism; the engine is the single orchestrator so those guarantees hold in one auditable place.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: bootstrap failures print CEP-LINT-BOOT-<n> with detail and exit 2 (50.4); lint failures exit 1 per fail_on.
// CEP:ASSUMES: configuration and scanned files are repository-trusted.
// CEP:COST: O(files x rules x lines).
// CEP:EVIDENCE: self-test manifest exercises exit codes and determinism.
// CEP:SECURITY: no network, no untrusted configuration paths.

#pragma once

#include <string>
#include <vector>

#include "checks.hpp"

namespace cep_lint {

// CEP:WHAT: Exit code meanings (CEP&CC 50.1).
// CEP:WHY: Stable contract for CI.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: main and selftest.
// CEP:SECURITY: none.
enum ExitCode {
    /// CEP:WHAT: No failing findings.
    ExitOk = 0,
    /// CEP:WHAT: Findings at a severity listed in fail_on.
    ExitFindings = 1,
    /// CEP:WHAT: Bootstrap failure (configuration, scan, or document load).
    ExitBootstrap = 2,
    /// CEP:WHAT: Command-line usage error.
    ExitUsage = 3,
};

// CEP:WHAT: Loaded configuration.
// CEP:WHY: One parsed home for standard version, fail_on, extensions, and rules.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none after successful load.
// CEP:ASSUMES: none.
// CEP:COST: value semantics.
// CEP:EVIDENCE: engine.
// CEP:SECURITY: none.
struct Configuration {
    /// CEP:WHAT: Standard version string the configuration is written against.
    std::string standard_version;
    /// CEP:WHAT: Path of the standard document for DOC-SYNC.
    std::string doc_path;
    /// CEP:WHAT: Severities that cause exit 1.
    std::vector<int> fail_on;
    /// CEP:WHAT: File extensions to lint.
    std::vector<std::string> extensions;
    /// CEP:WHAT: Class values that class-scoped rules apply to.
    std::vector<std::string> hot_classes;
    /// CEP:WHAT: Rules in configuration order.
    std::vector<std::pair<std::string, RuleConfig>> rules;
};

// CEP:WHAT: Loads the configuration from a JSON file.
// CEP:WHY: Data-driven rule loading with CEP-LINT-BOOT error codes (50.4).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: prints CEP-LINT-BOOT-1 (IO), -2 (parse), -4 (missing key), -5 (wrong type), -7 (severity), -8 (regex) and returns false.
// CEP:ASSUMES: repository-trusted file.
// CEP:COST: O(file).
// CEP:EVIDENCE: self-test bootstrap scenarios.
// CEP:SECURITY: repository-trusted input only.
bool load_configuration(const std::string& path, Configuration& out);

// CEP:WHAT: Reads a file from disk.
// CEP:WHY: Shared IO helper with a single failure point.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false on IO failure.
// CEP:ASSUMES: none.
// CEP:COST: O(file).
// CEP:EVIDENCE: engine and selftest.
// CEP:SECURITY: repository-trusted paths only.
bool read_file(const std::string& path, std::string& out);

// CEP:WHAT: Collects lintable files under paths, sorted.
// CEP:WHY: CEP&CC 50.1 determinism: directory traversal is sorted.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: unreadable directories are reported and skipped deterministically.
// CEP:ASSUMES: none.
// CEP:COST: O(tree).
// CEP:EVIDENCE: engine.
// CEP:SECURITY: path traversal stays within the given roots.
void collect_files(const std::vector<std::string>& roots,
                   const std::vector<std::string>& extensions,
                   std::vector<std::string>& out);

// CEP:WHAT: Lints one already-read file against the configuration.
// CEP:WHY: Shared by the engine run and the self-test runner.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: none.
// CEP:COST: O(rules x lines).
// CEP:EVIDENCE: engine and selftest.
// CEP:SECURITY: none.
std::vector<Finding> lint_text(const Configuration& config,
                               const std::string& path,
                               const std::string& text);

// CEP:WHAT: Runs the linter over files and prints findings.
// CEP:WHY: Main entry orchestration with deterministic output ordering.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns the process exit code (0, 1, or 2).
// CEP:ASSUMES: none.
// CEP:COST: O(files x rules x lines).
// CEP:EVIDENCE: self-test.
// CEP:SECURITY: none.
int run_lint(const Configuration& config, const std::vector<std::string>& paths);

// CEP:WHAT: Prints the usage banner.
// CEP:WHY: CEP&CC 50.1 --help.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: main.
// CEP:SECURITY: none.
void print_usage();

// CEP:WHAT: Prints the version banner.
// CEP:WHY: CEP&CC 50.1 --version prints tool and standard versions.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: main.
// CEP:SECURITY: none.
void print_version(const Configuration& config);

// CEP:WHAT: Runs the self-test manifest (declared here; implemented in selftest.cpp).
// CEP:WHY: main dispatches --self-test through the engine interface.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false on any scenario failure.
// CEP:ASSUMES: configuration already loaded.
// CEP:COST: O(scenarios).
// CEP:EVIDENCE: CI.
// CEP:SECURITY: none.
bool run_self_test(const Configuration& config, const std::string& manifest_path);

}  // namespace cep_lint
