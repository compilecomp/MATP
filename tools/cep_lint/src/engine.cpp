// CEP:FILE: tools/cep_lint/src/engine.cpp
// CEP:WHAT: Implementation of the lint engine: configuration loading, sorted file discovery, class-scoped rule dispatch, DOC-SYNC, and deterministic reporting.
// CEP:WHY: See engine.hpp; CEP&CC 50.1 and 50.4 define the observable behavior implemented here.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: bootstrap errors print CEP-LINT-BOOT-<n> codes; lint findings print as path:line: severity: rule: message.
// CEP:ASSUMES: repository-trusted inputs.
// CEP:COST: O(files x rules x lines).
// CEP:EVIDENCE: self-test scenarios.
// CEP:SECURITY: no network; traversal bounded to given roots.

#include "engine.hpp"

#include <algorithm>
#include <dirent.h>
#include <fstream>
#include <iostream>
#include <regex>
#include <sstream>
#include <sys/stat.h>

#include "json.hpp"
#include "source.hpp"

namespace cep_lint {

// CEP:WHAT: Tool version string.
// CEP:WHY: The version banner prints tool and standard versions (CEP&CC 50.1).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: --version output.
// CEP:SECURITY: none.
constexpr const char* kToolVersion = "0.1.0";

bool read_file(const std::string& path, std::string& out) {
    std::ifstream stream(path, std::ios::binary);
    if (!stream.is_open()) {
        return false;
    }
    std::ostringstream buffer;
    buffer << stream.rdbuf();
    out = buffer.str();
    return true;
}

// CEP:WHAT: Reports a bootstrap failure with its code and detail.
// CEP:WHY: CEP&CC 50.4 defines the CEP-LINT-BOOT-<n> reporting format.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: configuration load failures.
// CEP:SECURITY: none.
void report_bootstrap(int code, const std::string& detail) {
    std::cerr << "CEP-LINT-BOOT-" << code << ": " << detail << std::endl;
}

// CEP:WHAT: Loads and validates the lint configuration from JSON.
// CEP:WHY: CEP&CC 50.4 defines the bootstrap error codes this loader emits.
// CEP:STATUS: complete
// CEP:FAILURE: prints a CEP-LINT-BOOT code and returns false on any schema, type, or regex problem.
// CEP:ASSUMES: repository-trusted input.
// CEP:COST: O(file).
// CEP:EVIDENCE: bootstrap scenarios in CI.
// CEP:SECURITY: repository-trusted configuration only.
bool load_configuration(const std::string& path, Configuration& out) {
    std::string text;
    if (!read_file(path, text)) {
        report_bootstrap(1, "cannot read configuration " + path);
        return false;
    }
    JsonError error;
    auto parsed = json_parse(text, error);
    if (!parsed.second) {
        std::ostringstream detail;
        detail << "JSON parse failure in " << path << " at line " << error.line
               << ", column " << error.column << ": " << error.message;
        report_bootstrap(2, detail.str());
        return false;
    }
    const JsonValue& root = parsed.first;
    const JsonValue* standard = root.find("standard");
    if (standard == nullptr) {
        report_bootstrap(4, "missing key: standard");
        return false;
    }
    const JsonValue* version = standard->find("version");
    if (version == nullptr || version->get_kind() != JsonValue::Kind::String) {
        report_bootstrap(4, "missing key: standard.version");
        return false;
    }
    out.standard_version = version->as_string();
    const JsonValue* doc = standard->find("doc_path");
    if (doc == nullptr || doc->get_kind() != JsonValue::Kind::String) {
        report_bootstrap(4, "missing key: standard.doc_path");
        return false;
    }
    out.doc_path = doc->as_string();
    const JsonValue* fail_on = root.find("fail_on");
    if (fail_on == nullptr || fail_on->get_kind() != JsonValue::Kind::Array) {
        report_bootstrap(4, "missing key: fail_on");
        return false;
    }
    for (const JsonValue& item : fail_on->as_array()) {
        if (item.get_kind() != JsonValue::Kind::Number) {
            report_bootstrap(5, "fail_on entries must be numbers");
            return false;
        }
        int severity = static_cast<int>(item.as_number());
        if (severity < 0 || severity > 3) {
            report_bootstrap(7, "severity out of the 0 through 3 range");
            return false;
        }
        out.fail_on.push_back(severity);
    }
    const JsonValue* extensions = root.find("extensions");
    if (extensions == nullptr || extensions->get_kind() != JsonValue::Kind::Array) {
        report_bootstrap(4, "missing key: extensions");
        return false;
    }
    for (const JsonValue& item : extensions->as_array()) {
        if (item.get_kind() != JsonValue::Kind::String) {
            report_bootstrap(5, "extensions entries must be strings");
            return false;
        }
        out.extensions.push_back(item.as_string());
    }
    const JsonValue* hot_classes = root.find("hot_classes");
    if (hot_classes != nullptr && hot_classes->get_kind() == JsonValue::Kind::Array) {
        for (const JsonValue& item : hot_classes->as_array()) {
            if (item.get_kind() != JsonValue::Kind::String) {
                report_bootstrap(5, "hot_classes entries must be strings");
                return false;
            }
            out.hot_classes.push_back(item.as_string());
        }
    }
    const JsonValue* rules = root.find("rules");
    if (rules == nullptr || rules->get_kind() != JsonValue::Kind::Object) {
        report_bootstrap(4, "missing key: rules");
        return false;
    }
    for (const auto& member : rules->as_object()) {
        const JsonValue& body = member.second;
        if (body.get_kind() != JsonValue::Kind::Object) {
            report_bootstrap(5, "rule " + member.first + " must be an object");
            return false;
        }
        RuleConfig rule;
        rule.name = member.first;
        const JsonValue* severity = body.find("severity");
        if (severity == nullptr || severity->get_kind() != JsonValue::Kind::Number) {
            report_bootstrap(4, "rule " + member.first + " is missing severity");
            return false;
        }
        rule.severity = static_cast<int>(severity->as_number());
        if (rule.severity < 0 || rule.severity > 3) {
            report_bootstrap(7, "rule " + member.first + " severity out of range");
            return false;
        }
        const JsonValue* check = body.find("check");
        if (check == nullptr || check->get_kind() != JsonValue::Kind::String) {
            report_bootstrap(4, "rule " + member.first + " is missing check");
            return false;
        }
        rule.check = check->as_string();
        rule.parameters = body;
        const JsonValue* pattern = body.find("pattern");
        if (pattern != nullptr && pattern->get_kind() == JsonValue::Kind::String) {
            try {
                (void)std::regex(pattern->as_string());
            } catch (const std::regex_error&) {
                report_bootstrap(8, "rule " + member.first + " has an invalid regular expression");
                return false;
            }
        }
        out.rules.emplace_back(member.first, rule);
    }
    return true;
}

// CEP:WHAT: Returns true when a path has one of the configured extensions.
// CEP:WHY: File filtering.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(extensions).
// CEP:EVIDENCE: collect_files.
// CEP:SECURITY: none.
bool has_configured_extension(const std::string& path, const std::vector<std::string>& extensions) {
    for (const std::string& extension : extensions) {
        if (path.size() >= extension.size()
            && path.compare(path.size() - extension.size(), extension.size(), extension) == 0) {
            return true;
        }
    }
    return false;
}

// CEP:WHAT: Collects lintable files under the given roots in sorted order.
// CEP:WHY: CEP&CC 50.1 requires deterministic, sorted traversal.
// CEP:STATUS: complete
// CEP:FAILURE: unreadable directories are skipped.
// CEP:ASSUMES: none.
// CEP:COST: O(tree).
// CEP:EVIDENCE: run_lint determinism.
// CEP:SECURITY: traversal stays within the given roots.
void collect_files(const std::vector<std::string>& roots,
                   const std::vector<std::string>& extensions,
                   std::vector<std::string>& out) {
    std::vector<std::string> queue = roots;
    while (!queue.empty()) {
        std::string current = queue.back();
        queue.pop_back();
        struct stat info;
        if (stat(current.c_str(), &info) != 0) {
            continue;
        }
        if (S_ISDIR(info.st_mode)) {
            DIR* directory = opendir(current.c_str());
            if (directory == nullptr) {
                continue;
            }
            std::vector<std::string> children;
            struct dirent* entry = readdir(directory);
            while (entry != nullptr) {
                std::string name = entry->d_name;
                if (name != "." && name != "..") {
                    children.push_back(name);
                }
                entry = readdir(directory);
            }
            closedir(directory);
            std::sort(children.begin(), children.end());
            for (const std::string& child : children) {
                queue.push_back(current + "/" + child);
            }
            continue;
        }
        if (has_configured_extension(current, extensions)) {
            out.push_back(current);
        }
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
}

// CEP:WHAT: Returns true when a rule applies to the file's declared class.
// CEP:WHY: Class-scoped rules (HOT-BANNED, MAGIC-NUMBER) consult the applies_to_classes parameter; unscoped rules apply everywhere.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(classes).
// CEP:EVIDENCE: HOT-BANNED scoping.
// CEP:SECURITY: none.
bool rule_applies_to_file(const RuleConfig& rule, const SourceFile& file) {
    const JsonValue* scoped = rule.parameters.find("applies_to_classes");
    if (scoped == nullptr || scoped->get_kind() != JsonValue::Kind::Array) {
        return true;
    }
    for (const JsonValue& item : scoped->as_array()) {
        if (item.get_kind() == JsonValue::Kind::String && item.as_string() == file.declared_class()) {
            return true;
        }
    }
    return false;
}

// CEP:WHAT: Lints one file's text against every per-file rule.
// CEP:WHY: Shared by the engine run and the self-test runner so both observe identical behavior.
// CEP:STATUS: complete
// CEP:FAILURE: never throws; unknown primitives produce a severity-2 finding.
// CEP:ASSUMES: configuration validated at load.
// CEP:COST: O(rules x lines).
// CEP:EVIDENCE: self-test scenarios and engine runs.
// CEP:SECURITY: none.
std::vector<Finding> lint_text(const Configuration& config,
                               const std::string& path,
                               const std::string& text) {
    SourceFile file(path, text);
    std::vector<Finding> findings;
    for (const auto& entry : config.rules) {
        const RuleConfig& rule = entry.second;
        if (rule.check == "doc_rule_coverage") {
            continue;  // document coverage runs once against the standard, not per file.
        }
        if (!rule_applies_to_file(rule, file)) {
            continue;
        }
        std::vector<Finding> produced;
        if (rule.check == "comment_block_schema") {
            produced = check_comment_block_schema(file, rule);
        } else if (rule.check == "function_policy") {
            produced = check_function_policy(file, rule);
        } else if (rule.check == "comment_regex") {
            produced = check_comment_regex(file, rule);
        } else if (rule.check == "string_literal_regex") {
            produced = check_string_literal_regex(file, rule);
        } else if (rule.check == "numeric_literal_policy") {
            produced = check_numeric_literal_policy(file, rule);
        } else if (rule.check == "macro_prefix_policy") {
            produced = check_macro_prefix_policy(file, rule);
        } else if (rule.check == "banned_token_policy") {
            produced = check_banned_token_policy(file, rule);
        } else if (rule.check == "flat_code_regex") {
            produced = check_flat_code_regex(file, rule);
        } else if (rule.check == "naming_type") {
            produced = check_naming_type(file, rule);
        } else {
            Finding finding;
            finding.file = path;
            finding.line = 1;
            finding.rule = rule.name;
            finding.severity = 2;
            finding.message = "unknown check primitive " + rule.check;
            produced.push_back(finding);
        }
        for (Finding& finding : produced) {
            finding.rule = rule.name;
            finding.severity = rule.severity;
        }
        findings.insert(findings.end(), produced.begin(), produced.end());
    }
    return findings;
}

// CEP:WHAT: Comparison for deterministic finding order.
// CEP:WHY: CEP&CC 50.1: issues are sorted by file, line, rule, and message.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: run_lint output.
// CEP:SECURITY: none.
bool finding_less(const Finding& left, const Finding& right) {
    if (left.file != right.file) {
        return left.file < right.file;
    }
    if (left.line != right.line) {
        return left.line < right.line;
    }
    if (left.rule != right.rule) {
        return left.rule < right.rule;
    }
    return left.message < right.message;
}

// CEP:WHAT: Runs the linter over files, prints sorted findings, and maps to the process exit code.
// CEP:WHY: CEP&CC 50.1 defines exit codes 0, 1, and 2 for clean, findings, and bootstrap failures.
// CEP:STATUS: complete
// CEP:FAILURE: unreadable files or a missing standard document yield exit 2.
// CEP:ASSUMES: none.
// CEP:COST: O(files x rules x lines).
// CEP:EVIDENCE: CI lint gate.
// CEP:SECURITY: none.
int run_lint(const Configuration& config, const std::vector<std::string>& paths) {
    std::vector<std::string> files;
    collect_files(paths, config.extensions, files);
    std::vector<Finding> all_findings;
    bool read_failure = false;
    for (const std::string& path : files) {
        std::string text;
        if (!read_file(path, text)) {
            report_bootstrap(1, "cannot read file " + path);
            read_failure = true;
            continue;
        }
        std::vector<Finding> findings = lint_text(config, path, text);
        all_findings.insert(all_findings.end(), findings.begin(), findings.end());
    }
    // DOC-SYNC runs once against the standard document.
    bool has_doc_sync = false;
    for (const auto& entry : config.rules) {
        if (entry.first == "CEP-LINT-DOC-SYNC") {
            has_doc_sync = true;
            break;
        }
    }
    if (has_doc_sync) {
        std::string document;
        if (!read_file(config.doc_path, document)) {
            report_bootstrap(1, "cannot read standard document " + config.doc_path);
            read_failure = true;
        } else {
            std::vector<Finding> doc_findings = check_doc_rule_coverage(
                config.rules, document, config.doc_path, config.standard_version);
            all_findings.insert(all_findings.end(), doc_findings.begin(), doc_findings.end());
        }
    }
    std::sort(all_findings.begin(), all_findings.end(), finding_less);
    for (const Finding& finding : all_findings) {
        std::cout << finding.file << ":" << finding.line << ": severity " << finding.severity
                  << ": " << finding.rule << ": " << finding.message << std::endl;
    }
    if (read_failure) {
        return ExitBootstrap;
    }
    for (const Finding& finding : all_findings) {
        if (std::find(config.fail_on.begin(), config.fail_on.end(), finding.severity)
            != config.fail_on.end()) {
            return ExitFindings;
        }
    }
    return ExitOk;
}

// CEP:WHAT: Prints the usage banner.
// CEP:WHY: CEP&CC 50.1 requires a help option.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: CI option checks.
// CEP:SECURITY: none.
void print_usage() {
    std::cout << "usage: cep_lint [--config|-c <path>] [--self-test|-t] [--help|-h] [--version|-v]"
              << " [files or directories]" << std::endl;
    std::cout << "options:" << std::endl;
    std::cout << "  -c, --config <path>   lint configuration (default .cep/cep_lint.json, env CEP_LINT_CONFIG)"
              << std::endl;
    std::cout << "  -t, --self-test       run the self-test manifest and exit" << std::endl;
    std::cout << "  -h, --help            show this help" << std::endl;
    std::cout << "  -v, --version         print tool and standard versions" << std::endl;
}

// CEP:WHAT: Prints the tool and standard versions.
// CEP:WHY: CEP&CC 50.1 requires a version option.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: CI option checks.
// CEP:SECURITY: none.
void print_version(const Configuration& config) {
    std::cout << "cep_lint " << kToolVersion << " (CEP&CC " << config.standard_version << ")"
              << std::endl;
}

}  // namespace cep_lint
