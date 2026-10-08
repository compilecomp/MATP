// CEP:FILE: tools/cep_lint/src/selftest.cpp
// CEP:WHAT: Self-test runner: executes the scenarios in tools/cep_lint/tests/manifest.json, materializes their inline files into a private temporary directory, lints them, and compares exact expected violation counts per rule.
// CEP:WHY: CEP&CC 50.6 gate 3 requires every scenario to pass with exact expected counts; the runner is the executable proof that the primitives detect each violation class.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false when any scenario fails or the manifest is malformed; prints one PASS/FAIL line per scenario.
// CEP:ASSUMES: the manifest path is given by main.
// CEP:COST: O(scenarios x files x rules).
// CEP:EVIDENCE: CI gate and the 50.6 self-verification gate.
// CEP:SECURITY: manifest is repository-trusted; materialized files are written under a private temporary directory created with mkdtemp.

#include <algorithm>
#include <dirent.h>
#include <fstream>
#include <iostream>
#include <sys/stat.h>
#include <unistd.h>

#include "checks.hpp"
#include "engine.hpp"
#include "json.hpp"

namespace cep_lint {

// CEP:WHAT: Prints a self-test bootstrap failure.
// CEP:WHY: Mirrors the engine bootstrap reporting for manifest problems.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: self-test failures.
// CEP:SECURITY: none.
void report_bootstrap_selftest(const std::string& detail) {
    std::cerr << "CEP-LINT-BOOT-1: " << detail << std::endl;
}

// CEP:WHAT: Recursively removes a directory tree.
// CEP:WHY: The self-test cleans up its materialized files; paths are only those created by the runner itself.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: ignores individual removal failures (best effort; temporary directory).
// CEP:ASSUMES: the path is the runner's own temporary directory.
// CEP:COST: O(tree).
// CEP:EVIDENCE: self-test cleanup.
// CEP:SECURITY: never called with a path outside the mkdtemp result.
void rmdir_recursive(const std::string& path) {
    DIR* directory = opendir(path.c_str());
    if (directory == nullptr) {
        return;
    }
    struct dirent* entry = readdir(directory);
    while (entry != nullptr) {
        std::string name = entry->d_name;
        if (name != "." && name != "..") {
            std::string child = path + "/" + name;
            struct stat info;
            if (stat(child.c_str(), &info) == 0 && S_ISDIR(info.st_mode)) {
                rmdir_recursive(child);
            } else {
                unlink(child.c_str());
            }
        }
        entry = readdir(directory);
    }
    closedir(directory);
    rmdir(path.c_str());
}

// CEP:WHAT: Runs the self-test manifest at the given path under the given configuration.
// CEP:WHY: Entry point from main for --self-test (CEP&CC 50.6).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false on any scenario failure or manifest problem.
// CEP:ASSUMES: configuration already loaded.
// CEP:COST: O(scenarios).
// CEP:EVIDENCE: CI self-test gate.
// CEP:SECURITY: repository-trusted manifest; private temporary directory.
bool run_self_test(const Configuration& config, const std::string& manifest_path) {
    std::string text;
    if (!read_file(manifest_path, text)) {
        report_bootstrap_selftest("cannot read manifest " + manifest_path);
        return false;
    }
    JsonError error;
    auto parsed = json_parse(text, error);
    if (!parsed.second) {
        report_bootstrap_selftest(
            "manifest parse failure at line " + std::to_string(error.line) + ": " + error.message);
        return false;
    }
    const JsonValue* scenarios = parsed.first.find("scenarios");
    if (scenarios == nullptr || scenarios->get_kind() != JsonValue::Kind::Array) {
        report_bootstrap_selftest("manifest is missing the scenarios array");
        return false;
    }
    char template_path[] = "/tmp/cep_lint_selftest_XXXXXX";
    char* made = mkdtemp(template_path);
    if (made == nullptr) {
        report_bootstrap_selftest("cannot create temporary directory");
        return false;
    }
    std::string root = made;
    bool all_ok = true;
    for (const JsonValue& scenario : scenarios->as_array()) {
        const JsonValue* name = scenario.find("name");
        const JsonValue* files = scenario.find("files");
        const JsonValue* expected = scenario.find("expected_findings");
        if (name == nullptr || files == nullptr || expected == nullptr) {
            report_bootstrap_selftest("scenario is missing name, files, or expected_findings");
            all_ok = false;
            continue;
        }
        std::vector<std::pair<std::string, std::string>> written;
        for (const auto& member : files->as_object()) {
            std::string target = root + "/" + member.first;
            std::ofstream stream(target, std::ios::binary);
            stream << member.second.as_string();
            stream.close();
            written.emplace_back(target, member.first);
        }
        std::vector<Finding> all;
        for (const auto& entry : written) {
            std::string body;
            if (!read_file(entry.first, body)) {
                report_bootstrap_selftest("cannot read back materialized file " + entry.first);
                all_ok = false;
                continue;
            }
            std::vector<Finding> findings = lint_text(config, entry.first, body);
            all.insert(all.end(), findings.begin(), findings.end());
        }
        bool scenario_ok = true;
        std::vector<std::string> checked_rules;
        for (const JsonValue& expectation : expected->as_array()) {
            const JsonValue* rule = expectation.find("rule");
            const JsonValue* count = expectation.find("count");
            if (rule == nullptr || count == nullptr) {
                continue;
            }
            std::size_t actual = 0;
            for (const Finding& finding : all) {
                if (finding.rule == rule->as_string()) {
                    actual += 1;
                }
            }
            std::size_t wanted = static_cast<std::size_t>(count->as_number());
            if (actual != wanted) {
                std::cout << "FAIL " << name->as_string() << ": rule " << rule->as_string()
                          << " expected " << wanted << " findings, got " << actual << std::endl;
                scenario_ok = false;
            }
            checked_rules.push_back(rule->as_string());
        }
        for (const auto& entry : config.rules) {
            if (entry.first == "CEP-LINT-DOC-SYNC") {
                continue;  // document coverage is not exercised per scenario file.
            }
            if (std::find(checked_rules.begin(), checked_rules.end(), entry.first)
                != checked_rules.end()) {
                continue;
            }
            std::size_t actual = 0;
            for (const Finding& finding : all) {
                if (finding.rule == entry.first) {
                    actual += 1;
                }
            }
            if (actual != 0) {
                std::cout << "FAIL " << name->as_string() << ": rule " << entry.first
                          << " produced " << actual << " unexpected findings" << std::endl;
                scenario_ok = false;
            }
        }
        if (scenario_ok) {
            std::cout << "PASS " << name->as_string() << std::endl;
        } else {
            all_ok = false;
        }
    }
    rmdir_recursive(root);
    return all_ok;
}

}  // namespace cep_lint
