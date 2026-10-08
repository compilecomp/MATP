// CEP:FILE: tools/cep_lint/src/checks.hpp
// CEP:WHAT: Check primitives for cep_lint: the nine mechanisms (comment_block_schema, function_policy, comment_regex, string_literal_regex, numeric_literal_policy, macro_prefix_policy, banned_token_policy, flat_code_regex, doc_rule_coverage) driven entirely by rule configuration.
// CEP:WHY: CEP&CC 50 requires the engine to contain mechanism only; every pattern, threshold, and message lives in .cep/cep_lint.json and each rule maps onto exactly one of these primitives.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: primitives return findings, never throw; configuration shape errors are reported by the config loader before any primitive runs.
// CEP:ASSUMES: files were scanned by SourceFile; regular expressions in configuration are valid (validated at load).
// CEP:COST: O(lines) per primitive per file, except doc_rule_coverage which is O(rules + document headings).
// CEP:EVIDENCE: self-test scenarios cover every primitive and mode.
// CEP:SECURITY: repository-trusted configuration only.

#pragma once

#include <string>
#include <vector>

#include "json.hpp"
#include "source.hpp"

namespace cep_lint {

// CEP:WHAT: One lint finding.
// CEP:WHY: The engine sorts findings by (file, line, rule, message) for deterministic output (CEP&CC 50.1).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; a value type.
// CEP:ASSUMES: none.
// CEP:COST: value semantics.
// CEP:EVIDENCE: engine reporting.
// CEP:SECURITY: none.
struct Finding {
    /// CEP:WHAT: File path as scanned.
    std::string file;
    /// CEP:WHAT: One-based line number.
    std::size_t line;
    /// CEP:WHAT: Rule identifier (CEP-LINT-*).
    std::string rule;
    /// CEP:WHAT: Severity 0-3 (CEP&CC 34.2 classes).
    int severity;
    /// CEP:WHAT: Human-readable message.
    std::string message;
};

// CEP:WHAT: Rule configuration: identity plus primitive parameters.
// CEP:WHY: The data-driven bridge between .cep/cep_lint.json and the primitives.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; validated at load.
// CEP:ASSUMES: none.
// CEP:COST: value semantics.
// CEP:EVIDENCE: config loader.
// CEP:SECURITY: none.
struct RuleConfig {
    /// CEP:WHAT: Rule identifier.
    std::string name;
    /// CEP:WHAT: Severity 0-3.
    int severity;
    /// CEP:WHAT: Primitive name.
    std::string check;
    /// CEP:WHAT: Raw parameter object from configuration.
    JsonValue parameters;
};

// CEP:WHAT: Extracts a CEP field value from comment lines.
// CEP:WHY: Shared helper for schema checks ("CEP:FIELD: value" parsing).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns empty when absent.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: comment_block_schema.
// CEP:SECURITY: none.
std::string cep_field(const std::vector<std::string>& lines, const std::string& field);

// CEP:WHAT: Runs the comment_block_schema primitive.
// CEP:WHY: File headers, status values, and stub requirements (CEP&CC 50.3).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(comment blocks).
// CEP:EVIDENCE: the file-header, status-value, and stub-declaration rules.
// CEP:SECURITY: none.
std::vector<Finding> check_comment_block_schema(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the function_policy primitive.
// CEP:WHY: Function blocks, stub bodies, naming, and constant returns (CEP&CC 50.3).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: function extraction succeeded for the target definition.
// CEP:COST: O(functions).
// CEP:EVIDENCE: the function-block, stub-body, naming, and constant-return rules.
// CEP:SECURITY: none.
std::vector<Finding> check_function_policy(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the comment_regex primitive.
// CEP:WHY: Line-scoped comment patterns with suppression (anonymous work markers, marker text, commented code).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: the marker-owner, marker-comment, and commented-code rules.
// CEP:SECURITY: none.
std::vector<Finding> check_comment_regex(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the string_literal_regex primitive.
// CEP:WHY: Placeholder markers must not leak into runtime messages.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: the marker-text rule.
// CEP:SECURITY: none.
std::vector<Finding> check_string_literal_regex(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the numeric_literal_policy primitive.
// CEP:WHY: Magic-number ban with sanctioned contexts (CEP&CC Law 7, 11).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: MAGIC-NUMBER rule.
// CEP:SECURITY: none.
std::vector<Finding> check_numeric_literal_policy(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the macro_prefix_policy primitive.
// CEP:WHY: Macro naming (CEP&CC 33.16).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: MACRO-PREFIX rule.
// CEP:SECURITY: none.
std::vector<Finding> check_macro_prefix_policy(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the banned_token_policy primitive.
// CEP:WHY: Hot-path ban sets checked on code with comments and strings removed (CEP&CC 50.3).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: class scoping was decided by the engine.
// CEP:COST: O(lines x tokens).
// CEP:EVIDENCE: HOT-BANNED rule.
// CEP:SECURITY: none.
std::vector<Finding> check_banned_token_policy(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the flat_code_regex primitive.
// CEP:WHY: Code-level patterns regardless of comment context (empty branches, empty handlers).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: the empty-handler and empty-branch rules.
// CEP:SECURITY: none.
std::vector<Finding> check_flat_code_regex(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Runs the doc_rule_coverage primitive.
// CEP:WHY: The standard document and the configuration must agree (CEP&CC 50.3 DOC-SYNC, Law 8).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the standard document is readable.
// CEP:COST: O(document + rules).
// CEP:EVIDENCE: the document-synchronization rule.
// CEP:SECURITY: none.
std::vector<Finding> check_doc_rule_coverage(
    const std::vector<std::pair<std::string, RuleConfig>>& rules,
    const std::string& document_text,
    const std::string& document_path,
    const std::string& configured_version);

// CEP:WHAT: Runs the naming-type check (flat_code_regex with name validation).
// CEP:WHY: Type-name rules need identifier extraction beyond plain regex (CEP&CC 33.11).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: NAMING-TYPE rule.
// CEP:SECURITY: none.
std::vector<Finding> check_naming_type(const SourceFile& file, const RuleConfig& rule);

// CEP:WHAT: Returns true when a numeric string is in the allowed value list.
// CEP:WHY: Shared helper for the magic-number allow list.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(list).
// CEP:EVIDENCE: numeric_literal_policy.
// CEP:SECURITY: none.
bool number_allowed(const std::string& digits, const std::vector<double>& allowed);

}  // namespace cep_lint
