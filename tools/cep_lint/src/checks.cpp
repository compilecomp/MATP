// CEP:FILE: tools/cep_lint/src/checks.cpp
// CEP:WHAT: Implementation of the nine check primitives.
// CEP:WHY: See checks.hpp; every rule in .cep/cep_lint.json maps onto one primitive here, and nothing else in the engine interprets rule semantics.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: primitives never throw on well-formed configuration.
// CEP:ASSUMES: configuration validated at load (regex compiled, severities in range).
// CEP:COST: O(lines) per primitive.
// CEP:EVIDENCE: tools/cep_lint/tests/manifest.json scenarios.
// CEP:SECURITY: none.

#include "checks.hpp"

#include <algorithm>
#include <sstream>
#include <cctype>
#include <regex>

namespace cep_lint {

// CEP:WHAT: Extracts a CEP field value from comment lines.
// CEP:WHY: Schema checks parse 'CEP:FIELD: value' lines; one parser keeps the grammar in one place.
// CEP:STATUS: complete
// CEP:FAILURE: returns an empty string when the field is absent.
// CEP:ASSUMES: none.
// CEP:COST: O(block lines).
// CEP:EVIDENCE: comment_block_schema scenarios.
// CEP:SECURITY: none.
std::string cep_field(const std::vector<std::string>& lines, const std::string& field) {
    const std::string prefix = "CEP:" + field + ":";
    for (const std::string& line : lines) {
        if (line.rfind(prefix, 0) == 0) {
            return trim(line.substr(prefix.size()));
        }
    }
    return "";
}

// CEP:WHAT: Reads a string-list parameter.
// CEP:WHY: Shared parameter decoding.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns empty on absence or type mismatch.
// CEP:ASSUMES: none.
// CEP:COST: O(list).
// CEP:EVIDENCE: primitives.
// CEP:SECURITY: none.
std::vector<std::string> param_strings(const JsonValue& parameters, const std::string& key) {
    std::vector<std::string> out;
    const JsonValue* value = parameters.find(key);
    if (value == nullptr || value->get_kind() != JsonValue::Kind::Array) {
        return out;
    }
    for (const JsonValue& item : value->as_array()) {
        if (item.get_kind() == JsonValue::Kind::String) {
            out.push_back(item.as_string());
        }
    }
    return out;
}

// CEP:WHAT: Reads a numeric-list parameter.
// CEP:WHY: Allow-list decoding.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns empty on absence or mismatch.
// CEP:ASSUMES: none.
// CEP:COST: O(list).
// CEP:EVIDENCE: numeric_literal_policy.
// CEP:SECURITY: none.
std::vector<double> param_numbers(const JsonValue& parameters, const std::string& key) {
    std::vector<double> out;
    const JsonValue* value = parameters.find(key);
    if (value == nullptr || value->get_kind() != JsonValue::Kind::Array) {
        return out;
    }
    for (const JsonValue& item : value->as_array()) {
        if (item.get_kind() == JsonValue::Kind::Number) {
            out.push_back(item.as_number());
        }
    }
    return out;
}

// CEP:WHAT: Reads a string parameter.
// CEP:WHY: Single-value decoding.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns empty default on absence.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: primitives.
// CEP:SECURITY: none.
std::string param_string(const JsonValue& parameters, const std::string& key, const std::string& fallback) {
    const JsonValue* value = parameters.find(key);
    if (value == nullptr || value->get_kind() != JsonValue::Kind::String) {
        return fallback;
    }
    return value->as_string();
}

// CEP:WHAT: Returns true when a numeric literal is in the allowed value list.
// CEP:WHY: The magic-number allow list is numeric, so '0x0' and '0' compare equal (CEP&CC 50.3).
// CEP:STATUS: complete
// CEP:FAILURE: returns false for unparseable digit runs.
// CEP:ASSUMES: none.
// CEP:COST: O(list).
// CEP:EVIDENCE: magic-number scenarios.
// CEP:SECURITY: none.
bool number_allowed(const std::string& digits, const std::vector<double>& allowed) {
    if (digits.empty()) {
        return false;
    }
    try {
        double value = std::stod(digits);
        for (double candidate : allowed) {
            if (value == candidate) {
                return true;
            }
        }
    } catch (const std::exception&) {
        return false;
    }
    return false;
}

// CEP:WHAT: Validates comment-block schemas per the configured mode (file header, status values, stub requirements).
// CEP:WHY: CEP&CC 50.3 defines this primitive for three rules; one implementation keeps the modes consistent.
// CEP:STATUS: complete
// CEP:FAILURE: never throws; unknown modes return no findings (configuration error surfaces elsewhere).
// CEP:ASSUMES: configuration validated at load.
// CEP:COST: O(comment blocks).
// CEP:EVIDENCE: header, status, and stub scenarios in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_comment_block_schema(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string mode = param_string(rule.parameters, "mode", "file_header");
    if (mode == "file_header") {
        const std::vector<std::string> required = param_strings(rule.parameters, "required_fields");
        const std::string class_field = param_string(rule.parameters, "class_field", "CEP:CLASS:");
        const std::vector<std::string> allowed = param_strings(rule.parameters, "allowed_classes");
        const double max_start = [&]() {
            const JsonValue* value = rule.parameters.find("max_start_line");
            return value != nullptr && value->get_kind() == JsonValue::Kind::Number
                ? value->as_number()
                : 1.0;
        }();
        if (file.comment_blocks().empty()
            || static_cast<double>(file.comment_blocks().front().start_line) > max_start) {
            Finding finding;
            finding.file = file.path();
            finding.line = 1;
            finding.rule = rule.name;
            finding.severity = rule.severity;
            finding.message = "missing CEP file header block at the top of the file";
            findings.push_back(finding);
            return findings;
        }
        const CommentBlock& header = file.comment_blocks().front();
        for (const std::string& field : required) {
            if (cep_field(header.lines, field).empty()) {
                Finding finding;
                finding.file = file.path();
                finding.line = header.start_line;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "file header is missing " + field;
                findings.push_back(finding);
            }
        }
        const std::string declared = cep_field(header.lines, class_field.substr(4, class_field.size() - 5));
        if (!declared.empty() && !allowed.empty()
            && std::find(allowed.begin(), allowed.end(), declared) == allowed.end()) {
            Finding finding;
            finding.file = file.path();
            finding.line = header.start_line;
            finding.rule = rule.name;
            finding.severity = rule.severity;
            finding.message = "declared class " + declared + " is not an allowed class";
            findings.push_back(finding);
        }
        return findings;
    }
    if (mode == "status_value") {
        const std::vector<std::string> allowed = param_strings(rule.parameters, "allowed_values");
        const std::string field = param_string(rule.parameters, "status_field", "STATUS");
        for (const CommentBlock& block : file.comment_blocks()) {
            const std::string value = cep_field(block.lines, field);
            if (value.empty()) {
                continue;
            }
            if (std::find(allowed.begin(), allowed.end(), value) == allowed.end()) {
                Finding finding;
                finding.file = file.path();
                finding.line = block.start_line;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "CEP:STATUS value '" + value + "' is not one of the allowed values";
                findings.push_back(finding);
            }
        }
        return findings;
    }
    if (mode == "stub_requirements") {
        const std::vector<std::string> statuses = param_strings(rule.parameters, "statuses");
        const std::vector<std::string> required = param_strings(rule.parameters, "required_fields");
        for (const CommentBlock& block : file.comment_blocks()) {
            const std::string status = cep_field(block.lines, "STATUS");
            if (std::find(statuses.begin(), statuses.end(), status) == statuses.end()) {
                continue;
            }
            for (const std::string& field : required) {
                if (cep_field(block.lines, field).empty()) {
                    Finding finding;
                    finding.file = file.path();
                    finding.line = block.start_line;
                    finding.rule = rule.name;
                    finding.severity = rule.severity;
                    finding.message = "comment block declaring a non-production status is missing " + field;
                    findings.push_back(finding);
                }
            }
        }
        return findings;
    }
    return findings;
}

// CEP:WHAT: Validates function definitions per the configured mode (block presence, stub bodies, naming, constant returns).
// CEP:WHY: CEP&CC 50.3 defines this primitive for four rules over the extracted definitions.
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: extraction succeeded for the checked definitions.
// CEP:COST: O(functions).
// CEP:EVIDENCE: function-policy scenarios in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_function_policy(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string mode = param_string(rule.parameters, "mode", "block");
    const double min_statements = [&]() {
        const JsonValue* value = rule.parameters.find("min_body_statements");
        return value != nullptr && value->get_kind() == JsonValue::Kind::Number
            ? value->as_number()
            : 2.0;
    }();
    if (mode == "block") {
        const std::vector<std::string> required = param_strings(rule.parameters, "required_fields");
        for (const FunctionDefinition& definition : file.functions()) {
            if (static_cast<double>(definition.statement_count) < min_statements) {
                continue;
            }
            if (definition.preceding_comment.empty()) {
                Finding finding;
                finding.file = file.path();
                finding.line = definition.line;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "function " + definition.name + " needs a preceding CEP comment block";
                findings.push_back(finding);
                continue;
            }
            for (const std::string& field : required) {
                if (cep_field(definition.preceding_comment, field).empty()) {
                    Finding finding;
                    finding.file = file.path();
                    finding.line = definition.line;
                    finding.rule = rule.name;
                    finding.severity = rule.severity;
                    finding.message = "function " + definition.name + " block is missing " + field;
                    findings.push_back(finding);
                }
            }
        }
        return findings;
    }
    if (mode == "stub_body") {
        const std::vector<std::string> suppressed = param_strings(rule.parameters, "suppress_statuses");
        const std::string field = param_string(rule.parameters, "suppress_status_field", "STATUS");
        for (const FunctionDefinition& definition : file.functions()) {
            if (!definition.body_empty) {
                continue;
            }
            // Constructors with initializer lists are not empty bodies; the initializer
            // line carries the member initialization before the brace.
            const std::string& brace_line = file.line(definition.line - 1);
            const std::size_t brace_at = brace_line.find('{');
            if (brace_at != std::string::npos
                && brace_line.substr(0, brace_at).find(':') != std::string::npos) {
                continue;
            }
            if (!definition.preceding_comment.empty()) {
                const std::string status = cep_field(definition.preceding_comment, field);
                if (std::find(suppressed.begin(), suppressed.end(), status) != suppressed.end()) {
                    continue;
                }
            }
            Finding finding;
            finding.file = file.path();
            finding.line = definition.line;
            finding.rule = rule.name;
            finding.severity = rule.severity;
            finding.message = "function " + definition.name + " has an empty body without a declared non-production status";
            findings.push_back(finding);
        }
        return findings;
    }
    if (mode == "naming") {
        const std::string pattern = param_string(rule.parameters, "name_pattern", "^[a-z][a-z0-9_]*$");
        const std::regex expression(pattern);
        for (const FunctionDefinition& definition : file.functions()) {
            if (definition.name.find('~') != std::string::npos
                || definition.name.find("operator") == 0
                || definition.name.find('<') != std::string::npos) {
                continue;
            }
            // Constructors carry the PascalCase class name by language convention
            // (CEP&CC 33.13 exempts special member functions): the name starts the
            // signature line or follows a Class:: qualifier.
            const std::string signature = trim(file.code_only_line(definition.line - 1));
            const bool starts_with_name = signature.rfind(definition.name + "(", 0) == 0;
            const std::string qualified = definition.name + "::" + definition.name + "(";
            const bool qualified_ctor = signature.find(qualified) != std::string::npos;
            if (starts_with_name || qualified_ctor) {
                continue;
            }
            if (!std::regex_match(definition.name, expression)) {
                Finding finding;
                finding.file = file.path();
                finding.line = definition.line;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "function name " + definition.name + " does not match " + pattern;
                findings.push_back(finding);
            }
        }
        return findings;
    }
    if (mode == "constant_return") {
        for (const FunctionDefinition& definition : file.functions()) {
            if (definition.statement_count != 1) {
                continue;
            }
            // The single statement is the body text between the first '{' and its '}'.
            std::string body;
            std::size_t scan = definition.line - 1;
            bool opened = false;
            while (scan < file.line_count()) {
                const std::string& code = file.code_only_line(scan);
                for (char character : code) {
                    if (!opened) {
                        if (character == '{') {
                            opened = true;
                        }
                        continue;
                    }
                    if (character == '}') {
                        scan = file.line_count();
                        break;
                    }
                    body.push_back(character);
                }
                scan += 1;
            }
            body = trim(body);
            if (body == "return true;" || body == "return false;" || body == "return nullptr;") {
                Finding finding;
                finding.file = file.path();
                finding.line = definition.line;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "function " + definition.name + " returns a constant";
                findings.push_back(finding);
            }
        }
        return findings;
    }
    return findings;
}

// CEP:WHAT: Applies a line-scoped regular expression to comment lines with an optional suppression pattern.
// CEP:WHY: Marker rules (anonymous work markers, marker text, commented code) share this mechanism.
// CEP:STATUS: complete
// CEP:FAILURE: never throws; expressions were validated at load.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: marker scenarios in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_comment_regex(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string pattern = param_string(rule.parameters, "pattern", "");
    if (pattern.empty()) {
        return findings;
    }
    const bool ignore_case = [&]() {
        const JsonValue* value = rule.parameters.find("icase");
        return value != nullptr && value->get_kind() == JsonValue::Kind::Boolean && value->as_boolean();
    }();
    const std::string suppression = param_string(rule.parameters, "suppression_pattern", "");
    auto flags = std::regex_constants::ECMAScript;
    if (ignore_case) {
        flags |= std::regex_constants::icase;
    }
    const std::regex expression(pattern, flags);
    std::regex suppression_expression;
    bool has_suppression = false;
    if (!suppression.empty()) {
        suppression_expression = std::regex(suppression, flags);
        has_suppression = true;
    }
    const std::string marker = file.is_python() ? "#" : "//";
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& raw = trim(file.line(index));
        if (raw.rfind(marker, 0) != 0) {
            continue;
        }
        if (has_suppression && std::regex_search(raw, suppression_expression)) {
            continue;
        }
        if (std::regex_search(raw, expression)) {
            Finding finding;
            finding.file = file.path();
            finding.line = index + 1;
            finding.rule = rule.name;
            finding.severity = rule.severity;
            finding.message = "comment line matches forbidden pattern " + pattern;
            findings.push_back(finding);
        }
    }
    return findings;
}

// CEP:WHAT: Applies a regular expression to the contents of string literals.
// CEP:WHY: Marker text must not leak into runtime messages (CEP&CC 50.3).
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: single-line literals.
// CEP:COST: O(lines).
// CEP:EVIDENCE: marker-text scenario in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_string_literal_regex(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string pattern = param_string(rule.parameters, "pattern", "");
    if (pattern.empty()) {
        return findings;
    }
    const bool ignore_case = [&]() {
        const JsonValue* value = rule.parameters.find("icase");
        return value != nullptr && value->get_kind() == JsonValue::Kind::Boolean && value->as_boolean();
    }();
    auto flags = std::regex_constants::ECMAScript;
    if (ignore_case) {
        flags |= std::regex_constants::icase;
    }
    const std::regex expression(pattern, flags);
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& raw = file.line(index);
        std::size_t quote = 0;
        while (quote < raw.size()) {
            if (raw[quote] == '"') {
                std::size_t end = quote + 1;
                while (end < raw.size() && raw[end] != '"') {
                    if (raw[end] == '\\') {
                        end += 1;
                    }
                    end += 1;
                }
                if (end < raw.size()) {
                    std::string literal = raw.substr(quote + 1, end - quote - 1);
                    if (std::regex_search(literal, expression)) {
                        Finding finding;
                        finding.file = file.path();
                        finding.line = index + 1;
                        finding.rule = rule.name;
                        finding.severity = rule.severity;
                        finding.message = "string literal matches forbidden pattern " + pattern;
                        findings.push_back(finding);
                        break;
                    }
                }
                quote = end + 1;
                continue;
            }
            quote += 1;
        }
    }
    return findings;
}

// CEP:WHAT: Flags magic numbers outside sanctioned constant, enum, assertion, or preprocessor contexts.
// CEP:WHY: CEP&CC Law 7 and section 11 ban hard-coded assumptions; identifiers embedding digits are skipped.
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: magic-number scenarios in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_numeric_literal_policy(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::vector<double> allowed = param_numbers(rule.parameters, "allowed_values");
    const std::vector<std::string> exempt = param_strings(rule.parameters, "exempt_contexts");
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& code = file.code_only_line(index);
        if (trim(code).empty()) {
            continue;
        }
        bool exempted = false;
        for (const std::string& context : exempt) {
            if (contains(code, context)) {
                exempted = true;
                break;
            }
        }
        if (exempted) {
            continue;
        }
        // Sanctioned contexts (CEP&CC 50.3): constant declarations (const, constexpr,
        // static), enum definitions and entries, assertions, and preprocessor lines.
        std::string statement = code;
        std::string trimmed_statement = trim(statement);
        // Rust enum entries can sit on lines without the enum keyword (doc comments
        // interleave), so the explicit discriminant form "Name = digits," is sanctioned.
        static const std::regex enum_entry_pattern(
            "^[A-Za-z_][A-Za-z0-9_]*[[:space:]]*=[[:space:]]*[0-9]+[[:space:]]*,?$");
        if (statement.find("const") != std::string::npos
            || statement.find("static") != std::string::npos
            || statement.find("enum") != std::string::npos
            || statement.find("assert") != std::string::npos
            || trimmed_statement.rfind('#', 0) == 0
            || std::regex_match(trimmed_statement, enum_entry_pattern)) {
            continue;
        }
        std::size_t position = 0;
        while (position < statement.size()) {
            char current = statement[position];
            if (std::isdigit(static_cast<unsigned char>(current)) == 0) {
                position += 1;
                continue;
            }
            // Digits embedded in identifiers (u32, 0x1F, base64) belong to the identifier.
            std::size_t start = position;
            while (start > 0
                && (std::isalnum(static_cast<unsigned char>(statement[start - 1])) != 0
                    || statement[start - 1] == '_')) {
                start -= 1;
            }
            std::size_t end = position;
            while (end < statement.size()
                && (std::isalnum(static_cast<unsigned char>(statement[end])) != 0
                    || statement[end] == '.' || statement[end] == '_')) {
                end += 1;
            }
            if (start != position) {
                position = end;
                continue;
            }
            std::string digits = statement.substr(position, end - position);
            if (!number_allowed(digits, allowed)) {
                Finding finding;
                finding.file = file.path();
                finding.line = index + 1;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "magic number " + digits + " outside a sanctioned context";
                findings.push_back(finding);
            }
            position = end;
        }
    }
    return findings;
}

// CEP:WHAT: Flags object-like macros that do not match the CEP_ prefix or include-guard patterns.
// CEP:WHY: CEP&CC 33.16 restricts macros; function-like macros are review-enforced (CEP&CC 50.3 limits).
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: macro scenario in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_macro_prefix_policy(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string name_pattern = param_string(rule.parameters, "name_pattern", "^CEP_[A-Z0-9_]+$");
    const std::string guard_pattern = param_string(rule.parameters, "guard_pattern", "^[A-Z0-9_]+_HPP$");
    const std::regex name_expression(name_pattern);
    const std::regex guard_expression(guard_pattern);
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& code = file.code_only_line(index);
        const std::string trimmed = trim(code);
        if (trimmed.rfind("#define", 0) != 0) {
            continue;
        }
        std::size_t name_start = trimmed.find_first_not_of(" \t", std::string("#define").size());
        if (name_start == std::string::npos) {
            continue;
        }
        std::size_t name_end = name_start;
        while (name_end < trimmed.size()
            && (std::isalnum(static_cast<unsigned char>(trimmed[name_end])) != 0
                || trimmed[name_end] == '_')) {
            name_end += 1;
        }
        std::string name = trimmed.substr(name_start, name_end - name_start);
        if (std::regex_match(name, name_expression) || std::regex_match(name, guard_expression)) {
            continue;
        }
        if (name_end < trimmed.size() && trimmed[name_end] == '(') {
            continue;  // function-like macros are review-enforced (documented limit).
        }
        Finding finding;
        finding.file = file.path();
        finding.line = index + 1;
        finding.rule = rule.name;
        finding.severity = rule.severity;
        finding.message = "macro " + name + " does not match the CEP_ prefix pattern";
        findings.push_back(finding);
    }
    return findings;
}

// CEP:WHAT: Flags banned tokens in code with comments and strings removed, using word boundaries.
// CEP:WHY: CEP&CC 50.3 HOT-BANNED exterminates the hot-path ban set on sight; boundary matching prevents identifier false positives.
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: class scoping was decided by the engine.
// CEP:COST: O(lines x tokens).
// CEP:EVIDENCE: hot-ban scenarios in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_banned_token_policy(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::vector<std::string> tokens = param_strings(rule.parameters, "tokens");
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& code = file.code_only_line(index);
        for (const std::string& token : tokens) {
            std::size_t position = code.find(token);
            while (position != std::string::npos) {
                char before = position == 0 ? ' ' : code[position - 1];
                char after = position + token.size() < code.size() ? code[position + token.size()] : ' ';
                bool word_before = std::isalnum(static_cast<unsigned char>(before)) != 0 || before == '_';
                bool word_after = std::isalnum(static_cast<unsigned char>(after)) != 0 || after == '_';
                bool token_is_word = !token.empty()
                    && (std::isalnum(static_cast<unsigned char>(token.back())) != 0
                        || token.back() == '_');
                bool boundary_ok = true;
                if (token_is_word) {
                    boundary_ok = !word_before && !word_after;
                }
                if (boundary_ok) {
                    Finding finding;
                    finding.file = file.path();
                    finding.line = index + 1;
                    finding.rule = rule.name;
                    finding.severity = rule.severity;
                    finding.message = "banned token " + token + " in hot-path class file";
                    findings.push_back(finding);
                    break;
                }
                position = code.find(token, position + 1);
            }
        }
    }
    return findings;
}

// CEP:WHAT: Applies a regular expression to code lines regardless of comment context.
// CEP:WHY: Empty-branch and empty-handler rules inspect structure, not comments.
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: empty-branch scenario in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_flat_code_regex(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string pattern = param_string(rule.parameters, "pattern", "");
    if (pattern.empty()) {
        return findings;
    }
    const std::regex expression(pattern);
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& code = file.code_only_line(index);
        if (std::regex_search(code, expression)) {
            Finding finding;
            finding.file = file.path();
            finding.line = index + 1;
            finding.rule = rule.name;
            finding.severity = rule.severity;
            finding.message = "code matches forbidden pattern " + pattern;
            findings.push_back(finding);
        }
    }
    return findings;
}

// CEP:WHAT: Flags type names introduced by struct, class, enum, trait, or type that are not PascalCase.
// CEP:WHY: CEP&CC 33.11 requires PascalCase type names without underscores.
// CEP:STATUS: complete
// CEP:FAILURE: never throws.
// CEP:ASSUMES: none.
// CEP:COST: O(lines).
// CEP:EVIDENCE: naming scenario in the self-test manifest.
// CEP:SECURITY: none.
std::vector<Finding> check_naming_type(const SourceFile& file, const RuleConfig& rule) {
    std::vector<Finding> findings;
    const std::string pattern = param_string(rule.parameters, "name_pattern", "^[A-Z][A-Za-z0-9]*$");
    const std::regex expression(pattern);
    const std::regex introducer(
        "(struct|class|enum\\s+class|enum\\s+struct|enum|trait|type)\\s+([A-Za-z_][A-Za-z0-9_]*)");
    for (std::size_t index = 0; index < file.line_count(); index += 1) {
        const std::string& code = file.code_only_line(index);
        auto begin = std::sregex_iterator(code.begin(), code.end(), introducer);
        for (auto it = begin; it != std::sregex_iterator(); ++it) {
            std::smatch match = *it;
            std::string name = match[2].str();
            // Only type introductions count: the name must be followed by a definition
            // or declaration terminator, not by a variable name (struct stat info;).
            const std::size_t after = static_cast<std::size_t>(match.position(2)) + name.size();
            const std::string tail = code.substr(after);
            const std::string tail_trimmed = trim(tail);
            if (!tail_trimmed.empty() && tail_trimmed[0] != '{' && tail_trimmed[0] != ';'
                && tail_trimmed[0] != ':' && tail_trimmed[0] != '<') {
                continue;
            }
            if (name.empty() || !std::regex_match(name, expression)) {
                Finding finding;
                finding.file = file.path();
                finding.line = index + 1;
                finding.rule = rule.name;
                finding.severity = rule.severity;
                finding.message = "type name " + name + " is not PascalCase without underscores";
                findings.push_back(finding);
            }
        }
    }
    return findings;
}

// CEP:WHAT: Compares the configured rule set against the standard document's rule headings and version line.
// CEP:WHY: CEP&CC 50.3 and Law 8: configuration and documentation must agree mechanically.
// CEP:STATUS: complete
// CEP:FAILURE: reports each drift as a severity-1 finding.
// CEP:ASSUMES: the standard document is readable.
// CEP:COST: O(document lines + rules).
// CEP:EVIDENCE: CI document-synchronization gate.
// CEP:SECURITY: none.
std::vector<Finding> check_doc_rule_coverage(
    const std::vector<std::pair<std::string, RuleConfig>>& rules,
    const std::string& document_text,
    const std::string& document_path,
    const std::string& configured_version) {
    std::vector<Finding> findings;
    const std::regex heading("^### Rule (CEP-LINT-[A-Z0-9-]+)", std::regex_constants::ECMAScript);
    std::vector<std::string> documented;
    std::istringstream document_stream(document_text);
    std::string document_line;
    while (std::getline(document_stream, document_line)) {
        std::smatch match;
        if (std::regex_match(document_line, match, heading)) {
            documented.push_back(match[1].str());
        }
    }
    std::vector<std::string> duplicates;
    std::vector<std::string> seen;
    for (const std::string& name : documented) {
        if (std::find(seen.begin(), seen.end(), name) != seen.end()) {
            duplicates.push_back(name);
        }
        seen.push_back(name);
    }
    for (const std::string& name : duplicates) {
        Finding finding;
        finding.file = document_path;
        finding.line = 1;
        finding.rule = "CEP-LINT-DOC-SYNC";
        finding.severity = 1;
        finding.message = "rule heading " + name + " appears more than once in the standard";
        findings.push_back(finding);
    }
    for (const auto& entry : rules) {
        if (entry.first == "CEP-LINT-DOC-SYNC") {
            continue;
        }
        if (std::find(documented.begin(), documented.end(), entry.first) == documented.end()) {
            Finding finding;
            finding.file = document_path;
            finding.line = 1;
            finding.rule = "CEP-LINT-DOC-SYNC";
            finding.severity = 1;
            finding.message = "configured rule " + entry.first + " has no section in the standard";
            findings.push_back(finding);
        }
    }
    for (const std::string& name : documented) {
        bool configured = false;
        for (const auto& entry : rules) {
            if (entry.first == name) {
                configured = true;
                break;
            }
        }
        if (!configured) {
            Finding finding;
            finding.file = document_path;
            finding.line = 1;
            finding.rule = "CEP-LINT-DOC-SYNC";
            finding.severity = 1;
            finding.message = "documented rule " + name + " is missing from the configuration";
            findings.push_back(finding);
        }
    }
    const std::regex version("^Version: \\*\\*(.+)\\*\\*$", std::regex_constants::ECMAScript);
    std::smatch version_match;
    std::string document_version;
    std::istringstream version_stream(document_text);
    std::string version_line;
    while (std::getline(version_stream, version_line)) {
        const std::string trimmed_version_line = trim(version_line);
        if (std::regex_match(trimmed_version_line, version_match, version)) {
            document_version = version_match[1].str();
            break;
        }
    }
    if (document_version != configured_version) {
        Finding finding;
        finding.file = document_path;
        finding.line = 1;
        finding.rule = "CEP-LINT-DOC-SYNC";
        finding.severity = 1;
        finding.message = "standard version " + document_version + " differs from configured version "
            + configured_version;
        findings.push_back(finding);
    }
    return findings;
}

}  // namespace cep_lint
