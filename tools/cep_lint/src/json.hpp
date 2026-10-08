// CEP:FILE: tools/cep_lint/src/json.hpp
// CEP:WHAT: Minimal in-house JSON value model, parser, and serializer for cep_lint configuration and self-test manifests.
// CEP:WHY: CEP&CC 22.11 supply-chain rules require controlled dependencies; the linter has zero third-party dependencies by design, so it owns a small audited JSON implementation instead of vendoring one.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: parse returns a coded error (file, line, column) on malformed input; never throws, never allocates unboundedly on well-formed bounded input.
// CEP:ASSUMES: Input files are repository-trusted (CEP-2 configuration); object key order is preserved for deterministic serialization.
// CEP:COST: offline tool; O(n) parse in input size.
// CEP:EVIDENCE: self-test manifest tools/cep_lint/tests/manifest.json parses with this module.
// CEP:SECURITY: input is repository-trusted; nesting depth is bounded at kMaxJsonDepth to prevent stack exhaustion (CEP&CC 22.10).

#pragma once

#include <cstddef>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace cep_lint {

// CEP:WHAT: JSON parse/report error with position information.
// CEP:WHY: CEP&CC 50.4 bootstrap error 2 requires JSON parse failures to report file, line, and column.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; a value type.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: engine bootstrap error reporting.
// CEP:SECURITY: none.
struct JsonError {
    /// CEP:WHAT: Human-readable description.
    std::string message;
    /// CEP:WHAT: One-based line of the error.
    std::size_t line;
    /// CEP:WHAT: One-based column of the error.
    std::size_t column;
};

// CEP:WHAT: Parsed JSON value: null, boolean, number, string, array, or object.
// CEP:WHY: The configuration and manifest schema needs the full JSON value space.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; a value type.
// CEP:ASSUMES: none.
// CEP:COST: value semantics with shared children.
// CEP:EVIDENCE: used by config and selftest modules.
// CEP:SECURITY: none.
class JsonValue {
public:
    // CEP:WHAT: Value kind discriminant.
    // CEP:WHY: Tagged dispatch without RTTI (CEP&CC 5.1 bans RTTI in hot code; tooling keeps the same discipline for auditability).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser and accessors.
    // CEP:SECURITY: none.
    enum class Kind { Null, Boolean, Number, String, Array, Object };

    // CEP:WHAT: Constructs a null value.
    // CEP:WHY: Default construction.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    JsonValue() : kind(Kind::Null), boolean_value(false), number_value(0.0) {}

    // CEP:WHAT: Returns the value kind.
    // CEP:WHY: Discriminated access.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: accessors.
    // CEP:SECURITY: none.
    Kind get_kind() const { return kind; }

    // CEP:WHAT: Returns the boolean payload.
    // CEP:WHY: Typed accessor.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; returns false on kind mismatch (tool code checks kinds).
    // CEP:ASSUMES: caller checked the kind.
    // CEP:COST: constant.
    // CEP:EVIDENCE: config booleans.
    // CEP:SECURITY: none.
    bool as_boolean() const { return boolean_value; }

    // CEP:WHAT: Returns the number payload.
    // CEP:WHY: Typed accessor.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; returns zero on kind mismatch.
    // CEP:ASSUMES: caller checked the kind.
    // CEP:COST: constant.
    // CEP:EVIDENCE: severities and counts.
    // CEP:SECURITY: none.
    double as_number() const { return number_value; }

    // CEP:WHAT: Returns the string payload.
    // CEP:WHY: Typed accessor.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; returns empty on kind mismatch.
    // CEP:ASSUMES: caller checked the kind.
    // CEP:COST: constant.
    // CEP:EVIDENCE: patterns and messages.
    // CEP:SECURITY: none.
    const std::string& as_string() const { return string_value; }

    // CEP:WHAT: Returns the array payload.
    // CEP:WHY: Typed accessor.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; returns empty on kind mismatch.
    // CEP:ASSUMES: caller checked the kind.
    // CEP:COST: constant.
    // CEP:EVIDENCE: token lists and rule arrays.
    // CEP:SECURITY: none.
    const std::vector<JsonValue>& as_array() const { return array_value; }

    // CEP:WHAT: Returns the object payload.
    // CEP:WHY: Typed accessor preserving key insertion order.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; returns empty on kind mismatch.
    // CEP:ASSUMES: caller checked the kind.
    // CEP:COST: constant.
    // CEP:EVIDENCE: rule objects.
    // CEP:SECURITY: none.
    const std::vector<std::pair<std::string, JsonValue>>& as_object() const { return object_value; }

    // CEP:WHAT: Looks up an object member by key.
    // CEP:WHY: Config access; returns nullptr when absent so callers can require keys explicitly.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(members).
    // CEP:EVIDENCE: config loader.
    // CEP:SECURITY: none.
    const JsonValue* find(const std::string& key) const;

    // CEP:WHAT: Makes a boolean value.
    // CEP:WHY: Builder for the self-test manifest writer.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: selftest.
    // CEP:SECURITY: none.
    static JsonValue make_boolean(bool value);

    // CEP:WHAT: Makes a number value.
    // CEP:WHY: Builder.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: selftest.
    // CEP:SECURITY: none.
    static JsonValue make_number(double value);

    // CEP:WHAT: Makes a string value.
    // CEP:WHY: Builder.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: selftest.
    // CEP:SECURITY: none.
    static JsonValue make_string(std::string value);

    // CEP:WHAT: Makes an array value.
    // CEP:WHY: Builder.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: selftest.
    // CEP:SECURITY: none.
    static JsonValue make_array(std::vector<JsonValue> value);

    // CEP:WHAT: Makes an object value.
    // CEP:WHY: Builder.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: selftest.
    // CEP:SECURITY: none.
    static JsonValue make_object(std::vector<std::pair<std::string, JsonValue>> value);

private:
    Kind kind;
    bool boolean_value;
    double number_value;
    std::string string_value;
    std::vector<JsonValue> array_value;
    std::vector<std::pair<std::string, JsonValue>> object_value;
};

// CEP:WHAT: Maximum JSON nesting depth accepted by the parser.
// CEP:WHY: Bounds recursion on adversarial input (CEP&CC 22.10 unbounded recursion ban); a named constant per CEP&CC 11.3.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: deeper input is a parse error.
// CEP:ASSUMES: repository-trusted files are far shallower.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: parser depth check.
// CEP:SECURITY: stack-exhaustion mitigation.
inline constexpr std::size_t kMaxJsonDepth = 64;

// CEP:WHAT: Parses a JSON document from text.
// CEP:WHY: Configuration and manifest loading.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: Returns JsonError with position on malformed input; accepts the RFC 8259 subset used by the configuration (objects, arrays, strings with escapes, numbers, booleans, null).
// CEP:ASSUMES: repository-trusted input.
// CEP:COST: O(n).
// CEP:EVIDENCE: config loader and selftest.
// CEP:SECURITY: depth-bounded recursion.
std::pair<JsonValue, bool> json_parse(const std::string& text, JsonError& error);

// CEP:WHAT: Serializes a value back to JSON text.
// CEP:WHY: Debug output and deterministic self-test comparisons.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(size).
// CEP:EVIDENCE: selftest.
// CEP:SECURITY: none.
std::string json_serialize(const JsonValue& value);

}  // namespace cep_lint
