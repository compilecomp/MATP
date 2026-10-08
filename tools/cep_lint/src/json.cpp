// CEP:FILE: tools/cep_lint/src/json.cpp
// CEP:WHAT: Implementation of the in-house JSON parser and serializer.
// CEP:WHY: See json.hpp; the implementation is recursive descent with depth bounding and exact position tracking for CEP&CC 50.4 bootstrap error 2.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: parse errors carry line and column; serializer never fails.
// CEP:ASSUMES: repository-trusted input.
// CEP:COST: O(n).
// CEP:EVIDENCE: self-test manifest round trip.
// CEP:SECURITY: depth bound prevents stack exhaustion.

#include "json.hpp"

namespace cep_lint {

// CEP:WHAT: Internal cursor over the input text with position tracking.
// CEP:WHY: Exact error positions require a cursor that knows its line and column.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant per advance.
// CEP:EVIDENCE: parser error positions.
// CEP:SECURITY: none.
class JsonCursor {
public:
    // CEP:WHAT: Constructs a cursor over text.
    // CEP:WHY: Parser entry state.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    explicit JsonCursor(const std::string& source)
        : text(source), position(0), line(1), column(1) {}

    // CEP:WHAT: Returns the current character or NUL at end.
    // CEP:WHY: Lookahead.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    char peek() const { return position < text.size() ? text[position] : '\0'; }

    // CEP:WHAT: Returns the character at an offset from the cursor.
    // CEP:WHY: String escape handling.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    char peek(std::size_t offset) const {
        return position + offset < text.size() ? text[position + offset] : '\0';
    }

    // CEP:WHAT: Consumes one character, maintaining line and column.
    // CEP:WHY: Cursor advance.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    void advance() {
        if (position < text.size()) {
            if (text[position] == '\n') {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
            position += 1;
        }
    }

    // CEP:WHAT: Reports whether the cursor is at end.
    // CEP:WHY: Termination.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: parser.
    // CEP:SECURITY: none.
    bool at_end() const { return position >= text.size(); }

    // CEP:WHAT: Skips whitespace and JSON comments.
    // CEP:WHY: Lenient whitespace handling; comments are accepted because configuration files may carry them.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: linear in skipped span.
    // CEP:EVIDENCE: configuration files with // comments.
    // CEP:SECURITY: none.
    void skip_insignificant() {
        while (!at_end()) {
            char current = peek();
            if (current == ' ' || current == '\t' || current == '\r' || current == '\n') {
                advance();
                continue;
            }
            if (current == '/' && peek(1) == '/') {
                while (!at_end() && peek() != '\n') {
                    advance();
                }
                continue;
            }
            break;
        }
    }

    // CEP:WHAT: Current one-based line.
    // CEP:WHY: Error reporting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: JsonError.
    // CEP:SECURITY: none.
    std::size_t current_line() const { return line; }

    // CEP:WHAT: Current one-based column.
    // CEP:WHY: Error reporting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: JsonError.
    // CEP:SECURITY: none.
    std::size_t current_column() const { return column; }

private:
    const std::string& text;
    std::size_t position;
    std::size_t line;
    std::size_t column;
};

// CEP:WHAT: Parses a value at the cursor.
// CEP:WHY: Recursive descent core.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false and fills error on malformed input.
// CEP:ASSUMES: cursor positioned at a value start.
// CEP:COST: O(remaining).
// CEP:EVIDENCE: json_parse.
// CEP:SECURITY: depth bounded.
bool parse_value(JsonCursor& cursor, JsonValue& out, JsonError& error, std::size_t depth);

// CEP:WHAT: Parses a JSON string literal including escapes.
// CEP:WHY: String payload extraction.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false on unterminated or invalid escapes.
// CEP:ASSUMES: cursor at opening quote.
// CEP:COST: O(length).
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
bool parse_string_literal(JsonCursor& cursor, std::string& out, JsonError& error) {
    cursor.advance();  // consume the opening quote
    std::string buffer;
    while (!cursor.at_end()) {
        char current = cursor.peek();
        if (current == '"') {
            cursor.advance();
            out = buffer;
            return true;
        }
        if (current == '\\') {
            cursor.advance();
            char escaped = cursor.peek();
            switch (escaped) {
                case '"': buffer.push_back('"'); break;
                case '\\': buffer.push_back('\\'); break;
                case '/': buffer.push_back('/'); break;
                case 'b': buffer.push_back('\b'); break;
                case 'f': buffer.push_back('\f'); break;
                case 'n': buffer.push_back('\n'); break;
                case 'r': buffer.push_back('\r'); break;
                case 't': buffer.push_back('\t'); break;
                case 'u': {
                    unsigned int code = 0;
                    for (int digit = 0; digit < 4; digit += 1) {
                        cursor.advance();
                        char hex = cursor.peek();
                        code *= 16;
                        if (hex >= '0' && hex <= '9') {
                            code += static_cast<unsigned int>(hex - '0');
                        } else if (hex >= 'a' && hex <= 'f') {
                            code += static_cast<unsigned int>(hex - 'a' + 10);
                        } else if (hex >= 'A' && hex <= 'F') {
                            code += static_cast<unsigned int>(hex - 'A' + 10);
                        } else {
                            error.message = "invalid \\u escape";
                            error.line = cursor.current_line();
                            error.column = cursor.current_column();
                            return false;
                        }
                    }
                    if (code < 0x80) {
                        buffer.push_back(static_cast<char>(code));
                    } else if (code < 0x800) {
                        buffer.push_back(static_cast<char>(0xC0 | (code >> 6)));
                        buffer.push_back(static_cast<char>(0x80 | (code & 0x3F)));
                    } else {
                        buffer.push_back(static_cast<char>(0xE0 | (code >> 12)));
                        buffer.push_back(static_cast<char>(0x80 | ((code >> 6) & 0x3F)));
                        buffer.push_back(static_cast<char>(0x80 | (code & 0x3F)));
                    }
                    break;
                }
                default:
                    error.message = "invalid escape character";
                    error.line = cursor.current_line();
                    error.column = cursor.current_column();
                    return false;
            }
            cursor.advance();
            continue;
        }
        buffer.push_back(current);
        cursor.advance();
    }
    error.message = "unterminated string";
    error.line = cursor.current_line();
    error.column = cursor.current_column();
    return false;
}

// CEP:WHAT: Parses a numeric literal.
// CEP:WHY: Number payload extraction.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: returns false when no digits are present.
// CEP:ASSUMES: cursor at a number start.
// CEP:COST: O(digits).
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
bool parse_number_literal(JsonCursor& cursor, JsonValue& out, JsonError& error) {
    std::string buffer;
    if (cursor.peek() == '-') {
        buffer.push_back('-');
        cursor.advance();
    }
    while (!cursor.at_end()) {
        char current = cursor.peek();
        if ((current >= '0' && current <= '9') || current == '.' || current == 'e'
            || current == 'E' || current == '+' || current == '-') {
            buffer.push_back(current);
            cursor.advance();
        } else {
            break;
        }
    }
    if (buffer.empty() || buffer == "-") {
        error.message = "invalid number";
        error.line = cursor.current_line();
        error.column = cursor.current_column();
        return false;
    }
    try {
        out = JsonValue::make_number(std::stod(buffer));
    } catch (const std::exception&) {
        error.message = "invalid number";
        error.line = cursor.current_line();
        error.column = cursor.current_column();
        return false;
    }
    return true;
}

// CEP:WHAT: Parses one JSON value at the cursor.
// CEP:WHY: Recursive-descent core with depth bounding per the stack-exhaustion mitigation.
// CEP:STATUS: complete
// CEP:FAILURE: returns false and fills the error on malformed input.
// CEP:ASSUMES: cursor positioned at a value start.
// CEP:COST: O(remaining).
// CEP:EVIDENCE: configuration and manifest loading.
// CEP:SECURITY: depth bound kMaxJsonDepth.
bool parse_value(JsonCursor& cursor, JsonValue& out, JsonError& error, std::size_t depth) {
    if (depth > kMaxJsonDepth) {
        error.message = "nesting too deep";
        error.line = cursor.current_line();
        error.column = cursor.current_column();
        return false;
    }
    cursor.skip_insignificant();
    char current = cursor.peek();
    if (current == '{') {
        cursor.advance();
        std::vector<std::pair<std::string, JsonValue>> members;
        cursor.skip_insignificant();
        if (cursor.peek() == '}') {
            cursor.advance();
            out = JsonValue::make_object(std::move(members));
            return true;
        }
        while (true) {
            cursor.skip_insignificant();
            if (cursor.peek() != '"') {
                error.message = "expected object key";
                error.line = cursor.current_line();
                error.column = cursor.current_column();
                return false;
            }
            std::string key;
            if (!parse_string_literal(cursor, key, error)) {
                return false;
            }
            cursor.skip_insignificant();
            if (cursor.peek() != ':') {
                error.message = "expected ':' after key";
                error.line = cursor.current_line();
                error.column = cursor.current_column();
                return false;
            }
            cursor.advance();
            JsonValue member;
            if (!parse_value(cursor, member, error, depth + 1)) {
                return false;
            }
            members.emplace_back(std::move(key), std::move(member));
            cursor.skip_insignificant();
            if (cursor.peek() == ',') {
                cursor.advance();
                continue;
            }
            if (cursor.peek() == '}') {
                cursor.advance();
                out = JsonValue::make_object(std::move(members));
                return true;
            }
            error.message = "expected ',' or '}' in object";
            error.line = cursor.current_line();
            error.column = cursor.current_column();
            return false;
        }
    }
    if (current == '[') {
        cursor.advance();
        std::vector<JsonValue> items;
        cursor.skip_insignificant();
        if (cursor.peek() == ']') {
            cursor.advance();
            out = JsonValue::make_array(std::move(items));
            return true;
        }
        while (true) {
            JsonValue item;
            if (!parse_value(cursor, item, error, depth + 1)) {
                return false;
            }
            items.push_back(std::move(item));
            cursor.skip_insignificant();
            if (cursor.peek() == ',') {
                cursor.advance();
                continue;
            }
            if (cursor.peek() == ']') {
                cursor.advance();
                out = JsonValue::make_array(std::move(items));
                return true;
            }
            error.message = "expected ',' or ']' in array";
            error.line = cursor.current_line();
            error.column = cursor.current_column();
            return false;
        }
    }
    if (current == '"') {
        std::string text;
        if (!parse_string_literal(cursor, text, error)) {
            return false;
        }
        out = JsonValue::make_string(std::move(text));
        return true;
    }
    if (current == 't' && cursor.peek(1) == 'r' && cursor.peek(2) == 'u'
        && cursor.peek(3) == 'e') {
        for (int consumed = 0; consumed < 4; consumed += 1) {
            cursor.advance();
        }
        out = JsonValue::make_boolean(true);
        return true;
    }
    if (current == 'f' && cursor.peek(1) == 'a' && cursor.peek(2) == 'l'
        && cursor.peek(3) == 's' && cursor.peek(4) == 'e') {
        for (int consumed = 0; consumed < 5; consumed += 1) {
            cursor.advance();
        }
        out = JsonValue::make_boolean(false);
        return true;
    }
    if (current == 'n' && cursor.peek(1) == 'u' && cursor.peek(2) == 'l'
        && cursor.peek(3) == 'l') {
        for (int consumed = 0; consumed < 4; consumed += 1) {
            cursor.advance();
        }
        out = JsonValue();
        return true;
    }
    return parse_number_literal(cursor, out, error);
}

// CEP:WHAT: Looks up an object member by key.
// CEP:WHY: Configuration access needs key lookup that preserves insertion order.
// CEP:STATUS: complete
// CEP:FAILURE: returns nullptr when the key is absent.
// CEP:ASSUMES: none.
// CEP:COST: O(members).
// CEP:EVIDENCE: configuration loader.
// CEP:SECURITY: none.
const JsonValue* JsonValue::find(const std::string& key) const {
    if (kind != Kind::Object) {
        return nullptr;
    }
    for (const auto& member : object_value) {
        if (member.first == key) {
            return &member.second;
        }
    }
    return nullptr;
}

// CEP:WHAT: Constructs a boolean value.
// CEP:WHY: Builder for parsed and synthesized values.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
JsonValue JsonValue::make_boolean(bool value) {
    JsonValue result;
    result.kind = Kind::Boolean;
    result.boolean_value = value;
    return result;
}

// CEP:WHAT: Constructs a number value.
// CEP:WHY: Builder for parsed severities and counts.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
JsonValue JsonValue::make_number(double value) {
    JsonValue result;
    result.kind = Kind::Number;
    result.number_value = value;
    return result;
}

// CEP:WHAT: Constructs a string value.
// CEP:WHY: Builder for parsed patterns and messages.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
JsonValue JsonValue::make_string(std::string value) {
    JsonValue result;
    result.kind = Kind::String;
    result.string_value = std::move(value);
    return result;
}

// CEP:WHAT: Constructs an array value.
// CEP:WHY: Builder for parsed token lists.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
JsonValue JsonValue::make_array(std::vector<JsonValue> value) {
    JsonValue result;
    result.kind = Kind::Array;
    result.array_value = std::move(value);
    return result;
}

// CEP:WHAT: Constructs an object value.
// CEP:WHY: Builder for parsed rule bodies.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: parser.
// CEP:SECURITY: none.
JsonValue JsonValue::make_object(std::vector<std::pair<std::string, JsonValue>> value) {
    JsonValue result;
    result.kind = Kind::Object;
    result.object_value = std::move(value);
    return result;
}

// CEP:WHAT: Parses a complete JSON document.
// CEP:WHY: Entry point for configuration and manifest loading with trailing-content detection.
// CEP:STATUS: complete
// CEP:FAILURE: returns false with a positioned error on malformed or trailing input.
// CEP:ASSUMES: repository-trusted input.
// CEP:COST: O(n).
// CEP:EVIDENCE: configuration and self-test loading.
// CEP:SECURITY: depth-bounded recursion.
std::pair<JsonValue, bool> json_parse(const std::string& text, JsonError& error) {
    JsonCursor cursor(text);
    JsonValue value;
    if (!parse_value(cursor, value, error, 0)) {
        return {JsonValue(), false};
    }
    cursor.skip_insignificant();
    if (!cursor.at_end()) {
        error.message = "trailing content after value";
        error.line = cursor.current_line();
        error.column = cursor.current_column();
        return {JsonValue(), false};
    }
    return {value, true};
}

// CEP:WHAT: Appends a JSON-escaped string to a buffer.
// CEP:WHY: Serializer helper.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(length).
// CEP:EVIDENCE: json_serialize.
// CEP:SECURITY: none.
void append_escaped(std::string& out, const std::string& text) {
    out.push_back('"');
    for (char current : text) {
        switch (current) {
            case '"': out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\n': out += "\\n"; break;
            case '\r': out += "\\r"; break;
            case '\t': out += "\\t"; break;
            default: out.push_back(current); break;
        }
    }
    out.push_back('"');
}

// CEP:WHAT: Serializes a value back to JSON text.
// CEP:WHY: Debug output and deterministic comparisons.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(size).
// CEP:EVIDENCE: self-test support.
// CEP:SECURITY: none.
std::string json_serialize(const JsonValue& value) {
    switch (value.get_kind()) {
        case JsonValue::Kind::Null:
            return "null";
        case JsonValue::Kind::Boolean:
            return value.as_boolean() ? "true" : "false";
        case JsonValue::Kind::Number: {
            double number = value.as_number();
            if (number == static_cast<long long>(number)) {
                return std::to_string(static_cast<long long>(number));
            }
            return std::to_string(number);
        }
        case JsonValue::Kind::String: {
            std::string out;
            append_escaped(out, value.as_string());
            return out;
        }
        case JsonValue::Kind::Array: {
            std::string out = "[";
            bool first = true;
            for (const auto& item : value.as_array()) {
                if (!first) {
                    out += ",";
                }
                first = false;
                out += json_serialize(item);
            }
            out += "]";
            return out;
        }
        case JsonValue::Kind::Object: {
            std::string out = "{";
            bool first = true;
            for (const auto& member : value.as_object()) {
                if (!first) {
                    out += ",";
                }
                first = false;
                append_escaped(out, member.first);
                out += ":";
                out += json_serialize(member.second);
            }
            out += "}";
            return out;
        }
    }
    return "null";
}

}  // namespace cep_lint
