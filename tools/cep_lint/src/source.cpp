// CEP:FILE: tools/cep_lint/src/source.cpp
// CEP:WHAT: Implementation of the source scanner: line splitting, comment masking, comment-block extraction, and function extraction for Rust and C++.
// CEP:WHY: See source.hpp; the extractor is deliberately lexical (CEP&CC 50.5 documents that enforcement is lexical and structural, not semantic).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; heuristics degrade to fewer extractions, never wrong rejections.
// CEP:ASSUMES: functions are defined with brace-delimited bodies at the top level or inside impl/namespace blocks; single-line string literals.
// CEP:COST: O(n).
// CEP:EVIDENCE: self-test scenarios.
// CEP:SECURITY: none.

#include "source.hpp"

#include <cctype>

namespace cep_lint {

// CEP:WHAT: Maximum lines searched for the opening brace of a signature.
// CEP:WHY: Bounds the multi-line-signature search (CEP&CC 11.3 named constant; CEP&CC 22.10 bounded loops).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: signatures longer than this are not extracted (documented extractor limit).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: function extraction.
// CEP:SECURITY: none.
constexpr std::size_t kMaxSignatureLines = 12;

// CEP:WHAT: Trims ASCII whitespace from both ends.
// CEP:WHY: Pattern matching operates on trimmed fragments.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(length).
// CEP:EVIDENCE: all primitives.
// CEP:SECURITY: none.
std::string trim(const std::string& text) {
    std::size_t start = 0;
    std::size_t end = text.size();
    while (start < end && std::isspace(static_cast<unsigned char>(text[start])) != 0) {
        start += 1;
    }
    while (end > start && std::isspace(static_cast<unsigned char>(text[end - 1])) != 0) {
        end -= 1;
    }
    return text.substr(start, end - start);
}

// CEP:WHAT: Returns true when a substring is present.
// CEP:WHY: Containment helper shared by extractor and checks.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(n times m).
// CEP:EVIDENCE: extractor.
// CEP:SECURITY: none.
bool contains(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}

// CEP:WHAT: Lowercases ASCII text in a copy.
// CEP:WHY: Case-insensitive rule variants need normalized comparisons.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: ASCII input.
// CEP:COST: O(n).
// CEP:EVIDENCE: marker rules.
// CEP:SECURITY: none.
std::string lowercase(const std::string& text) {
    std::string out = text;
    for (char& current : out) {
        if (current >= 'A' && current <= 'Z') {
            current = static_cast<char>(current - 'A' + 'a');
        }
    }
    return out;
}

// CEP:WHAT: Splits text into lines on LF, tolerating CRLF.
// CEP:WHY: Line-based checks need exact line boundaries.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(n).
// CEP:EVIDENCE: scanner construction.
// CEP:SECURITY: none.
std::vector<std::string> split_lines(const std::string& text) {
    std::vector<std::string> out;
    std::string current;
    for (char character : text) {
        if (character == '\n') {
            if (!current.empty() && current.back() == '\r') {
                current.pop_back();
            }
            out.push_back(current);
            current.clear();
        } else {
            current.push_back(character);
        }
    }
    out.push_back(current);
    return out;
}

// CEP:WHAT: Returns the line-comment marker for a file.
// CEP:WHY: Python uses #, Rust and C++ use //.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: extension-based.
// CEP:COST: constant.
// CEP:EVIDENCE: scanner.
// CEP:SECURITY: none.
std::string line_marker(bool python) {
    return python ? "#" : "//";
}

// CEP:WHAT: Blanks comments and string contents in one line.
// CEP:WHY: Token bans and code checks must not match comments or messages; block comments opened on earlier lines blank whole lines until closed.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: single-line string literals; block comments do not nest.
// CEP:COST: O(line).
// CEP:EVIDENCE: code_only_line.
// CEP:SECURITY: none.
std::string blank_line(const std::string& text, bool python, bool& in_block_comment) {
    std::string out = text;
    std::size_t index = 0;
    while (index < out.size()) {
        if (in_block_comment) {
            std::size_t close = out.find("*/", index);
            for (std::size_t blank = index; blank < (close == std::string::npos ? out.size() : close); blank += 1) {
                out[blank] = ' ';
            }
            if (close == std::string::npos) {
                return out;
            }
            out[close] = ' ';
            out[close + 1] = ' ';
            index = close + 2;
            in_block_comment = false;
            continue;
        }
        if (!python && out[index] == '/' && index + 1 < out.size() && out[index + 1] == '*') {
            in_block_comment = true;
            out[index] = ' ';
            out[index + 1] = ' ';
            index += 2;
            continue;
        }
        char current = out[index];
        bool string_start = current == '"' || (!python && current == '\'');
        if (string_start) {
            char quote = current;
            std::size_t cursor = index + 1;
            while (cursor < out.size() && out[cursor] != quote) {
                if (out[cursor] == '\\') {
                    out[cursor] = ' ';
                    cursor += 1;
                    if (cursor < out.size()) {
                        out[cursor] = ' ';
                    }
                } else {
                    out[cursor] = ' ';
                }
                cursor += 1;
            }
            out[index] = ' ';
            if (cursor < out.size()) {
                out[cursor] = ' ';
            }
            index = cursor + 1;
            continue;
        }
        if ((!python && current == '/' && index + 1 < out.size() && out[index + 1] == '/')
            || (python && current == '#')) {
            for (std::size_t blank = index; blank < out.size(); blank += 1) {
                out[blank] = ' ';
            }
            return out;
        }
        index += 1;
    }
    return out;
}

// CEP:WHAT: Returns the leading marker length when a line is a full-line comment.
// CEP:WHY: Comment-block extraction only accepts full-line comments (doc comments /// and //! and #! count).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(prefix).
// CEP:EVIDENCE: comment_blocks.
// CEP:SECURITY: none.
std::size_t full_line_comment_prefix(const std::string& text, bool python) {
    std::size_t index = 0;
    while (index < text.size() && (text[index] == ' ' || text[index] == '\t')) {
        index += 1;
    }
    if (python) {
        if (index < text.size() && text[index] == '#') {
            return index + 1;
        }
        return 0;
    }
    if (index + 1 < text.size() && text[index] == '/' && text[index + 1] == '/') {
        return index + 2;
    }
    return 0;
}

// CEP:WHAT: Strips one level of CEP field prefix from a comment line.
// CEP:WHY: Field checks parse "CEP:FIELD: value" lines.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(line).
// CEP:EVIDENCE: comment_block_schema.
// CEP:SECURITY: none.
std::string strip_comment_prefix(const std::string& text, bool python) {
    std::size_t prefix = full_line_comment_prefix(text, python);
    if (prefix == 0) {
        return trim(text);
    }
    std::string body = text.substr(prefix);
    // Doc-comment markers (/// and //!) and inner-comment markers (//! and ///) leave
    // additional punctuation that would break CEP field parsing; strip them.
    std::size_t extra = 0;
    while (extra < body.size() && (body[extra] == '/' || body[extra] == '!')) {
        extra += 1;
    }
    if (extra > 0) {
        body = body.substr(extra);
    }
    return trim(body);
}

// CEP:WHAT: Constructs the scanner: splits lines, blanks comments, extracts blocks and functions, and reads the declared class.
// CEP:WHY: All per-file state is computed once so check primitives are O(1) setup.
// CEP:STATUS: complete
// CEP:FAILURE: none; extraction is heuristic and degrades to fewer extractions.
// CEP:ASSUMES: text is ASCII or UTF-8; single-line string literals.
// CEP:COST: O(text size).
// CEP:EVIDENCE: self-test scenarios exercise every extraction path.
// CEP:SECURITY: none.
SourceFile::SourceFile(std::string path, std::string text)
    : file_path(std::move(path)), python_file(false), rust_file(false) {
    const std::size_t dot = file_path.find_last_of('.');
    std::string extension = dot == std::string::npos ? "" : file_path.substr(dot + 1);
    python_file = extension == "py";
    rust_file = extension == "rs";
    lines = split_lines(text);
    bool in_block_comment = false;
    for (const std::string& raw : lines) {
        code_lines.push_back(blank_line(raw, python_file, in_block_comment));
    }
    // Comment blocks: maximal runs of consecutive full-line comments.
    std::size_t index = 0;
    while (index < lines.size()) {
        std::size_t prefix = full_line_comment_prefix(lines[index], python_file);
        if (prefix == 0) {
            index += 1;
            continue;
        }
        CommentBlock block;
        block.start_line = index + 1;
        while (index < lines.size()) {
            std::size_t next_prefix = full_line_comment_prefix(lines[index], python_file);
            if (next_prefix == 0) {
                break;
            }
            block.lines.push_back(strip_comment_prefix(lines[index], python_file));
            index += 1;
        }
        blocks.push_back(block);
    }
    // Declared class from the first block.
    if (!blocks.empty()) {
        for (const std::string& field : blocks.front().lines) {
            if (field.rfind("CEP:CLASS:", 0) == 0) {
                class_value = trim(field.substr(std::string("CEP:CLASS:").size()));
            }
        }
    }
    // Function extraction.
    for (std::size_t line_index = 0; line_index < lines.size(); line_index += 1) {
        const std::string& code = code_lines[line_index];
        bool is_rust_fn = rust_file && contains(code, "fn ") && contains(code, "(")
            && code.find(';') == std::string::npos;
        bool is_cpp_fn = !python_file && !rust_file && contains(code, "(")
            && code.find(';') == std::string::npos && code.find("fn ") == std::string::npos
            && trim(code).size() > 2;
        if (!is_rust_fn && !is_cpp_fn) {
            continue;
        }
// CEP:WHAT: Trims ASCII whitespace from both ends.
// CEP:WHY: Pattern matching operates on trimmed fragments.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(length).
// CEP:EVIDENCE: all primitives.
// CEP:SECURITY: none.
        std::string trimmed_code = trim(code);
        if (trimmed_code.rfind("if", 0) == 0 || trimmed_code.rfind("for", 0) == 0
            || trimmed_code.rfind("while", 0) == 0 || trimmed_code.rfind("match", 0) == 0
            || trimmed_code.rfind("switch", 0) == 0 || trimmed_code.rfind("else", 0) == 0
            || trimmed_code.rfind("loop", 0) == 0 || trimmed_code.rfind(":", 0) == 0
            || trimmed_code.rfind("try", 0) == 0 || trimmed_code.rfind("catch", 0) == 0
            || trimmed_code.rfind("do", 0) == 0 || trimmed_code.rfind("return", 0) == 0
            || trimmed_code.rfind("&&", 0) == 0 || trimmed_code.rfind("||", 0) == 0) {
            continue;
        }
        // The first parenthesis must open the candidate name's parameter list: no
        // assignment, no earlier call, and no member-access dot before the name.
        const std::size_t first_paren = code.find('(');
        if (first_paren == std::string::npos) {
            continue;
        }
        const std::string before_paren = code.substr(0, first_paren);
        if (before_paren.find('=') != std::string::npos) {
            continue;
        }
        std::size_t name_probe = first_paren;
        while (name_probe > 0
            && (std::isalnum(static_cast<unsigned char>(code[name_probe - 1])) != 0
                || code[name_probe - 1] == '_')) {
            name_probe -= 1;
        }
        if (name_probe > 0 && code[name_probe - 1] == '.') {
            continue;
        }
        // The opening brace may sit on a later line (multi-line parameter lists).
        std::size_t brace_line = line_index;
        bool opened = false;
        for (std::size_t lookahead = 0; lookahead < kMaxSignatureLines && brace_line < lines.size(); lookahead += 1) {
            if (code_lines[brace_line].find('{') != std::string::npos) {
                opened = true;
                break;
            }
            if (code_lines[brace_line].find(';') != std::string::npos) {
                break;
            }
            brace_line += 1;
        }
        if (!opened) {
            continue;
        }
        FunctionDefinition definition;
        definition.line = brace_line + 1;
        // Name extraction: word before the first '(' on the signature line.
        std::size_t paren = code.find('(');
        std::size_t name_end = paren;
        while (name_end > 0
            && (std::isalnum(static_cast<unsigned char>(code[name_end - 1])) != 0
                || code[name_end - 1] == '_')) {
            name_end -= 1;
        }
        if (name_end == paren) {
            continue;
        }
        definition.name = code.substr(name_end, paren - name_end);
        if (definition.name.empty()) {
            continue;
        }
        // Body statement count and emptiness: scan forward with brace balance from
        // the brace line, tracking whether any non-whitespace appears inside the body.
        std::size_t depth = 0;
        bool body_opened = false;
        std::size_t statements = 0;
        bool saw_body_content = false;
        std::size_t scan = brace_line;
        while (scan < lines.size()) {
            const std::string& scan_code = code_lines[scan];
            bool leave = false;
            for (char character : scan_code) {
                if (character == '{') {
                    depth += 1;
                    body_opened = true;
                } else if (character == '}') {
                    if (depth == 0) {
                        leave = true;
                        break;
                    }
                    depth -= 1;
                    if (depth == 0) {
                        leave = true;
                        break;
                    }
                } else if (character == ';' && depth >= 1) {
                    statements += 1;
                }
                if (character != '{' && character != '}' && body_opened && depth >= 1
                    && std::isspace(static_cast<unsigned char>(character)) == 0) {
                    saw_body_content = true;
                }
            }
            if (leave || (body_opened && depth == 0)) {
                break;
            }
            scan += 1;
        }
        definition.statement_count = statements;
        definition.body_empty = body_opened && !saw_body_content;
        // Nearest preceding comment block: walk upward over gap lines (attributes,
        // modifiers, and continuation lines of a multi-line signature).
        std::size_t search = line_index;
        while (search > 0) {
            std::size_t previous = search - 1;
            const std::string& previous_raw = trim(lines[previous]);
            if (previous_raw.empty() || previous_raw.rfind("#[", 0) == 0
                || previous_raw.rfind("#!", 0) == 0) {
                search = previous;
                continue;
            }
            if (!python_file
                && (previous_raw.rfind("pub", 0) == 0 || previous_raw.rfind("unsafe", 0) == 0
                    || previous_raw.rfind("extern", 0) == 0
                    || previous_raw.rfind("template", 0) == 0
                    || previous_raw.rfind("constexpr", 0) == 0
                    || previous_raw.rfind("inline", 0) == 0
                    || previous_raw.rfind("static", 0) == 0
                    || previous_raw.rfind("noexcept", 0) == 0)) {
                search = previous;
                continue;
            }
            if (previous_raw.rfind("//", 0) == 0 || previous_raw.rfind('#', 0) == 0) {
                break;
            }
            // Continuation lines of a multi-line signature (parameters, return types,
            // and constructor initializer lists).
            const std::string& previous_code = trim(code_lines[previous]);
            if ((!previous_code.empty() && previous_code != "{"
                 && previous_code.find(')') == std::string::npos
                 && previous_code.find('{') == std::string::npos
                 && previous_code.find('=') == std::string::npos)
                || previous_raw.rfind(":", 0) == 0) {
                search = previous;
                continue;
            }
            break;
        }
        for (const CommentBlock& block : blocks) {
            // The file header block is never accepted as a function block (CEP&CC 50.3).
            if (block.start_line == 1) {
                continue;
            }
            std::size_t block_end = block.start_line + block.lines.size() - 1;
            if (block_end == search) {
                definition.preceding_comment = block.lines;
                definition.comment_line = block.start_line;
                break;
            }
        }
        function_list.push_back(definition);
    }
}

// CEP:WHAT: Returns one raw line, or empty for out-of-range indices.
// CEP:WHY: Check primitives need bounded line access without error plumbing.
// CEP:STATUS: complete
// CEP:FAILURE: returns the shared empty string on out-of-range access.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: line-based checks.
// CEP:SECURITY: none.
const std::string& SourceFile::line(std::size_t index) const {
    static const std::string empty;
    if (index >= lines.size()) {
        return empty;
    }
    return lines[index];
}

// CEP:WHAT: Returns one line with comments and string contents blanked.
// CEP:WHY: Token bans must not match comments or messages (CEP&CC 50.3 limits).
// CEP:STATUS: complete
// CEP:FAILURE: returns the shared empty string on out-of-range access.
// CEP:ASSUMES: single-line literals; block comments tracked at scan time.
// CEP:COST: constant.
// CEP:EVIDENCE: banned-token checks.
// CEP:SECURITY: none.
const std::string& SourceFile::code_only_line(std::size_t index) const {
    static const std::string empty;
    if (index >= code_lines.size()) {
        return empty;
    }
    return code_lines[index];
}

}  // namespace cep_lint
