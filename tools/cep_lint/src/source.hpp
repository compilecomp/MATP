// CEP:FILE: tools/cep_lint/src/source.hpp
// CEP:WHAT: Source file model for linting: line access with comment/string awareness, CEP comment-block extraction, and function-definition extraction for Rust and C++.
// CEP:WHY: CEP&CC 50.3 defines check primitives that operate on comment blocks, code with comments removed, and function definitions; one scanner shared by all primitives keeps behavior consistent and testable.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: construction fails only on unreadable files (reported by the engine); scanning itself cannot fail.
// CEP:ASSUMES: UTF-8 or ASCII text; line comments are // (Rust, C++) or # (Python); block comments are /* */.
// CEP:COST: O(file size) construction, O(1) line access.
// CEP:EVIDENCE: self-test scenarios exercise every extractor path.
// CEP:SECURITY: input files are repository-trusted; the scanner never executes anything.

#pragma once

#include <cstddef>
#include <map>
#include <string>
#include <vector>

namespace cep_lint {

// CEP:WHAT: One extracted function definition.
// CEP:WHY: The function_policy primitive needs the definition line, the nearest preceding comment block, and a body statement count.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; a value type.
// CEP:ASSUMES: heuristic extraction (see the standard's documented limits in 50.3).
// CEP:COST: value semantics.
// CEP:EVIDENCE: function_policy checks.
// CEP:SECURITY: none.
struct FunctionDefinition {
    /// CEP:WHAT: One-based line of the definition signature.
    std::size_t line;
    /// CEP:WHAT: Function name as written.
    std::string name;
    /// CEP:WHAT: Nearest preceding comment block lines (may be empty).
    std::vector<std::string> preceding_comment;
    /// CEP:WHAT: One-based start line of the preceding comment block (0 when absent).
    std::size_t comment_line;
    /// CEP:WHAT: Count of statements inside the body (semicolons plus nesting events).
    std::size_t statement_count;
    /// CEP:WHAT: True when the body between braces contains only whitespace.
    bool body_empty;
};

// CEP:WHAT: A single extracted full-line comment block with its location.
// CEP:WHY: The comment_block_schema primitive validates the first contiguous block; other checks scan all blocks.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none; a value type.
// CEP:ASSUMES: none.
// CEP:COST: value semantics.
// CEP:EVIDENCE: comment_block_schema checks.
// CEP:SECURITY: none.
struct CommentBlock {
    /// CEP:WHAT: One-based start line.
    std::size_t start_line;
    /// CEP:WHAT: Comment lines with the marker prefix removed.
    std::vector<std::string> lines;
};

// CEP:WHAT: Scanned source file.
// CEP:WHY: Shared model for all checks.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none after construction.
// CEP:ASSUMES: text already read by the engine.
// CEP:COST: O(n) construction.
// CEP:EVIDENCE: all check primitives.
// CEP:SECURITY: none.
class SourceFile {
public:
    // CEP:WHAT: Constructs the scanner over file text.
    // CEP:WHY: Precomputes lines, comment mask, and extractions.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(n).
    // CEP:EVIDENCE: engine.
    // CEP:SECURITY: none.
    SourceFile(std::string path, std::string text);

    // CEP:WHAT: Returns the file path as given.
    // CEP:WHY: Reporting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: findings.
    // CEP:SECURITY: none.
    const std::string& path() const { return file_path; }

    // CEP:WHAT: Returns the number of lines.
    // CEP:WHY: Bounds.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: checks.
    // CEP:SECURITY: none.
    std::size_t line_count() const { return lines.size(); }

    // CEP:WHAT: Returns one line (empty when out of range).
    // CEP:WHY: Check primitives.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; out-of-range access is empty, not an error.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: checks.
    // CEP:SECURITY: none.
    const std::string& line(std::size_t index) const;

    // CEP:WHAT: Returns one line with comments and string literals blanked.
    // CEP:WHY: Token bans must not match inside comments or messages (CEP&CC 50.3 HOT-BANNED limits).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: single-line string literals and comments; unterminated block comments blank the rest of the line.
    // CEP:COST: constant per line.
    // CEP:EVIDENCE: banned_token_policy.
    // CEP:SECURITY: none.
    const std::string& code_only_line(std::size_t index) const;

    // CEP:WHAT: Returns the extracted full-line comment blocks in order.
    // CEP:WHY: Comment-block schemas and field checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: blocks are maximal runs of consecutive full-line comments with the same marker.
    // CEP:COST: O(blocks).
    // CEP:EVIDENCE: comment_block_schema.
    // CEP:SECURITY: none.
    const std::vector<CommentBlock>& comment_blocks() const { return blocks; }

    // CEP:WHAT: Returns the extracted function definitions.
    // CEP:WHY: function_policy checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: heuristic extractor; limits documented in the standard (50.3).
    // CEP:COST: O(functions).
    // CEP:EVIDENCE: function_policy.
    // CEP:SECURITY: none.
    const std::vector<FunctionDefinition>& functions() const { return function_list; }

    // CEP:WHAT: Returns the file's declared CEP:CLASS value (empty when absent).
    // CEP:WHY: Class-scoped rules (HOT-BANNED, MAGIC-NUMBER scoping).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the declaration appears in the first comment block.
    // CEP:COST: constant.
    // CEP:EVIDENCE: class-scoped rules.
    // CEP:SECURITY: none.
    const std::string& declared_class() const { return class_value; }

    // CEP:WHAT: Returns true when the file is Python (uses # comments).
    // CEP:WHY: Comment marker selection.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: extension-based detection.
    // CEP:COST: constant.
    // CEP:EVIDENCE: scanner.
    // CEP:SECURITY: none.
    bool is_python() const { return python_file; }

    // CEP:WHAT: Returns true when the file is Rust.
    // CEP:WHY: Function extraction must not apply C++ signature heuristics to Rust files.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: extension-based detection.
    // CEP:COST: constant.
    // CEP:EVIDENCE: extractor.
    // CEP:SECURITY: none.
    bool is_rust() const { return rust_file; }

private:
    std::string file_path;
    std::vector<std::string> lines;
    std::vector<std::string> code_lines;
    std::vector<CommentBlock> blocks;
    std::vector<FunctionDefinition> function_list;
    std::string class_value;
    bool python_file;
    bool rust_file;
};

// CEP:WHAT: Trims ASCII whitespace from both ends.
// CEP:WHY: Shared helper for pattern matching on line fragments.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(length).
// CEP:EVIDENCE: checks.
// CEP:SECURITY: none.
std::string trim(const std::string& text);

// CEP:WHAT: Returns true when text contains the substring.
// CEP:WHY: Case-sensitive containment helper.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(n*m).
// CEP:EVIDENCE: checks.
// CEP:SECURITY: none.
bool contains(const std::string& text, const std::string& needle);

// CEP:WHAT: Lowercases ASCII text.
// CEP:WHY: Case-insensitive rule variants.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: ASCII.
// CEP:COST: O(n).
// CEP:EVIDENCE: case-insensitive checks.
// CEP:SECURITY: none.
std::string lowercase(const std::string& text);

}  // namespace cep_lint
