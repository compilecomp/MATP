// CEP:FILE: cold/parsing/tptp_parser.rs
/// CEP:WHAT: The TPTP front end (design 6.1): tokenizes and parses CNF (cnf) and FOF (fof) input directives with include resolution, validates roles, arities, variable binding, and the design 6.3 bound set, builds the unified IR for CNF input clauses, and returns the FOF ASTs for the design 7 clausification pipeline.
/// CEP:WHY: Design 6.1 lists TPTP as the primary ATP input format; ticket CEP-1006; the five-stage shape of design 6.2 (lex, recursive descent, validate, IR construction, return) is realized with bounded recursion (kMaxParseDepth), a bounded node budget (kMaxFormulaNodes), a bounded symbol universe (kMaxSymbolCount), bounded quantifier nesting (kMaxQuantifierDepth), and bounded include resolution (kMaxIncludeDepth, kMaxIncludeCount).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns ParseError per the shared vocabulary (super::ParseError); no panic, no exception (design 6.3).
/// CEP:ASSUMES: input bytes are untrusted; the arena outlives the returned problem; include paths resolve under the caller-supplied root.
/// CEP:COST: linear in input size under the bounds; allocations cold-path legal.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, fof_formulas_reach_the_ast, binds_all_connectives, syntax_error_reports_line, rejects_unknown_role, rejects_arity_change, rejects_free_variable, rejects_quantifier_depth, rejects_parse_depth, rejects_node_budget, include_depth_is_bounded, include_count_is_bounded, include_selection_filters_by_name}.
/// CEP:SECURITY: byte size, nesting depth, node count, symbol count, quantifier depth, and include fan-out are each enforced against a named config bound before any unbounded growth (design 6.3); include files pass the same kMaxInputBytes gate.
use super::{FofFormula, FofTerm, NameTable, ParseError, ParsedFof, ParsedProblem, TptpRole};
use crate::symbol_table_builder::SymbolTableBuilder;
use mapt_config::limits::{
    kInvalidClauseId, kInvalidSubstitutionOffset, kMaxClauseLiterals, kMaxDerivationParents,
    kMaxFormulaNodes, kMaxIncludeCount, kMaxIncludeDepth, kMaxInputBytes, kMaxParseDepth,
    kMaxQuantifierDepth, kMaxSymbolCount,
};
use mapt_hot::ir::clause::{ClauseError, ClauseStore, DerivationStep, InferenceRule};
use mapt_hot::ir::literal::Literal;
use mapt_hot::ir::symbol_table::{SortId, SymbolKind};
use mapt_hot::ir::term::{TermPtr, TermStore};
use mapt_hot::memory::arena::Arena;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::string::String;
use std::vec::Vec;

/// CEP:WHAT: One lexical token: its class, its byte content, and its 1-based position.
/// CEP:WHY: The recursive descent needs classification (word classes drive the variable-versus-symbol distinction) and exact error positions (ParseError::Syntax).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: one small struct per token; the lexer holds one token at a time (no token-stream materialization).
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
/// CEP:SECURITY: token content is a byte slice of the input, never an owned copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    /// A lowercase-initial word: a symbol or directive name.
    LowerWord,
    /// An uppercase- or underscore-initial word: a variable.
    UpperWord,
    /// A $-prefixed word: $true, $false, and the sort tokens.
    DollarWord,
    /// A single-quoted atom (accepted as an ordinary constant name; distinct-object semantics are a documented limitation).
    QuotedWord,
    /// An unsigned decimal integer (accepted only inside names and the include grammar; numeric terms are rejected).
    Integer,
    /// Punctuation or a multi-character connective (compared by content).
    Punct,
}

/// CEP:WHAT: One lexical token with its kind, byte content, and 1-based line and column.
/// CEP:WHY: See TokenKind.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: copy.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy)]
struct Token<'i> {
    kind: TokenKind,
    text: &'i [u8],
    line: u32,
    column: u32,
}

impl<'i> Token<'i> {
    /// CEP:WHAT: Renders the token content as a string slice (valid because every token class is ASCII by construction).
    /// CEP:WHY: The parser compares names and punctuation as strings.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails for lexer-produced tokens.
    /// CEP:ASSUMES: the token was produced by Lexer::next.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn as_str(&self) -> &'i str {
        // Tokens are ASCII runs by construction (the lexer only emits ASCII
        // word bytes and punctuation), so the UTF-8 conversion cannot fail.
        std::str::from_utf8(self.text).unwrap_or("")
    }
}

/// CEP:WHAT: The TPTP lexer: one-token lookahead over the byte slice with line/column tracking and comment skipping (% line comments and /* block comments).
/// CEP:WHY: Design 6.2 stage 1: bounded token buffer (one token, no stream materialization); comment handling belongs to the lexical layer of the TPTP grammar.
/// CEP:STATUS: complete
/// CEP:FAILURE: next() returns a Syntax error for an unterminated block comment or an unrecognized byte; never panics.
/// CEP:ASSUMES: input passed the kMaxInputBytes gate.
/// CEP:COST: O(input) across all next() calls.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
/// CEP:SECURITY: no allocation; every token borrows the input.
struct Lexer<'i> {
    input: &'i [u8],
    position: usize,
    line: u32,
    column: u32,
}

impl<'i> Lexer<'i> {
    /// CEP:WHAT: Creates a lexer at the start of the input.
    /// CEP:WHY: Explicit construction point.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn new(input: &'i [u8]) -> Self {
        Lexer {
            input,
            position: 0,
            line: 1,
            column: 1,
        }
    }

    /// CEP:WHAT: Advances past whitespace and comments and returns the next token, or None at end of input.
    /// CEP:WHY: The single lexical entry point of the parser.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns ParseError::Syntax on an unterminated block comment or a byte outside the TPTP alphabet; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(1) amortized per token.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
    /// CEP:SECURITY: none.
    fn next(&mut self) -> Result<Option<Token<'i>>, ParseError> {
        self.skip_trivia()?;
        if self.position >= self.input.len() {
            return Ok(None);
        }
        let line = self.line;
        let column = self.column;
        let byte = self.input[self.position];
        let kind = match byte {
            b'a'..=b'z' => TokenKind::LowerWord,
            b'A'..=b'Z' | b'_' => TokenKind::UpperWord,
            b'$' => TokenKind::DollarWord,
            b'\'' => TokenKind::QuotedWord,
            b'0'..=b'9' => TokenKind::Integer,
            b'(' | b')' | b'[' | b']' | b',' | b'.' | b':' | b'=' | b'~' | b'|' | b'&' | b'<'
            | b'>' | b'!' | b'?' | b'*' | b'^' | b'@' => TokenKind::Punct,
            _ => return Err(self.syntax_error()),
        };
        let start = self.position;
        match kind {
            TokenKind::LowerWord | TokenKind::UpperWord => {
                while self.position < self.input.len()
                    && (self.input[self.position].is_ascii_alphanumeric()
                        || self.input[self.position] == b'_')
                {
                    self.advance();
                }
            }
            TokenKind::DollarWord => {
                self.advance();
                while self.position < self.input.len()
                    && (self.input[self.position].is_ascii_lowercase()
                        || self.input[self.position] == b'_')
                {
                    self.advance();
                }
            }
            TokenKind::QuotedWord => {
                self.advance();
                while self.position < self.input.len() && self.input[self.position] != b'\'' {
                    self.advance();
                }
                if self.position >= self.input.len() {
                    return Err(self.syntax_error());
                }
                self.advance();
            }
            TokenKind::Integer => {
                while self.position < self.input.len() && self.input[self.position].is_ascii_digit()
                {
                    self.advance();
                }
            }
            TokenKind::Punct => {
                // Three-character connectives first so "<=" cannot consume
                // the prefix of "<=>", then the two-character connectives,
                // then the single punctuation byte.
                let rest = &self.input[self.position..];
                let length = if rest.starts_with(b"<=>") || rest.starts_with(b"<~>") {
                    3
                } else if rest.starts_with(b"=>")
                    || rest.starts_with(b"<=")
                    || rest.starts_with(b"~|")
                    || rest.starts_with(b"~&")
                    || rest.starts_with(b"!=")
                {
                    2
                } else {
                    1
                };
                for _ in 0..length {
                    self.advance();
                }
            }
        }
        Ok(Some(Token {
            kind,
            text: &self.input[start..self.position],
            line,
            column,
        }))
    }

    /// CEP:WHAT: Builds a Syntax error at the current position.
    /// CEP:WHY: One attribution point keeps line/column reporting consistent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
    /// CEP:SECURITY: none.
    fn syntax_error(&self) -> ParseError {
        ParseError::Syntax {
            line: self.line,
            column: self.column,
        }
    }

    /// CEP:WHAT: Consumes whitespace and % line and /* block */ comments.
    /// CEP:WHY: Lexical trivia of the TPTP grammar.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns ParseError::Syntax on an unterminated block comment; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: linear in skipped bytes.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn skip_trivia(&mut self) -> Result<(), ParseError> {
        loop {
            while self.position < self.input.len()
                && (self.input[self.position] == b' '
                    || self.input[self.position] == b'\t'
                    || self.input[self.position] == b'\r'
                    || self.input[self.position] == b'\n')
            {
                if self.input[self.position] == b'\n' {
                    self.line += 1;
                    self.column = 1;
                } else {
                    self.column += 1;
                }
                self.position += 1;
            }
            if self.position < self.input.len() && self.input[self.position] == b'%' {
                while self.position < self.input.len() && self.input[self.position] != b'\n' {
                    self.position += 1;
                    self.column += 1;
                }
                continue;
            }
            if self.position + 1 < self.input.len()
                && self.input[self.position] == b'/'
                && self.input[self.position + 1] == b'*'
            {
                self.position += 2;
                self.column += 2;
                loop {
                    if self.position + 1 >= self.input.len() {
                        return Err(self.syntax_error());
                    }
                    if self.input[self.position] == b'*' && self.input[self.position + 1] == b'/' {
                        self.position += 2;
                        self.column += 2;
                        break;
                    }
                    if self.input[self.position] == b'\n' {
                        self.line += 1;
                        self.column = 1;
                    } else {
                        self.column += 1;
                    }
                    self.position += 1;
                }
                continue;
            }
            return Ok(());
        }
    }

    /// CEP:WHAT: Advances one byte, maintaining the line/column counters.
    /// CEP:WHY: Position attribution for every token and error.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: position < input.len().
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn advance(&mut self) {
        if self.input[self.position] == b'\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        self.position += 1;
    }
}

/// CEP:WHAT: The TPTP recursive-descent parser state: the lexer, the symbol-table builder, the name table, the per-name symbol registry, the node budget, the quantifier depth, the include counters, and the accumulated output.
/// CEP:WHY: One mutable state object keeps the bound enforcement (design 6.3) at the mutation points: every AST allocation charges the node budget, every quantifier layer charges the quantifier depth, every declaration checks the symbol universe, and every include charges both include bounds; the two lifetimes separate the current file's bytes from the include root so include files parse with fresh lexers over shared semantic state.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: every bound violation surfaces as the corresponding ParseError variant at the charge point.
/// CEP:ASSUMES: one parser chain per parse; includes move the semantic state (builder, name table, registries, budgets) into the child parser and back so symbol ids stay coherent across files.
/// CEP:COST: the registries are O(distinct names).
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{rejects_node_budget, rejects_quantifier_depth, include_depth_is_bounded, include_count_is_bounded, rejects_arity_change}.
/// CEP:SECURITY: all bounds of design 6.3 that apply to this format are charged here.
struct Parser<'i, 'r> {
    lexer: Lexer<'i>,
    lookahead: Option<Token<'i>>,
    builder: SymbolTableBuilder,
    names: NameTable,
    symbol_ids: HashMap<String, u32>,
    symbols_arity: HashMap<u32, (SymbolKind, u16)>,
    limits: ParserLimits,
    nodes_charged: u64,
    depth: u32,
    quantifier_depth: u32,
    include_depth: u32,
    include_count: u32,
    include_root: Option<&'r Path>,
    formulas: Vec<ParsedFof>,
}

impl<'i, 'r> Parser<'i, 'r> {
    /// CEP:WHAT: Creates the parser over one file's bytes with the include root, declaring the untyped $i sort as symbol 0.
    /// CEP:WHY: Explicit construction point; the $i sort must exist before any symbol declaration references it (the builder rejects undeclared sorts), and untyped TPTP has exactly one individual sort.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns IrSymbol when the $i declaration fails; never panics.
    /// CEP:ASSUMES: input passed the kMaxInputBytes gate.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn new(input: &'i [u8], include_root: Option<&'r Path>) -> Result<Self, ParseError> {
        let mut lexer = Lexer::new(input);
        let lookahead = lexer.next()?;
        let mut builder = SymbolTableBuilder::new();
        builder.declare_sort("$i").map_err(ParseError::IrSymbol)?;
        Ok(Parser {
            lexer,
            lookahead,
            builder,
            names: NameTable::default(),
            symbol_ids: HashMap::new(),
            symbols_arity: HashMap::new(),
            limits: ParserLimits::standard(),
            nodes_charged: 0,
            depth: 0,
            quantifier_depth: 0,
            include_depth: 0,
            include_count: 0,
            include_root,
            formulas: Vec::new(),
        })
    }

    /// CEP:WHAT: Consumes and returns the current lookahead token.
    /// CEP:WHY: Single-token-consumption discipline of the recursive descent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax at end of input (a caller at end of input always wanted a real token).
    /// CEP:ASSUMES: none.
    /// CEP:COST: one lex step.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn eat(&mut self) -> Result<Token<'i>, ParseError> {
        match self.lookahead.take() {
            Some(token) => {
                self.lookahead = self.lexer.next()?;
                Ok(token)
            }
            None => Err(self.lexer.syntax_error()),
        }
    }

    /// CEP:WHAT: Consumes the lookahead when its text matches, reporting success.
    /// CEP:WHY: The punctuation-driven branch discipline of the descent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails; a false report leaves the lookahead.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one lex step on success.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn accept(&mut self, text: &str) -> Result<bool, ParseError> {
        match self.lookahead {
            Some(token) if token.as_str() == text => {
                self.eat()?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// CEP:WHAT: Consumes the next token, requiring its text to match.
    /// CEP:WHY: The structural delimiters of the TPTP grammar.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax at the token's position on mismatch; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one lex step.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::syntax_error_reports_line.
    /// CEP:SECURITY: none.
    fn expect(&mut self, text: &str) -> Result<Token<'i>, ParseError> {
        let token = self.eat()?;
        if token.as_str() == text {
            Ok(token)
        } else {
            Err(ParseError::Syntax {
                line: token.line,
                column: token.column,
            })
        }
    }

    /// CEP:WHAT: Charges one AST node against kMaxFormulaNodes.
    /// CEP:WHY: Design 6.3: the node budget prevents CPU exhaustion; charging at allocation keeps the bound exact.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TooManyNodes when the budget is exhausted.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_node_budget.
    /// CEP:SECURITY: CPU denial-of-service mitigation.
    fn charge_node(&mut self) -> Result<(), ParseError> {
        let budget = self.limits.node_budget.min(kMaxFormulaNodes);
        if self.nodes_charged >= budget {
            return Err(ParseError::TooManyNodes);
        }
        self.nodes_charged += 1;
        Ok(())
    }

    /// CEP:WHAT: Enters one recursive-descent level, charging the parse-depth bound (injected value clamped to kMaxParseDepth).
    /// CEP:WHY: Design 6.2 requires bounded recursion depth; the guard is charged at the two recursive entry points (unit formula and term) which dominate the descent's nesting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TooDeep past the bound.
    /// CEP:ASSUMES: paired depth release on every path.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_parse_depth.
    /// CEP:SECURITY: stack-overflow mitigation.
    fn enter_depth(&mut self) -> Result<(), ParseError> {
        let bound = self.limits.parse_depth.min(kMaxParseDepth);
        if self.depth >= bound {
            return Err(ParseError::TooDeep);
        }
        self.depth += 1;
        Ok(())
    }

    /// CEP:WHAT: Enters a quantifier scope, charging kMaxQuantifierDepth.
    /// CEP:WHY: Design 6.3: quantifier nesting drives exponential CNF blowup; the bound is charged at scope entry and released at exit.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns QuantifierTooDeep past the bound.
    /// CEP:ASSUMES: paired with leave_quantifier on every path.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_quantifier_depth.
    /// CEP:SECURITY: CPU denial-of-service mitigation.
    fn enter_quantifier(&mut self) -> Result<(), ParseError> {
        let bound = self.limits.quantifier_depth.min(kMaxQuantifierDepth);
        if self.quantifier_depth >= bound {
            return Err(ParseError::QuantifierTooDeep);
        }
        self.quantifier_depth += 1;
        Ok(())
    }

    /// CEP:WHAT: Leaves a quantifier scope.
    /// CEP:WHY: Paired with enter_quantifier.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: quantifier_depth > 0.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_quantifier_depth.
    /// CEP:SECURITY: none.
    fn leave_quantifier(&mut self) {
        self.quantifier_depth -= 1;
    }

    /// CEP:WHAT: Enters one include level, charging both include bounds.
    /// CEP:WHY: Design 6.3: kMaxIncludeDepth prevents include cycles, kMaxIncludeCount prevents resource exhaustion through fan-out.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns IncludeTooDeep or TooManyIncludes; never panics.
    /// CEP:ASSUMES: paired with leave_include on every path.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{include_depth_is_bounded, include_count_is_bounded}.
    /// CEP:SECURITY: resource-exhaustion mitigation.
    fn enter_include(&mut self) -> Result<(), ParseError> {
        if self.include_depth >= kMaxIncludeDepth {
            return Err(ParseError::IncludeTooDeep);
        }
        if self.include_count >= kMaxIncludeCount {
            return Err(ParseError::TooManyIncludes);
        }
        self.include_depth += 1;
        self.include_count += 1;
        Ok(())
    }

    /// CEP:WHAT: Leaves one include level.
    /// CEP:WHY: Paired with enter_include.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: include_depth > 0.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::include_depth_is_bounded.
    /// CEP:SECURITY: none.
    fn leave_include(&mut self) {
        self.include_depth -= 1;
    }

    /// CEP:WHAT: Declares or reuses a symbol by name with the given kind and arity, enforcing the TPTP consistency rule (same name implies same kind and arity) and the symbol-universe bound.
    /// CEP:WHY: TPTP is untyped and declaration-free: the signature of a name is fixed by its first use, and any divergent later use is the input defect ArityMismatch; kMaxSymbolCount bounds the universe (design 6.3). The AST references the builder's dense ids directly through symbol_ids.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns ArityMismatch on a kind or arity change, TooManySymbols past the universe bound, IrSymbol on builder rejection (name length, capacity); never panics.
    /// CEP:ASSUMES: names are non-empty tokens of the word classes.
    /// CEP:COST: O(1) registry lookup plus the builder declaration on first use.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_arity_change.
    /// CEP:SECURITY: symbol count bounded by kMaxSymbolCount.
    fn declare_symbol(
        &mut self,
        name: &str,
        kind: SymbolKind,
        arity: u16,
        sorts: &[SortId],
    ) -> Result<u32, ParseError> {
        if let Some(id) = self.symbol_ids.get(name) {
            let (recorded_kind, recorded_arity) = self.symbols_arity[id];
            if recorded_kind != kind || recorded_arity != arity {
                return Err(ParseError::ArityMismatch);
            }
            return Ok(*id);
        }
        if self.builder.symbol_count() >= kMaxSymbolCount {
            return Err(ParseError::TooManySymbols);
        }
        let declared = match kind {
            SymbolKind::Predicate => self.builder.declare_predicate(name, arity, 1, sorts),
            _ => {
                let return_sort = SortId(0);
                self.builder
                    .declare_function(name, arity, 1, sorts, return_sort)
            }
        };
        let declared = declared.map_err(ParseError::IrSymbol)?;
        self.symbols_arity.insert(declared, (kind, arity));
        self.symbol_ids.insert(String::from(name), declared);
        Ok(declared)
    }
}

/// CEP:WHAT: The injectable parser limits: the AST node budget, the recursive-descent depth, and the quantifier depth.
/// CEP:WHY: Design 6.3 fixes the standard bound set (ParserLimits::standard reads the named config constants); the injectable form lets a driver impose tighter host-specific budgets and lets the test suite exercise the bound paths without materializing inputs at the full standard sizes (the same injectable-capacity pattern as filter::MiniCapacities).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: values are clamped to the config constants at use (a larger injection never exceeds the design bound).
/// CEP:COST: three words.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{rejects_node_budget, rejects_parse_depth, rejects_quantifier_depth}.
/// CEP:SECURITY: clamping preserves the design 6.3 bounds under any injection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParserLimits {
    /// The AST node budget (standard: kMaxFormulaNodes).
    pub node_budget: u64,
    /// The recursive-descent depth bound (standard: kMaxParseDepth).
    pub parse_depth: u32,
    /// The quantifier nesting bound (standard: kMaxQuantifierDepth).
    pub quantifier_depth: u32,
}

impl ParserLimits {
    /// CEP:WHAT: The standard limits from the config constants.
    /// CEP:WHY: One name for the design 6.3 bound set.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
    /// CEP:SECURITY: none.
    pub fn standard() -> ParserLimits {
        ParserLimits {
            node_budget: kMaxFormulaNodes,
            parse_depth: kMaxParseDepth,
            quantifier_depth: kMaxQuantifierDepth,
        }
    }
}

/// CEP:WHAT: One parsed CNF directive: role, name, and the literal AST list.
/// CEP:WHY: The driver needs role and name with the clause (same reasons as ParsedFof); the IR conversion consumes this shape.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: one owned record per CNF directive.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: literal count bounded by kMaxClauseLiterals at IR construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CnfLiteral {
    /// A positive or negative predicate atom by symbol id with argument terms.
    Atom(bool, u32, Vec<FofTerm>),
    /// The $true literal with its polarity (tautologous when positive, vacuous when negative).
    True(bool),
    /// The $false literal with its polarity (vacuous when positive, tautologous when negative).
    False(bool),
    /// A polarity with an equality atom; the polarity is the equality's sign after negation folding.
    Equality(bool, FofTerm, FofTerm),
}

/// CEP:WHAT: One parsed CNF directive's payload: role, name, literals.
/// CEP:WHY: The driver and the include selection key on role and name (negated_conjecture CNF clauses are the goal); the IR conversion consumes the literals.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: owned record.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedCnf {
    /// The declared role of the clause.
    pub role: TptpRole,
    /// The declared clause name.
    pub name: String,
    /// The parsed literals in input order.
    pub literals: Vec<CnfLiteral>,
}

impl<'i, 'r> Parser<'i, 'r> {
    /// CEP:WHAT: Parses the TPTP top level: a sequence of fof/cnf/include directives terminated by '.'.
    /// CEP:WHY: The driver loop of design 6.2 stage 2; the directive keyword selects the sub-parser.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax for unknown directives and malformed shapes, the bound errors per charge point, IncludeUnreadable for unreadable include files; never panics.
    /// CEP:ASSUMES: the parser is fresh.
    /// CEP:COST: linear in input.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, fof_formulas_reach_the_ast}.
    /// CEP:SECURITY: none.
    fn parse_top_level(&mut self) -> Result<Vec<ParsedCnf>, ParseError> {
        let mut clauses: Vec<ParsedCnf> = Vec::new();
        while self.lookahead.is_some() {
            let directive = self.eat()?;
            if directive.kind != TokenKind::LowerWord {
                return Err(self.lexer.syntax_error());
            }
            match directive.as_str() {
                "fof" | "cnf" => {
                    self.expect("(")?;
                    let name = self.parse_name()?;
                    self.expect(",")?;
                    let role = self.parse_role()?;
                    self.expect(",")?;
                    if directive.as_str() == "fof" {
                        let formula = self.parse_formula()?;
                        let formula = self.check_binding(formula)?;
                        self.formulas.push(ParsedFof {
                            role,
                            name: String::from(name),
                            formula,
                        });
                    } else {
                        let literals = self.parse_cnf_formula()?;
                        clauses.push(ParsedCnf {
                            role,
                            name: String::from(name),
                            literals,
                        });
                    }
                    // Optional source and annotation.
                    if self.accept(",")? {
                        self.skip_source()?;
                    }
                    self.expect(")")?;
                    self.expect(".")?;
                }
                "include" => {
                    self.expect("(")?;
                    let file = self.parse_name()?;
                    let selection = self.parse_optional_selection()?;
                    self.expect(")")?;
                    self.expect(".")?;
                    let (mut included_formulas, mut included_clauses) =
                        self.parse_include(file, selection.as_ref())?;
                    self.formulas.append(&mut included_formulas);
                    clauses.append(&mut included_clauses);
                }
                _ => {
                    return Err(ParseError::Syntax {
                        line: directive.line,
                        column: directive.column,
                    })
                }
            }
        }
        Ok(clauses)
    }

    /// CEP:WHAT: Parses a name token (lowercase word, quoted word, or integer).
    /// CEP:WHY: Directive names accept the three TPTP name classes.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax for a non-name token; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one token.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn parse_name(&mut self) -> Result<&'i str, ParseError> {
        let token = self.eat()?;
        match token.kind {
            TokenKind::LowerWord | TokenKind::Integer => Ok(token.as_str()),
            TokenKind::QuotedWord => {
                let bytes = token.text;
                // Strip the surrounding quotes so the name (and the include
                // path it may become) is the quoted content itself.
                Ok(
                    std::str::from_utf8(&bytes[1..bytes.len() - 1]).map_err(|_| {
                        ParseError::Syntax {
                            line: token.line,
                            column: token.column,
                        }
                    })?,
                )
            }
            _ => Err(ParseError::Syntax {
                line: token.line,
                column: token.column,
            }),
        }
    }

    /// CEP:WHAT: Parses and validates a role token.
    /// CEP:WHY: Roles drive the driver's stage-1 handling; unknown roles are rejected, not downgraded.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax for a non-word token, UnknownRole for a token outside TptpRole::from_token; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one token plus a match.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_unknown_role.
    /// CEP:SECURITY: none.
    fn parse_role(&mut self) -> Result<TptpRole, ParseError> {
        let token = self.eat()?;
        if token.kind != TokenKind::LowerWord {
            return Err(ParseError::Syntax {
                line: token.line,
                column: token.column,
            });
        }
        TptpRole::from_token(token.as_str()).ok_or(ParseError::UnknownRole)
    }

    /// CEP:WHAT: Parses an optional include selection list ([name, ...]).
    /// CEP:WHY: TPTP include directives may select named formulas; the selection filters the included unit.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax for a malformed list; never panics.
    /// CEP:ASSUMES: called after the include file name.
    /// CEP:COST: linear in the selection.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::include_selection_filters_by_name.
    /// CEP:SECURITY: none.
    fn parse_optional_selection(&mut self) -> Result<Option<Vec<String>>, ParseError> {
        if !self.accept(",")? {
            return Ok(None);
        }
        self.expect("[")?;
        let mut selection = Vec::new();
        if !self.accept("]")? {
            loop {
                let name = self.parse_name()?;
                selection.push(String::from(name));
                if self.accept("]")? {
                    break;
                }
                self.expect(",")?;
            }
        }
        Ok(Some(selection))
    }

    /// CEP:WHAT: Skips the optional source/annotation suffix of a directive (everything up to the depth-0 closing parenthesis).
    /// CEP:WHY: Sources and annotations carry no semantic weight for the refutation; the nesting counter keeps '(' ')' '[' ']' inside annotations from terminating the scan early.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax at end of input before the closing parenthesis; never panics.
    /// CEP:ASSUMES: called after the formula body with the ',' consumed; stops BEFORE consuming the depth-0 ')'.
    /// CEP:COST: linear in the annotation.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
    /// CEP:SECURITY: none.
    fn skip_source(&mut self) -> Result<(), ParseError> {
        let mut depth: u32 = 0;
        loop {
            match self.lookahead {
                Some(token) if token.as_str() == ")" && depth == 0 => return Ok(()),
                None => return Err(self.lexer.syntax_error()),
                _ => {}
            }
            let token = self.eat()?;
            match token.as_str() {
                "(" | "[" => depth += 1,
                ")" | "]" => {
                    if depth == 0 {
                        return Err(ParseError::Syntax {
                            line: token.line,
                            column: token.column,
                        });
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
    }

    /// CEP:WHAT: Reads an include file under the include root and parses it recursively with the selection filter, sharing the semantic state (builder, name table, registries, budgets) so symbol ids stay coherent across files.
    /// CEP:WHY: TPTP libraries organize axioms in files; one shared signature is the TPTP semantic; the semantic state moves into the child parser over the file's bytes and back (the child's own fresh state is discarded).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns IncludeUnreadable when the file cannot be read or no root is configured, TooLarge past the byte bound, the include bounds via enter_include, and everything the recursive top level can return; never panics.
    /// CEP:ASSUMES: called with the include bounds not yet charged for this file.
    /// CEP:COST: O(file) plus the recursive parse.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{include_depth_is_bounded, include_count_is_bounded, include_selection_filters_by_name}.
    /// CEP:SECURITY: the include path is joined under the caller-supplied root only; include files pass the same kMaxInputBytes gate.
    fn parse_include(
        &mut self,
        file: &str,
        selection: Option<&Vec<String>>,
    ) -> Result<(Vec<ParsedFof>, Vec<ParsedCnf>), ParseError> {
        self.enter_include()?;
        let root = match self.include_root {
            Some(root) => root,
            None => {
                self.leave_include();
                return Err(ParseError::IncludeUnreadable);
            }
        };
        let path = root.join(file);
        let bytes = match std::fs::read(&path) {
            Ok(bytes) => bytes,
            Err(_) => {
                self.leave_include();
                return Err(ParseError::IncludeUnreadable);
            }
        };
        if bytes.len() as u64 > kMaxInputBytes {
            self.leave_include();
            return Err(ParseError::TooLarge);
        }
        let mut child = Parser::new(&bytes, self.include_root)?;
        std::mem::swap(&mut child.builder, &mut self.builder);
        child.names = std::mem::take(&mut self.names);
        child.symbol_ids = std::mem::take(&mut self.symbol_ids);
        child.symbols_arity = std::mem::take(&mut self.symbols_arity);
        child.limits = self.limits;
        child.nodes_charged = self.nodes_charged;
        child.include_depth = self.include_depth;
        child.include_count = self.include_count;
        let result = child.parse_top_level();
        std::mem::swap(&mut child.builder, &mut self.builder);
        self.names = std::mem::take(&mut child.names);
        self.symbol_ids = std::mem::take(&mut child.symbol_ids);
        self.symbols_arity = std::mem::take(&mut child.symbols_arity);
        self.limits = child.limits;
        self.nodes_charged = child.nodes_charged;
        self.include_depth = child.include_depth;
        self.include_count = child.include_count;
        self.leave_include();
        let mut included_formulas = std::mem::take(&mut child.formulas);
        let mut clauses = result?;
        if let Some(selection) = selection {
            included_formulas.retain(|formula| selection.contains(&formula.name));
            clauses.retain(|clause| selection.contains(&clause.name));
        }
        Ok((included_formulas, clauses))
    }
}

/// CEP:WHAT: The shape of one parsed atomic formula: a predicate application (symbol id and argument terms) or an equality over two terms.
/// CEP:WHY: The FOF and CNF layers share the atom grammar; the shared shape keeps the predicate-versus-function declaration decision in one place (an atom head is declared as a predicate, an equality side as a function).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: owned record.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, binds_all_connectives}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AtomicShape {
    /// A predicate application by symbol id with argument terms.
    Predicate(u32, Vec<FofTerm>),
    /// An equality atom over the parsed left and right terms.
    Equality(FofTerm, FofTerm),
}

impl<'i, 'r> Parser<'i, 'r> {
    /// CEP:WHAT: Parses a unit formula: unary negation, quantified formulas, parenthesized formulas, the constants, and atoms.
    /// CEP:WHY: The tightest formula layer of the TPTP precedence (quantifiers, negation, atoms).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes, TooDeep past kMaxParseDepth, QuantifierTooDeep past kMaxQuantifierDepth, TooManyNodes past the node budget; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(subformula nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{rejects_parse_depth, rejects_quantifier_depth, binds_all_connectives}.
    /// CEP:SECURITY: recursion bounded by kMaxParseDepth.
    fn parse_unit_formula(&mut self) -> Result<FofFormula, ParseError> {
        self.enter_depth()?;
        let result = self.parse_unit_formula_inner();
        self.depth -= 1;
        result
    }

    /// CEP:WHAT: The depth-guarded body of parse_unit_formula.
    /// CEP:WHY: The guard wrapper charges kMaxParseDepth (or the injected bound) at every recursive-descent entry and releases it at exit, so runaway nesting surfaces as TooDeep instead of a stack overflow (CEP&CC 22.10).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: enter_depth returns TooDeep past the bound.
    /// CEP:ASSUMES: paired depth release on every path.
    /// CEP:COST: constant per entry.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_parse_depth.
    /// CEP:SECURITY: stack-overflow mitigation.
    fn parse_unit_formula_inner(&mut self) -> Result<FofFormula, ParseError> {
        let token = match self.lookahead {
            Some(token) => token,
            None => return Err(self.lexer.syntax_error()),
        };
        match token.as_str() {
            "~" => {
                self.eat()?;
                let body = self.parse_unit_formula()?;
                self.charge_node()?;
                Ok(FofFormula::Not(Box::new(body)))
            }
            "!" | "?" => {
                self.eat()?;
                self.enter_quantifier()?;
                let result = self.parse_quantified_body(token.as_str() == "!");
                self.leave_quantifier();
                result
            }
            "(" => {
                self.eat()?;
                let formula = self.parse_formula()?;
                self.expect(")")?;
                Ok(formula)
            }
            "$true" => {
                self.eat()?;
                self.charge_node()?;
                Ok(FofFormula::True)
            }
            "$false" => {
                self.eat()?;
                self.charge_node()?;
                Ok(FofFormula::False)
            }
            _ => self.parse_atomic_formula(),
        }
    }

    /// CEP:WHAT: Parses the quantifier tail: [variable list] : body (the body is a unit formula per the TPTP grammar).
    /// CEP:WHY: Quantifier grammar; the bound variables are interned in the name table.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes and the unit-formula errors of the body; never panics.
    /// CEP:ASSUMES: the quantifier token was consumed; the depth was charged by the caller.
    /// CEP:COST: O(variables + body nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::fof_formulas_reach_the_ast.
    /// CEP:SECURITY: none.
    fn parse_quantified_body(&mut self, universal: bool) -> Result<FofFormula, ParseError> {
        self.expect("[")?;
        let mut variables = Vec::new();
        loop {
            let token = self.eat()?;
            if token.kind != TokenKind::UpperWord {
                return Err(ParseError::Syntax {
                    line: token.line,
                    column: token.column,
                });
            }
            variables.push(self.names.intern(token.as_str()));
            if self.accept("]")? {
                break;
            }
            self.expect(",")?;
        }
        self.expect(":")?;
        let body = self.parse_unit_formula()?;
        self.charge_node()?;
        Ok(if universal {
            FofFormula::Forall(variables, Box::new(body))
        } else {
            FofFormula::Exists(variables, Box::new(body))
        })
    }

    /// CEP:WHAT: Parses an atomic formula: a predicate application, a term equality, or a disequality (negated equality).
    /// CEP:WHY: The atom layer of the TPTP grammar; the head token is declared as a PREDICATE (an atom is never a term), the equality sides as functions, so the frozen table's kinds match the IR interning calls.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes (a bare variable atom, a predicate application on an equality side), ArityMismatch on a signature change, TooManySymbols past the universe, TooManyNodes past the budget; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(atom size).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::binds_all_connectives.
    /// CEP:SECURITY: none.
    fn parse_atomic_formula(&mut self) -> Result<FofFormula, ParseError> {
        match self.parse_atomic_shape()? {
            AtomicShape::Predicate(symbol, args) => Ok(FofFormula::Predicate(symbol, args)),
            AtomicShape::Equality(left, right) => Ok(FofFormula::Equality(left, right)),
        }
    }

    // CEP:WHAT: Parses the shared atom shape: a word head with an optional argument list (declared as a predicate) or a term equality over '=' or '!=' (the head declared as a function when the equality form wins).
    // CEP:WHY: TPTP plain atoms and equality atoms share the term syntax; the lookahead after the head token decides the declaration kind, so the frozen table never carries a Function entry that the IR layer interns as a Predicate (the SymbolKindMismatch class).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns Syntax for a bare variable atom, a numeric head, or an equality whose left side is a parenthesized predicate application; declaration and budget errors propagate; never panics.
    // CEP:ASSUMES: the caller consumed any negation.
    // CEP:COST: O(atom size).
    // CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
    // CEP:SECURITY: none.
    fn parse_atomic_shape(&mut self) -> Result<AtomicShape, ParseError> {
        let token = self.eat()?;
        match token.kind {
            TokenKind::UpperWord => {
                let left = FofTerm::Variable(self.names.intern(token.as_str()));
                if self.accept("=")? {
                    let right = self.parse_term()?;
                    return Ok(AtomicShape::Equality(left, right));
                }
                if self.accept("!=")? {
                    let right = self.parse_term()?;
                    return Ok(AtomicShape::Equality(left, right));
                }
                Err(ParseError::Syntax {
                    line: token.line,
                    column: token.column,
                })
            }
            TokenKind::LowerWord | TokenKind::QuotedWord | TokenKind::DollarWord => {
                let parenthesized = self.accept("(")?;
                if parenthesized {
                    let mut args: Vec<FofTerm> = Vec::new();
                    if !self.accept(")")? {
                        loop {
                            args.push(self.parse_term()?);
                            if self.accept(")")? {
                                break;
                            }
                            self.expect(",")?;
                        }
                    }
                    // A parenthesized head is a predicate application; an
                    // equality over it is malformed (predicates are not terms).
                    let equality_follows = self
                        .lookahead
                        .as_ref()
                        .map(|token| token.as_str() == "=" || token.as_str() == "!=")
                        .unwrap_or(false);
                    if equality_follows {
                        return Err(self.lexer.syntax_error());
                    }
                    let arity = args.len() as u16;
                    let sorts = vec![SortId(0); arity as usize];
                    let symbol =
                        self.declare_symbol(token.as_str(), SymbolKind::Predicate, arity, &sorts)?;
                    self.charge_node()?;
                    Ok(AtomicShape::Predicate(symbol, args))
                } else {
                    let equality_follows = self
                        .lookahead
                        .as_ref()
                        .map(|token| token.as_str() == "=" || token.as_str() == "!=")
                        .unwrap_or(false);
                    if equality_follows {
                        self.eat()?;
                        let sorts = [];
                        let symbol =
                            self.declare_symbol(token.as_str(), SymbolKind::Function, 0, &sorts)?;
                        let left = FofTerm::Application(symbol, Vec::new());
                        let right = self.parse_term()?;
                        self.charge_node()?;
                        Ok(AtomicShape::Equality(left, right))
                    } else {
                        let sorts = [];
                        let symbol =
                            self.declare_symbol(token.as_str(), SymbolKind::Predicate, 0, &sorts)?;
                        self.charge_node()?;
                        Ok(AtomicShape::Predicate(symbol, Vec::new()))
                    }
                }
            }
            _ => Err(ParseError::Syntax {
                line: token.line,
                column: token.column,
            }),
        }
    }

    /// CEP:WHAT: Parses a term: a variable or a function application with arguments.
    /// CEP:WHY: The term layer of the TPTP grammar; numeric terms are rejected (documented limitation: untyped FOF carries no numeric syntax in this delivery).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes (including numeric terms), TooDeep past kMaxParseDepth, TooManyNodes past the budget, ArityMismatch/TooManySymbols from declaration; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(term nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
    /// CEP:SECURITY: recursion bounded by kMaxParseDepth.
    fn parse_term(&mut self) -> Result<FofTerm, ParseError> {
        self.enter_depth()?;
        let result = self.parse_term_inner();
        self.depth -= 1;
        result
    }

    /// CEP:WHAT: The depth-guarded body of parse_term.
    /// CEP:WHY: The guard wrapper of the term recursion (argument lists nest).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: enter_depth returns TooDeep past the bound.
    /// CEP:ASSUMES: paired depth release on every path.
    /// CEP:COST: constant per entry.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_parse_depth.
    /// CEP:SECURITY: stack-overflow mitigation.
    fn parse_term_inner(&mut self) -> Result<FofTerm, ParseError> {
        let token = self.eat()?;
        match token.kind {
            TokenKind::UpperWord => {
                self.charge_node()?;
                Ok(FofTerm::Variable(self.names.intern(token.as_str())))
            }
            TokenKind::LowerWord | TokenKind::QuotedWord | TokenKind::DollarWord => {
                if self.accept("(")? {
                    let mut args = Vec::new();
                    if !self.accept(")")? {
                        loop {
                            args.push(self.parse_term()?);
                            if self.accept(")")? {
                                break;
                            }
                            self.expect(",")?;
                        }
                    }
                    let arity = args.len() as u16;
                    let sorts = vec![SortId(0); arity as usize];
                    let symbol =
                        self.declare_symbol(token.as_str(), SymbolKind::Function, arity, &sorts)?;
                    self.charge_node()?;
                    Ok(FofTerm::Application(symbol, args))
                } else {
                    let symbol =
                        self.declare_symbol(token.as_str(), SymbolKind::Function, 0, &[])?;
                    self.charge_node()?;
                    Ok(FofTerm::Application(symbol, Vec::new()))
                }
            }
            _ => Err(ParseError::Syntax {
                line: token.line,
                column: token.column,
            }),
        }
    }

    /// CEP:WHAT: Parses the full formula precedence ladder: the non-associative binary layer over the implication layer over disjunction over conjunction over unit formulas.
    /// CEP:WHY: TPTP precedence: & binds tighter than |, which binds tighter than => and <=, which bind tighter than the non-associative <=>, <~>, ~|, ~&.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on a second non-associative connective at one level and the sub-layer errors; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(formula nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::binds_all_connectives.
    /// CEP:SECURITY: recursion bounded by kMaxParseDepth through the unit layer.
    fn parse_formula(&mut self) -> Result<FofFormula, ParseError> {
        let left = self.parse_implies_formula()?;
        let text = match self.lookahead {
            Some(token) => token.as_str(),
            None => return Ok(left),
        };
        if text == "<=>" || text == "<~>" || text == "~|" || text == "~&" {
            self.eat()?;
            let right = self.parse_implies_formula()?;
            self.charge_node()?;
            if let Some(second) = self.lookahead {
                let second_text = second.as_str();
                if second_text == "<=>"
                    || second_text == "<~>"
                    || second_text == "~|"
                    || second_text == "~&"
                {
                    return Err(self.lexer.syntax_error());
                }
            }
            return Ok(match text {
                "<=>" => FofFormula::Equivalent(Box::new(left), Box::new(right)),
                "<~>" => FofFormula::NotEquivalent(Box::new(left), Box::new(right)),
                "~|" => FofFormula::NotOr(Box::new(left), Box::new(right)),
                _ => FofFormula::NotAnd(Box::new(left), Box::new(right)),
            });
        }
        Ok(left)
    }

    /// CEP:WHAT: Parses the implication layer: => chains nest right, <= chains nest left, mixing the two at one level is a syntax error.
    /// CEP:WHY: The TPTP associativity of the implication connectives.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on mixed chains and sub-layer errors; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(operands).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::binds_all_connectives.
    /// CEP:SECURITY: none.
    fn parse_implies_formula(&mut self) -> Result<FofFormula, ParseError> {
        let left = self.parse_or_formula()?;
        let text = match self.lookahead {
            Some(token) => token.as_str(),
            None => return Ok(left),
        };
        if text == "=>" {
            self.eat()?;
            let right = self.parse_implies_formula()?;
            self.charge_node()?;
            return Ok(FofFormula::Implies(Box::new(left), Box::new(right)));
        }
        if text == "<=" {
            self.eat()?;
            let mut acc = left;
            loop {
                let right = self.parse_or_formula()?;
                self.charge_node()?;
                acc = FofFormula::ReverseImplies(Box::new(acc), Box::new(right));
                match self.lookahead {
                    Some(token) if token.as_str() == "<=" => {
                        self.eat()?;
                    }
                    Some(token) if token.as_str() == "=>" => {
                        return Err(self.lexer.syntax_error());
                    }
                    _ => return Ok(acc),
                }
            }
        }
        Ok(left)
    }

    /// CEP:WHAT: Parses the disjunction layer: one or more 'a | b' operands flattened into one Or node.
    /// CEP:WHY: '|' is associative in TPTP; flattening keeps the AST close to the clause shape.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: sub-layer errors; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(operands).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::binds_all_connectives.
    /// CEP:SECURITY: none.
    fn parse_or_formula(&mut self) -> Result<FofFormula, ParseError> {
        let first = self.parse_and_formula()?;
        if !self.accept("|")? {
            return Ok(first);
        }
        let mut operands = vec![first];
        loop {
            operands.push(self.parse_and_formula()?);
            if !self.accept("|")? {
                break;
            }
        }
        self.charge_node()?;
        Ok(FofFormula::Or(operands))
    }

    /// CEP:WHAT: Parses the conjunction layer: one or more 'a & b' operands flattened into one And node.
    /// CEP:WHY: '&' is associative in TPTP; flattening keeps the AST close to the clause shape.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: sub-layer errors; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(operands).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::binds_all_connectives.
    /// CEP:SECURITY: none.
    fn parse_and_formula(&mut self) -> Result<FofFormula, ParseError> {
        let first = self.parse_unit_formula()?;
        if !self.accept("&")? {
            return Ok(first);
        }
        let mut operands = vec![first];
        loop {
            operands.push(self.parse_unit_formula()?);
            if !self.accept("&")? {
                break;
            }
        }
        self.charge_node()?;
        Ok(FofFormula::And(operands))
    }

    /// CEP:WHAT: Parses a CNF formula: a literal or a parenthesized disjunction of literals, returned as the flat literal list.
    /// CEP:WHY: The CNF layer of the TPTP grammar; parenthesized disjunctions recurse with the parse-depth guard (nested parens wrap disjunctions, so the recursion re-enters this parser), and the disjunction stays flat for the IR conversion.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes, TooDeep past kMaxParseDepth (or the injected bound), TooManyNodes past the budget; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(literals).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, rejects_parse_depth}.
    /// CEP:SECURITY: literal count bounded at IR construction by kMaxClauseLiterals; recursion bounded by the parse-depth guard.
    fn parse_cnf_formula(&mut self) -> Result<Vec<CnfLiteral>, ParseError> {
        if self.accept("(")? {
            self.enter_depth()?;
            let nested = self.parse_cnf_formula();
            self.depth -= 1;
            let mut literals = nested?;
            self.expect(")")?;
            while self.accept("|")? {
                literals.push(self.parse_cnf_literal()?);
            }
            return Ok(literals);
        }
        let first = self.parse_cnf_literal()?;
        let mut literals = vec![first];
        while self.accept("|")? {
            literals.push(self.parse_cnf_literal()?);
        }
        Ok(literals)
    }

    /// CEP:WHAT: Parses one CNF literal: optional negation over an atom, $true, $false, or an equality/disequality.
    /// CEP:WHY: The literal layer of the CNF grammar; the shared atom shape decides the declaration kinds, and the disequality folds its negation into the Equality variant's sign.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Syntax on malformed shapes (a bare variable atom) and the declaration/budget errors; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(literal size).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
    /// CEP:SECURITY: none.
    fn parse_cnf_literal(&mut self) -> Result<CnfLiteral, ParseError> {
        let negated = self.accept("~")?;
        let polarity = !negated;
        if self.accept("$true")? {
            return Ok(CnfLiteral::True(polarity));
        }
        if self.accept("$false")? {
            return Ok(CnfLiteral::False(polarity));
        }
        match self.parse_atomic_shape()? {
            AtomicShape::Predicate(symbol, args) => Ok(CnfLiteral::Atom(polarity, symbol, args)),
            AtomicShape::Equality(left, right) => Ok(CnfLiteral::Equality(polarity, left, right)),
        }
    }

    /// CEP:WHAT: Verifies that every variable in the formula is bound by an enclosing quantifier.
    /// CEP:WHY: TPTP FOF prohibits free variables; the check is a bottom-up walk carrying the bound set (names bound by Forall/Exists nodes). CNF clauses skip this check: clause variables are universally quantified by convention.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns FreeVariable when a variable escapes its quantifiers; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_free_variable.
    /// CEP:SECURITY: none.
    fn check_binding(&self, formula: FofFormula) -> Result<FofFormula, ParseError> {
        let mut bound: HashSet<u32> = HashSet::new();
        if self.formula_is_bound(&formula, &mut bound) {
            Ok(formula)
        } else {
            Err(ParseError::FreeVariable)
        }
    }

    /// CEP:WHAT: The binding walk: true when every variable under the node is in the bound set (quantifier bodies extend it, then restore it).
    /// CEP:WHY: The recursive core of check_binding.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails; recursion depth equals the AST depth (bounded by kMaxParseDepth at parse time).
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_free_variable.
    /// CEP:SECURITY: none.
    fn formula_is_bound(&self, formula: &FofFormula, bound: &mut HashSet<u32>) -> bool {
        match formula {
            FofFormula::True | FofFormula::False => true,
            FofFormula::Predicate(_, args) => self.terms_are_bound(args, bound),
            FofFormula::Equality(left, right) => {
                self.term_is_bound(left, bound) && self.term_is_bound(right, bound)
            }
            FofFormula::Not(body) => self.formula_is_bound(body, bound),
            FofFormula::And(operands) | FofFormula::Or(operands) => operands
                .iter()
                .all(|operand| self.formula_is_bound(operand, bound)),
            FofFormula::Implies(left, right)
            | FofFormula::ReverseImplies(left, right)
            | FofFormula::Equivalent(left, right)
            | FofFormula::NotEquivalent(left, right)
            | FofFormula::NotOr(left, right)
            | FofFormula::NotAnd(left, right) => {
                self.formula_is_bound(left, bound) && self.formula_is_bound(right, bound)
            }
            FofFormula::Forall(variables, body) | FofFormula::Exists(variables, body) => {
                for variable in variables {
                    bound.insert(*variable);
                }
                let result = self.formula_is_bound(body, bound);
                for variable in variables {
                    bound.remove(variable);
                }
                result
            }
        }
    }

    /// CEP:WHAT: The term binding walk: variables must be in the bound set, application arguments recurse.
    /// CEP:WHY: The term case of formula_is_bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(term nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_free_variable.
    /// CEP:SECURITY: none.
    fn term_is_bound(&self, term: &FofTerm, bound: &mut HashSet<u32>) -> bool {
        match term {
            FofTerm::Variable(id) => bound.contains(id),
            FofTerm::Application(_, args) => self.terms_are_bound(args, bound),
        }
    }

    /// CEP:WHAT: The multi-term binding walk.
    /// CEP:WHY: The argument-list case of the binding walk.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(term nodes).
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_free_variable.
    /// CEP:SECURITY: none.
    fn terms_are_bound(&self, terms: &[FofTerm], bound: &mut HashSet<u32>) -> bool {
        terms.iter().all(|term| self.term_is_bound(term, bound))
    }
}

/// CEP:WHAT: Parses a TPTP input (CNF and FOF directives with includes) into the parsed problem: the unified IR for every CNF clause, the validated FOF ASTs, the frozen symbol table, and the name table.
/// CEP:WHY: The design 6.2 five-stage shape for the primary input format: the size gate (stage 0), the lexer and recursive descent (stages 1-2), role/binding/arity validation (stage 3), IR construction through the builder and the term/clause stores (stage 4), and the ParsedProblem return (stage 5); ticket CEP-1006.
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns the shared ParseError vocabulary (size, depth, node, symbol, quantifier, include bounds; syntax, role, arity, binding defects; IrSymbol/IrTerm/IrClause construction exhaustion); never panics.
/// CEP:ASSUMES: the arena outlives the returned problem; include paths resolve under the caller-supplied root.
/// CEP:COST: O(input) for parsing plus O(IR) for construction, both under the config bounds.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: every bound of design 6.3 is enforced (see the module and Parser fields); input bytes are never echoed into errors.
pub fn parse_tptp<'a>(
    arena: &'a Arena,
    input: &[u8],
    include_root: Option<&Path>,
) -> Result<ParsedProblem<'a>, ParseError> {
    parse_tptp_with_limits(arena, input, include_root, ParserLimits::standard())
}

/// CEP:WHAT: Parses a TPTP input under injected parser limits (node budget, parse depth, quantifier depth).
/// CEP:WHY: The injectable-limits pattern lets a driver impose tighter host-specific budgets and lets the test suite exercise the bound paths without materializing standard-size inputs; the injected values are clamped to the config constants so the design 6.3 bounds are never exceeded.
/// CEP:STATUS: complete
/// CEP:FAILURE: as parse_tptp.
/// CEP:ASSUMES: as parse_tptp.
/// CEP:COST: as parse_tptp.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{rejects_node_budget, rejects_parse_depth, rejects_quantifier_depth}.
/// CEP:SECURITY: clamping preserves the design 6.3 bounds under any injection.
pub fn parse_tptp_with_limits<'a>(
    arena: &'a Arena,
    input: &[u8],
    include_root: Option<&Path>,
    limits: ParserLimits,
) -> Result<ParsedProblem<'a>, ParseError> {
    if input.len() as u64 > kMaxInputBytes {
        return Err(ParseError::TooLarge);
    }
    let mut parser = Parser::new(input, include_root)?;
    parser.limits = limits;
    let clause_directives = parser.parse_top_level()?;
    let cnf_clauses = clause_directives.clone();
    let symbols = parser
        .builder
        .finalize(arena)
        .map_err(ParseError::IrSymbol)?;
    let terms = TermStore::new(arena).map_err(ParseError::IrTerm)?;
    let clause_store = ClauseStore::new(arena);
    let mut clause_ptrs: Vec<mapt_hot::ir::clause::ClausePtr> =
        Vec::with_capacity(clause_directives.len());
    for directive in clause_directives.iter() {
        if let Some(ptr) =
            build_cnf_clause(&terms, &symbols, &parser.names, directive, &clause_store)?
        {
            clause_ptrs.push(ptr);
        }
    }
    Ok(ParsedProblem {
        symbols,
        builder: parser.builder,
        terms,
        clauses: clause_store,
        clause_ptrs,
        formulas: parser.formulas,
        cnf_clauses,
        names: parser.names,
    })
}

/// CEP:WHAT: Converts one parsed CNF directive into an IR clause record, applying the True/False literal semantics (a $true positive or $false negative literal makes the clause tautologous and drops it; the vacuous residue of the opposite polarities is skipped; an all-vacuous clause becomes the empty clause).
/// CEP:WHY: Design 6.2 stage 4: AST to unified IR with hash-consed terms and assigned clause ids; the constants have their disjunctive semantics applied at the boundary so the search never sees a literal it cannot order.
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns ParseError::IrTerm/IrClause for interning and store failures (depth, variable, capacity bounds with exact kinds); never panics.
/// CEP:ASSUMES: the directive passed parsing and validation.
/// CEP:COST: O(clause size) interning.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: literal count bounded by kMaxClauseLiterals through the store; distinct variable count bounded by kMaxVariablesPerClause through intern_var.
fn build_cnf_clause(
    terms: &TermStore<'_>,
    symbols: &mapt_hot::ir::symbol_table::SymbolTable<'_>,
    names: &NameTable,
    directive: &ParsedCnf,
    clause_store: &ClauseStore<'_>,
) -> Result<Option<mapt_hot::ir::clause::ClausePtr>, ParseError> {
    let mut tautology = false;
    let mut literals: Vec<Literal> = Vec::new();
    let mut variable_index: HashMap<u32, u32> = HashMap::new();
    for literal in directive.literals.iter() {
        match literal {
            CnfLiteral::True(polarity) => {
                if *polarity {
                    tautology = true;
                }
            }
            CnfLiteral::False(polarity) => {
                if !*polarity {
                    tautology = true;
                }
            }
            CnfLiteral::Atom(polarity, symbol, args) => {
                // The atom head is a PREDICATE symbol; only its arguments go
                // through the function-term interning path.
                let mut children: Vec<TermPtr> = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    children.push(intern_ast_term(
                        terms,
                        symbols,
                        names,
                        arg,
                        &mut variable_index,
                    )?);
                }
                let atom = terms.intern_pred(symbols, *symbol, &children)?;
                literals.push(Literal::new(atom, *polarity));
            }
            CnfLiteral::Equality(polarity, left, right) => {
                let left_ptr = intern_ast_term(terms, symbols, names, left, &mut variable_index)?;
                let right_ptr = intern_ast_term(terms, symbols, names, right, &mut variable_index)?;
                let atom = terms.intern_eq(symbols, left_ptr, right_ptr)?;
                literals.push(Literal::new(atom, *polarity));
            }
        }
    }
    if tautology {
        return Ok(None);
    }
    if literals.len() > kMaxClauseLiterals as usize {
        return Err(ParseError::IrClause(ClauseError::TooManyLiterals));
    }
    let ptr = clause_store
        .new_clause(terms, &literals, 0, input_derivation())
        .map_err(ParseError::IrClause)?;
    Ok(Some(ptr))
}

/// CEP:WHAT: Interns one AST term into the term store, mapping clause variables to dense clause-local indices in first-appearance order.
/// CEP:WHY: Design 6.2 stage 4: hash-consed terms; the per-clause namespace is the renamed-apart discipline of Spec 02 section 5 (every clause owns variables 0..n).
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns ParseError::IrTerm for interning failures (VariableOutOfRange past kMaxVariablesPerClause, DepthExceeded past kMaxTermDepth, capacity); never panics.
/// CEP:ASSUMES: the AST term was parsed by the same parser that produced the name table.
/// CEP:COST: O(term nodes), each intern O(1) amortized.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: recursion depth equals the AST depth (bounded by kMaxParseDepth at parse time).
fn intern_ast_term(
    terms: &TermStore<'_>,
    symbols: &mapt_hot::ir::symbol_table::SymbolTable<'_>,
    names: &NameTable,
    term: &FofTerm,
    variable_index: &mut HashMap<u32, u32>,
) -> Result<TermPtr, ParseError> {
    match term {
        FofTerm::Variable(id) => {
            let next = variable_index.len() as u32;
            let index = *variable_index.entry(*id).or_insert(next);
            let _ = names;
            Ok(terms.intern_var(index)?)
        }
        FofTerm::Application(symbol, args) => {
            let mut children: Vec<TermPtr> = Vec::with_capacity(args.len());
            for arg in args.iter() {
                children.push(intern_ast_term(terms, symbols, names, arg, variable_index)?);
            }
            Ok(terms.intern_fun(symbols, *symbol, &children)?)
        }
    }
}

/// CEP:WHAT: Builds the input derivation record shared by every parsed clause.
/// CEP:WHY: Design 5.3: input clauses carry the Input rule with no parents; one constructor keeps the sentinel discipline in one place.
/// CEP:STATUS: complete
/// CEP:FAILURE: never fails.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; kMaxDerivationParents],
        substitution: kInvalidSubstitutionOffset,
    }
}
