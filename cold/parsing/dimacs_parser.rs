// CEP:FILE: cold/parsing/dimacs_parser.rs
/// CEP:WHAT: The DIMACS CNF front end (design 6.1): parses the "p cnf <vars> <clauses>" header, comment lines, and 0-terminated integer clause lines into input clauses of the unified IR (variables as 0-ary predicate symbols v1..vn, one hash-consed atom per literal).
/// CEP:WHY: Design 6.1 lists DIMACS as the tertiary input format (pure SAT benchmarks); routing it through the unified IR (design 6.2 stage 4) lets the SAT-competition corpus feed the same engines as TPTP input; ticket CEP-1006.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns ParseError per the shared vocabulary (super::ParseError); no panic, no exception (design 6.3).
/// CEP:ASSUMES: input bytes are untrusted; the arena is writable and large enough for the IR of the parsed formula.
/// CEP:COST: one pass over the bytes plus one interning pass; O(input) time, IR size bounded by the config bounds.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::{parses_header_and_clauses_into_ir, rejects_variable_beyond_header, rejects_missing_header, empty_clause_is_accepted, comments_and_trailing_percent_are_ignored, oversize_input_is_rejected}.
/// CEP:SECURITY: byte size gated by kMaxInputBytes before any IR construction; variable count gated by the declared header count and kMaxSymbolCount; per-clause literal count and total clause count enforced by the clause store's own bounds.
use super::{NameTable, ParseError, ParsedProblem};
use mapt_config::limits::{
    kInvalidClauseId, kInvalidSubstitutionOffset, kMaxClauseLiterals, kMaxDerivationParents,
    kMaxInputBytes, kMaxSymbolCount,
};
use mapt_hot::ir::clause::{ClauseError, ClauseStore, DerivationStep, InferenceRule};
use mapt_hot::ir::literal::Literal;
use mapt_hot::ir::term::TermStore;
use mapt_hot::memory::arena::Arena;
use std::string::String;
use std::vec::Vec;

/// CEP:WHAT: Parses a DIMACS CNF input into the unified IR.
/// CEP:WHY: The design 6.2 five-stage shape in one entry point: size gate (stage 0), lexing and parsing fused over the byte slice (DIMACS is line-oriented integers), validation against the header, IR construction through the symbol-table builder and the term/clause stores, and the ParsedProblem return.
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns ParseError::TooLarge over the byte bound, MissingHeader for header-order violations, VariableBeyondHeader for an index past the declared count, Syntax for a malformed token, IrSymbol/IrTerm/IrClause for IR construction exhaustion; never panics.
/// CEP:ASSUMES: the arena outlives the returned problem.
/// CEP:COST: O(input) plus IR construction; allocations cold-path legal.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::parses_header_and_clauses_into_ir.
/// CEP:SECURITY: every bound of design 6.3 that applies to this format is enforced (kMaxInputBytes here; symbol, clause, and literal bounds by the builder and stores).
pub fn parse_dimacs<'a>(arena: &'a Arena, input: &[u8]) -> Result<ParsedProblem<'a>, ParseError> {
    if input.len() as u64 > kMaxInputBytes {
        return Err(ParseError::TooLarge);
    }
    let mut context = DimacsContext::new();
    let clauses = scan_dimacs(input, &mut context)?;
    let mut builder = crate::symbol_table_builder::SymbolTableBuilder::new();
    // Sort pool: one untyped individual sort $i (DIMACS is propositional; the
    // sort occupies symbol id 0, so predicate v1 receives id 1, v2 id 2, ...).
    builder.declare_sort("$i").map_err(ParseError::IrSymbol)?;
    let mut variable_ids: Vec<u32> = Vec::with_capacity(context.variable_count as usize);
    for index in 1..=context.variable_count {
        let name = format_dimacs_variable(index);
        let declared = builder
            .declare_predicate(&name, 0, 1, &[])
            .map_err(ParseError::IrSymbol)?;
        variable_ids.push(declared);
    }
    let symbols = builder.finalize(arena).map_err(ParseError::IrSymbol)?;
    let terms = TermStore::new(arena).map_err(ParseError::IrTerm)?;
    let clause_store = ClauseStore::new(arena);
    let mut clause_ptrs: Vec<mapt_hot::ir::clause::ClausePtr> = Vec::with_capacity(clauses.len());
    for clause in clauses.iter() {
        let mut literals: Vec<Literal> = Vec::with_capacity(clause.len());
        for signed in clause.iter() {
            // The declared id of v<n> (the builder pre-declares the $i and $o
            // sorts, so the mapping is not the identity).
            let symbol_id = variable_ids[(signed.unsigned_abs() - 1) as usize];
            let atom = terms
                .intern_pred(&symbols, symbol_id, &[])
                .map_err(ParseError::IrTerm)?;
            literals.push(Literal::new(atom, *signed > 0));
        }
        let ptr = clause_store
            .new_clause(&terms, &literals, 0, input_derivation())
            .map_err(ParseError::IrClause)?;
        clause_ptrs.push(ptr);
    }
    Ok(ParsedProblem {
        symbols,
        builder,
        terms,
        clauses: clause_store,
        clause_ptrs,
        formulas: Vec::new(),
        cnf_clauses: Vec::new(),
        names: NameTable::default(),
    })
}

/// CEP:WHAT: Builds the input derivation record shared by every parsed clause.
/// CEP:WHY: Design 5.3: input clauses carry the Input rule with no parents; one constructor keeps the sentinel discipline (invalid ids, invalid substitution offset) in one place.
/// CEP:STATUS: complete
/// CEP:FAILURE: never fails.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::parses_header_and_clauses_into_ir.
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

/// CEP:WHAT: Renders the DIMACS variable spelling v<index> for the symbol table.
/// CEP:WHY: DIMACS variables are integers; the symbol table needs names, and the v-prefix cannot collide with a TPTP-style lowercase name space.
/// CEP:STATUS: complete
/// CEP:FAILURE: never fails.
/// CEP:ASSUMES: none.
/// CEP:COST: O(digits).
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::parses_header_and_clauses_into_ir.
/// CEP:SECURITY: none.
fn format_dimacs_variable(index: u32) -> String {
    std::format!("v{}", index)
}

/// CEP:WHAT: The DIMACS scan state: the declared variable count, the literals of the clause under construction, and the completed clauses.
/// CEP:WHY: The header count is the validation reference for every later variable index; the accumulation buffer keeps the clause shape until the 0 terminator.
/// CEP:STATUS: complete
/// CEP:FAILURE: never fails on its own; scan_dimacs translates the failures.
/// CEP:ASSUMES: none.
/// CEP:COST: buffers bounded by the declared counts.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::{rejects_variable_beyond_header, rejects_missing_header}.
/// CEP:SECURITY: none.
struct DimacsContext {
    variable_count: u32,
    current: Vec<i64>,
    clauses: Vec<Vec<i64>>,
}

impl DimacsContext {
    /// CEP:WHAT: Creates an empty scan state.
    /// CEP:WHY: Explicit construction point.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs.
    /// CEP:SECURITY: none.
    fn new() -> Self {
        DimacsContext {
            variable_count: 0,
            current: Vec::new(),
            clauses: Vec::new(),
        }
    }
}

/// CEP:WHAT: One pass over the DIMACS bytes: line-start comments ('c'), the single header, and 0-terminated clause lines; the SAT-competition '%' end marker truncates the input.
/// CEP:WHY: The DIMACS grammar is line-oriented integers; one fused lex/parse pass avoids a token materialization layer (design 6.2 stage 1-2) while keeping line/column attribution exact for Syntax errors.
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns MissingHeader when clauses precede the header or the header is missing/duplicated/malformed, VariableBeyondHeader for an index past the declared count, Syntax for a malformed integer or a clause without its terminator, IrClause past the literal bound; never panics.
/// CEP:ASSUMES: input passed the kMaxInputBytes gate.
/// CEP:COST: O(input).
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::{rejects_variable_beyond_header, rejects_missing_header, comments_and_trailing_percent_are_ignored}.
/// CEP:SECURITY: literal buffers bounded by kMaxClauseLiterals; the format has no nesting, so the parse-depth bound is trivially satisfied (depth 1, far below kMaxParseDepth).
fn scan_dimacs(input: &[u8], context: &mut DimacsContext) -> Result<Vec<Vec<i64>>, ParseError> {
    let mut header_seen = false;
    let mut line: u32 = 1;
    let mut column: u32 = 0;
    let mut index = 0usize;
    while index < input.len() {
        let byte = input[index];
        if byte == b'\n' {
            line += 1;
            column = 0;
            index += 1;
            continue;
        }
        column += 1;
        let at_line_start = column == 1;
        match byte {
            b'c' if at_line_start => {
                // Comment line: skip to end of line (the newline is consumed by the loop head).
                while index < input.len() && input[index] != b'\n' {
                    index += 1;
                    column += 1;
                }
            }
            b'%' if at_line_start && context.current.is_empty() => {
                // SAT-competition end marker: the remainder of the file is ignored.
                break;
            }
            b'p' if at_line_start => {
                if header_seen || !context.clauses.is_empty() || !context.current.is_empty() {
                    return Err(ParseError::MissingHeader);
                }
                index = scan_header(input, index, line, column, context)?;
                header_seen = true;
                column = 0;
            }
            b'-' | b'0'..=b'9' => {
                if !header_seen {
                    return Err(ParseError::MissingHeader);
                }
                let (value, next) = scan_integer(input, index, line, column)?;
                column += (next - index - 1) as u32;
                index = next;
                if value == 0 {
                    let completed = std::mem::take(&mut context.current);
                    context.clauses.push(completed);
                } else {
                    let variable = value.unsigned_abs();
                    if variable > context.variable_count as u64 {
                        return Err(ParseError::VariableBeyondHeader);
                    }
                    if context.current.len() >= kMaxClauseLiterals as usize {
                        return Err(ParseError::IrClause(ClauseError::TooManyLiterals));
                    }
                    context.current.push(value);
                }
            }
            b' ' | b'\t' | b'\r' => {
                index += 1;
            }
            _ => return Err(ParseError::Syntax { line, column }),
        }
    }
    if !header_seen {
        return Err(ParseError::MissingHeader);
    }
    if !context.current.is_empty() {
        // A final clause without its 0 terminator is malformed (DIMACS requires the terminator).
        return Err(ParseError::Syntax { line, column });
    }
    Ok(std::mem::take(&mut context.clauses))
}

/// CEP:WHAT: Scans the "p cnf <vars> <clauses>" header line.
/// CEP:WHY: The header declares the variable universe every later index is validated against (the VariableBeyondHeader bound) and the expected clause count (recorded but not enforced as an equality: real-world files under-declare; the clause store's own bound governs the total).
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns MissingHeader for a malformed header, Syntax for malformed integers, TooManySymbols past kMaxSymbolCount; never panics.
/// CEP:ASSUMES: index points at the line-start 'p'.
/// CEP:COST: O(header length).
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::{parses_header_and_clauses_into_ir, rejects_missing_header}.
/// CEP:SECURITY: the declared count is gated by kMaxSymbolCount.
fn scan_header(
    input: &[u8],
    index: usize,
    line: u32,
    column: u32,
    context: &mut DimacsContext,
) -> Result<usize, ParseError> {
    let line_end = input[index..]
        .iter()
        .position(|byte| *byte == b'\n')
        .map(|offset| index + offset)
        .unwrap_or(input.len());
    let header = &input[index..line_end];
    let text = std::str::from_utf8(header).map_err(|_| ParseError::Syntax { line, column })?;
    let mut fields = text.split_whitespace();
    let p = fields.next().unwrap_or("");
    let kind = fields.next().unwrap_or("");
    if p != "p" || kind != "cnf" {
        return Err(ParseError::MissingHeader);
    }
    let vars_token = fields.next().unwrap_or("");
    let clauses_token = fields.next().unwrap_or("");
    let vars: u64 = vars_token
        .parse()
        .map_err(|_| ParseError::Syntax { line, column })?;
    let _clauses: u64 = clauses_token
        .parse()
        .map_err(|_| ParseError::Syntax { line, column })?;
    if fields.next().is_some() {
        return Err(ParseError::MissingHeader);
    }
    if vars > kMaxSymbolCount as u64 {
        return Err(ParseError::TooManySymbols);
    }
    context.variable_count = vars as u32;
    Ok(line_end)
}

/// CEP:WHAT: Scans one signed decimal integer at the given byte offset.
/// CEP:WHY: DIMACS literals are optionally signed integers; one scanner keeps the overflow and empty-token handling exact.
/// CEP:STATUS: complete
/// CEP:FAILURE: Returns Syntax on an empty run, i64 overflow, or a trailing garbage byte; never panics.
/// CEP:ASSUMES: input[index] is '-' or an ASCII digit.
/// CEP:COST: O(digits).
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::parses_header_and_clauses_into_ir.
/// CEP:SECURITY: the value bound is i64; variable magnitudes are re-checked against the header before use.
fn scan_integer(
    input: &[u8],
    mut index: usize,
    line: u32,
    column: u32,
) -> Result<(i64, usize), ParseError> {
    let mut negative = false;
    if input[index] == b'-' {
        negative = true;
        index += 1;
        if index >= input.len() || !input[index].is_ascii_digit() {
            return Err(ParseError::Syntax { line, column });
        }
    }
    let mut magnitude: u64 = 0;
    while index < input.len() && input[index].is_ascii_digit() {
        let digit = (input[index] - b'0') as u64;
        magnitude = magnitude
            .checked_mul(10)
            .and_then(|value| value.checked_add(digit))
            .ok_or(ParseError::Syntax { line, column })?;
        index += 1;
    }
    let value = if negative {
        // i64::MIN has no positive counterpart; the checked pipeline reports it as a syntax defect.
        let bound = (i64::MAX as u64) + 1;
        if magnitude >= bound {
            return Err(ParseError::Syntax { line, column });
        }
        (magnitude as i64).wrapping_neg()
    } else {
        if magnitude > i64::MAX as u64 {
            return Err(ParseError::Syntax { line, column });
        }
        magnitude as i64
    };
    Ok((value, index))
}
