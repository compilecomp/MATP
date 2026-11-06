// CEP:FILE: tests/unit/cold/dimacs_parser_test.rs
// CEP:WHAT: Unit tests for the DIMACS CNF front end: header and clause IR construction, the variable-beyond-header bound, the header-order contract, the empty-clause shape, comment and end-marker handling, and the input-size gate.
// CEP:WHY: Law 4: every parser behavior claimed in the CEP:EVIDENCE fields of cold/parsing/dimacs_parser.rs is pinned by an executable test here (design 6.3 bound enforcement is the security surface).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: any test failure fails the CI test gate.
// CEP:ASSUMES: the test arena capacity covers the parsed problems.
// CEP:COST: small fixtures; runs in milliseconds.
// CEP:EVIDENCE: CI test job; cited by cold/parsing/dimacs_parser.rs.
// CEP:SECURITY: inputs are test-controlled.

#[path = "../../common/mod.rs"]
mod common;

use common::{kTestArenaBytes, make_arena};
use mapt::cold::parsing::{parse_dimacs, ParseError};
use mapt_hot::ir::term::TermTag;

// CEP:WHAT: Verifies that a header, comments, and two clauses reach the unified IR with the expected symbol layout ($i at 0, v1..v3 at 1..3), polarity multiset, and Input derivation.
// CEP:WHY: The primary DIMACS path: variable-to-symbol mapping is dense (v<n> at id n) and literals carry the DIMACS sign.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any shape mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs parse_dimacs.
// CEP:SECURITY: none.
#[test]
fn parses_header_and_clauses_into_ir() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"p cnf 3 2\nc comment line\n1 -2 0\n-1 3 0\n";
    let problem = parse_dimacs(arena, input).expect("parse");
    assert_eq!(problem.clause_ptrs.len(), 2);
    // The builder pre-declares the $i and $o sorts at ids 0 and 1.
    assert_eq!(problem.builder.name_of(0), Some("$i"));
    assert_eq!(problem.builder.name_of(1), Some("$o"));
    assert_eq!(problem.builder.name_of(2), Some("v1"));
    assert_eq!(problem.builder.name_of(3), Some("v2"));
    assert_eq!(problem.builder.name_of(4), Some("v3"));
    // Clause 1: positive v1 (symbol 1), negative v2 (symbol 2).
    let clause = problem
        .clauses
        .clause(problem.clause_ptrs[0])
        .expect("clause");
    assert_eq!(
        clause.derivation.rule,
        mapt_hot::ir::clause::InferenceRule::Input
    );
    let mut entries: Vec<(bool, u32)> = Vec::new();
    for index in 0..clause.literal_count {
        let literal = problem.clauses.literal(clause, index).expect("literal");
        let view = problem.terms.term(literal.atom()).expect("atom");
        assert_eq!(view.tag(), TermTag::Predicate);
        entries.push((literal.is_positive(), view.symbol()));
    }
    entries.sort();
    // v1 carries symbol id 2 and v2 id 3 (the $i and $o sorts occupy 0 and 1).
    assert_eq!(entries, vec![(false, 3), (true, 2)]);
}

// CEP:WHAT: Verifies that a variable index beyond the declared header count is rejected with VariableBeyondHeader.
// CEP:WHY: The header declares the variable universe; exceeding it is the format-level bound of design 6.3.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error is not VariableBeyondHeader.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs scan_dimacs.
// CEP:SECURITY: none.
#[test]
fn rejects_variable_beyond_header() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"p cnf 2 1\n1 3 0\n";
    let result = parse_dimacs(arena, input);
    assert!(matches!(result, Err(ParseError::VariableBeyondHeader)));
}

// CEP:WHAT: Verifies that clause data before the header and a malformed header are rejected with MissingHeader.
// CEP:WHY: The header-order contract of the DIMACS grammar.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error is not MissingHeader.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs scan_dimacs.
// CEP:SECURITY: none.
#[test]
fn rejects_missing_header() {
    let arena = make_arena(kTestArenaBytes);
    assert!(matches!(
        parse_dimacs(arena, b"1 0\n"),
        Err(ParseError::MissingHeader)
    ));
    assert!(matches!(
        parse_dimacs(arena, b"p sat 1 1\n1 0\n"),
        Err(ParseError::MissingHeader)
    ));
}

// CEP:WHAT: Verifies that an empty clause (a bare 0 line) is accepted as a zero-literal record and later clauses still parse.
// CEP:WHY: An empty clause is a legal DIMACS input (an immediately refutable formula); the search treats its record as the refutation.
// CEP:STATUS: complete
// CEP:FAILURE: panics on shape mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs scan_dimacs.
// CEP:SECURITY: none.
#[test]
fn empty_clause_is_accepted() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"p cnf 1 2\n0\n1 0\n";
    let problem = parse_dimacs(arena, input).expect("parse");
    assert_eq!(problem.clause_ptrs.len(), 2);
    let empty = problem
        .clauses
        .clause(problem.clause_ptrs[0])
        .expect("clause");
    assert_eq!(empty.literal_count, 0);
    let unit = problem
        .clauses
        .clause(problem.clause_ptrs[1])
        .expect("clause");
    assert_eq!(unit.literal_count, 1);
}

// CEP:WHAT: Verifies that comment lines and the SAT-competition '%' end marker are ignored, including an integer run like 47 that contains a comment-introducer byte.
// CEP:WHY: The lexical trivia of the format; a comment byte inside an integer run must not truncate the clause.
// CEP:STATUS: complete
// CEP:FAILURE: panics on shape mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs scan_dimacs.
// CEP:SECURITY: none.
#[test]
fn comments_and_trailing_percent_are_ignored() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"c header comment\np cnf 47 2\nc inner\n47 0\n-47 0\n%\n0 status line\n";
    let problem = parse_dimacs(arena, input).expect("parse");
    assert_eq!(problem.clause_ptrs.len(), 2);
    let first = problem
        .clauses
        .clause(problem.clause_ptrs[0])
        .expect("clause");
    assert_eq!(first.literal_count, 1);
    let second = problem
        .clauses
        .clause(problem.clause_ptrs[1])
        .expect("clause");
    assert_eq!(second.literal_count, 1);
}

// CEP:WHAT: Verifies that an input past kMaxInputBytes is rejected with TooLarge before any IR construction.
// CEP:WHY: The design 6.3 input-size gate (memory denial-of-service mitigation).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error is not TooLarge.
// CEP:ASSUMES: the test allocation of 64 MiB + 1 byte is acceptable for the suite.
// CEP:COST: one transient 64 MiB buffer.
// CEP:EVIDENCE: cited by cold/parsing/dimacs_parser.rs parse_dimacs.
// CEP:SECURITY: memory denial-of-service mitigation pin.
#[test]
fn oversize_input_is_rejected() {
    let arena = make_arena(kTestArenaBytes);
    let input = vec![b'c'; (mapt_config::limits::kMaxInputBytes + 1) as usize];
    let result = parse_dimacs(arena, &input);
    assert!(matches!(result, Err(ParseError::TooLarge)));
}
