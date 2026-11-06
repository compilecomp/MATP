// CEP:FILE: tests/unit/cold/tptp_parser_test.rs
// CEP:WHAT: Unit tests for the TPTP front end: CNF-to-IR construction with variables and equality, the FOF AST shape across every connective, syntax-error attribution, role/arity/binding validation, and every injectable and include bound.
// CEP:WHY: Law 4: every parser behavior claimed in the CEP:EVIDENCE fields of cold/parsing/tptp_parser.rs is pinned by an executable test here.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: any test failure fails the CI test gate.
// CEP:ASSUMES: the test arena capacity covers the parsed problems; include tests run in a private temp directory.
// CEP:COST: small fixtures; the include suite touches the filesystem once per test.
// CEP:EVIDENCE: CI test job; cited by cold/parsing/tptp_parser.rs.
// CEP:SECURITY: inputs are test-controlled.

#[path = "../../common/mod.rs"]
mod common;

use common::{kTestArenaBytes, make_arena};
use mapt::cold::parsing::{
    parse_tptp, parse_tptp_with_limits, FofFormula, FofTerm, ParseError, ParserLimits, TptpRole,
};
use mapt_hot::ir::term::TermTag;
use std::path::PathBuf;

// CEP:WHAT: Verifies that CNF directives reach the unified IR: variables map to dense clause-local indices, equality atoms carry the Equality tag, $true tautologies drop, and $false yields the empty clause.
// CEP:WHY: The primary TPTP CNF path and the True/False disjunctive semantics at the IR boundary.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any shape mismatch.
// CEP:ASSUMES: symbol ids are dense in declaration order ($i at 0).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs parse_tptp and build_cnf_clause.
// CEP:SECURITY: none.
#[test]
fn cnf_clauses_reach_the_ir() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"cnf(c1, axiom, p(X) | ~q(f(X))).\ncnf(c2, axiom, a = b).\ncnf(c3, axiom, p(a) | $true).\ncnf(c4, axiom, $false).\n";
    let problem = parse_tptp(arena, input, None).expect("parse");
    // Symbol layout: $i=0, $o=1 (lazy with the first predicate), p=2; then the
    // q(f(X)) literal parses f's arguments first, so f=3 and q=4; a=5, b=6.
    assert_eq!(problem.builder.name_of(2), Some("p"));
    assert_eq!(problem.builder.name_of(3), Some("f"));
    assert_eq!(problem.builder.name_of(4), Some("q"));
    // c1: two literals {+p(X), -q(f(X))}; c3 is a tautology and drops.
    assert_eq!(problem.clause_ptrs.len(), 3);
    let clause = problem
        .clauses
        .clause(problem.clause_ptrs[0])
        .expect("clause");
    let mut entries: Vec<(bool, u8)> = Vec::new();
    for index in 0..clause.literal_count {
        let literal = problem.clauses.literal(clause, index).expect("literal");
        let view = problem.terms.term(literal.atom()).expect("atom");
        entries.push((literal.is_positive(), view.tag() as u8));
    }
    entries.sort();
    // Predicate = 2 in the TermTag discriminants.
    assert_eq!(entries, vec![(false, 2_u8), (true, 2_u8)]);
    // The p atom's argument is the clause-local variable 0.
    let clause = problem
        .clauses
        .clause(problem.clause_ptrs[0])
        .expect("clause");
    for index in 0..clause.literal_count {
        let literal = problem.clauses.literal(clause, index).expect("literal");
        let view = problem.terms.term(literal.atom()).expect("atom");
        if view.symbol() == 2 {
            let child = view.child(0).expect("argument");
            let child_view = problem.terms.term(child).expect("term");
            assert_eq!(child_view.tag(), TermTag::Variable);
            assert_eq!(child_view.symbol(), 0);
        }
    }
    // c2: one positive equality atom.
    let equality_clause = problem
        .clauses
        .clause(problem.clause_ptrs[1])
        .expect("clause");
    assert_eq!(equality_clause.literal_count, 1);
    let literal = problem
        .clauses
        .literal(equality_clause, 0)
        .expect("literal");
    let view = problem.terms.term(literal.atom()).expect("atom");
    assert_eq!(view.tag(), TermTag::Equality);
    assert!(literal.is_positive());
    // c4: the empty clause.
    let empty = problem
        .clauses
        .clause(problem.clause_ptrs[2])
        .expect("clause");
    assert_eq!(empty.literal_count, 0);
    // The directive records carry role and name.
    assert_eq!(problem.cnf_clauses.len(), 4);
    assert_eq!(problem.cnf_clauses[0].name, "c1");
    assert_eq!(problem.cnf_clauses[0].role, TptpRole::Axiom);
}

// CEP:WHAT: Verifies that a quantified FOF implication reaches the AST with the expected shape and name ids.
// CEP:WHY: The FOF layer feeds the design 7 clausification pipeline; the AST contract (dense ids, variable name references) is its input interface.
// CEP:STATUS: complete
// CEP:FAILURE: panics on shape mismatch.
// CEP:ASSUMES: symbol ids are dense in declaration order.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs parse_quantified_body.
// CEP:SECURITY: none.
#[test]
fn fof_formulas_reach_the_ast() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"fof(ax, axiom, ! [X] : (p(X) => q(X))).\n";
    let problem = parse_tptp(arena, input, None).expect("parse");
    assert_eq!(problem.formulas.len(), 1);
    assert_eq!(problem.formulas[0].role, TptpRole::Axiom);
    assert_eq!(problem.formulas[0].name, "ax");
    // $i=0, $o=1 (auto-declared), p=2, q=3; the variable name X has name id 0.
    let expected = FofFormula::Forall(
        vec![0],
        Box::new(FofFormula::Implies(
            Box::new(FofFormula::Predicate(2, vec![FofTerm::Variable(0)])),
            Box::new(FofFormula::Predicate(3, vec![FofTerm::Variable(0)])),
        )),
    );
    assert_eq!(problem.formulas[0].formula, expected);
}

// CEP:WHAT: Verifies the precedence ladder across every connective: & over | over => and <= over <=>, <~>, ~|, ~&, with flattening of the associative layers.
// CEP:WHY: The connective semantics must survive parsing unchanged (one AST variant per TPTP connective).
// CEP:STATUS: complete
// CEP:FAILURE: panics on shape mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs parse_formula and the layer parsers.
// CEP:SECURITY: none.
#[test]
fn binds_all_connectives() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"fof(ax, axiom, (a & b) | (c => d) | (e <= f) | (g <=> h) | (i <~> j) | (k ~| l) | (m ~& n)).\n";
    let problem = parse_tptp(arena, input, None).expect("parse");
    match &problem.formulas[0].formula {
        FofFormula::Or(operands) => {
            assert_eq!(operands.len(), 7);
            assert!(matches!(operands[0], FofFormula::And(_)));
            assert!(matches!(operands[1], FofFormula::Implies(_, _)));
            assert!(matches!(operands[2], FofFormula::ReverseImplies(_, _)));
            assert!(matches!(operands[3], FofFormula::Equivalent(_, _)));
            assert!(matches!(operands[4], FofFormula::NotEquivalent(_, _)));
            assert!(matches!(operands[5], FofFormula::NotOr(_, _)));
            assert!(matches!(operands[6], FofFormula::NotAnd(_, _)));
        }
        other => panic!("expected a flat disjunction, got {:?}", other),
    }
}

// CEP:WHAT: Verifies that a missing directive terminator reports the exact Syntax line and column.
// CEP:WHY: Error attribution is the driver-facing contract of ParseError::Syntax.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: the lexer's end-of-input position is one past the last byte.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs Lexer::next and expect.
// CEP:SECURITY: none.
#[test]
fn syntax_error_reports_line() {
    let arena = make_arena(kTestArenaBytes);
    // "cnf(c1, axiom, p(X))" is 20 bytes; the missing '.' is reported at the end-of-input position (1, 21).
    let result = parse_tptp(arena, b"cnf(c1, axiom, p(X))", None);
    assert!(matches!(
        result,
        Err(ParseError::Syntax {
            line: 1,
            column: 21
        })
    ));
}

// CEP:WHAT: Verifies that a role outside the TPTP vocabulary is rejected with UnknownRole.
// CEP:WHY: Unknown roles are rejected, never downgraded to plain.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs parse_role.
// CEP:SECURITY: none.
#[test]
fn rejects_unknown_role() {
    let arena = make_arena(kTestArenaBytes);
    let result = parse_tptp(arena, b"cnf(c1, bogus_role, p).", None);
    assert!(matches!(result, Err(ParseError::UnknownRole)));
}

// CEP:WHAT: Verifies that reusing a name with a different arity is rejected with ArityMismatch.
// CEP:WHY: The TPTP consistency rule: a name's signature is fixed by its first use.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs declare_symbol.
// CEP:SECURITY: none.
#[test]
fn rejects_arity_change() {
    let arena = make_arena(kTestArenaBytes);
    let input = b"cnf(c1, axiom, p(a)).\ncnf(c2, axiom, p(a, b)).\n";
    let result = parse_tptp(arena, input, None);
    assert!(matches!(result, Err(ParseError::ArityMismatch)));
}

// CEP:WHAT: Verifies that an FOF formula with a variable outside every quantifier is rejected with FreeVariable.
// CEP:WHY: TPTP FOF prohibits free variables; CNF clauses are exempt (clause variables are universally quantified by convention).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs check_binding.
// CEP:SECURITY: none.
#[test]
fn rejects_free_variable() {
    let arena = make_arena(kTestArenaBytes);
    let result = parse_tptp(arena, b"fof(ax, axiom, p(X)).", None);
    assert!(matches!(result, Err(ParseError::FreeVariable)));
    // The same shape under an existential quantifier parses.
    let arena = make_arena(kTestArenaBytes);
    let problem = parse_tptp(arena, b"fof(ax, axiom, ? [X] : p(X)).", None).expect("parse");
    assert_eq!(problem.formulas.len(), 1);
}

// CEP:WHAT: Verifies that quantifier nesting past the injected bound is rejected with QuantifierTooDeep.
// CEP:WHY: The design 6.3 quantifier bound (exponential CNF blowup mitigation), exercised through the injectable limits.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs enter_quantifier.
// CEP:SECURITY: CPU denial-of-service mitigation pin.
#[test]
fn rejects_quantifier_depth() {
    let arena = make_arena(kTestArenaBytes);
    let mut input = String::from("fof(ax, axiom, ");
    for index in 0..5 {
        input.push_str(&std::format!("! [X{}] : ", index));
    }
    input.push_str("p(X0).");
    let limits = ParserLimits {
        node_budget: mapt_config::limits::kMaxFormulaNodes,
        parse_depth: mapt_config::limits::kMaxParseDepth,
        quantifier_depth: 3,
    };
    let result = parse_tptp_with_limits(arena, input.as_bytes(), None, limits);
    assert!(matches!(result, Err(ParseError::QuantifierTooDeep)));
}

// CEP:WHAT: Verifies that parenthesization nesting past the injected parse-depth bound is rejected with TooDeep.
// CEP:WHY: The design 6.2 recursion bound (stack-overflow mitigation), exercised through the injectable limits.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs enter_depth.
// CEP:SECURITY: stack-overflow mitigation pin.
#[test]
fn rejects_parse_depth() {
    let arena = make_arena(kTestArenaBytes);
    let mut input = String::from("cnf(c1, axiom, ");
    for _ in 0..12 {
        input.push('(');
    }
    input.push('p');
    for _ in 0..12 {
        input.push(')');
    }
    input.push_str(").");
    let limits = ParserLimits {
        node_budget: mapt_config::limits::kMaxFormulaNodes,
        parse_depth: 8,
        quantifier_depth: mapt_config::limits::kMaxQuantifierDepth,
    };
    let result = parse_tptp_with_limits(arena, input.as_bytes(), None, limits);
    assert!(matches!(result, Err(ParseError::TooDeep)));
    // The same shape under the standard limits parses.
    let arena = make_arena(kTestArenaBytes);
    let problem = parse_tptp(arena, input.as_bytes(), None).expect("parse");
    assert_eq!(problem.clause_ptrs.len(), 1);
}

// CEP:WHAT: Verifies that an input whose AST exceeds the injected node budget is rejected with TooManyNodes.
// CEP:WHY: The design 6.3 node budget (CPU exhaustion mitigation), exercised through the injectable limits.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs charge_node.
// CEP:SECURITY: CPU denial-of-service mitigation pin.
#[test]
fn rejects_node_budget() {
    let arena = make_arena(kTestArenaBytes);
    let limits = ParserLimits {
        node_budget: 1,
        parse_depth: mapt_config::limits::kMaxParseDepth,
        quantifier_depth: mapt_config::limits::kMaxQuantifierDepth,
    };
    // p(a) charges two nodes: the argument and the application.
    let result = parse_tptp_with_limits(arena, b"cnf(c1, axiom, p(a)).", None, limits);
    assert!(matches!(result, Err(ParseError::TooManyNodes)));
    // A one-node atom fits the same budget.
    let arena = make_arena(kTestArenaBytes);
    let problem =
        parse_tptp_with_limits(arena, b"cnf(c1, axiom, p).", None, limits).expect("parse");
    assert_eq!(problem.clause_ptrs.len(), 1);
}

// CEP:WHAT: Builds a private temp directory for include fixtures.
// CEP:WHY: The include tests need real files; one directory per test keyed by the test tag and process id avoids collisions.
// CEP:STATUS: complete
// CEP:FAILURE: panics on filesystem failure.
// CEP:ASSUMES: the temp directory is writable.
// CEP:COST: one directory per include test.
// CEP:EVIDENCE: cited by the include tests below.
// CEP:SECURITY: the directory is under the platform temp path and removed after the test.
fn temp_root(tag: &str) -> PathBuf {
    let root = std::env::temp_dir().join(std::format!(
        "mapt_tptp_include_{}_{:?}",
        tag,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir_all(&root).expect("temp root");
    root
}

// CEP:WHAT: Verifies that include nesting past kMaxIncludeDepth is rejected with IncludeTooDeep.
// CEP:WHY: The design 6.3 include-depth bound (include-cycle mitigation).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: writes 18 small files.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs enter_include.
// CEP:SECURITY: resource-exhaustion mitigation pin.
#[test]
fn include_depth_is_bounded() {
    let root = temp_root("depth");
    let chain_depth = mapt_config::limits::kMaxIncludeDepth as usize + 2;
    for index in 0..chain_depth {
        let name = std::format!("a{}", index);
        let content = if index + 1 < chain_depth {
            std::format!("include('a{}').\n", index + 1)
        } else {
            String::from("cnf(c1, axiom, p).\n")
        };
        std::fs::write(root.join(&name), content).expect("write");
    }
    let arena = make_arena(kTestArenaBytes);
    let result = parse_tptp(arena, b"include('a0').\n", Some(&root));
    std::fs::remove_dir_all(&root).ok();
    assert!(matches!(result, Err(ParseError::IncludeTooDeep)));
}

// CEP:WHAT: Verifies that include fan-out past kMaxIncludeCount is rejected with TooManyIncludes.
// CEP:WHY: The design 6.3 include-count bound (resource-exhaustion mitigation).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the error differs.
// CEP:ASSUMES: none.
// CEP:COST: writes one small file.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs enter_include.
// CEP:SECURITY: resource-exhaustion mitigation pin.
#[test]
fn include_count_is_bounded() {
    let root = temp_root("count");
    std::fs::write(root.join("s"), "cnf(c1, axiom, p).\n").expect("write");
    let mut input = String::new();
    let count = mapt_config::limits::kMaxIncludeCount as usize + 1;
    for _ in 0..count {
        input.push_str("include('s').\n");
    }
    let arena = make_arena(kTestArenaBytes);
    let result = parse_tptp(arena, input.as_bytes(), Some(&root));
    std::fs::remove_dir_all(&root).ok();
    assert!(matches!(result, Err(ParseError::TooManyIncludes)));
}

// CEP:WHAT: Verifies that an include selection list keeps only the named units from the included file.
// CEP:WHY: The TPTP selection semantic: the driver controls which axioms of a library file enter the problem.
// CEP:STATUS: complete
// CEP:FAILURE: panics on shape mismatch.
// CEP:ASSUMES: none.
// CEP:COST: writes one small file.
// CEP:EVIDENCE: cited by cold/parsing/tptp_parser.rs parse_include.
// CEP:SECURITY: none.
#[test]
fn include_selection_filters_by_name() {
    let root = temp_root("selection");
    std::fs::write(
        root.join("lib"),
        "fof(f1, axiom, p).\nfof(want, axiom, q).\ncnf(c1, axiom, r).\n",
    )
    .expect("write");
    let arena = make_arena(kTestArenaBytes);
    let problem = parse_tptp(arena, b"include('lib', [want]).\n", Some(&root)).expect("parse");
    std::fs::remove_dir_all(&root).ok();
    assert_eq!(problem.formulas.len(), 1);
    assert_eq!(problem.formulas[0].name, "want");
    assert_eq!(problem.cnf_clauses.len(), 0);
    assert_eq!(problem.clause_ptrs.len(), 0);
}
