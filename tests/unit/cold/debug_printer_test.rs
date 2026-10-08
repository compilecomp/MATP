// CEP:FILE: tests/unit/cold/debug_printer_test.rs
// CEP:WHAT: Unit tests for the debug printer: term syntax, clause syntax, fallbacks, and rejection of unreadable handles.
// CEP:WHY: CEP&CC 32.8 and design 5.7 (printable IR); the golden test in tests/golden pins the exact output.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any output drift.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/debug_printer.rs.
// CEP:SECURITY: none.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::cold::debug_printer::{
    kFalseClauseMarker, kUnknownSymbolName, print_clause, print_term, PrintError,
};
use mapt::hot::ir::clause::DerivationStep;
use mapt::hot::ir::literal::Literal;
use mapt_config::limits::{kInvalidClauseId, kInvalidSubstitutionOffset};

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Verifies term syntax for every term kind.
// CEP:WHY: The internal debug format is a stable contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on syntax drift.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/debug_printer.rs print_term.
// CEP:SECURITY: none.
#[test]
fn term_syntax() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let mut out = String::new();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    print_term(&terms, &builder, a, &mut out).expect("print");
    assert_eq!(out, "(a)");
    out.clear();
    let f_id = symbol_id(&builder, "f");
    let var = terms.intern_var(3).expect("V3");
    let f_var = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V3)");
    print_term(&terms, &builder, f_var, &mut out).expect("print");
    assert_eq!(out, "(f V3)");
    out.clear();
    let eq = terms.intern_eq(&symbols, a, var).expect("a = V3");
    print_term(&terms, &builder, eq, &mut out).expect("print");
    assert_eq!(out, "(= (a) V3)");
}

// CEP:WHAT: Verifies clause syntax including negation and the empty clause marker.
// CEP:WHY: Clause printing closes the printable-IR contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on syntax drift.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/debug_printer.rs print_clause.
// CEP:SECURITY: none.
#[test]
fn clause_syntax() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let p_id = symbol_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(&symbols, p_id, &[b]).expect("p(b)");
    let mut out = String::new();
    let ptr = clauses
        .new_clause(
            &terms,
            &[Literal::new(pa, true), Literal::new(pb, false)],
            0,
            input_derivation(),
        )
        .expect("clause");
    print_clause(&terms, &builder, &clauses, ptr, &mut out).expect("print");
    let id = clauses.clause(ptr).expect("read").id.0;
    let expected = format!("c{}: (p (a)) | ~(p (b))", id);
    assert_eq!(out, expected);
    out.clear();
    let empty = clauses
        .new_clause(&terms, &[], 0, input_derivation())
        .expect("empty clause");
    print_clause(&terms, &builder, &clauses, empty, &mut out).expect("print");
    let empty_id = clauses.clause(empty).expect("read").id.0;
    assert_eq!(out, format!("c{}: {}", empty_id, kFalseClauseMarker));
}

// CEP:WHAT: Verifies the unknown-name fallback.
// CEP:WHY: The printer stays total on inconsistent fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the sentinel is not used.
// CEP:ASSUMES: a builder missing the symbol.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/debug_printer.rs kUnknownSymbolName.
// CEP:SECURITY: none.
#[test]
fn missing_name_falls_back() {
    let (_arena, symbols, _builder, terms, _clauses) = make_term_fixture();
    // Build a term with the fixture table, then print it with a builder that lacks those names.
    let a_id = symbol_id(&_builder, "a");
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let mut bare_builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    let _ = bare_builder.declare_sort("S").expect("sort");
    let mut out = String::new();
    print_term(&terms, &bare_builder, a, &mut out).expect("print");
    assert!(
        out.contains(kUnknownSymbolName),
        "a symbol missing from the printer's builder must fall back to the sentinel, got {}",
        out
    );
}

// CEP:WHAT: Verifies unreadable handles are rejected.
// CEP:WHY: The printer must fail loudly, never print garbage.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if garbage is printed.
// CEP:ASSUMES: forged handles.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/debug_printer.rs PrintError.
// CEP:SECURITY: none.
#[test]
fn unreadable_handles_rejected() {
    let (_arena, _symbols, builder, terms, _clauses) = make_term_fixture();
    let forged = mapt::hot::ir::term::TermPtr::from_verified_offset(u32::MAX - 8);
    let mut out = String::new();
    assert_eq!(
        print_term(&terms, &builder, forged, &mut out),
        Err(PrintError::UnreadableTerm)
    );
}

// CEP:WHAT: Builds an input derivation step.
// CEP:WHY: Shared fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: mapt::hot::ir::clause::InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; 4],
        substitution: kInvalidSubstitutionOffset,
    }
}
