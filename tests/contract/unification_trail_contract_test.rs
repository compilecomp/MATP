// CEP:FILE: tests/contract/unification_trail_contract_test.rs
// CEP:WHAT: Contract tests for the unification trail discipline: nested speculative attempts unwind to their own save points, entry depths are monotone, and failure at any nesting level leaves outer substitutions intact.
// CEP:WHY: CEP&CC 32.7 and Formal Spec 02 section 4: the trail discipline is the contract between the substitution engine and every future inference rule; nested unification attempts (superposition tries several positions) depend on it.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any contract break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/unification/substitution.rs trail pointers.
// CEP:SECURITY: none; no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::unification::substitution::Substitution;
use mapt::hot::unification::unify::unify;

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable fixture setup.
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

// CEP:WHAT: Contract: a successful nested unification keeps its bindings while the outer level stays intact.
// CEP:WHY: Spec 02 section 4 invariant 1: a variable is bound at most once between undos; nested successes compose.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any binding leak.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify.
// CEP:SECURITY: none.
#[test]
fn nested_success_composes() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let h = symbol_id(&builder, "h");
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    // Outer: h(x, a) vs h(a, a) binds x := a.
    let outer_left = terms.intern_fun(&symbols, h, &[x, a]).expect("h(x, a)");
    let outer_right = terms.intern_fun(&symbols, h, &[a, a]).expect("h(a, a)");
    let outer_depth = substitution.trail_depth();
    assert_eq!(
        unify(&terms, &substitution, outer_left, outer_right),
        Ok(true)
    );
    assert_eq!(substitution.trail_depth(), outer_depth + 1);
    // Inner (nested): h(y, b) vs h(b, b) binds y := b.
    let inner_left = terms.intern_fun(&symbols, h, &[y, b]).expect("h(y, b)");
    let inner_right = terms.intern_fun(&symbols, h, &[b, b]).expect("h(b, b)");
    let inner_depth = substitution.trail_depth();
    assert_eq!(
        unify(&terms, &substitution, inner_left, inner_right),
        Ok(true)
    );
    assert_eq!(substitution.trail_depth(), inner_depth + 1);
    // Both bindings coexist.
    assert_eq!(substitution.lookup(0), Ok(Some(a)));
    assert_eq!(substitution.lookup(1), Ok(Some(b)));
}

// CEP:WHAT: Contract: a failed nested unification unwinds exactly its own bindings.
// CEP:WHY: Spec 02 section 4 invariant 2: after undo, the domain equals the domain before the attempt.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if outer bindings are lost or inner bindings leak.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify and hot/unification/substitution.rs undo_to.
// CEP:SECURITY: none.
#[test]
fn nested_failure_unwinds_to_save_point() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let h = symbol_id(&builder, "h");
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    // Outer success: x := a.
    let outer_left = terms.intern_fun(&symbols, h, &[x, a]).expect("h(x, a)");
    let outer_right = terms.intern_fun(&symbols, h, &[a, a]).expect("h(a, a)");
    assert_eq!(
        unify(&terms, &substitution, outer_left, outer_right),
        Ok(true)
    );
    let save_point = substitution.trail_depth();
    // Inner failure: h(y, a) vs h(b, b) binds y := b on the first child, then the
    // second child clashes (a vs b): a failure AFTER a binding, the hardest case.
    let inner_left = terms.intern_fun(&symbols, h, &[y, a]).expect("h(y, a)");
    let inner_right = terms.intern_fun(&symbols, h, &[b, b]).expect("h(b, b)");
    assert_eq!(
        unify(&terms, &substitution, inner_left, inner_right),
        Ok(false)
    );
    assert_eq!(
        substitution.trail_depth(),
        save_point,
        "the failed inner attempt must leave the trail exactly at its save point"
    );
    // Outer binding intact.
    assert_eq!(substitution.lookup(0), Ok(Some(a)));
    assert_eq!(substitution.lookup(1), Ok(None));
}

// CEP:WHAT: Contract: trail depth is monotone between undos and undo_to is idempotent at a fixed depth.
// CEP:WHY: Spec 02 section 4 invariant 3 + determinism of the rewind: the discipline must be predictable for backtracking search.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any non-monotone depth.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs trail_depth and undo_to.
// CEP:SECURITY: none.
#[test]
fn trail_depth_monotone_between_undos() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let f = symbol_id(&builder, "f");
    let previous = substitution.trail_depth();
    substitution.bind(0, a).expect("bind 0");
    assert_eq!(substitution.trail_depth(), previous + 1);
    substitution
        .bind(1, terms.intern_fun(&symbols, f, &[x]).expect("f(x)"))
        .expect("bind 1");
    assert_eq!(substitution.trail_depth(), previous + 2);
    substitution.undo_to(previous + 1);
    assert_eq!(substitution.trail_depth(), previous + 1);
    substitution.undo_to(previous + 1);
    assert_eq!(
        substitution.trail_depth(),
        previous + 1,
        "undo_to at a fixed depth must be idempotent"
    );
    substitution.undo_to(previous);
    assert_eq!(substitution.trail_depth(), previous);
    assert_eq!(substitution.lookup(0), Ok(None));
}
