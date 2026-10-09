// CEP:FILE: tests/property/unify_property_test.rs
// CEP:WHAT: Property tests for unification and matching: MGU soundness and idempotency on random term pairs, and occurs-check agreement with a naive scan.
// CEP:WHY: CEP&CC 32.9 and Formal Spec 02 section 5: the MGU theorem holds for every unifiable pair; property tests over deterministic random inputs are the executable form of the theorem.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any violated property.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the deterministic LCG makes every run identical.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/unification/unify.rs property pointers.
// CEP:SECURITY: none; no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_term_fixture, DeterministicRng};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::unification::substitution::Substitution;
use mapt::hot::unification::unify::{match_terms, unify};

// CEP:WHAT: Property iterations per test.
// CEP:WHY: Named constant (CEP&CC 11.3); 64 random pairs keep the suite fast while covering the term space.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyIterations: u32 = 64;

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

// CEP:WHAT: Generates a random term of bounded depth over the fixture vocabulary.
// CEP:WHY: Property inputs must be structurally valid terms; the generator picks variables, constants, and unary/binary applications with a depth budget.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: depth >= 1.
// CEP:COST: exponential in depth (bounded by the generator constants).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_term(
    rng: &mut DeterministicRng,
    terms: &TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    depth: u32,
) -> TermPtr {
    if depth == 0 || rng.below(4) == 0 {
        let choice = rng.below(3);
        if choice == 0 {
            return terms.intern_var(rng.below(4) as u32).expect("var");
        }
        if choice == 1 {
            return terms
                .intern_fun(symbols, symbol_id(builder, "a"), &[])
                .expect("a");
        }
        return terms
            .intern_fun(symbols, symbol_id(builder, "b"), &[])
            .expect("b");
    }
    let choice = rng.below(3);
    if choice == 0 {
        let child = random_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "f"), &[child])
            .expect("f")
    } else {
        let left = random_term(rng, terms, symbols, builder, depth - 1);
        let right = random_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "h"), &[left, right])
            .expect("h")
    }
}

// CEP:WHAT: Property: whenever unification succeeds, applying the result to both sides yields the same term, and applying it twice changes nothing (idempotency).
// CEP:WHY: Spec 02 section 5: the computed substitution is a unifier and, being most general over the pair, idempotent on those terms.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any unifier that does not unify or is not idempotent.
// CEP:ASSUMES: random pairs from the generator.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify.
// CEP:SECURITY: none.
#[test]
fn mgu_is_unifier_and_idempotent() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let mut rng = DeterministicRng::new(0x5eed_0002);
    let mut unified_count = 0;
    for _ in 0..kPropertyIterations {
        let left = random_term(&mut rng, &terms, &symbols, &builder, 3);
        let right = random_term(&mut rng, &terms, &symbols, &builder, 3);
        let entry_depth = substitution.trail_depth();
        if unify(&terms, &substitution, left, right) == Ok(true) {
            unified_count += 1;
            let applied_left = substitution
                .apply(&terms, left, &symbols)
                .expect("apply left");
            let applied_right = substitution
                .apply(&terms, right, &symbols)
                .expect("apply right");
            assert_eq!(
                applied_left, applied_right,
                "the MGU must unify the pair it was computed for"
            );
            let twice = substitution
                .apply(&terms, applied_left, &symbols)
                .expect("apply twice");
            assert_eq!(
                twice, applied_left,
                "the MGU must be idempotent on the unified pair"
            );
        }
        substitution.undo_to(entry_depth);
    }
    assert!(
        unified_count > 0,
        "the generator must produce unifiable pairs"
    );
}

// CEP:WHAT: Property: the occurs check agrees with a naive variable scan on every pair the generator produces.
// CEP:WHY: Spec 02 section 5: x unifies with t iff x does not occur in t; a naive scan is the reference oracle.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: random pairs.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/unification/unify.rs occurs.
// CEP:SECURITY: none.
#[test]
fn occurs_check_matches_naive_scan() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let mut rng = DeterministicRng::new(0x5eed_0003);
    for _ in 0..kPropertyIterations {
        let variable = rng.below(4) as u32;
        let term = random_term(&mut rng, &terms, &symbols, &builder, 3);
        let var_term = terms.intern_var(variable).expect("var");
        let expected = naive_occurs(&terms, variable, term, 0);
        let outcome = unify(&terms, &substitution, var_term, term);
        if expected {
            assert_eq!(
                outcome,
                Ok(false),
                "x must not unify with a term containing x"
            );
            assert_eq!(substitution.trail_depth(), 0, "failure must unwind");
        } else {
            // x does not occur in t: the pair unifies by binding x to t.
            assert_eq!(outcome, Ok(true), "x must unify with x-free terms");
            substitution.undo_to(0);
        }
    }
}

// CEP:WHAT: Naive reference: does the variable occur in the term?
// CEP:WHY: The property-test oracle, written independently of the implementation.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(term size).
// CEP:EVIDENCE: used by occurs_check_matches_naive_scan.
// CEP:SECURITY: none.
fn naive_occurs(terms: &TermStore<'_>, variable: u32, term: TermPtr, depth: u32) -> bool {
    if depth > 32 {
        return false;
    }
    let view = match terms.term(term) {
        Ok(view) => view,
        Err(_) => return false,
    };
    if view.tag() == mapt::hot::ir::term::TermTag::Variable {
        return view.symbol() == variable;
    }
    for index in 0..view.child_count() {
        if let Ok(child) = view.child(index) {
            if naive_occurs(terms, variable, child, depth + 1) {
                return true;
            }
        }
    }
    false
}

// CEP:WHAT: Property: whenever matching succeeds, applying the matcher to the pattern reproduces the subject exactly.
// CEP:WHY: Spec 02 section 5: hat-sigma(pattern) = subject is the definition of matching; the witness inside match_terms makes this near-tautological, and the property test guards against future witness removal.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any matcher that does not reproduce the subject.
// CEP:ASSUMES: random pattern/subject pairs with variable-disjoint subjects (fresh variables above the pattern range).
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_terms.
// CEP:SECURITY: none.
#[test]
fn matcher_reproduces_subject() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let mut rng = DeterministicRng::new(0x5eed_0004);
    let mut matched = 0;
    for _ in 0..kPropertyIterations {
        // Patterns use variables 0..4; subjects are ground over a and b (disjoint by
        // construction), which is the demodulation shape.
        let pattern = random_term(&mut rng, &terms, &symbols, &builder, 3);
        let subject = ground_term(&mut rng, &terms, &symbols, &builder, 3);
        let entry_depth = substitution.trail_depth();
        if match_terms(&terms, &symbols, &substitution, pattern, subject) == Ok(true) {
            matched += 1;
            let applied = substitution
                .apply(&terms, pattern, &symbols)
                .expect("apply pattern");
            assert_eq!(
                applied, subject,
                "the matcher must reproduce the subject exactly"
            );
        }
        substitution.undo_to(entry_depth);
    }
    assert!(matched > 0, "the generator must produce matchable pairs");
}

// CEP:WHAT: Generates a random ground term (no variables).
// CEP:WHY: Matching subjects in the demodulation shape are ground.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: depth >= 1.
// CEP:COST: exponential in depth (bounded).
// CEP:EVIDENCE: used by matcher_reproduces_subject.
// CEP:SECURITY: none.
fn ground_term(
    rng: &mut DeterministicRng,
    terms: &TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    depth: u32,
) -> TermPtr {
    if depth == 0 || rng.below(4) == 0 {
        let name = if rng.below(2) == 0 { "a" } else { "b" };
        return terms
            .intern_fun(symbols, symbol_id(builder, name), &[])
            .expect("constant");
    }
    if rng.below(2) == 0 {
        let child = ground_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "f"), &[child])
            .expect("f")
    } else {
        let left = ground_term(rng, terms, symbols, builder, depth - 1);
        let right = ground_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "h"), &[left, right])
            .expect("h")
    }
}
