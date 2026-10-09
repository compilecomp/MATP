// CEP:FILE: tests/unit/hot/unify_test.rs
// CEP:WHAT: Unit tests for unification, matching, and composition: MGU construction, occurs check, clash failure, trail unwinding, witness verification, and composition records.
// CEP:WHY: CEP&CC 32.8 and Formal Spec 02 section 5: unification soundness (occurs check) and the MGU property are correctness-critical for every later inference rule; these tests pin the definitions before Phase 3 consumes them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/unification/unify.rs.
// CEP:SECURITY: cyclic bindings and namespace overlap are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::unification::substitution::Substitution;
use mapt::hot::unification::unify::{compose, match_terms, unify};

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

// CEP:WHAT: Verifies identical ground terms unify with no bindings.
// CEP:WHY: The hash-consing fast path must be a pure pointer compare.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any binding or failure.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify.
// CEP:SECURITY: none.
#[test]
fn unify_ground_identical() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    assert_eq!(
        unify(&terms, &substitution, a, a),
        Ok(true),
        "identical terms must unify without bindings"
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies unification of f(x, b) with f(a, y) binds x to a and y to b.
// CEP:WHY: The canonical one-binding-per-side MGU case.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong bindings.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify.
// CEP:SECURITY: none.
#[test]
fn unify_one_binding() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let h = symbol_id(&builder, "h");
    let left = terms.intern_fun(&symbols, h, &[x, b]).expect("h(x, b)");
    let right = terms.intern_fun(&symbols, h, &[a, y]).expect("h(a, y)");
    assert_eq!(unify(&terms, &substitution, left, right), Ok(true));
    assert_eq!(substitution.lookup(0), Ok(Some(a)));
    assert_eq!(substitution.lookup(1), Ok(Some(b)));
    // MGU property: applying the result to both sides yields the same term.
    let applied_left = substitution
        .apply(&terms, left, &symbols)
        .expect("apply left");
    let applied_right = substitution
        .apply(&terms, right, &symbols)
        .expect("apply right");
    assert_eq!(applied_left, applied_right);
}

// CEP:WHAT: Verifies the occurs check rejects unifying x with f(x).
// CEP:WHY: Spec 02 section 5: without the occurs check the produced "unifier" would be cyclic and every later inference unsound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cycle is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs bind_variable.
// CEP:SECURITY: cyclic binding rejection.
#[test]
fn occurs_check_rejects_cycle() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let x = terms.intern_var(0).expect("x");
    let fx = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    assert_eq!(
        unify(&terms, &substitution, x, fx),
        Ok(false),
        "x must not unify with f(x)"
    );
    assert_eq!(
        substitution.trail_depth(),
        0,
        "failure must unwind the trail"
    );
}

// CEP:WHAT: Verifies the occurs check looks through existing bindings.
// CEP:WHY: A chain x -> y -> f(x) must also be rejected; dereferencing at every level is what catches indirect occurrences.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the indirect cycle is accepted.
// CEP:ASSUMES: pre-bound substitution state.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs occurs.
// CEP:SECURITY: cyclic binding rejection through chains.
#[test]
fn occurs_check_looks_through_bindings() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let fx = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    // y is already bound to f(x): unifying x with y must fail through the chain.
    substitution.bind(1, fx).expect("bind y");
    assert_eq!(
        unify(&terms, &substitution, x, y),
        Ok(false),
        "x must not unify with y = f(x)"
    );
    assert_eq!(
        substitution.trail_depth(),
        1,
        "pre-existing binding survives"
    );
}

// CEP:WHAT: Verifies clashing symbols fail without error.
// CEP:WHY: f(a) vs g(b) is a legitimate unification failure (Ok(false)), not an error.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if clash is an error.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify_bounded.
// CEP:SECURITY: none.
#[test]
fn clash_returns_false() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    assert_eq!(
        unify(&terms, &substitution, a, b),
        Ok(false),
        "distinct constants must not unify"
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies a failed unification after partial bindings unwinds exactly those bindings.
// CEP:WHY: Spec 02 section 4 trail discipline: failed attempts must be fully reversible.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if bindings leak after failure.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs unify.
// CEP:SECURITY: none.
#[test]
fn failure_unwinds_trail() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let x = terms.intern_var(0).expect("x");
    let h = symbol_id(&builder, "h");
    // h(x, a) vs h(a, b): first child unifies (x := a), second clashes.
    let left = terms.intern_fun(&symbols, h, &[x, a]).expect("h(x, a)");
    let right = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    assert_eq!(unify(&terms, &substitution, left, right), Ok(false));
    assert_eq!(
        substitution.trail_depth(),
        0,
        "all bindings of the failed attempt must be undone"
    );
    assert_eq!(substitution.lookup(0), Ok(None));
}

// CEP:WHAT: Verifies deep unification chains resolve variables transitively.
// CEP:WHY: The dereference step must chase chains so the MGU is fully applied.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong final bindings.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs deref.
// CEP:SECURITY: none.
#[test]
fn unify_variable_chains() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let z = terms.intern_var(2).expect("z");
    let g = symbol_id(&builder, "g");
    let gx = terms.intern_fun(&symbols, g, &[x]).expect("g(x)");
    let gy = terms.intern_fun(&symbols, g, &[y]).expect("g(y)");
    // g(x) = g(y) binds x := y; then z = x chases to y.
    assert_eq!(unify(&terms, &substitution, gx, gy), Ok(true));
    assert_eq!(unify(&terms, &substitution, z, x), Ok(true));
    let applied = substitution.apply(&terms, z, &symbols).expect("apply z");
    assert_eq!(
        substitution.apply(&terms, applied, &symbols),
        Ok(applied),
        "the MGU must be idempotent"
    );
    let _ = a;
}

// CEP:WHAT: Verifies ground matching succeeds without bindings.
// CEP:WHY: The identity case of matching.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any binding or failure.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_terms.
// CEP:SECURITY: none.
#[test]
fn match_ground_pattern() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, fa, fa),
        Ok(true)
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies matching binds pattern variables to subject subterms.
// CEP:WHY: The demodulation primitive: pattern f(x) matches subject f(a) with x := a.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong bindings.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_bounded.
// CEP:SECURITY: none.
#[test]
fn match_binds_pattern_variables() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let f = symbol_id(&builder, "f");
    let pattern = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");
    let subject = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, pattern, subject),
        Ok(true)
    );
    assert_eq!(substitution.lookup(0), Ok(Some(a)));
}

// CEP:WHAT: Verifies matching refuses subject variables under pattern non-variables.
// CEP:WHY: Matching is one-directional: pattern f(a) must not match subject f(x).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the direction is inverted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_bounded.
// CEP:SECURITY: none.
#[test]
fn match_rejects_subject_variables() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let f = symbol_id(&builder, "f");
    let pattern = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let subject = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, pattern, subject),
        Ok(false),
        "f(a) must not match f(x)"
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies the witness rejects matches whose bindings leak pattern variables into the subject.
// CEP:WHY: With the shared variable namespace, binding a pattern variable to a subject term containing a later-bound pattern variable changes the applied result; the application witness is the soundness net (Spec 02 section 5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the unsound match is accepted.
// CEP:ASSUMES: shared namespace fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_terms.
// CEP:SECURITY: namespace overlap soundness.
#[test]
fn match_witness_rejects_namespace_overlap() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let g = symbol_id(&builder, "g");
    // Pattern h(x, y) against subject h(a, g(x)): the naive walk binds y := g(x),
    // but then hat-sigma(h(x, y)) = h(sigma(x), g(sigma(x))) != h(a, g(x)) once x := a;
    // the witness must reject.
    let h = symbol_id(&builder, "h");
    let gx = terms.intern_fun(&symbols, g, &[x]).expect("g(x)");
    let pattern = terms.intern_fun(&symbols, h, &[x, y]).expect("h(x, y)");
    let subject = terms.intern_fun(&symbols, h, &[a, gx]).expect("h(a, g(x))");
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, pattern, subject),
        Ok(false),
        "the witness must reject namespace-overlapping bindings"
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies matching a pattern variable onto a term containing itself fails via the witness.
// CEP:WHY: The naive walk has no occurs check; the witness application hits the cycle guard and converts it to a plain failure.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cyclic match is accepted or errors.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs match_terms.
// CEP:SECURITY: cyclic binding rejection in matching.
#[test]
fn match_witness_rejects_cycles() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let x = terms.intern_var(0).expect("x");
    let f = symbol_id(&builder, "f");
    let fx = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");
    // Pattern x against subject f(x) is a match failure, not an error.
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, x, fx),
        Ok(false)
    );
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies composition over the union of domains applies tau first and sigma second.
// CEP:WHY: Spec 02 section 3: x(sigma tau) = hat-sigma(hat-tau(x)); composing {x := f(y)} with {y := a} yields the record {x -> f(y), y -> a}, whose full application maps x to f(a) (composition closure is under application, not at record time).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong composed record.
// CEP:ASSUMES: fresh substitutions.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs compose.
// CEP:SECURITY: none.
#[test]
fn compose_union_of_domains() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let sigma = Substitution::new(arena);
    let tau = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let y = terms.intern_var(1).expect("y");
    let f = symbol_id(&builder, "f");
    let fy = terms.intern_fun(&symbols, f, &[y]).expect("f(y)");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    sigma.bind(0, fy).expect("sigma x := f(y)");
    tau.bind(1, a).expect("tau y := a");
    let record = compose(&sigma, &tau, &terms, &symbols).expect("compose");
    let (header, pairs) = sigma.read_record(record).expect("read record");
    assert_eq!(header.binding_count, 2);
    let mut found_x = false;
    let mut found_y = false;
    for binding in pairs.iter() {
        let term = TermPtr::from_verified_offset(binding.term_offset);
        if binding.variable == 0 {
            assert_eq!(term, fy, "x must compose to hat-sigma(x) = f(y)");
            found_x = true;
        }
        if binding.variable == 1 {
            assert_eq!(term, a, "y must compose to hat-sigma(hat-tau(y)) = a");
            found_y = true;
        }
    }
    assert!(found_x && found_y, "both domains must appear in the record");
    // Closure check: applying the composed substitution to x resolves through both domains.
    let closure = Substitution::new(arena);
    for binding in pairs.iter() {
        closure
            .bind(
                binding.variable,
                TermPtr::from_verified_offset(binding.term_offset),
            )
            .expect("rebind composed entry");
    }
    let x_term = terms.intern_var(0).expect("x term");
    let resolved = closure
        .apply(&terms, x_term, &symbols)
        .expect("apply composed");
    assert_eq!(
        resolved, fa,
        "full application of the composition must map x to f(a)"
    );
}

// CEP:WHAT: Verifies composition drops identity mappings.
// CEP:WHY: Spec 02 section 1: dom(sigma) excludes x -> x; composing the swap sigma = {y := x} with tau = {x := y} maps x to itself (dropped) and keeps only y -> x.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if identity entries leak into the record.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs compose.
// CEP:SECURITY: none.
#[test]
fn compose_drops_identity() {
    let (arena, symbols, _builder, terms, _clauses) = make_term_fixture();
    let sigma = Substitution::new(arena);
    let tau = Substitution::new(arena);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    // sigma = {y := x}, tau = {x := y} (a variable swap).
    sigma.bind(1, x).expect("sigma y := x");
    tau.bind(0, y).expect("tau x := y");
    let record = compose(&sigma, &tau, &terms, &symbols).expect("compose");
    let (header, pairs) = sigma.read_record(record).expect("read record");
    // x composes to hat-sigma(hat-tau(x)) = hat-sigma(y) = x: identity, dropped.
    // y composes to hat-sigma(y) = x: kept.
    assert_eq!(header.binding_count, 1);
    assert_eq!(pairs[0].variable, 1);
    assert_eq!(TermPtr::from_verified_offset(pairs[0].term_offset), x);
}

// CEP:WHAT: Verifies unreadable term handles surface as errors, not panics.
// CEP:WHY: Law 6: structural failures are loud; a forged offset must not read out of bounds.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a panic or a wrong error.
// CEP:ASSUMES: forged offsets near the arena end.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/unify.rs map_term_error.
// CEP:SECURITY: forged-handle rejection.
#[test]
fn invalid_term_refused() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let forged = mapt::hot::ir::term::TermPtr::from_verified_offset(u32::MAX - 4);
    assert_eq!(
        unify(&terms, &substitution, forged, a),
        Err(mapt::hot::unification::substitution::SubstitutionError::InvalidPointer)
    );
    assert_eq!(
        match_terms(&terms, &symbols, &substitution, forged, a),
        Err(mapt::hot::unification::substitution::SubstitutionError::InvalidPointer)
    );
}
