// CEP:FILE: tests/unit/hot/subsumption_resolution_test.rs
// CEP:WHAT: Unit tests for subsumption resolution and condensation (CEP-1034): the firing shapes (one and two side literals mapped onto the resolution literal, target reuse across role-B assignments), the rejection shapes (no opposite-polarity match, an unassignable side literal, a size-guard rejection), the deterministic first-hit scan, the attempt budget's bounded abort, the condensation firing and non-firing shapes, and the trail hygiene of every failed attempt.
// CEP:WHY: Spec 07 sections 11-12 and Design 10.1: subsumption resolution is the Riazanov & Voronkov 2003 "resolution + subsumption" fusion (formally Definition 2 of arXiv:2412.16058: sigma(S') = {not m'} and sigma(S \ S') subset of M \ {m'} as exact matches) and condensation is its self-case; each test hand-computes the expected decision so a wrong role assignment cannot pass, and the trail checks pin the Spec 02 section 4 discipline on the shared substitution.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs (id-order precedence, KBO default weights: all symbols 1, variables 1); side and main namespaces are kept disjoint by construction (the loop's rename-apart discipline is exercised in the loop and kernel tests).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/inference/subsumption.rs::{subsumption_resolves, subsumption_resolves_onto, condensation_target, condensation_resolves_onto} and config/limits.rs::kMaxSrMatchAttempts.
// CEP:SECURITY: the attempt budget bound is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::inference::subsumption::{condensation_target, subsumption_resolves};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;

// CEP:WHAT: Builds a predicate literal over the fixture vocabulary.
// CEP:WHY: Readable fixture construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn pred(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Interns a variable term.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn var(terms: &mapt::hot::ir::term::TermStore<'_>, index: u32) -> TermPtr {
    terms.intern_var(index).expect("var")
}

// CEP:WHAT: Interns a function application.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fun(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[TermPtr],
) -> TermPtr {
    terms
        .intern_fun(symbols, symbol_id(builder, name), args)
        .expect("term")
}

// CEP:WHAT: The paper's S4 shape (adapted to the fixture vocabulary): side = not p(h(x1,x2)) v not q(x3,a), main = p(h(a,b)) v not p(g(b)) v not q(x0,a) with the side's variables above the main's window.
// CEP:WHY: Definition 2's canonical firing case: sigma = {x1->a, x2->b, x3->x0} maps not p(h(x1,x2)) onto not m' = not p(h(a,b)) and not q(x3,a) onto the exact member not q(x0,a), licensing the deletion of the resolution literal p(h(a,b)).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the decision rejects or names the wrong resolution literal.
// CEP:ASSUMES: disjoint namespaces by construction (side vars 1-3, main var 0).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves.
// CEP:SECURITY: none.
#[test]
fn sr_fires_on_resolution_literal() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let x3 = var(&terms, 3);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let ga = fun(&terms, &symbols, &builder, "g", &[a]);
    let h_ab = fun(&terms, &symbols, &builder, "h", &[a, b]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], false),
        pred(&terms, &symbols, &builder, "q", &[x3, a], false),
    ];
    let side_wrong_vars = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], false),
        pred(&terms, &symbols, &builder, "q", &[x1, a], false),
    ];
    let _ = (x1, x2, ga);
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], true),
        pred(&terms, &symbols, &builder, "p", &[ga], false),
        pred(&terms, &symbols, &builder, "q", &[x0, a], false),
    ];
    let _ = side_wrong_vars;
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution,
        Some(0),
        "the positive p(h(a,b)) literal is the first licensed resolution literal"
    );
}

// CEP:WHAT: The paper's S5 shape: two side literals map onto the same resolution literal.
// CEP:WHY: The S' set may hold several literals (both not p(...) atoms sigma-match not m' = not p(h(a,b)) under one shared substitution) - a single-literal-only implementation would miss this legal deletion; the shared-substitution role search of Spec 07 section 11 covers it.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the two-into-one mapping is rejected.
// CEP:ASSUMES: disjoint namespaces by construction.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn sr_two_side_literals_map_to_resolution_literal() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let x3 = var(&terms, 3);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let gb = fun(&terms, &symbols, &builder, "g", &[b]);
    let h_ab = fun(&terms, &symbols, &builder, "h", &[a, b]);
    let h_x1_b = fun(&terms, &symbols, &builder, "h", &[x1, b]);
    let h_a_x2 = fun(&terms, &symbols, &builder, "h", &[a, x2]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[h_x1_b], false),
        pred(&terms, &symbols, &builder, "p", &[h_a_x2], false),
        pred(&terms, &symbols, &builder, "q", &[x3, a], false),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], true),
        pred(&terms, &symbols, &builder, "p", &[gb], false),
        pred(&terms, &symbols, &builder, "q", &[x0, a], false),
    ];
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution,
        Some(0),
        "both not p literals map onto not p(h(a,b)) (the S5 shape)"
    );
}

// CEP:WHAT: The paper's S6 shape: no side literal can match the resolution literal's complement.
// CEP:WHY: Role A needs an opposite-polarity match onto not m'; with every side literal of m''s polarity the S' set stays empty and the decision must reject.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a false accept.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn sr_rejects_no_opposite_polarity_match() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let x0 = var(&terms, 0);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let ga = fun(&terms, &symbols, &builder, "g", &[a]);
    let h_ab = fun(&terms, &symbols, &builder, "h", &[a, b]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[ga], true),
        pred(&terms, &symbols, &builder, "q", &[x2, b], true),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], true),
        pred(&terms, &symbols, &builder, "p", &[ga], false),
        pred(&terms, &symbols, &builder, "q", &[x0, a], false),
    ];
    let _ = x1;
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution, None,
        "no side literal matches not m' (S6 shape)"
    );
}

// CEP:WHAT: The paper's S8 shape: a side literal with no possible role-B match.
// CEP:WHY: Every side literal must sigma-match either not m' or an exact member of M \ {m'}; the unmatched r() literal rejects the whole decision even though the rest assigns.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a false accept.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::assign_side_literal.
// CEP:SECURITY: none.
#[test]
fn sr_rejects_unmatched_side_literal() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let h_ab = fun(&terms, &symbols, &builder, "h", &[a, b]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], false),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[h_ab], true),
        pred(&terms, &symbols, &builder, "p", &[b], false),
        pred(&terms, &symbols, &builder, "q", &[x0, a], false),
    ];
    let _ = (x1, x2);
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution, None,
        "the r() literal has no role-B target (S8 shape)"
    );
}

// CEP:WHAT: The size guard: a side premise longer than the main premise never subsumption-resolves.
// CEP:WHY: sigma(S \ S') subset of M \ {m'} forces |S| - |S'| <= |M| - 1 and S' >= 1, so |S| <= |M| is a necessary condition; the guard rejects loudly before any matching work.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a decision over an oversized side premise.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn sr_rejects_oversized_side_premise() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[a], false),
        pred(&terms, &symbols, &builder, "p", &[a], false),
        pred(&terms, &symbols, &builder, "p", &[a], false),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[a], false),
    ];
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(resolution, None, "|side| > |main| rejects before matching");
}

// CEP:WHAT: The deterministic first-hit scan: the earliest licensed resolution literal wins.
// CEP:WHY: CEP&CC 38.10: the loop's deletion and the kernel's replay must agree on WHICH literal is removed; the ascending scan fixes the choice as a pure function of the premises.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when a later literal is chosen.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves.
// CEP:SECURITY: none.
#[test]
fn sr_first_resolution_literal_wins() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let side = vec![
        pred(&terms, &symbols, &builder, "q", &[x2, a], false),
        pred(&terms, &symbols, &builder, "p", &[b], false),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "q", &[x0, a], true),
        pred(&terms, &symbols, &builder, "p", &[b], false),
    ];
    // m' = 0 (p(a)): side not q(x2,a) has no role onto not p(a) (head q) and
    // role B onto {q(x0,a)+, not p(b)-}: not p(b) matches not p(b) identity...
    // but then not q(x2,a) is unassignable (role A onto not p(a) head-mismatches;
    // role B targets exclude index 0 and not q(x0,a) is positive) -> rejected.
    // m' = 1 (q(x0,a)): side not q(x2,a) maps onto not m' = not q(x0,a) via
    // x2->x0, and not p(b) maps onto the exact member not p(b) -> licensed.
    let _ = x1;
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution,
        Some(1),
        "the earliest licensed resolution literal is index 1"
    );
}

// CEP:WHAT: The attempt budget bounds the exponential backtracking: a role-B-heavy decision aborts as Ok(false) without hanging or leaking bindings.
// CEP:WHY: Law 6 (bounded failure): the kMaxSrMatchAttempts budget caps every decision; the engineered shape (five variable literals, each with eight role-B alternatives, in front of an unassignable literal) forces the search past the budget deterministically; the same bound replays in the kernel, so recorded steps still verify (CEP-1034).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on an Err, a hang (the budget aborts), or a trail leak.
// CEP:ASSUMES: the budget is 1024 (config/limits.rs).
// CEP:COST: bounded by the budget.
// CEP:EVIDENCE: cited by config/limits.rs::kMaxSrMatchAttempts.
// CEP:SECURITY: the CPU bound of the exponential decision.
#[test]
fn sr_attempt_budget_bounds_the_search() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    // Eight distinct p-terms for the role-B alternatives.
    let ps = [
        fun(&terms, &symbols, &builder, "f", &[a]),
        fun(&terms, &symbols, &builder, "f", &[b]),
        fun(&terms, &symbols, &builder, "g", &[a]),
        fun(&terms, &symbols, &builder, "g", &[b]),
        fun(&terms, &symbols, &builder, "h", &[a, b]),
        fun(&terms, &symbols, &builder, "h", &[b, a]),
        fun(
            &terms,
            &symbols,
            &builder,
            "f",
            &[fun(&terms, &symbols, &builder, "g", &[a])],
        ),
        fun(
            &terms,
            &symbols,
            &builder,
            "g",
            &[fun(&terms, &symbols, &builder, "f", &[b])],
        ),
    ];
    let mut side: Vec<Literal> = Vec::new();
    for index in 0..5u32 {
        side.push(pred(
            &terms,
            &symbols,
            &builder,
            "p",
            &[var(&terms, index)],
            true,
        ));
    }
    side.push(pred(&terms, &symbols, &builder, "r", &[], true));
    let mut main: Vec<Literal> = ps
        .iter()
        .map(|term| pred(&terms, &symbols, &builder, "p", &[*term], true))
        .collect();
    main.push(pred(&terms, &symbols, &builder, "p", &[a], false));
    let entry_depth = substitution.trail_depth();
    let resolution = subsumption_resolves(&context, &side, &main).expect("bounded decision");
    assert_eq!(
        resolution, None,
        "the r() literal never assigns; the budget aborts the backtracking"
    );
    assert_eq!(
        substitution.trail_depth(),
        entry_depth,
        "the bounded abort leaves the substitution trail untouched"
    );
}

// CEP:WHAT: The condensation firing shape: the canonical Bachmair-Ganzinger instance P(x0) v P(f(x0)) condenses to P(x0).
// CEP:WHY: Spec 07 section 12: deleting the second literal is licensed because every clause literal is a sigma-instance of the kept target under one shared substitution (sigma = {renamed x -> x0} maps P(x1) onto P(x0) and onto P(f(x0))); the conclusion P(x0) entails the original clause pointwise, so the strengthening is sound.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the condensation is missed or names the wrong literal.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::condensation_target.
// CEP:SECURITY: none.
#[test]
fn condensation_fires() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let fa = fun(&terms, &symbols, &builder, "f", &[a]);
    let _ = (a, fa);
    let clause = vec![
        pred(&terms, &symbols, &builder, "p", &[x0], true),
        pred(
            &terms,
            &symbols,
            &builder,
            "p",
            &[fun(&terms, &symbols, &builder, "f", &[x0])],
            true,
        ),
    ];
    let target = condensation_target(&context, &clause).expect("decision");
    assert_eq!(
        target,
        Some(1),
        "the deeper literal P(f(x0)) is the licensed deletion (removing P(x0) is not: P(f(x0)) does not instance P(x0))"
    );
}

// CEP:WHAT: A clause without an opposite-polarity same-head pair never condenses.
// CEP:WHY: Condensation needs a side literal sigma-matching the resolution literal's complement; with no opposite-polarity pair the S' set stays empty for every candidate; the head-pair prefilter in the loop's simplify path rests on the same necessary condition.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a false accept.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::condensation_target and the loop prefilter.
// CEP:SECURITY: none.
#[test]
fn condensation_keeps_unmatched_clause() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let clause = vec![
        pred(&terms, &symbols, &builder, "p", &[x0], true),
        pred(&terms, &symbols, &builder, "q", &[x1, b], true),
    ];
    let target = condensation_target(&context, &clause).expect("decision");
    assert_eq!(target, None, "no opposite-polarity pair, no condensation");
}

// CEP:WHAT: The condensation decision leaves the substitution trail untouched on failure.
// CEP:WHY: Spec 02 section 4's trail discipline: a failed self-resolution attempt composes with later inferences without state leakage; the renamed-apart side copy (condensation_resolves_onto) keeps the self-match from binding variables to themselves.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any trail-depth change.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::condensation_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn condensation_trail_untouched_on_failure() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let clause = vec![
        pred(&terms, &symbols, &builder, "p", &[x0], true),
        pred(&terms, &symbols, &builder, "q", &[x1, b], true),
    ];
    let entry_depth = substitution.trail_depth();
    let target = condensation_target(&context, &clause).expect("decision");
    assert_eq!(target, None);
    assert_eq!(
        substitution.trail_depth(),
        entry_depth,
        "the failed attempts unwind completely"
    );
}

// CEP:WHAT: The SR decision leaves the substitution trail untouched on failure.
// CEP:WHY: Spec 07 section 11 Invariant 4 (trail hygiene): every failed match branch unwinds its own bindings and the top call unwinds to the entry depth, so rule attempts compose without state leakage.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any trail-depth change.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn sr_trail_untouched_on_failure() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let x1 = var(&terms, 1);
    let x0 = var(&terms, 0);
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let ga = fun(&terms, &symbols, &builder, "g", &[a]);
    let side = vec![
        pred(&terms, &symbols, &builder, "p", &[ga], true),
        pred(&terms, &symbols, &builder, "q", &[x1, a], true),
    ];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[ga], false),
        pred(&terms, &symbols, &builder, "q", &[x0, a], false),
    ];
    let entry_depth = substitution.trail_depth();
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(resolution, None);
    assert_eq!(
        substitution.trail_depth(),
        entry_depth,
        "the failed attempts unwind completely"
    );
}

// CEP:WHAT: The paper's resolution-literal-target shape: the side literal's only exact main match is the resolution literal itself.
// CEP:WHY: The backtracking search assigns each side literal one of two roles - the opposite-polarity resolution match (role A, into the non-empty S') or an exact same-polarity match at an index DIFFERENT from the resolution literal (role B) - and soundness needs both: a side literal allowed to map onto the resolution literal itself would leave sigma(side) unconstrained by the falsifying valuation of main \ {m'} (Spec 07 section 11), so the decision must reject when the only match is the resolution literal and no role-A literal exists.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a false accept.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumption_resolves_onto.
// CEP:SECURITY: none.
#[test]
fn sr_rejects_resolution_literal_target() {
    let (_arena, symbols, builder, terms, _p, substitution) = make_inference_fixture();
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &_p,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    // Side: p(a) positive. Main: p(a) positive (the resolution literal) and
    // q(x1, b) negative. The side literal exactly equals the resolution
    // literal; role A needs an opposite-polarity match (none), and role B must
    // target an index other than the resolution literal (only q(x1, b), which
    // does not match). Either resolution-literal choice rejects.
    let x1 = var(&terms, 1);
    let side = vec![pred(&terms, &symbols, &builder, "p", &[a], true)];
    let main = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "q", &[x1, b], false),
    ];
    let resolution = subsumption_resolves(&context, &side, &main).expect("decision");
    assert_eq!(
        resolution, None,
        "mapping onto the resolution literal itself is not a licensed role"
    );
}

// CEP:WHAT: The head-symbol prefilter of the given-time simplification scans stays sound across the equality pseudo-head: a subsumption-resolution whose resolution literal carries the equality head fires, and the pseudo-head never collides with a real symbol id.
// CEP:WHY: The scan runs behind a sound head-occurrence prefilter; the equality pseudo-head class (design 8.3's comparable-with-everything equality) is its own class and the side premise's equality-headed resolution literal must pass the prefilter exactly when the main premise carries an equality atom - a collision with a real symbol id would either block a legal deletion or license an illegal one (hot/search/given_clause.rs).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the equality-headed SR is blocked or fires for the wrong reason.
// CEP:ASSUMES: the S4 shape with the equality atom as the resolution literal; the search runs to saturation.
// CEP:COST: one saturation over two clauses.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs's head-class prefilter and config/limits.rs kSrHeadSymbols.
// CEP:SECURITY: none.
#[test]
fn sr_head_prefilter_soundness() {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = mapt::hot::search::given_clause::SearchOptions::new();
    let space = mapt::hot::search::given_clause::SearchSpace::new_with(
        arena, &options, 16, 4096, 8192, 8192, 65536, 4096,
    )
    .expect("space");
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let a = fun(&terms, &symbols, &builder, "a", &[]);
    let b = fun(&terms, &symbols, &builder, "b", &[]);
    let x0 = var(&terms, 0);
    let x1 = var(&terms, 1);
    let x2 = var(&terms, 2);
    let x3 = var(&terms, 3);
    let x4 = var(&terms, 4);
    let eq_main = mapt::hot::ir::literal::Literal::new(
        terms.intern_eq(&symbols, x0, a).expect("eq main"),
        true,
    );
    let eq_side = mapt::hot::ir::literal::Literal::new(
        terms.intern_eq(&symbols, x1, a).expect("eq side"),
        false,
    );
    // Side premise (selected first): its equality literal sigma-matches the
    // negation of the main's equality literal (role A: x1 := x0), and its
    // q literal sigma-matches one main q literal (role B: x4 := x2).
    let side = vec![
        eq_side,
        pred(&terms, &symbols, &builder, "q", &[x4, a], false),
    ];
    space
        .add_input_clause(&context, &options, &side)
        .expect("side");
    // Main premise: the equality atom is the resolution literal; the clause
    // has no other equality literal, so the head-occurrence prefilter must
    // admit the side premise through the pseudo-head class.
    let main = vec![
        eq_main,
        pred(&terms, &symbols, &builder, "q", &[x2, a], false),
        pred(&terms, &symbols, &builder, "q", &[x3, b], false),
    ];
    space
        .add_input_clause(&context, &options, &main)
        .expect("main");
    let mut stats = mapt::hot::search::given_clause::SearchStats::default();
    let outcome = mapt::hot::search::given_clause::saturate(
        &space,
        &context,
        &options,
        &|_iterations: u64| false,
        &mut stats,
    )
    .expect("saturate");
    assert_eq!(
        outcome,
        mapt::hot::search::given_clause::SearchOutcome::Saturated
    );
    assert_eq!(
        stats.subsumption_resolutions, 1,
        "the equality-headed resolution literal passes the head prefilter"
    );
    let mut found = false;
    for id in 1..=space.store.next_clause_id().0 {
        if let Ok(record) = space
            .store
            .clause_by_id(mapt::hot::ir::clause::ClauseId(id))
        {
            if record.derivation.rule == mapt::hot::ir::clause::InferenceRule::SubsumptionResolution
            {
                found = true;
            }
        }
    }
    assert!(found, "an SR chain record must exist in the store");
}
