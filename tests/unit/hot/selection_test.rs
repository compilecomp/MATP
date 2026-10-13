// CEP:FILE: tests/unit/hot/selection_test.rs
// CEP:WHAT: Unit tests for literal selection and maximality: KBO-computed maximal flags, ties, selection override, the first-negative function, and the empty-clause edge.
// CEP:WHY: Design 10.1/10.2 and Spec 07 section 3: eligibility drives every ordered rule; the flag computation and the two eligibility predicates are pinned here on hand-computed KBO comparisons.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs (id-order precedence, KBO default weights).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/inference/selection.rs.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::inference::selection::{
    compute_selection_flags, eligible_negative, eligible_positive, SelectionFunction,
};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;

// CEP:WHAT: Builds a predicate literal.
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
    args: &[mapt::hot::ir::term::TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Verifies KBO maximality flags: the heavier atom is maximal.
// CEP:WHY: Spec 07 section 3.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong flags.
// CEP:ASSUMES: p(a) vs p(f(a)): the latter is heavier.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::compute_selection_flags.
// CEP:SECURITY: none.
#[test]
fn maximality_computed() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
    ];
    compute_selection_flags(&context, SelectionFunction::None, &mut literals).expect("flags");
    assert!(!literals[0].is_maximal(), "p(a) is smaller");
    assert!(literals[1].is_maximal(), "p(f(a)) is maximal");
    assert!(eligible_positive(&context, &literals, 1));
    assert!(!eligible_positive(&context, &literals, 0));
    assert!(eligible_negative(&literals, 1));
}

// CEP:WHAT: Verifies ties are maximal but not strictly maximal.
// CEP:WHY: The strictness rule sends duplicate atoms to factoring, not resolution.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a tied literal is eligible-positive.
// CEP:ASSUMES: p(a) twice.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::{compute_selection_flags, eligible_positive}.
// CEP:SECURITY: none.
#[test]
fn ties_are_maximal_but_not_strict() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[a], true),
    ];
    compute_selection_flags(&context, SelectionFunction::None, &mut literals).expect("flags");
    assert!(literals[0].is_maximal() && literals[1].is_maximal());
    assert!(
        !eligible_positive(&context, &literals, 0),
        "a tied atom is not strictly maximal"
    );
}

// CEP:WHAT: Verifies a selected literal overrides maximality.
// CEP:WHY: Design 10.2: selection licenses inference regardless of maximality.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the selected small atom is ineligible.
// CEP:ASSUMES: FirstNegative selects the negative literal.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::{compute_selection_flags, eligible_negative}.
// CEP:SECURITY: none.
#[test]
fn selection_overrides_maximality() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    // The negative literal p(a) is the smaller atom but gets selected.
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[a], false),
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
    ];
    compute_selection_flags(&context, SelectionFunction::FirstNegative, &mut literals)
        .expect("flags");
    assert!(literals[0].is_selected());
    assert!(eligible_negative(&literals, 0), "selection overrides");
    assert!(
        !eligible_positive(&context, &literals, 1),
        "unselected side is blocked"
    );
}

// CEP:WHAT: Verifies FirstNegative selects exactly the first negative literal.
// CEP:WHY: The selection function's contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong selection.
// CEP:ASSUMES: two negative literals.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::{compute_selection_flags, SelectionFunction}.
// CEP:SECURITY: none.
#[test]
fn first_negative_selects() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
        pred(&terms, &symbols, &builder, "p", &[a], false),
        pred(&terms, &symbols, &builder, "p", &[f_a], false),
    ];
    compute_selection_flags(&context, SelectionFunction::FirstNegative, &mut literals)
        .expect("flags");
    assert!(!literals[0].is_selected());
    assert!(literals[1].is_selected(), "the first negative literal");
    assert!(!literals[2].is_selected());
}

// CEP:WHAT: Verifies the empty clause needs no flags.
// CEP:WHY: The loop stores the empty conclusion without flag computation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the empty slice errors.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::compute_selection_flags.
// CEP:SECURITY: none.
#[test]
fn empty_clause_flags() {
    let (_arena, symbols, _builder, terms, precedence, substitution) = make_inference_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let mut literals: [Literal; 0] = [];
    assert!(compute_selection_flags(&context, SelectionFunction::None, &mut literals).is_ok());
}
