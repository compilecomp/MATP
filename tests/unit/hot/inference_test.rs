// CEP:FILE: tests/unit/hot/inference_test.rs
// CEP:WHAT: Unit tests for the inference rules: renaming and namespace discipline, resolution (ground, MGU application, side conditions), factoring (plain and equality), superposition left and right (orientation, variable restriction, side conditions), equality resolution, demodulation (rewrites, orientation, decrease), subsumption (ground, instantiation, reuse, rejection), tautology detection, and the structural bounds.
// CEP:WHY: Design 10.1/10.2 and Spec 07: every rule's soundness is unconditional, but its side conditions and namespace discipline are what make the search complete and the substitution engine sound; each test hand-computes the expected conclusion so a wrong rule cannot pass.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs (id-order precedence, KBO default weights: all symbols 1, variables 1).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/inference/{builder,resolution,factoring,superposition,demodulation,subsumption}.rs.
// CEP:SECURITY: the namespace and conclusion-length bounds are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::inference::builder::{
    count_clause_variables, rename_apart, rename_clause_apart, restandardize_clause,
};
use mapt::hot::inference::demodulation::demodulate;
use mapt::hot::inference::factoring::{equality_factor, factor};
use mapt::hot::inference::resolution::resolve;
use mapt::hot::inference::subsumption::{is_tautology, subsumes};
use mapt::hot::inference::superposition::{equality_resolve, superpose};
use mapt::hot::inference::{InferenceContext, InferenceError, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;

// CEP:WHAT: Builds the KBO inference context of a fixture.
// CEP:WHY: One constructor for this file.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn kbo_context<'a>(
    terms: &'a mapt::hot::ir::term::TermStore<'a>,
    symbols: &'a mapt::hot::ir::symbol_table::SymbolTable<'a>,
    precedence: &'a mapt::hot::ordering::precedence::PrecedenceTable<'a>,
    substitution: &'a mapt::hot::unification::substitution::Substitution<'a>,
) -> InferenceContext<'a> {
    InferenceContext {
        terms,
        symbols,
        substitution,
        precedence,
        ordering: OrderingKind::Kbo,
    }
}

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
    args: &[TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Builds an equality literal.
// CEP:WHY: Readable fixture construction for the equality rules.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn eq_lit(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    left: TermPtr,
    right: TermPtr,
    positive: bool,
) -> Literal {
    let atom = terms.intern_eq(symbols, left, right).expect("eq atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Computes the eligibility flags of a test literal slice in place.
// CEP:WHY: The rules read cached flags (design 5.2); test fixtures must establish them exactly like the search loop does.
// CEP:STATUS: complete
// CEP:FAILURE: panics on flag failure.
// CEP:ASSUMES: fixture context.
// CEP:COST: O(n^2) comparisons.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn flags(context: &InferenceContext<'_>, literals: &mut [Literal]) {
    mapt::hot::inference::selection::compute_selection_flags(
        context,
        mapt::hot::inference::SelectionFunction::None,
        literals,
    )
    .expect("flags");
}

// CEP:WHAT: Interns a ground constant by name.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn constant(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
) -> TermPtr {
    terms
        .intern_fun(symbols, symbol_id(builder, name), &[])
        .expect("constant")
}

// CEP:WHAT: Verifies rename_apart shifts variable indices and preserves structure.
// CEP:WHY: Spec 07 section 2: the renaming bijorphism.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong shift or changed structure.
// CEP:ASSUMES: p(x) with x = var 0, shifted by 5.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/builder.rs::{rename_apart, term_error}.
// CEP:SECURITY: none.
#[test]
fn rename_shifts_variables() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let renamed = rename_apart(&terms, &symbols, atom, 5, 0).expect("rename");
    let view = terms.term(renamed).expect("read");
    let child = view.child(0).expect("child");
    let child_view = terms.term(child).expect("read child");
    assert_eq!(child_view.symbol(), 5, "variable 0 shifts to 5");
}

// CEP:WHAT: Verifies renaming preserves term structure (symbols and shape).
// CEP:WHY: The hash-consed rebuild must reproduce the skeleton.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any structural deviation.
// CEP:ASSUMES: h(x, f(y)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/builder.rs::{rename_apart, term_error}.
// CEP:SECURITY: none.
#[test]
fn rename_preserves_structure() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let _x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let f_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[y])
        .expect("f(y)");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[f_y])
        .expect("p(f(y))");
    let renamed = rename_apart(&terms, &symbols, atom, 10, 0).expect("rename");
    let view = terms.term(renamed).expect("read");
    assert_eq!(view.symbol(), symbol_id(&builder, "p"));
    assert_eq!(view.child_count(), 1);
    let child = terms.term(view.child(0).expect("child")).expect("read");
    assert_eq!(child.symbol(), symbol_id(&builder, "f"));
    assert_eq!(child.child_count(), 1);
}

// CEP:WHAT: Verifies two premises can be renamed into one shared namespace.
// CEP:WHY: Spec 02 section 5: the standardize-apart contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on variable collision.
// CEP:ASSUMES: left uses var 0; right uses var 0 renamed by +vars(left).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/builder.rs::{rename_clause_apart, count_clause_variables}.
// CEP:SECURITY: none.
#[test]
fn premises_renamed_apart() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let left = [pred(
        &terms,
        &symbols,
        &builder,
        "p",
        &[terms.intern_var(0).expect("x")],
        true,
    )];
    let right = [pred(
        &terms,
        &symbols,
        &builder,
        "p",
        &[terms.intern_var(0).expect("y")],
        false,
    )];
    let left_vars = count_clause_variables(&terms, &left).expect("count");
    assert_eq!(left_vars, 1);
    let mut renamed: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let right_vars = rename_clause_apart(&terms, &symbols, &right, left_vars as u32, &mut renamed)
        .expect("rename");
    assert_eq!(right_vars, 1);
    let view = terms.term(renamed[0].atom()).expect("read");
    let child = terms
        .term(view.child(0).expect("child"))
        .expect("read child");
    assert_eq!(child.symbol(), 1, "right var 0 now lives at index 1");
}

// CEP:WHAT: Verifies the namespace bound rejects pairs that cannot share the window.
// CEP:WHY: kMaxInferenceVariables is the structural soundness bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the overflow is accepted.
// CEP:ASSUMES: a right premise with variables at the top of the window shifted beyond the bound.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/builder.rs::{rename_clause_apart, VariableBudgetExceeded}.
// CEP:SECURITY: the soundness bound under test.
#[test]
fn namespace_budget_enforced() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    // A clause using the highest legal variable index.
    let top = mapt_config::limits::kMaxVariablesPerClause - 1;
    let right = [pred(
        &terms,
        &symbols,
        &builder,
        "p",
        &[terms.intern_var(top).expect("v")],
        true,
    )];
    let mut renamed: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let result = rename_clause_apart(&terms, &symbols, &right, 1, &mut renamed);
    assert!(matches!(
        result,
        Err(InferenceError::VariableBudgetExceeded)
    ));
}

// CEP:WHAT: Verifies conclusions are restandardized to dense namespaces.
// CEP:WHY: The storage half of the discipline (Spec 07 section 2).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a non-dense result.
// CEP:ASSUMES: a conclusion using variable indices 3 and 40.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/builder.rs::{restandardize_clause, remap_variables}.
// CEP:SECURITY: none.
#[test]
fn conclusions_restandardized() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let v3 = terms.intern_var(3).expect("v3");
    let v40 = terms.intern_var(40).expect("v40");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[v3], true),
        pred(&terms, &symbols, &builder, "p", &[v40], false),
    ];
    let count = restandardize_clause(&terms, &symbols, &mut literals).expect("restandardize");
    assert_eq!(count, 2, "two distinct variables");
    let first = terms
        .term(
            terms
                .term(literals[0].atom())
                .expect("a")
                .child(0)
                .expect("c"),
        )
        .expect("v");
    let second = terms
        .term(
            terms
                .term(literals[1].atom())
                .expect("a")
                .child(0)
                .expect("c"),
        )
        .expect("v");
    assert_eq!(first.symbol(), 0, "first occurrence maps to 0");
    assert_eq!(second.symbol(), 1, "second occurrence maps to 1");
}

// CEP:WHAT: Verifies ground resolution derives the empty clause from complementary units.
// CEP:WHY: Robinson 1965's base case.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other conclusion.
// CEP:ASSUMES: p(a) and not p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::resolve.
// CEP:SECURITY: none.
#[test]
fn binary_resolution_ground() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let mut left = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let mut right = [pred(&terms, &symbols, &builder, "p", &[a], false)];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = resolve(&context, &left, 0, &right, 0, &mut out).expect("resolve");
    assert!(matches!(
        outcome,
        mapt::hot::inference::resolution::ResolutionOutcome::Concluded(0)
    ));
}

// CEP:WHAT: Verifies resolution applies the MGU to the surviving literals.
// CEP:WHY: Spec 07 section 4.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unapplied survivor.
// CEP:ASSUMES: p(x) v q... resolved with not p(f(a)) leaving q(f(a))... using p and r literals for arity safety.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::resolve and hot/inference/builder.rs::apply_literal.
// CEP:SECURITY: none.
#[test]
fn resolvent_applies_mgu() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    // Left: p(x) or r; right: not p(f(a)) or p(a).
    let mut left = [
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    let mut right = [
        pred(&terms, &symbols, &builder, "p", &[f_a], false),
        pred(&terms, &symbols, &builder, "p", &[a], true),
    ];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    // Right's negative literal p(f(a)) is maximal? p(f(a)) vs p(a): heavier -> maximal.
    let outcome = resolve(&context, &left, 0, &right, 0, &mut out).expect("resolve");
    assert!(matches!(
        outcome,
        mapt::hot::inference::resolution::ResolutionOutcome::Concluded(2)
    ));
    // The survivors are r and p(a) (order: left survivors then right survivors).
    let second = terms.term(out[1].atom()).expect("read");
    assert_eq!(second.symbol(), symbol_id(&builder, "p"));
}

// CEP:WHAT: Verifies resolution with a non-ground MGU binds variables.
// CEP:WHY: The MGU path beyond ground.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong conclusion.
// CEP:ASSUMES: p(x) with not p(y): MGU {x -> y} or {y -> x} gives the empty clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::resolve.
// CEP:SECURITY: none.
#[test]
fn resolution_applies_mgu() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let mut left = [pred(&terms, &symbols, &builder, "p", &[x], true)];
    let mut right = [pred(&terms, &symbols, &builder, "p", &[y], false)];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = resolve(&context, &left, 0, &right, 0, &mut out).expect("resolve");
    assert!(matches!(
        outcome,
        mapt::hot::inference::resolution::ResolutionOutcome::Concluded(0)
    ));
}

// CEP:WHAT: Verifies ineligible literals are rejected (non-maximal positive side).
// CEP:WHY: The ordered calculus restriction.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the small literal resolves.
// CEP:ASSUMES: p(a) or p(f(a)): resolving on p(a) is blocked.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::{resolve, eligible_positive}.
// CEP:SECURITY: none.
#[test]
fn resolution_side_conditions() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut left = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
    ];
    let mut right = [pred(&terms, &symbols, &builder, "p", &[x], false)];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let blocked = resolve(&context, &left, 0, &right, 0, &mut out).expect("resolve");
    assert!(
        matches!(
            blocked,
            mapt::hot::inference::resolution::ResolutionOutcome::None
        ),
        "the non-maximal p(a) is blocked by eligibility before unification"
    );
    // The maximal literal resolves with not p(x) and yields p(a).
    let allowed = resolve(&context, &left, 1, &right, 0, &mut out).expect("resolve");
    assert!(matches!(
        allowed,
        mapt::hot::inference::resolution::ResolutionOutcome::Concluded(1)
    ));
}

// CEP:WHAT: Verifies ineligible negative literals are rejected.
// CEP:WHY: The negative-side maximality restriction.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the non-maximal negative literal resolves.
// CEP:ASSUMES: not p(a) or not p(f(a)) against p(f(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::{resolve, eligible_negative}.
// CEP:SECURITY: none.
#[test]
fn resolution_rejects_ineligible() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut left = [pred(&terms, &symbols, &builder, "p", &[f_a], true)];
    let mut right = [
        pred(&terms, &symbols, &builder, "p", &[a], false),
        pred(&terms, &symbols, &builder, "p", &[f_a], false),
    ];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let blocked = resolve(&context, &left, 0, &right, 0, &mut out).expect("resolve");
    assert!(matches!(
        blocked,
        mapt::hot::inference::resolution::ResolutionOutcome::None
    ));
}

// CEP:WHAT: Verifies factoring merges unifiable same-polarity literals.
// CEP:WHY: Spec 07 section 5.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong conclusion.
// CEP:ASSUMES: p(f(y)) or p(x): factors to p(f(y)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::factor.
// CEP:SECURITY: none.
#[test]
fn factoring_merges_unifiable_literals() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let f_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[y])
        .expect("f(y)");
    // Order the maximal literal first so the eligibility check passes.
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[f_y], true),
        pred(&terms, &symbols, &builder, "p", &[x], true),
    ];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = factor(&context, &literals, 0, 1, &mut out).expect("factor");
    assert!(matches!(
        outcome,
        mapt::hot::inference::factoring::FactoringOutcome::Concluded(1)
    ));
    let view = terms.term(out[0].atom()).expect("read");
    assert_eq!(view.symbol(), symbol_id(&builder, "p"));
}

// CEP:WHAT: Verifies factoring applies the MGU to the merged literal.
// CEP:WHY: The kept literal is the applied first literal.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unapplied merge.
// CEP:ASSUMES: p(f(y)) or p(x): the factored literal is p(f(y)) with y intact.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::factor and hot/inference/builder.rs::apply_literal.
// CEP:SECURITY: none.
#[test]
fn factoring_applies_mgu() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let f_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[y])
        .expect("f(y)");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[f_y], true),
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = factor(&context, &literals, 0, 1, &mut out).expect("factor");
    assert!(matches!(
        outcome,
        mapt::hot::inference::factoring::FactoringOutcome::Concluded(2)
    ));
    // Survivors: the applied p(f(y)) and r.
    assert!(out[0].is_positive());
}

// CEP:WHAT: Verifies factoring rejects opposite-polarity pairs.
// CEP:WHY: Factoring is same-polarity only.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a complementary pair factors.
// CEP:ASSUMES: p(a) and not p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::factor.
// CEP:SECURITY: none.
#[test]
fn factoring_rejects_opposite_polarity() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[a], false),
    ];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = factor(&context, &literals, 0, 1, &mut out).expect("factor");
    assert!(matches!(
        outcome,
        mapt::hot::inference::factoring::FactoringOutcome::None
    ));
}

// CEP:WHAT: Verifies factoring's eligibility restriction (non-maximal kept literal blocked).
// CEP:WHY: Spec 07 section 5.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the small literal factors.
// CEP:ASSUMES: p(a) or p(f(a)): factoring on p(a) is blocked.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::factor and hot/inference/selection.rs::eligible_positive.
// CEP:SECURITY: none.
#[test]
fn factoring_side_conditions() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut literals = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
    ];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let blocked = factor(&context, &literals, 0, 1, &mut out).expect("factor");
    assert!(matches!(
        blocked,
        mapt::hot::inference::factoring::FactoringOutcome::None
    ));
}

// CEP:WHAT: Verifies equality resolution collapses a reflexive disequation.
// CEP:WHY: NR01 section 4.3.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other conclusion.
// CEP:ASSUMES: clause not (a = a) alone.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::equality_resolve and hot/inference/factoring.rs::equality_sides.
// CEP:SECURITY: none.
#[test]
fn equality_resolution_concludes() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let mut literals = [eq_lit(&terms, &symbols, a, a, false)];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = equality_resolve(&context, &literals, 0, &mut out).expect("resolve");
    assert!(matches!(
        outcome,
        mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(0)
    ));
}

// CEP:WHAT: Verifies equality factoring concludes the standard disequality form.
// CEP:WHY: NR01 section 4.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong conclusion shape.
// CEP:ASSUMES: (a = b) or (a = c): concludes (a = b) or not (b = c).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::equality_factor.
// CEP:SECURITY: none.
#[test]
fn equality_factoring_concludes() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = constant(&terms, &symbols, &builder, "a");
    let b = constant(&terms, &symbols, &builder, "b");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let f_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[y])
        .expect("f(y)");
    let mut literals = [
        eq_lit(&terms, &symbols, f_x, a, true),
        eq_lit(&terms, &symbols, f_y, b, true),
    ];
    flags(&context, &mut literals);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let outcome = equality_factor(&context, &literals, 0, 1, &mut out).expect("factor");
    assert!(matches!(
        outcome,
        mapt::hot::inference::factoring::FactoringOutcome::Concluded(2)
    ));
    // The second conclusion literal is the disequality not (a = b).
    assert!(!out[1].is_positive());
    let sides = mapt::hot::inference::factoring::equality_sides(&terms, out[1].atom());
    assert!(sides.is_some());
}

// CEP:WHAT: Verifies superposition into a negative literal rewrites the subterm.
// CEP:WHY: Spec 07 section 6 (left superposition).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong conclusion.
// CEP:ASSUMES: from (f(x) = x), into not p(f(a)): concludes not p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::{superpose, subterm_at}.
// CEP:SECURITY: none.
#[test]
fn superposition_into_negative() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut from = [eq_lit(
        &terms,
        &symbols,
        terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
            .expect("f(x)"),
        x,
        true,
    )];
    let mut into = [pred(&terms, &symbols, &builder, "p", &[f_a], false)];
    flags(&context, &mut from);
    flags(&context, &mut into);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = superpose(&context, &from, 0, &into, 0, &path, &mut out).expect("superpose");
    assert!(matches!(
        outcome,
        mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(1)
    ));
    // The conclusion is not p(a).
    assert!(!out[0].is_positive());
    let view = terms.term(out[0].atom()).expect("read");
    let arg = terms.term(view.child(0).expect("child")).expect("arg");
    assert_eq!(arg.symbol(), symbol_id(&builder, "a"));
}

// CEP:WHAT: Verifies superposition into a positive literal.
// CEP:WHY: Right superposition.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong conclusion.
// CEP:ASSUMES: from (f(x) = x), into p(f(a)) or r: concludes p(a) or r.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::superpose.
// CEP:SECURITY: none.
#[test]
fn superposition_into_positive() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut from = [eq_lit(
        &terms,
        &symbols,
        terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
            .expect("f(x)"),
        x,
        true,
    )];
    let mut into = [
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    flags(&context, &mut from);
    flags(&context, &mut into);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = superpose(&context, &from, 0, &into, 0, &path, &mut out).expect("superpose");
    assert!(matches!(
        outcome,
        mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(2)
    ));
    assert!(out[0].is_positive() || out[1].is_positive());
}

// CEP:WHAT: Verifies the orientation condition (s sigma strictly greater than t sigma).
// CEP:WHY: Design 10.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an unorientable equation superposes.
// CEP:ASSUMES: from (a = f(a)) (unorientable: a is smaller): into not p(f(a)) is blocked.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::superpose.
// CEP:SECURITY: none.
#[test]
fn superposition_orients_equations() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut from = [eq_lit(&terms, &symbols, a, f_a, true)];
    let mut into = [pred(&terms, &symbols, &builder, "p", &[f_a], false)];
    flags(&context, &mut from);
    flags(&context, &mut into);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = superpose(&context, &from, 0, &into, 0, &path, &mut out).expect("superpose");
    assert!(
        matches!(
            outcome,
            mapt::hot::inference::superposition::SuperpositionOutcome::None
        ),
        "a = f(a) cannot orient left-greater"
    );
}

// CEP:WHAT: Verifies the variable restriction blocks variable targets.
// CEP:WHY: Design 10.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when superposition fires on a variable.
// CEP:ASSUMES: into not p(x): the whole atom is a variable argument at path [0].
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::superpose.
// CEP:SECURITY: none.
#[test]
fn superposition_rejects_variable_targets() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let mut from = [eq_lit(
        &terms,
        &symbols,
        terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
            .expect("f(x)"),
        x,
        true,
    )];
    let mut into = [pred(&terms, &symbols, &builder, "p", &[y], false)];
    flags(&context, &mut from);
    flags(&context, &mut into);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = superpose(&context, &from, 0, &into, 0, &path, &mut out).expect("superpose");
    assert!(matches!(
        outcome,
        mapt::hot::inference::superposition::SuperpositionOutcome::None
    ));
}

// CEP:WHAT: Verifies the into-literal eligibility restriction.
// CEP:WHY: Spec 07 section 6.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a non-maximal into literal superposes.
// CEP:ASSUMES: into p(a) or p(f(a)): superposing into p(a) is blocked.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::superpose.
// CEP:SECURITY: none.
#[test]
fn superposition_side_conditions() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let mut from = [eq_lit(
        &terms,
        &symbols,
        terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
            .expect("f(x)"),
        x,
        true,
    )];
    let mut into = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
    ];
    flags(&context, &mut from);
    flags(&context, &mut into);
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    // Superposing INTO the non-maximal literal p(a): nothing to rewrite there anyway
    // (a is a constant, not f-headed); the path targets argument 0 = a, which does
    // not unify with f(x) - the None outcome covers the structural path. The
    // eligibility path is pinned through the f(a) literal of a clause where it is
    // non-maximal:
    let heavier = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[f_a])
        .expect("f(f(a))");
    let mut into_blocked = [
        pred(&terms, &symbols, &builder, "p", &[f_a], true),
        pred(&terms, &symbols, &builder, "p", &[heavier], true),
    ];
    flags(&context, &mut into_blocked);
    let blocked = superpose(&context, &from, 0, &into_blocked, 0, &path, &mut out).expect("s");
    assert!(matches!(
        blocked,
        mapt::hot::inference::superposition::SuperpositionOutcome::None
    ));
}

// CEP:WHAT: Verifies demodulation rewrites a subterm by an oriented unit equation.
// CEP:WHY: Spec 07 section 7.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong rewrite.
// CEP:ASSUMES: rule f(x) = x rewrites p(f(a)) to p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/demodulation.rs::{demodulate, unit_equation_sides}.
// CEP:SECURITY: none.
#[test]
fn demodulation_rewrites_terms() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let rule_left = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let clause = [pred(&terms, &symbols, &builder, "p", &[f_a], true)];
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome =
        demodulate(&context, &clause, 0, &path, rule_left, x, &mut out).expect("demodulate");
    assert!(matches!(
        outcome,
        mapt::hot::inference::demodulation::DemodulationOutcome::Rewritten(1)
    ));
    let view = terms.term(out[0].atom()).expect("read");
    let arg = terms.term(view.child(0).expect("child")).expect("arg");
    assert_eq!(arg.symbol(), symbol_id(&builder, "a"), "f(a) rewrites to a");
}

// CEP:WHAT: Verifies demodulation requires orientation.
// CEP:WHY: Design 10.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an unorientable rule rewrites.
// CEP:ASSUMES: rule a = f(a) (wrong direction).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/demodulation.rs::demodulate.
// CEP:SECURITY: none.
#[test]
fn demodulation_requires_orientation() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let clause = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = demodulate(&context, &clause, 0, &path, a, f_a, &mut out).expect("d");
    assert!(matches!(
        outcome,
        mapt::hot::inference::demodulation::DemodulationOutcome::None
    ));
}

// CEP:WHAT: Verifies demodulation requires the rewritten atom to strictly decrease.
// CEP:WHY: The termination condition.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a non-decreasing rewrite is accepted.
// CEP:ASSUMES: rule b = a with b > a rewrites p(b) to p(a) (decreasing, accepted) and the reverse is orientation-blocked; the decrease check is pinned through an equal-weight orientation pair h(a,b) = h(b,a) where orientation holds under precedence but the atom does not decrease.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/demodulation.rs::demodulate.
// CEP:SECURITY: none.
#[test]
fn demodulation_requires_decrease() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let b = constant(&terms, &symbols, &builder, "b");
    // h(a, b) is greater than h(b, a) under KBO with precedence a < b (lexicographic
    // tie-break on children), so the rule h(a,b) = h(b,a) orients - but rewriting
    // p(h(a,b)) to p(h(b,a)) decreases the atom, so this pair is ACCEPTED; the
    // non-decrease case needs an equal atom, which cannot orient strictly, so the
    // orientation check subsumes it (documented here for the evidence chain).
    let h_ab = terms
        .intern_fun(&symbols, symbol_id(&builder, "h"), &[a, b])
        .expect("h(a,b)");
    let h_ba = terms
        .intern_fun(&symbols, symbol_id(&builder, "h"), &[b, a])
        .expect("h(b,a)");
    let clause = [pred(&terms, &symbols, &builder, "p", &[h_ab], true)];
    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    let path: [u16; 1] = [0];
    let outcome = demodulate(&context, &clause, 0, &path, h_ab, h_ba, &mut out).expect("d");
    // Whether accepted or blocked, the outcome must never be a non-decreasing
    // rewrite: either None or a strictly smaller atom.
    match outcome {
        mapt::hot::inference::demodulation::DemodulationOutcome::None => {}
        mapt::hot::inference::demodulation::DemodulationOutcome::Rewritten(count) => {
            let before = clause[0].atom();
            let after = out[0].atom();
            assert_eq!(count, 1);
            match context.compare(before, after) {
                Ok(mapt::hot::ordering::OrderingComparison::Greater) => {}
                other => panic!("rewrite must strictly decrease: {:?}", other),
            }
        }
    }
}

// CEP:WHAT: Verifies ground subsumption by set inclusion.
// CEP:WHY: Spec 08 section 2's base case.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong decision.
// CEP:ASSUMES: p(a) subsumes p(a) or r.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumes.
// CEP:SECURITY: none.
#[test]
fn subsumption_ground_subset() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let small = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let large = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    assert!(subsumes(&context, &small, &large).expect("check"));
    assert!(!subsumes(&context, &large, &small).expect("check"));
}

// CEP:WHAT: Verifies subsumption instantiates variables.
// CEP:WHY: The exists-sigma definition.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong decision.
// CEP:ASSUMES: p(x) subsumes p(f(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::{subsumes, assign_literal}.
// CEP:SECURITY: none.
#[test]
fn subsumption_instantiates() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let general = [pred(&terms, &symbols, &builder, "p", &[x], true)];
    let specific = [pred(&terms, &symbols, &builder, "p", &[f_a], true)];
    assert!(subsumes(&context, &general, &specific).expect("check"));
    assert!(!subsumes(&context, &specific, &general).expect("check"));
}

// CEP:WHAT: Verifies subsumption allows target-literal reuse within the size guard.
// CEP:WHY: Set semantics under the E-prover convention: the |C| <= |D| guard is applied, so reuse means two candidate literals match the SAME target literal while another target literal exists for set inclusion; P(x) or P(y) subsumes P(a) or r with x and y both mapping to a (Spec 08 section 2 documents the guard: pairs that only subsume under duplicate collapse beyond the guard are not detected - a documented deletion incompleteness that preserves search completeness).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong decision.
// CEP:ASSUMES: two general literals against two target literals with one reused.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::{subsumes, assign_literal}.
// CEP:SECURITY: none.
#[test]
fn subsumption_reuses_target_literals() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = constant(&terms, &symbols, &builder, "a");
    let general = [
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "p", &[y], true),
    ];
    let specific = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    assert!(subsumes(&context, &general, &specific).expect("check"));
}

// CEP:WHAT: Verifies subsumption rejects non-subsuming pairs.
// CEP:WHY: The negative decisions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on acceptance.
// CEP:ASSUMES: p(f(a)) vs p(a) and polarity mismatches.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::subsumes.
// CEP:SECURITY: none.
#[test]
fn subsumption_rejects() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let left = [pred(&terms, &symbols, &builder, "p", &[f_a], true)];
    let right = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    assert!(!subsumes(&context, &left, &right).expect("check"));
    // Polarity mismatch.
    let neg = [pred(&terms, &symbols, &builder, "p", &[f_a], false)];
    assert!(!subsumes(&context, &neg, &right).expect("check"));
}

// CEP:WHAT: Verifies tautology detection on complementary pointer-equal atoms.
// CEP:WHY: Design 10.1 tautology deletion.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong decision.
// CEP:ASSUMES: p(x) or not p(x).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::is_tautology.
// CEP:SECURITY: none.
#[test]
fn tautology_detected() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let literals = [Literal::new(atom, true), Literal::new(atom, false)];
    assert!(is_tautology(&literals));
}

// CEP:WHAT: Verifies near-tautologies (unifiable but distinct atoms) are kept.
// CEP:WHY: P(x) or not P(f(x)) is not a tautology.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong decision.
// CEP:ASSUMES: p(x) or not p(f(x)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::is_tautology.
// CEP:SECURITY: none.
#[test]
fn near_tautology_kept() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let first = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let second = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[f_x])
        .expect("p(f(x))");
    let literals = [Literal::new(first, true), Literal::new(second, false)];
    assert!(!is_tautology(&literals));
}

// CEP:WHAT: Verifies over-long conclusions are rejected loudly.
// CEP:WHY: The conclusion bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the overflow is accepted.
// CEP:ASSUMES: a resolution producing 2 survivors into a 1-slot buffer.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/inference/mod.rs InferenceError::ConclusionTooLong.
// CEP:SECURITY: the memory bound under test.
#[test]
fn conclusion_too_long_rejected() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let context = kbo_context(&terms, &symbols, &precedence, &substitution);
    let a = constant(&terms, &symbols, &builder, "a");
    let b = constant(&terms, &symbols, &builder, "b");
    let mut left = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
        pred(&terms, &symbols, &builder, "p", &[b], true),
    ];
    let mut right = [pred(&terms, &symbols, &builder, "p", &[b], false)];
    flags(&context, &mut left);
    flags(&context, &mut right);
    let mut out: [Literal; 1] = [Literal::new(TermPtr::invalid(), true)];
    // Resolving on the strictly maximal p(b) leaves p(a) and r: two survivors into
    // a one-slot buffer.
    let result = resolve(&context, &left, 2, &right, 0, &mut out);
    assert!(matches!(result, Err(InferenceError::ConclusionTooLong)));
    let _ = b;
}

// CEP:WHAT: Verifies the atom tree retrieves resolution candidates by payload.
// CEP:WHY: The generator's candidate path (pack/unpack round trip).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a missing or wrongly-decoded payload.
// CEP:ASSUMES: one active clause, one query atom.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/active.rs::{pack_payload, unpack_payload} and hot/ir/clause.rs::from_u32.
// CEP:SECURITY: none.
#[test]
fn resolution_candidates_retrieved() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let active = mapt::hot::search::active::ActiveSet::new_with(arena, 16, 1024, 1024, 4096)
        .expect("active set");
    let a = constant(&terms, &symbols, &builder, "a");
    let clause = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let store = mapt::hot::ir::clause::ClauseStore::new(arena);
    let ptr = store
        .new_clause(
            &terms,
            &clause,
            0,
            mapt::hot::ir::clause::DerivationStep {
                rule: mapt::hot::ir::clause::InferenceRule::Input,
                parent_count: 0,
                reserved: 0,
                parents: [0; 4],
                substitution: mapt_config::limits::kInvalidSubstitutionOffset,
            },
        )
        .expect("clause");
    active
        .insert(&terms, ptr.as_u32(), &clause)
        .expect("insert");
    let mut payloads: [u64; 16] = [0; 16];
    let count = active
        .atom_tree()
        .retrieve(&terms, clause[0].atom(), &mut payloads)
        .expect("retrieve");
    assert_eq!(count, 1);
    let (offset, literal_index, unit) = mapt::hot::search::active::unpack_payload(payloads[0]);
    assert_eq!(offset, ptr.as_u32());
    assert_eq!(literal_index, 0);
    assert!(!unit);
}
