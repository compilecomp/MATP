// CEP:FILE: tests/unit/hot/given_clause_test.rs
// CEP:WHAT: Unit and loop-level tests for the given-clause saturation: refutation and saturation outcomes, each rule firing through the loop, simplification (tautology, demodulation, forward and backward subsumption), the budgets (time, inference, memory), per-clause bounds, deferral resumption, retrieval overflow accounting, and determinism.
// CEP:WHY: Design 15.1/10.3/20 and Spec 08 section 7: the loop is the Phase 3 deliverable; every outcome path and bound is pinned here on hand-traced problems before the property tests verify agreement with the SAT solver and brute force.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; small injected capacities; a self-resolving clause family drives the unbounded-budget tests.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/search/given_clause.rs and hot/search/generate.rs.
// CEP:SECURITY: every budget is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::search::given_clause::{
    saturate, GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

#[allow(dead_code)]
// CEP:WHAT: The fixture bundle with the precedence kept for context construction.
// CEP:WHY: The loop tests need the full inference context.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
type Fixture = (
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    mapt::hot::ir::term::TermStore<'static>,
    mapt::hot::ordering::precedence::PrecedenceTable<'static>,
);

// CEP:WHAT: Builds a fixture and a small search space with the given passive capacity.
// CEP:WHY: One constructor for this file; small caps keep every test fast.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena with room for the term table plus the small caps.
// CEP:COST: one space.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_space(
    passive_capacity: u32,
) -> (
    SearchSpace<'static>,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    mapt::hot::ir::term::TermStore<'static>,
    mapt::hot::ordering::precedence::PrecedenceTable<'static>,
) {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &options, passive_capacity, 4096, 8192, 8192, 65536)
        .expect("space");
    (space, symbols, builder, terms, precedence)
}

// CEP:WHAT: Builds the inference context over a space's shared substitution.
// CEP:WHY: The context borrows the space, so tests construct it after the space exists (the loop entry point takes both).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the pieces come from one fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn context_of<'a>(
    space: &'a SearchSpace<'static>,
    symbols: &'a mapt::hot::ir::symbol_table::SymbolTable<'static>,
    terms: &'a mapt::hot::ir::term::TermStore<'static>,
    precedence: &'a mapt::hot::ordering::precedence::PrecedenceTable<'static>,
) -> InferenceContext<'a> {
    InferenceContext {
        terms,
        symbols,
        substitution: &space.substitution,
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

// CEP:WHAT: The never-stop callback.
// CEP:WHY: Budget-free runs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn never_stop(_iterations: u64) -> bool {
    false
}

// CEP:WHAT: Verifies an empty input clause refutes immediately.
// CEP:WHY: Design 15.1 step 7's base case.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: one empty input clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{saturate, add_input_clause}.
// CEP:SECURITY: none.
#[test]
fn refutes_contradiction() {
    let (space, _symbols, _builder, _terms, _precedence) = make_space(16);
    let context = context_of(&space, &_symbols, &_terms, &_precedence);
    space
        .add_input_clause(&context, &SearchOptions::new(), &[])
        .expect("empty");
    let mut stats = SearchStats::default();
    let outcome = saturate(
        &space,
        &context,
        &SearchOptions::new(),
        &never_stop,
        &mut stats,
    )
    .expect("saturate");
    assert!(matches!(outcome, SearchOutcome::Theorem { .. }));
}

// CEP:WHAT: Verifies a satisfiable input saturates.
// CEP:WHY: Design 15.1 step 8.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: p(a) and p(b) with no complementary pair.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate.
// CEP:SECURITY: none.
#[test]
fn saturates_on_satisfiable() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[a], true)],
        )
        .expect("c1");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[b], true)],
        )
        .expect("c2");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(matches!(outcome, SearchOutcome::Saturated), "{:?}", outcome);
}

// CEP:WHAT: Verifies resolution fires through the loop and refutes.
// CEP:WHY: The core rule path end to end.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: p(a) and not p(a): the resolvent is the empty clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::{generate_step, step_resolution} and hot/search/given_clause.rs::drain_buffer.
// CEP:SECURITY: none.
#[test]
fn resolution_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[a], true)],
        )
        .expect("c1");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[a], false)],
        )
        .expect("c2");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        matches!(outcome, SearchOutcome::Theorem { .. }),
        "{:?} stats {:?}",
        outcome,
        stats
    );
    assert!(stats.inferences >= 1);
}

// CEP:WHAT: Verifies factoring fires through the loop.
// CEP:WHY: The intra-clause rule path.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no factoring conclusion is derived.
// CEP:ASSUMES: p(f(y)) or p(x).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::step_factoring.
// CEP:SECURITY: none.
#[test]
fn factoring_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let f_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[y])
        .expect("f(y)");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[f_y], true),
                pred(&terms, &symbols, &builder, "p", &[x], true),
            ],
        )
        .expect("c1");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(matches!(outcome, SearchOutcome::Saturated), "{:?}", outcome);
    assert!(stats.inferences >= 1, "factoring must fire: {:?}", stats);
}

// CEP:WHAT: Verifies the equality rules fire through the loop.
// CEP:WHY: Equality resolution and factoring paths.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the reflexive disequation does not refute.
// CEP:ASSUMES: not (a = a) alone: equality resolution derives the empty clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::step_equality_rules.
// CEP:SECURITY: none.
#[test]
fn equality_rules_fire() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let atom = terms.intern_eq(&symbols, a, a).expect("eq");
    let options = SearchOptions::new();
    space
        .add_input_clause(&context, &options, &[Literal::new(atom, false)])
        .expect("c1");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        matches!(outcome, SearchOutcome::Theorem { .. }),
        "{:?}",
        outcome
    );
}

// CEP:WHAT: Verifies superposition into the given clause fires (non-unit equation, so demodulation stays out of the way).
// CEP:WHY: The indexed into-direction path.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no superposition conclusion is derived.
// CEP:ASSUMES: active (f(x) = x or r), given not p(f(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::step_superposition_into.
// CEP:SECURITY: none.
#[test]
fn superposition_into_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let eq_atom = terms.intern_eq(&symbols, f_x, x).expect("eq");
    let options = SearchOptions::new();
    // The equation clause is an input first (age 0) so it is active when the target
    // is given.
    space
        .add_input_clause(
            &context,
            &options,
            &[
                Literal::new(eq_atom, true),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("eq clause");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[f_a], false)],
        )
        .expect("target");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        stats.inferences >= 1,
        "superposition into must fire: {:?} outcome {:?}",
        stats,
        outcome
    );
}

// CEP:WHAT: Verifies superposition from the given clause fires (the active scan).
// CEP:WHY: The unindexed from-direction path (ticket CEP-1027's residual scan).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no from-direction conclusion is derived.
// CEP:ASSUMES: active not p(f(a)), given (f(x) = x or r).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::step_superposition_from.
// CEP:SECURITY: none.
#[test]
fn superposition_from_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let eq_atom = terms.intern_eq(&symbols, f_x, x).expect("eq");
    let options = SearchOptions::new();
    // The target is an input first so it is active when the equation is given.
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[f_a], false)],
        )
        .expect("target");
    space
        .add_input_clause(
            &context,
            &options,
            &[
                Literal::new(eq_atom, true),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("eq clause");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        stats.inferences >= 1,
        "superposition from must fire: {:?} outcome {:?}",
        stats,
        outcome
    );
}

// CEP:WHAT: Verifies demodulation rewrites a given clause before activation.
// CEP:WHY: Design 10.3 step 1's demodulation half.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no rewrite is recorded.
// CEP:ASSUMES: active unit f(x) = x, given p(f(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{simplify_given, saturate}.
// CEP:SECURITY: none.
#[test]
fn demodulation_simplifies() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let eq_atom = terms.intern_eq(&symbols, f_x, x).expect("eq");
    let options = SearchOptions::new();
    // The unit equation is input first (age 0, priority 0): it activates before the
    // target is given.
    space
        .add_input_clause(&context, &options, &[Literal::new(eq_atom, true)])
        .expect("unit rule");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[f_a], true)],
        )
        .expect("target");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        stats.demodulations >= 1,
        "demodulation must rewrite p(f(a)): {:?} outcome {:?}",
        stats,
        outcome
    );
}

// CEP:WHAT: Verifies tautologies are discarded.
// CEP:WHY: Design 10.1 tautology deletion in the loop.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a tautology activates.
// CEP:ASSUMES: input p(a) or not p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{simplify_given, drain_buffer}.
// CEP:SECURITY: none.
#[test]
fn tautologies_discarded() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[a])
        .expect("p(a)");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[Literal::new(atom, true), Literal::new(atom, false)],
        )
        .expect("tautology");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(matches!(outcome, SearchOutcome::Saturated));
    assert!(stats.tautologies >= 1);
    assert_eq!(space.active.len(), 0, "the tautology never activates");
}

// CEP:WHAT: Verifies forward subsumption discards the given clause.
// CEP:WHY: Design 10.3 step 2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the subsumed clause activates.
// CEP:ASSUMES: active p(a) (input first), given p(a) or r.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::forward_subsumed.
// CEP:SECURITY: none.
#[test]
fn forward_subsumption_discards() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let options = SearchOptions::new();
    let unit = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    // Input the subsumer first; its weight (2) is below the target's (3), so it is
    // given first and active when the target is processed.
    space
        .add_input_clause(&context, &options, &unit)
        .expect("subsumer");
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[a], true),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("target");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(matches!(outcome, SearchOutcome::Saturated));
    assert!(stats.forward_subsumed >= 1, "{:?}", stats);
    assert_eq!(space.active.len(), 1, "only the subsumer activates");
}

// CEP:WHAT: Verifies backward subsumption removes the active clause.
// CEP:WHY: Design 10.1 backward subsumption in the loop.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the subsumed clause stays active.
// CEP:ASSUMES: active p(a) or r (heavier, input first... ordering: the general clause must be given while the specific is active; the general p(x) has weight 2, the specific p(a) or r has weight 3, so the general is given first - use ages instead: input the specific first (age 0), the general second: priorities: specific 0*scale/3 = 0, general 1*scale/2 = 32768: the specific pops first, activates; then the general pops and subsumes it.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::backward_subsume.
// CEP:SECURITY: none.
#[test]
fn backward_subsumption_removes() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[a], true),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("specific (age 0)");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[x], true)],
        )
        .expect("general (age 1)");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(matches!(outcome, SearchOutcome::Saturated));
    assert!(stats.backward_subsumed >= 1, "{:?}", stats);
}

// CEP:WHAT: Adds the unbounded chain inputs: not p(x) or p(f(x)), not p(x) or p(g(x)), and p(a), with first-negative selection.
// CEP:WHY: Under the selection function the chain's negative literal is eligible and every positive unit p(t) resolves with both equations, generating two fresh units p(f(t)) and p(g(t)) per given clause - an infinite, subsumption-free family that drives the budget tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: three input clauses.
// CEP:EVIDENCE: used by this file's budget and determinism tests.
// CEP:SECURITY: none.
fn add_chain_inputs(
    space: &SearchSpace<'static>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    terms: &mapt::hot::ir::term::TermStore<'static>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
) {
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(symbols, symbol_id(builder, "a"), &[])
        .expect("a");
    let f_x = terms
        .intern_fun(symbols, symbol_id(builder, "f"), &[x])
        .expect("f(x)");
    let g_x = terms
        .intern_fun(symbols, symbol_id(builder, "g"), &[x])
        .expect("g(x)");
    space
        .add_input_clause(
            context,
            options,
            &[
                pred(terms, symbols, builder, "p", &[x], false),
                pred(terms, symbols, builder, "p", &[f_x], true),
            ],
        )
        .expect("chain f");
    space
        .add_input_clause(
            context,
            options,
            &[
                pred(terms, symbols, builder, "p", &[x], false),
                pred(terms, symbols, builder, "p", &[g_x], true),
            ],
        )
        .expect("chain g");
    space
        .add_input_clause(
            context,
            options,
            &[pred(terms, symbols, builder, "p", &[a], true)],
        )
        .expect("root");
}

// CEP:WHAT: First-negative selection options for the chain tests.
// CEP:WHY: The chain's negative literals must be eligible.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file's budget and determinism tests.
// CEP:SECURITY: none.
fn chain_options() -> SearchOptions {
    let mut options = SearchOptions::new();
    options.selection = mapt::hot::inference::SelectionFunction::FirstNegative;
    options
}

// CEP:WHAT: Builds the ground atom encoding an index in binary over f (1) and g (0) at a fixed depth.
// CEP:WHY: Distinct ground atoms without exceeding the term depth bound (the retrieval-overflow fixture needs more distinct atoms than the depth bound allows for a unary chain).
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: index < 2^depth.
// CEP:COST: O(depth) interns.
// CEP:EVIDENCE: used by retrieval_overflow_counts_drops.
// CEP:SECURITY: none.
fn binary_atom(
    index: u32,
    depth: u32,
    terms: &mapt::hot::ir::term::TermStore<'static>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
) -> TermPtr {
    let a = terms
        .intern_fun(symbols, symbol_id(builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(builder, "f");
    let g_id = symbol_id(builder, "g");
    let mut current = a;
    for position in (0..depth).rev() {
        let head = if (index >> position) & 1 == 1 {
            f_id
        } else {
            g_id
        };
        current = terms.intern_fun(symbols, head, &[current]).expect("wrap");
    }
    current
}

// CEP:WHAT: Verifies the injected time budget stops the search.
// CEP:WHY: CEP-1005: the callback checked every kBudgetCheckInterval iterations.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: a self-resolving clause that runs past 1024 iterations; the callback fires from iteration 1024 on.
// CEP:COST: bounded by the callback.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{saturate, GaveUpReason::TimeBudget} and config/limits.rs kBudgetCheckInterval.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn time_budget_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(8192);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let options = chain_options();
    add_chain_inputs(&space, &context, &options, &terms, &symbols, &builder);
    let mut stats = SearchStats::default();
    let stop_at = |iterations: u64| iterations >= mapt_config::limits::kBudgetCheckInterval;
    let outcome = saturate(&space, &context, &options, &stop_at, &mut stats).expect("s");
    assert!(
        matches!(outcome, SearchOutcome::GaveUp(GaveUpReason::TimeBudget)),
        "{:?}",
        outcome
    );
}

// CEP:WHAT: Verifies the inference budget stops the search.
// CEP:WHY: Design 20.1.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: budget 1 with a pair that derives one non-empty resolvent.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{saturate, GaveUpReason::InferenceBudget}.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn inference_budget_fires() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let x = terms.intern_var(0).expect("x");
    let mut options = SearchOptions::new();
    options.inference_budget = 1;
    // The general pair: p(x) or r with not p(a) or r derives r or r (one inference),
    // then the budget stops the loop before the next generation.
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[x], true),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("c1");
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[a], false),
                pred(&terms, &symbols, &builder, "r", &[], true),
            ],
        )
        .expect("c2");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        matches!(
            outcome,
            SearchOutcome::GaveUp(GaveUpReason::InferenceBudget)
        ),
        "{:?} stats {:?}",
        outcome,
        stats
    );
}

// CEP:WHAT: Verifies a passive-capacity overflow gives up loudly.
// CEP:WHY: Design 20.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: capacity 4 with the self-resolving chain.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{drain_buffer, GaveUpReason::MemoryBudget}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn passive_overflow_stops() {
    let (space, symbols, builder, terms, precedence) = make_space(4);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let options = chain_options();
    add_chain_inputs(&space, &context, &options, &terms, &symbols, &builder);
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    assert!(
        matches!(outcome, SearchOutcome::GaveUp(GaveUpReason::MemoryBudget)),
        "{:?} stats {:?}",
        outcome,
        stats
    );
}

// CEP:WHAT: Verifies the per-clause inference budget ends a given clause's generation with the remainder counted.
// CEP:WHY: Design 10.3's kMaxInferencesPerClause bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a pre-charged cursor generates more.
// CEP:ASSUMES: a cursor pre-charged to the cap: generate_step must return Complete immediately.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/generate.rs::{generate_step, GenerationCursor} and config/limits.rs kMaxInferencesPerClause.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn per_clause_bound_enforced() {
    let (space, symbols, builder, terms, precedence) = make_space(64);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let options = SearchOptions::new();
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[a], true)],
        )
        .expect("c1");
    space
        .add_input_clause(
            &context,
            &options,
            &[pred(&terms, &symbols, &builder, "p", &[a], false)],
        )
        .expect("c2");
    // Activate the first clause manually and pre-charge a cursor for the second.
    let first = space.passive.pop().expect("pop");
    let clause = space
        .store
        .clause(mapt::hot::ir::clause::ClausePtr::from_u32(first.offset))
        .expect("clause");
    let mut literals: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    for index in 0..clause.literal_count {
        literals[index as usize] = space.store.literal(clause, index).expect("lit");
    }
    space
        .active
        .insert(
            &terms,
            first.offset,
            &literals[..clause.literal_count as usize],
        )
        .expect("insert");
    let second = space.passive.pop().expect("pop");
    let second_clause = space
        .store
        .clause(mapt::hot::ir::clause::ClausePtr::from_u32(second.offset))
        .expect("clause");
    let mut second_literals: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
    for index in 0..second_clause.literal_count {
        second_literals[index as usize] = space.store.literal(second_clause, index).expect("lit");
    }
    let mut cursor = mapt::hot::search::GenerationCursor::new();
    cursor.inferences = mapt_config::limits::kMaxInferencesPerClause as u64;
    let mut buffer = mapt::hot::search::InferenceBuffer::new();
    let status = mapt::hot::search::generate::generate_step(
        &context,
        &space.store,
        &space.active,
        &second_literals[..second_clause.literal_count as usize],
        second.clause_id,
        &mut cursor,
        &mut buffer,
    )
    .expect("generate");
    assert!(matches!(
        status,
        mapt::hot::search::GenerationStatus::Complete
    ));
    assert_eq!(buffer.count, 0, "the budget must block all generation");
}

// CEP:WHAT: Verifies buffer-full generation defers and resumes.
// CEP:WHY: Design 10.3's deferral.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the deferred remainder is lost.
// CEP:ASSUMES: a given clause with more than kInferenceBufferClauses candidate pairs: the not p(x) or q clause against 70 active p(t) or r clauses.
// CEP:COST: bounded by the active size.
// CEP:EVIDENCE: cited by hot/search/generate.rs::{generate_step, append} and hot/search/given_clause.rs::saturate.
// CEP:SECURITY: none.
#[test]
fn inference_deferral_resumes() {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let mut options = SearchOptions::new();
    options.selection = mapt::hot::inference::SelectionFunction::FirstNegative;
    let space = SearchSpace::new_with(arena, &options, 512, 256, 4096, 8192, 65536).expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let x = terms.intern_var(0).expect("x");
    // 70 distinct ground atoms over p (binary-encoded at depth 7: 128 >= 70).
    let mut atoms: Vec<TermPtr> = Vec::new();
    for index in 0..70u32 {
        atoms.push(binary_atom(index, 7, &terms, &symbols, &builder));
    }
    // Input the p(t) or r clauses first (they become active as they are given),
    // then the general not p(x) or q clause whose 70 resolutions exceed the buffer.
    for atom in atoms.iter() {
        space
            .add_input_clause(
                &context,
                &options,
                &[
                    pred(&terms, &symbols, &builder, "p", &[*atom], true),
                    pred(&terms, &symbols, &builder, "r", &[], true),
                ],
            )
            .expect("active clause");
    }
    // The given clause's second literal is q(x), so the 70 resolvents q(t) or r are
    // pairwise distinct (no subsumption collapse) and all 70 must be derived.
    space
        .add_input_clause(
            &context,
            &options,
            &[
                pred(&terms, &symbols, &builder, "p", &[x], false),
                pred(&terms, &symbols, &builder, "q", &[x, x], true),
            ],
        )
        .expect("given clause");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("s");
    // All 70 resolutions must be derived despite the 64-slot buffer: deferral
    // resumed the remainder across iterations.
    assert!(
        stats.inferences >= 70,
        "deferral must resume the remainder: {:?} outcome {:?}",
        stats,
        outcome
    );
}

// CEP:WHAT: Verifies that candidate pairs the scan cannot admit (namespace overflow: vars(given) + vars(active) above kMaxInferenceVariables) are counted as drops.
// CEP:WHY: Law 4: bounded drops are counted, never silent; the scan-based generation's drop source is the standardize-apart bound (the earlier retrieval-buffer overflow died with the flat-tree retrieval, Spec 08 section 6); the drop is driven through generate_step directly so the factoring cascade of the wide clauses cannot fill the passive set first (the loop-level GaveUp path is covered by passive_overflow_stops).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the overflow is silent.
// CEP:ASSUMES: a 32-variable given clause against a 33-variable active clause: 65 > 64.
// CEP:COST: bounded by the factoring phase of one clause.
// CEP:EVIDENCE: cited by hot/search/generate.rs::{step_resolution, load_renamed_premise} and config/limits.rs kMaxInferenceVariables.
// CEP:SECURITY: the soundness bound under test.
#[test]
fn retrieval_overflow_counts_drops() {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &options, 512, 64, 2048, 4096, 65536).expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    // The active clause: 33 negative p-literals over distinct variables.
    let mut active_literals: Vec<Literal> = Vec::new();
    for index in 0..33u32 {
        let var = terms.intern_var(index).expect("var");
        active_literals.push(pred(&terms, &symbols, &builder, "p", &[var], false));
    }
    space
        .add_input_clause(&context, &options, &active_literals)
        .expect("active");
    // The given clause: 32 positive p-literals over distinct variables.
    let mut given_literals: Vec<Literal> = Vec::new();
    for index in 0..32u32 {
        let var = terms.intern_var(index).expect("var");
        given_literals.push(pred(&terms, &symbols, &builder, "p", &[var], true));
    }
    space
        .add_input_clause(&context, &options, &given_literals)
        .expect("given");
    // Activate the wide clause and drive the given clause's generation to
    // completion: the resolution scan hits the namespace bound and counts it.
    let entry = space.passive.pop().expect("pop");
    let clause = space
        .store
        .clause(mapt::hot::ir::clause::ClausePtr::from_u32(entry.offset))
        .expect("clause");
    let mut staged: [Literal; 512] = [Literal::new(TermPtr::invalid(), true); 512];
    for index in 0..clause.literal_count {
        staged[index as usize] = space.store.literal(clause, index).expect("lit");
    }
    space
        .active
        .insert(
            &terms,
            entry.offset,
            &staged[..clause.literal_count as usize],
        )
        .expect("insert");
    let given_entry = space.passive.pop().expect("given pop");
    let given_clause = space
        .store
        .clause(mapt::hot::ir::clause::ClausePtr::from_u32(
            given_entry.offset,
        ))
        .expect("clause");
    let mut given_staged: [Literal; 512] = [Literal::new(TermPtr::invalid(), true); 512];
    for index in 0..given_clause.literal_count {
        given_staged[index as usize] = space.store.literal(given_clause, index).expect("lit");
    }
    let mut cursor = mapt::hot::search::GenerationCursor::new();
    let mut buffer = mapt::hot::search::InferenceBuffer::new();
    let mut total_drops: u64 = 0;
    for _ in 0..64 {
        let status = mapt::hot::search::generate::generate_step(
            &context,
            &space.store,
            &space.active,
            &given_staged[..given_clause.literal_count as usize],
            given_entry.clause_id,
            &mut cursor,
            &mut buffer,
        )
        .expect("generate");
        total_drops += cursor.dropped;
        cursor.dropped = 0;
        if let mapt::hot::search::GenerationStatus::Complete = status {
            break;
        }
    }
    assert!(
        total_drops >= 1,
        "the namespace overflow must be counted as a drop: {}",
        total_drops
    );
}

// CEP:WHAT: Verifies the loop is deterministic for a fixed stop callback.
// CEP:WHY: CEP&CC 38.10 end to end.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when two identical runs disagree.
// CEP:ASSUMES: the self-resolving chain under a fixed iteration budget.
// CEP:COST: two bounded runs.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate and property/given_clause_property_test.rs::selection_is_deterministic.
// CEP:SECURITY: none.
#[test]
fn generation_is_deterministic() {
    let run = || {
        let (space, symbols, builder, terms, precedence) = make_space(4096);
        let context = context_of(&space, &symbols, &terms, &precedence);
        let x = terms.intern_var(0).expect("x");
        let f_x = terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
            .expect("f(x)");
        let options = SearchOptions::new();
        space
            .add_input_clause(
                &context,
                &options,
                &[
                    pred(&terms, &symbols, &builder, "p", &[x], false),
                    pred(&terms, &symbols, &builder, "p", &[f_x], true),
                ],
            )
            .expect("chain");
        let mut stats = SearchStats::default();
        let stop_at = |iterations: u64| iterations >= 3 * mapt_config::limits::kBudgetCheckInterval;
        let outcome = saturate(&space, &context, &options, &stop_at, &mut stats).expect("s");
        (outcome, stats)
    };
    let first = run();
    let second = run();
    assert_eq!(format!("{:?}", first.0), format!("{:?}", second.0));
    assert_eq!(first.1.given_processed, second.1.given_processed);
    assert_eq!(first.1.inferences, second.1.inferences);
    assert_eq!(first.1.dropped, second.1.dropped);
}
