// CEP:FILE: tests/bug_first_negative_selection.rs
// CEP:WHAT: Long-running regression for the engine crash reported as "superposition position-scan InvalidPointer from replace_at on Peano recursion self-superposition" (ticket CEP-1056); the file name preserves the reporter's debugging trail - the crash was first suspected to be a negative-literal selection bug (the run used SelectionFunction::FirstNegative), but selection was a red herring and small capacity caps had merely masked the trigger.
// CEP:WHY: Root cause (CEP-1056): a long-running saturation exhausts the term arena or hash table mid-inference; the capacity failures (TermError::ArenaFull / TermError::TableFull) are legal named bounds (design 7.1, config kTermHashTableCapacity x kTermHashTableLoadFactorPercent), but three inference-layer translation points collapsed every TermError into SubstitutionError::InvalidPointer - hot/inference/mod.rs From<TermError>, hot/inference/builder.rs term_error, and hot/inference/superposition.rs replace_at's explicit intern .map_err closures - so the generator's fatal arm (hot/search/generate.rs, the Err catch-all that only drops ConclusionTooLong / VariableBudgetExceeded / DepthExceeded / WeightExceeded) aborted the whole search with a corruption-flavored error; the same bug class was fixed once before for substitution.rs map_term_error (ticket CEP-1050's honest-error fix, pinned by unit/hot/substitution_test.rs::term_bound_errors_not_misclassified) but the parallel inference-layer mappings were left blind. Secondary defect at the same site: step_superposition_from's buffer-full deferral returned without advancing the position cursor (the resumed-scan contract in generate.rs - every other phase advances after completion), so the resumed call re-derived and re-appended the just-stored conclusion (duplicate emission, double budget count). Fix contract under test: (1) the capacity family surfaces honestly (Structural(ArenaFull), never InvalidPointer), (2) the saturation loop converts the capacity family to SearchOutcome::GaveUp(GaveUpReason::MemoryBudget) exactly as design 20.2 and the GaveUpReason::MemoryBudget documentation ("passive full, active full, arena exhausted, clause budget") promise, and (3) the from-scan advances past a stored conclusion before deferring.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any Err from saturate (the crash), on any outcome other than GaveUp(MemoryBudget), or when the search terminated without doing inference work; #[ignore]d because reaching the bound takes a long saturation run (the reporter's "once the search runs long enough").
// CEP:ASSUMES: the Peano recursion axiom set below is satisfiable and superposition-productive (the recursion equation orients under KBO with the fixture's id-order precedence, h declared after f); the chain pair grows the resolution family without bound so the shared arena (kAtpFixtureArenaBytes minus the term table and the space structures) exhausts deterministically - arithmetic, not chance; demodulation cannot collapse the family (kMaxSimplifyRounds bounds the rewrite chain per clause).
// CEP:COST: one saturate run bounded by the arena capacity; minutes-scale wall time, hence #[ignore].
// CEP:EVIDENCE: cited by hot/inference/mod.rs (From<TermError>), hot/inference/builder.rs (term_error), hot/inference/superposition.rs (replace_at), hot/search/generate.rs (step_superposition_from, the drop policy), hot/search/given_clause.rs (saturate capacity conversion); ticket docs/tickets.md CEP-1056.
// CEP:SECURITY: the memory bound under test is the denial-of-service boundary (CEP&CC 22.10, design 20.2).

#![allow(non_upper_case_globals)]

#[path = "common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::inference::{InferenceContext, OrderingKind, SelectionFunction};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::search::given_clause::{
    saturate, GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

// CEP:WHAT: The reporter's configuration: FirstNegative selection over a Peano recursion axiom set.
// CEP:WHY: The negative goal literal must be eligible as a superposition-into target (the negative-side eligibility of Spec 07 section 6), which FirstNegative guarantees; this is the configuration the crash was filed against.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: mirrors chain_options in unit/hot/given_clause_test.rs.
// CEP:SECURITY: none.
fn first_negative_options() -> SearchOptions {
    let mut options = SearchOptions::new();
    options.selection = SelectionFunction::FirstNegative;
    options
}

// CEP:WHAT: Builds one predicate literal over the fixture vocabulary.
// CEP:WHY: Readable fixture construction (the house pred helper, local to keep this target self-contained).
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

// CEP:WHAT: The regression body: Peano recursion self-superposition under FirstNegative until the memory bound.
// CEP:WHY: The clause set: h(f(X), Y) = f(h(X, Y)) (the recursion equation - add(s(X),Y) = s(add(X,Y)) over the fixture vocabulary s=f, add=h, with the base case omitted so the equation family keeps superposing), the self-resolving chain pair not-p(X) or p(f(X)) / not-p(X) or p(g(X)) (unbounded resolution growth - the same family the budget tests use), and not-p(h(X, Y)) (the Peano goal-shaped negative literal the recursion superposes into); nothing is refutable, so the only legal terminal is the memory bound.
// CEP:STATUS: complete
// CEP:FAILURE: asserts Ok(GaveUp(MemoryBudget)) with inferences > 0; fails on the crash (Err), on an early wrong terminal, or on a no-op run.
// CEP:ASSUMES: fresh 12 MiB fixture arena (kAtpFixtureArenaBytes): the 8 MiB term table plus the space structures leave a bounded record region that the growing families exhaust.
// CEP:COST: one saturate run; see the file header.
// CEP:EVIDENCE: this is the CEP-1056 regression; run explicitly with `cargo test --test bug_first_negative_selection -- --ignored`.
// CEP:SECURITY: exercises the arena exhaustion boundary end to end.
#[test]
#[ignore = "long-running: drives the search to the arena bound (CEP-1056)"]
fn peano_recursion_self_superposition_exhausts_memory_without_crashing() {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = first_negative_options();
    let space = SearchSpace::new_with(arena, &options, 65536, 4096, 8192, 8192, 65536, 4096)
        .expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let f_id = symbol_id(&builder, "f");
    let f_x = terms.intern_fun(&symbols, f_id, &[x]).expect("f(x)");
    let g_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "g"), &[x])
        .expect("g(x)");
    let h_x_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "h"), &[x, y])
        .expect("h(x, y)");
    let h_f_x_y = terms
        .intern_fun(&symbols, symbol_id(&builder, "h"), &[f_x, y])
        .expect("h(f(x), y)");
    let f_h_x_y = terms
        .intern_fun(&symbols, f_id, &[h_x_y])
        .expect("f(h(x, y))");
    // The recursion equation: h(f(X), Y) = f(h(X, Y)).
    let recursion = terms
        .intern_eq(&symbols, h_f_x_y, f_h_x_y)
        .expect("recursion");
    let recursion_literal = Literal::new(recursion, true);
    // The Peano goal-shaped negative literal: not p(h(X, Y)).
    let goal = pred(&terms, &symbols, &builder, "p", &[h_x_y], false);
    // The self-resolving chain pair (unbounded resolution growth).
    let chain_f = [
        pred(&terms, &symbols, &builder, "p", &[x], false),
        pred(&terms, &symbols, &builder, "p", &[f_x], true),
    ];
    let chain_g = [
        pred(&terms, &symbols, &builder, "p", &[x], false),
        pred(&terms, &symbols, &builder, "p", &[g_x], true),
    ];
    space
        .add_input_clause(&context, &options, &[recursion_literal])
        .expect("recursion input");
    space
        .add_input_clause(&context, &options, &[goal])
        .expect("goal input");
    space
        .add_input_clause(&context, &options, &chain_f)
        .expect("chain f input");
    space
        .add_input_clause(&context, &options, &chain_g)
        .expect("chain g input");
    let mut stats = SearchStats::default();
    // No wall-time stop: the bound is deterministic arithmetic (the arena
    // capacity), so a stop callback would only mask a regression into a
    // different terminal. If the memory bound is ever replaced by a different
    // outcome, the assertion below fails loudly and the fixture gets re-tuned.
    let never_stop = |_iterations: u64| false;
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats);
    // The crash contract: saturate returns Ok, never
    // Err(SearchError::Inference(Structural(InvalidPointer))) - the pre-fix
    // engine aborted here with a corruption-flavored error the moment the
    // term arena or hash table exhausted inside replace_at.
    let outcome = outcome.expect("CEP-1056 regression: the search must not crash");
    assert!(
        matches!(outcome, SearchOutcome::GaveUp(GaveUpReason::MemoryBudget)),
        "expected GaveUp(MemoryBudget), got {:?} (stats {:?})",
        outcome,
        stats
    );
    assert!(
        stats.inferences > 0,
        "the search must do inference work before the bound (stats {:?})",
        stats
    );
}
