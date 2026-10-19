// CEP:FILE: hot/conjecture/mod.rs
// CEP:WHAT: Automated conjecture generation (revised build order Phase 4): the harvest orchestrator that collects the recent derived unit equations, enumerates bounded deterministic template candidates (symmetry, transitivity, constructor instantiation), and filters them through bounded mini refutations, importing proved lemmas with their complete subproofs into the main search.
// CEP:WHY: The SOTA "speculative lemma" speedup (Vampire's internal theory exploration, iProver's instance generation, the IsaCoSy/Hipster school) is made CEP&CC-legal here by construction: every candidate comes from a fixed syntactic template over hash-consed terms (no statistics, no learning - the zero-ML rule), every filter run is a bounded mini saturation over the production engine with named budgets (kConjectureRefuteInferences, the kConjecture* capacities), only candidates whose negation was actually refuted become lemmas (soundness by the Spec 16 section 6 reductio theorem), failed attempts leave the main space byte-identical (the fresh-mini-store isolation of Spec 16 section 5), and the whole feature is schedule-bounded (kConjectureHarvestInterval, kMaxConjectureHarvests) with the total speculative work asserted at compile time to stay within kMaxInferences (CEP&CC 23: the cost is named and measurable; 39.1: no unbounded resource); the proof-recording half of the feature is the ConjectureLemma reductio rule whose mechanical check the TSTP replay checker enforces (Spec 17 section 4), so every harvested lemma ships with an independently checkable proof.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: the harvest never fails the search: mini-run discards and aborts are counted outcomes (Law 4), and only MAIN-store structural errors (the lemma add) propagate as SearchError; never panics.
// CEP:ASSUMES: called by the saturate loop (options.conjecture set, under kMaxConjectureHarvests) or by the CEP-1 driver pre-search (harvest_with_types with the induction declaration); the main space's input range is the axiom set.
// CEP:COST: per harvest: one window scan (bounded), one enumeration (bounded), and at most kMaxConjectureCandidates filter runs at kConjectureRefuteInferences each; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs; property/conjecture_property_test.rs::{only_proved_lemmas_added, harvest_deterministic_double_run, harvest_preserves_existing_clauses}; fuzz/conjecture_fuzz_test.rs; bench CEP-BENCH-0037.
// CEP:SECURITY: every stage is bounded by named constants; the arena pressure path aborts speculation instead of the search.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic: the window, the enumeration, and the filter are pure functions of the main space state (fixed orders, fixed budgets, the saturate loop's own determinism); property/conjecture_property_test.rs::harvest_deterministic_double_run pins the two-run discipline.
// CEP:HPC-PASS-LEGALITY: Formal Spec 16 (16_conjecture_generation.md) fixes the templates, the enumeration order, the mini-run contract, the isolation theorem, the reductio import, and the budget arithmetic; the property tests verify the no-unproven-lemma invariant and the subsumption-free preservation of existing clauses executably.

pub mod filter;
pub mod template;

use crate::induction::InductionDeclaration;
use crate::inference::InferenceContext;
use crate::search::given_clause::{SearchOptions, SearchSpace, SearchStats};
use crate::search::SearchError;
use filter::CandidateOutcome;

// CEP:WHAT: One in-loop harvest: T1/T2 templates over the recent derived units.
// CEP:WHY: The saturate loop's hook (options.conjecture, every kConjectureHarvestInterval iterations, under kMaxConjectureHarvests): the loop calls this entry because it holds no datatype declaration; the driver's pre-search pass calls harvest_with_types for the T3 constructor templates.
// CEP:STATUS: complete
// CEP:FAILURE: as harvest_with_types.
// CEP:ASSUMES: as harvest_with_types.
// CEP:COST: as harvest_with_types (T3 skipped).
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{harvest_schedule_fires, symmetry_candidates}.
// CEP:SECURITY: as harvest_with_types.
pub fn harvest(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    stats: &mut SearchStats,
) -> Result<(), SearchError> {
    harvest_with_types(space, context, options, None, stats)
}

// CEP:WHAT: One harvest pass with the optional datatype declaration enabling the T3 constructor templates.
// CEP:WHY: The orchestrator (Spec 16 section 5): count the harvest, collect the window, enumerate candidates (T1/T2 always, T3 when the declaration is given), then for each candidate run the bounded filter - Imported lemmas and Discarded candidates are counted, the first Aborted (arena pressure) stops the pass so speculation never kills the search; the stats are the Law 4 accounting the loop reports at every terminal.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError only from MAIN-store operations; discards and aborts are counted, never silent.
// CEP:ASSUMES: the space, context, and options belong to one search; stats is the search's stats.
// CEP:COST: see file header; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{harvest_schedule_fires, harvest_budget_enforced, candidate_budget_enforced, refuted_candidate_imports_proof}; property/conjecture_property_test.rs::{only_proved_lemmas_added, harvest_deterministic_double_run}.
// CEP:SECURITY: bounded stages; arena-pressure abort.
pub fn harvest_with_types(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    declaration: Option<&InductionDeclaration>,
    stats: &mut SearchStats,
) -> Result<(), SearchError> {
    stats.harvests += 1;
    let window = template::collect_recent_units(space, context);
    let candidates = template::enumerate_candidates(space, context, &window, declaration);
    for index in 0..candidates.count {
        stats.candidates += 1;
        match filter::refute_and_maybe_import(
            space,
            context,
            options,
            candidates.literals[index],
            &filter::MiniCapacities::production(),
        )? {
            CandidateOutcome::Imported => {
                stats.lemmas += 1;
            }
            CandidateOutcome::Discarded => {}
            CandidateOutcome::Aborted => break,
        }
    }
    Ok(())
}
