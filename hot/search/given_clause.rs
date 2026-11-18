// CEP:FILE: hot/search/given_clause.rs
// CEP:WHAT: The given-clause saturation loop (design 15.1) with the clause database (design 8.4), the selection weight function (design 15.3), the conjecture-distance weight (design 15.2 row 2, CEP-1035), the set-of-support selection restriction (design 15.2 row 5, CEP-1035), simplification (demodulation, subsumption resolution, condensation, forward subsumption, tautology deletion - design 10.3 step 1, CEP-1034), backward subsumption, bounded inference generation, the design 20 budgets (CEP-1005), and - since CEP-1036 - the simplification step chain: every rewrite (demodulation, subsumption resolution, condensation) records a restandardized, deduplicated snapshot with the simplifying rule clause's id, and the park point stores one clause record per step (parents [previous, rule]) so the certified kernel replays simplification exactly per step (Spec 19).
// CEP:WHY: Design 26 Phase 3 build order: the loop is the ATP search - select from the passive set, move to the active set, simplify against the active set, discard the redundant, generate all inferences between the given clause and the active set, add the conclusions to the passive set, and terminate with Theorem on the empty clause, Saturated on an empty passive set, or GaveUp on a budget; the loop step order is fixed (select, simplify, forward-subsume, backward-subsume, activate, generate) so the active array never mutates during one given clause's generation (the generator's slot scan stays consistent); fairness follows from the strategy's priority function (Spec 08 section 4), and the set-of-support restriction (CEP-1035) skips generation for non-supported clauses, which activates them as inference partners without ever selecting them as given (Spec 08 section 7's SOS contract); the time budget is an injected should_stop callback checked every kBudgetCheckInterval iterations, which keeps the hot crate clock-free (the CEP-1 driver supplies wall time; tests supply deterministic stop predicates - the mechanism is what CEP-1005 demands); CounterSatisfiable needs model building (design 17, Phase 5) and Saturated is the honest Phase 3 terminal for satisfiable inputs.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns Result<SearchOutcome, SearchError>: structural failures surface loudly; the capacity family (arena or term-table exhaustion from the rules, clause-store and active-set capacity) is converted by the saturate wrapper into GaveUp(MemoryBudget) per design 20.2 and the GaveUpReason::MemoryBudget documentation (CEP-1056) - a bound firing is a legal bounded outcome, never an Err; never panics.
// CEP:ASSUMES: One search space per arena; input clauses are added through add_input_clause (which computes flags and weights); the injected stop callback is pure w.r.t. its iteration counter (no hidden state).
// CEP:COST: per iteration: one passive pop O(log n), simplification (bounded demodulation rounds, FV-filtered subsumption), one active insertion, and generation steps (measured in bench CEP-BENCH-0010/0011); the loop is allocation-free after construction.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force, loop_refutes_pigeonhole}; fuzz/given_clause_fuzz_test.rs.
// CEP:SECURITY: every budget is enforced (inference count, clause budget, arena, capacities, injected time); the loop cannot run unbounded without the callback firing.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic for a fixed stop callback: selection, simplification, and generation are pure functions of the state; unit/hot/given_clause_test.rs::generation_is_deterministic and property/given_clause_property_test.rs::selection_is_deterministic verify the two-run discipline (identical conclusions and identical selection sequences on fresh double runs).
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 7 fixes the loop contract: the empty clause is derived only by sound inferences (Theorem is trustworthy), Saturated means every selected clause had all its budgeted inferences computed (fairness per the strategy's priority argument), and every GaveUp reason names its budget; the property tests verify the loop against the SAT solver and brute force on propositional problems.

use crate::index::feature_vector::FeatureError;
use crate::index::IndexError;
use crate::inference::demodulation::{demodulate, unit_equation_sides};
use crate::inference::selection::compute_selection_flags;
use crate::inference::subsumption::{
    condensation_target, is_tautology, subsumes, subsumption_resolves,
};
use crate::inference::{InferenceContext, InferenceError, SelectionFunction};
use crate::ir::clause::{
    kClauseFlagSos, ClauseError, ClausePtr, ClauseStore, DerivationStep, InferenceRule,
};
use crate::ir::literal::Literal;
use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::TermStore;
use crate::memory::arena::Arena;
use crate::search::active::{ActiveError, ActiveSet};
use crate::search::generate::{generate_step, GenerationCursor, InferenceBuffer};
use crate::search::passive::{PassiveError, PassiveHeap, SelectionStrategy};
use crate::search::SearchError;
use crate::unification::substitution::{Substitution, SubstitutionError};
use mapt_config::limits::{
    kBudgetCheckInterval, kConjectureDistanceSymbols, kConjectureHarvestInterval,
    kDefaultSymbolWeight, kInvalidClauseId, kInvalidSubstitutionOffset, kMaxClauseLiterals,
    kMaxConjectureHarvests, kMaxDerivationParents, kMaxInferences, kMaxSimplifyRounds,
    kSelectionVariableWeight, kSrHeadSymbols,
};

// CEP:WHAT: Parent counts of unary and binary inference rules (demodulation and factoring-style rules have one parent; resolution and superposition have two).
// CEP:WHY: The derivation label's parent count names its values (CEP&CC 11.3) instead of bare 1/2 literals at every construction site.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: parent_count is u8 in DerivationStep.
// CEP:COST: compile-time constants.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, demodulation_simplifies}.
// CEP:SECURITY: none.
const kUnaryRuleParents: u8 = 1;
const kBinaryRuleParents: u8 = 2;

// CEP:WHAT: Payload capacity of one demodulation rule-tree retrieval.
// CEP:WHY: The retrieval buffer is a fixed stack array (no allocation in the hot path); when more unit rules match a subterm than the buffer holds, the visible prefix is tried and the overflow is counted into stats.dropped (Law 4: bounded drops are never silent); the next simplify round retries on the rewritten clause.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the rule tree's payload count per query stays small in practice (unit equations with equal left sides).
// CEP:COST: 8 bytes per slot on the stack.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{retrieval_overflow_counts_drops, demodulation_simplifies}.
// CEP:SECURITY: the capacity bounds the retrieval work per subterm.
const kDemodulationPayloads: usize = 16;

/// CEP:WHAT: Why the search gave up.
/// CEP:WHY: CEP&CC Law 6 and design 20.2: a bounded stop reports its budget; the reasons map onto the design 2.2 ProverResult vocabulary (Timeout, InferenceLimit, MemoryExhausted).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{time_budget_fires, inference_budget_fires, passive_overflow_stops}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GaveUpReason {
    /// CEP:WHAT: The injected stop callback fired.
    /// CEP:WHY: CEP-1005: the time budget checked every kBudgetCheckInterval iterations.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the callback's semantics are the caller's contract.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::time_budget_fires.
    /// CEP:SECURITY: denial-of-service bound.
    TimeBudget,
    /// CEP:WHAT: The inference budget kMaxInferences is exhausted.
    /// CEP:WHY: Design 20.1.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_budget_fires.
    /// CEP:SECURITY: denial-of-service bound.
    InferenceBudget,
    /// CEP:WHAT: A capacity or storage budget ended the search (passive full, active full, arena exhausted, clause budget).
    /// CEP:WHY: Design 20.1/20.2.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the stats carry the state at the stop.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    /// CEP:SECURITY: memory bound.
    MemoryBudget,
    /// CEP:WHAT: The AVATAR abstraction exhausted its conflict-round budget (design 12.2 rule 4).
    /// CEP:WHY: Each conflict round adds one abstraction clause and requires a complete first-order refutation; the named budget bounds pathological oscillation loudly (Spec 12 section 5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only saturate_with_avatar returns this variant.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    AvatarConflictBudget,
    /// CEP:WHAT: The AVATAR model-rotation sweep exhausted its budget before testing every waiting component (design 12.2 rule 3).
    /// CEP:WHY: Rotations probe one waiting component per assumption solve; the budget bounds the sweep instead of claiming Saturated without evidence (Spec 12 section 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only saturate_with_avatar returns this variant.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    AvatarModelBudget,
}

/// CEP:WHAT: The terminal outcome of the saturation loop.
/// CEP:WHY: Design 15.1: the empty clause means Theorem (with the refuting clause's derivation chain reachable through the store), an exhausted passive set means Saturated, and every bounded stop means GaveUp with its reason; mapping onto the design 2.2 vocabulary is the caller's (CEP-1 driver's) job.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable, time_budget_fires, inference_budget_fires}; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchOutcome {
    /// CEP:WHAT: The empty clause was derived; the payload is its clause record offset.
    /// CEP:WHY: The refuting outcome; the derivation chain (design 5.4) is reachable through the store.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the clause record exists for the search's lifetime.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction; property/given_clause_property_test.rs::{loop_agrees_with_brute_force, loop_refutes_pigeonhole}.
    /// CEP:SECURITY: none.
    Theorem {
        /// CEP:WHAT: The empty clause's record offset.
        /// CEP:WHY: Proof extraction entry point.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: store-produced.
        /// CEP:COST: 4 bytes.
        /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
        /// CEP:SECURITY: bounds-checked reads.
        refutation: u32,
    },
    /// CEP:WHAT: The passive set emptied without deriving the empty clause.
    /// CEP:WHY: The saturated outcome (every processed clause had its inferences computed under the budget discipline).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::saturates_on_satisfiable; property/given_clause_property_test.rs::loop_agrees_with_sat_solver.
    /// CEP:SECURITY: none.
    Saturated,
    /// CEP:WHAT: A budget ended the search.
    /// CEP:WHY: The bounded outcome with its reason.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{time_budget_fires, inference_budget_fires, passive_overflow_stops}.
    /// CEP:SECURITY: none.
    GaveUp(GaveUpReason),
}

/// CEP:WHAT: The search's measurement record.
/// CEP:WHY: CEP&CC Law 4 and design 20.2: bounded search reports what it did; the counters feed diagnostics and the budget tests.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: counters only increase.
/// CEP:COST: 64 bytes.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{per_clause_bound_enforced, retrieval_overflow_counts_drops, demodulation_simplifies, forward_subsumption_discards, backward_subsumption_removes}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, Default)]
pub struct SearchStats {
    /// CEP:WHAT: Given clauses processed.
    /// CEP:WHY: Loop progress.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
    /// CEP:SECURITY: none.
    pub given_processed: u64,
    /// CEP:WHAT: Conclusions derived (buffered inferences).
    /// CEP:WHY: The inference budget counter.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_budget_fires.
    /// CEP:SECURITY: none.
    pub inferences: u64,
    /// CEP:WHAT: Candidates and conclusions dropped (retrieval overflow, namespace overflow, over-long conclusions, and the one-drop budget-tail marker of cap exhaustion).
    /// CEP:WHY: Bounded-search accounting (Law 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{retrieval_overflow_counts_drops, per_clause_bound_enforced}.
    /// CEP:SECURITY: none.
    pub dropped: u64,
    /// CEP:WHAT: Clauses discarded as tautologies.
    /// CEP:WHY: Simplification accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::tautologies_discarded.
    /// CEP:SECURITY: none.
    pub tautologies: u32,
    /// CEP:WHAT: Given clauses discarded by forward subsumption.
    /// CEP:WHY: Simplification accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::forward_subsumption_discards.
    /// CEP:SECURITY: none.
    pub forward_subsumed: u32,
    /// CEP:WHAT: Active clauses removed by backward subsumption.
    /// CEP:WHY: Simplification accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::backward_subsumption_removes.
    /// CEP:SECURITY: none.
    pub backward_subsumed: u32,
    /// CEP:WHAT: Demodulation rewrites applied to given clauses.
    /// CEP:WHY: Simplification accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_simplifies.
    /// CEP:SECURITY: none.
    pub demodulations: u32,
    /// CEP:WHAT: Condensation literal deletions applied to given clauses (CEP-1034).
    /// CEP:WHY: Simplification accounting (design 10.1 condensation row): each deletion is a self-subsumption resolution recorded in the simplification step chain.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::condensation_simplifies_given.
    /// CEP:SECURITY: none.
    pub condensations: u32,
    /// CEP:WHAT: Subsumption-resolution literal deletions applied to given clauses (CEP-1034).
    /// CEP:WHY: Simplification accounting (design 10.1 subsumption-resolution row): each deletion is an active clause's SR against the given clause, recorded in the simplification step chain.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::subsumption_resolution_simplifies_given.
    /// CEP:SECURITY: none.
    pub subsumption_resolutions: u32,
    /// CEP:WHAT: Conjecture harvests run (revised build order Phase 4, Spec 16).
    /// CEP:WHY: Speculative-work accounting (Law 4): every harvest increments, and the count never exceeds kMaxConjectureHarvests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only saturate increments when options.conjecture is set.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::harvest_schedule_fires.
    /// CEP:SECURITY: none.
    pub harvests: u32,
    /// CEP:WHAT: Conjecture candidates tried across all harvests.
    /// CEP:WHY: Speculative-work accounting: bounded by harvests x kMaxConjectureCandidates.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only saturate increments when options.conjecture is set.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
    /// CEP:SECURITY: none.
    pub candidates: u32,
    /// CEP:WHAT: Lemmas imported (candidates whose negation the mini refutation refuted).
    /// CEP:WHY: The harvest's success accounting: every imported lemma carries a complete reductio subproof in the derivation DAG (Spec 17).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only saturate increments when options.conjecture is set.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    /// CEP:SECURITY: none.
    pub lemmas: u32,
}

/// CEP:WHAT: The search configuration: strategy, ordering, selection function, and budgets.
/// CEP:WHY: CEP&CC 34.3: every budget injectable for the exhaustion tests; the defaults are the named constants (the inference budget defaults to kMaxInferences).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record.
/// CEP:ASSUMES: inference_budget >= 1.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{time_budget_fires, inference_budget_fires}.
/// CEP:SECURITY: the budgets are the denial-of-service bounds under test.
#[derive(Default)]
pub struct SearchOptions {
    /// CEP:WHAT: The passive-set selection strategy (design 15.2).
    /// CEP:WHY: Fixes the priority function.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed per search.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_age}.
    /// CEP:SECURITY: none.
    pub strategy: SelectionStrategy,
    /// CEP:WHAT: The term ordering for side conditions.
    /// CEP:WHY: KBO default, LPO alternative (design 8.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: matches the precedence table.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::superposition_orients_equations.
    /// CEP:SECURITY: none.
    pub ordering: crate::inference::OrderingKind,
    /// CEP:WHAT: The literal selection function.
    /// CEP:WHY: Design 10.1 literal selection.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed per search.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/selection_test.rs::{selection_overrides_maximality, first_negative_selects}.
    /// CEP:SECURITY: none.
    pub selection: SelectionFunction,
    /// CEP:WHAT: The total inference budget (production: kMaxInferences).
    /// CEP:WHY: Design 20.1.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: GaveUp(InferenceBudget) at the bound.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_budget_fires.
    /// CEP:SECURITY: denial-of-service bound.
    pub inference_budget: u64,
    /// CEP:WHAT: Whether the in-loop conjecture harvest is enabled (revised build order Phase 4, Spec 16).
    /// CEP:WHY: Harvesting is speculative work with a fixed schedule (every kConjectureHarvestInterval iterations, at most kMaxConjectureHarvests harvests); the flag is OFF by default so the Phase 1-3 search behavior is byte-identical unless the driver opts in, which keeps the determinism discipline (CEP&CC 38.10) and the existing golden tests stable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; a configuration flag.
    /// CEP:ASSUMES: harvest budgets are the named constants (not injectable through this record; the bounds tests exercise the harvest functions directly at small scales).
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{harvest_schedule_fires, harvest_budget_enforced}.
    /// CEP:SECURITY: the schedule and harvest count are the speculative-work bounds.
    pub conjecture: bool,
    /// CEP:WHAT: Whether the set-of-support selection restriction is enabled (design 15.2 row 5, CEP-1035).
    /// CEP:WHY: With the flag on, only conjecture descendants (clauses carrying the kClauseFlagSos mark: NegatedConjecture/ConjectureNegation seeds and their derivation descendants) become given clauses; non-supported clauses are simplified, subsumption-checked, and ACTIVATED (they serve as inference partners) but never selected, so every inference involves at least one supported clause - the classical set-of-support strategy (Wos, Robinson & Carson 1965). Completeness position (documented, Spec 08 section 7): refutationally complete when the non-supported clause set is satisfiable and the conjecture's negation is present in the input; the OFF default keeps every existing search byte-identical (CEP&CC 38.10).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; a configuration flag.
    /// CEP:ASSUMES: the driver marks conjecture inputs with the NegatedConjecture rule (or ConjectureNegation); with no marked clause the loop activates everything and saturates without generation (the honest empty-support behavior, unit-tested).
    /// CEP:COST: 1 byte plus one flag read per selected clause.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{sos_restriction_spares_nonsupport_clauses, sos_descendants_stay_selectable, sos_without_seeds_saturates}.
    /// CEP:SECURITY: none.
    pub set_of_support: bool,
}

impl SearchOptions {
    /// CEP:WHAT: Production defaults.
    /// CEP:WHY: One named place for the default configuration (CEP&CC 11.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}.
    /// CEP:SECURITY: none.
    pub fn new() -> SearchOptions {
        SearchOptions {
            strategy: SelectionStrategy::AgeWeightRatio,
            ordering: crate::inference::OrderingKind::Kbo,
            selection: SelectionFunction::None,
            inference_budget: kMaxInferences,
            conjecture: false,
            set_of_support: false,
        }
    }

    /// CEP:WHAT: Translates a config-layer strategy preset (design 21.1) into search options (CEP-1035).
    /// CEP:WHY: config/strategy.rs is the dependency-free constant layer; this is the single tag-to-enum translation point (CEP&CC 33.18) and the tag contract is pinned by unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums, so a one-sided enum or preset edit fails the pin test instead of silently reinterpreting a preset (CEP&CC Law 8); the inference budget is the production default (presets carry no budget fields by design - the driver injects budgets).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; every tag value maps (the pin test keeps the vocabularies identical).
    /// CEP:ASSUMES: the preset's tags are kStrategyTag*/kSelectionTag*/kOrderingTag* values.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
    /// CEP:SECURITY: none.
    pub fn from_preset(preset: &mapt_config::strategy::StrategyPreset) -> SearchOptions {
        let strategy = match preset.passive_strategy {
            mapt_config::strategy::kStrategyTagWeightOnly => SelectionStrategy::WeightOnly,
            mapt_config::strategy::kStrategyTagAgeOnly => SelectionStrategy::AgeOnly,
            mapt_config::strategy::kStrategyTagConjectureDistance => {
                SelectionStrategy::ConjectureDistance
            }
            // The default tag and every unknown value fall back to the design
            // default (the pin test keeps unknown values from occurring).
            _ => SelectionStrategy::AgeWeightRatio,
        };
        let selection = match preset.selection_function {
            mapt_config::strategy::kSelectionTagFirstNegative => SelectionFunction::FirstNegative,
            _ => SelectionFunction::None,
        };
        let ordering = match preset.ordering {
            mapt_config::strategy::kOrderingTagLpo => crate::inference::OrderingKind::Lpo,
            _ => crate::inference::OrderingKind::Kbo,
        };
        SearchOptions {
            strategy,
            ordering,
            selection,
            inference_budget: kMaxInferences,
            conjecture: preset.conjecture,
            set_of_support: preset.set_of_support,
        }
    }
}

/// CEP:WHAT: The selection weight function (design 15.3).
/// CEP:WHY: weight = sum over the clause's subterm nodes of the symbol weight (function and predicate symbols at their configured weight, default 1) with variables at kSelectionVariableWeight (0) - the design's "symbol_weight(s) x occurrence_count(s)" with the documented defaults; the weight is computed at clause creation for the passive-set key and is distinct from the cached clause weight (which counts variables at the KBO weight for ordering purposes) An unknown symbol id falls back to kDefaultSymbolWeight (a defensive default: the frozen table answers every interned symbol, so the fallback covers only forged ids and keeps the weight positive and deterministic).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: saturates at u32::MAX on overflow (weights bounded by kMaxTermWeight make this unreachable for legal clauses; the saturation is documented, not silent, via the store's WeightOverflow check at record level).
/// CEP:ASSUMES: atoms interned by the store; symbol weights are the frozen table's.
/// CEP:COST: O(total term nodes) per clause.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{selection_weight_counts_symbols, selection_weight_ignores_variables}.
/// CEP:SECURITY: depth-bounded recursion.
pub struct SelectionWeight;

impl SelectionWeight {
    /// CEP:WHAT: Computes the selection weight of one clause.
    /// CEP:WHY: Design 15.3 with the default weights.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturating add (see type header).
    /// CEP:ASSUMES: literals interned by the store.
    /// CEP:COST: O(total term nodes).
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{selection_weight_counts_symbols, selection_weight_ignores_variables}.
    /// CEP:SECURITY: depth-bounded.
    pub fn of(terms: &TermStore<'_>, symbols: &SymbolTable<'_>, literals: &[Literal]) -> u32 {
        let mut total: u64 = 0;
        for literal in literals.iter() {
            total += Self::of_term(terms, symbols, literal.atom(), 0) as u64;
        }
        if total > u32::MAX as u64 {
            u32::MAX
        } else {
            total as u32
        }
    }

    // CEP:WHAT: Recursive per-symbol weight sum of one term.
    // CEP:WHY: Variables contribute kSelectionVariableWeight (0 by default); function and predicate symbols contribute their configured weight; equality atoms contribute their arguments (the equality tag carries no symbol-table entry, design 5.1).
    // CEP:STATUS: complete
    // CEP:FAILURE: depth exhaustion returns the partial sum (unreachable for store-interned terms, which respect kMaxTermDepth).
    // CEP:ASSUMES: term interned.
    // CEP:COST: O(term nodes).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{selection_weight_counts_symbols, selection_weight_ignores_variables}.
    // CEP:SECURITY: depth-bounded.
    fn of_term(
        terms: &TermStore<'_>,
        symbols: &SymbolTable<'_>,
        term: crate::ir::term::TermPtr,
        depth: u32,
    ) -> u32 {
        if depth > mapt_config::limits::kMaxTermDepth as u32 {
            return 0;
        }
        let view = match terms.term(term) {
            Ok(value) => value,
            Err(_) => return 0,
        };
        match view.tag() {
            crate::ir::term::TermTag::Variable => kSelectionVariableWeight,
            crate::ir::term::TermTag::Equality => {
                let mut sum = 0u32;
                for child in view.children() {
                    sum = sum.saturating_add(Self::of_term(terms, symbols, child, depth + 1));
                }
                sum
            }
            _ => {
                let symbol_weight = symbols
                    .symbol_weight(view.symbol())
                    .unwrap_or(kDefaultSymbolWeight);
                let mut sum = symbol_weight;
                for child in view.children() {
                    sum = sum.saturating_add(Self::of_term(terms, symbols, child, depth + 1));
                }
                sum
            }
        }
    }

    /// CEP:WHAT: Computes the conjecture distance of one clause (design 15.2 row 2, CEP-1035): the summed symbol weight of the clause's DISTINCT symbols that do not occur in the frozen conjecture symbol set.
    /// CEP:WHY: The conjecture-distance strategy pops clauses closest to the conjecture's vocabulary first; the distance is fixed at birth (computed once at push against the same frozen set) so the heap order stays a pure function of the push sequence (CEP&CC 38.10); a None set (never provided) makes every distance 0, degenerating the priority to the clause-id tiebreak (birth order, AgeOnly-like fair - documented in Spec 08 section 4); the distinct-symbol collection is bounded by kConjectureDistanceSymbols and truncation lowers the distance deterministically (documented sound degradation, never a soundness or determinism change); unknown symbol ids fall back to kDefaultSymbolWeight like the selection weight.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturates at u32::MAX on overflow (unreachable for legal clauses, documented like SelectionWeight::of).
    /// CEP:ASSUMES: the conjecture set (when present) is sorted ascending; atoms interned by the store.
    /// CEP:COST: O(total term nodes) plus O(foreign distinct symbols x set size) membership checks (binary search over the sorted set).
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{heap_orders_by_conjecture_distance, conjecture_distance_ignores_conjecture_symbols, conjecture_distance_unset_degenerates_to_id_order}.
    /// CEP:SECURITY: depth-bounded recursion; bounded scratch.
    pub fn conjecture_distance(
        terms: &TermStore<'_>,
        symbols: &SymbolTable<'_>,
        conjecture: Option<&[core::cell::Cell<u32>]>,
        literals: &[Literal],
    ) -> u32 {
        // Distinct foreign symbol collection: sorted insertion into a bounded
        // stack array keeps the walk allocation-free (no_std discipline) and the
        // dedup exact up to the documented truncation.
        let mut foreign: [u32; kConjectureDistanceSymbols] = [0; kConjectureDistanceSymbols];
        let mut foreign_count: usize = 0;
        for literal in literals.iter() {
            Self::collect_foreign(
                terms,
                conjecture,
                literal.atom(),
                0,
                &mut foreign,
                &mut foreign_count,
            );
        }
        let mut total: u64 = 0;
        for symbol in foreign[..foreign_count].iter() {
            let weight = symbols
                .symbol_weight(*symbol)
                .unwrap_or(kDefaultSymbolWeight);
            total = total.saturating_add(weight as u64);
        }
        if total > u32::MAX as u64 {
            u32::MAX
        } else {
            total as u32
        }
    }

    // CEP:WHAT: Recursive foreign-symbol collector for the conjecture distance: walks one atom, inserting every symbol id outside the conjecture set into the sorted distinct array.
    // CEP:WHY: The distance counts DISTINCT symbols (design 15.2's "symbol overlap" reads occurrence classes, not multiplicities); equality atoms contribute their arguments (the equality tag carries no symbol-table entry, matching SelectionWeight::of_term); depth-bounded like the weight walk; the array is full-truncated (a symbol beyond kConjectureDistanceSymbols is skipped deterministically).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (truncation documented in conjecture_distance).
    // CEP:ASSUMES: the conjecture set is sorted ascending (binary search).
    // CEP:COST: O(term nodes) plus O(cap) insert scans.
    // CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::conjecture_distance_ignores_conjecture_symbols.
    // CEP:SECURITY: depth-bounded.
    fn collect_foreign(
        terms: &TermStore<'_>,
        conjecture: Option<&[core::cell::Cell<u32>]>,
        term: crate::ir::term::TermPtr,
        depth: u32,
        foreign: &mut [u32; kConjectureDistanceSymbols],
        foreign_count: &mut usize,
    ) {
        if depth > mapt_config::limits::kMaxTermDepth as u32 {
            return;
        }
        let view = match terms.term(term) {
            Ok(value) => value,
            Err(_) => return,
        };
        match view.tag() {
            crate::ir::term::TermTag::Variable => {}
            crate::ir::term::TermTag::Equality => {
                for child in view.children() {
                    Self::collect_foreign(
                        terms,
                        conjecture,
                        child,
                        depth + 1,
                        foreign,
                        foreign_count,
                    );
                }
            }
            _ => {
                let symbol = view.symbol();
                let in_conjecture = match conjecture {
                    None => false,
                    Some(set) => set
                        .binary_search_by(|probe| probe.get().cmp(&symbol))
                        .is_ok(),
                };
                if !in_conjecture
                    && !foreign[..*foreign_count].contains(&symbol)
                    && *foreign_count < foreign.len()
                {
                    // Full array: the symbol is skipped deterministically (the
                    // documented truncation - a missed foreign symbol only
                    // lowers the distance, never changes soundness).
                    foreign[*foreign_count] = symbol;
                    *foreign_count += 1;
                }
                for child in view.children() {
                    Self::collect_foreign(
                        terms,
                        conjecture,
                        child,
                        depth + 1,
                        foreign,
                        foreign_count,
                    );
                }
            }
        }
    }
}

// CEP:WHAT: Removes duplicate literals (same atom pointer and polarity) from a staged slice in place; returns the deduplicated length.
// CEP:WHY: Design 7.2 stage 10 (duplicate-literal removal) belongs to clause normalization: the store keeps literals verbatim by design (Phase 1 layout), so the search layer deduplicates before storage; without it, hash-consing-equal duplicates make the duplicated literal non-strictly-maximal (eligible_positive rejects equal atoms), blocking both resolution on it and the factoring that would merge it - the PHP refutation unit clauses (a or a) become unresolvable, an incompleteness the loop_refutes_pigeonhole property test pins.
// CEP:STATUS: complete
// CEP:FAILURE: none (a shorter slice is always sound: a disjunction with a repeated literal is logically identical).
// CEP:ASSUMES: hash-consing makes structural term equality pointer equality.
// CEP:COST: O(n^2) at the clause-literal bound.
// CEP:EVIDENCE: property/given_clause_property_test.rs::loop_refutes_pigeonhole; unit/hot/given_clause_test.rs::{resolution_fires, saturates_on_satisfiable}.
// CEP:SECURITY: none.
fn dedupe_literals(literals: &mut [Literal]) -> usize {
    let mut write: usize = 0;
    for read in 0..literals.len() {
        let duplicate = (0..write).any(|slot| {
            literals[slot].atom() == literals[read].atom()
                && literals[slot].is_positive() == literals[read].is_positive()
        });
        if !duplicate {
            literals[write] = literals[read];
            write += 1;
        }
    }
    write
}

/// CEP:WHAT: The search space: the clause store, the passive heap, the active set, the substitution, and the per-search state (input counter, in-progress generation).
/// CEP:WHY: Design 8.4's clause database as one owning structure (passive + active over one store); the in-progress generation (given clause + cursor) is carried between saturate iterations so deferred inference work resumes on the next call; the substitution is shared by simplification and generation with trail discipline.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: construction returns SearchError on capacity exhaustion.
/// CEP:ASSUMES: one search space per arena; terms and symbols outlive the space (borrowed).
/// CEP:COST: construction is O(capacities); saturate iterations are allocation-free.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs; unit/hot/search_db_test.rs; property/given_clause_property_test.rs.
/// CEP:SECURITY: capacities bounded.
pub struct SearchSpace<'a> {
    /// CEP:WHAT: The ATP clause store.
    /// CEP:WHY: Sole creator of clause records and ids (design 5.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: shared with the caller for proof extraction.
    /// CEP:COST: see ClauseStore.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
    /// CEP:SECURITY: bounds-checked.
    pub store: ClauseStore<'a>,
    /// CEP:WHAT: The passive set.
    /// CEP:WHY: Design 8.4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: strategy fixed at construction.
    /// CEP:COST: see PassiveHeap.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, capacity_enforced}.
    /// CEP:SECURITY: capacity bounded.
    pub passive: PassiveHeap<'a>,
    /// CEP:WHAT: The active set.
    /// CEP:WHY: Design 8.4/9.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: trees consistent with slots.
    /// CEP:COST: see ActiveSet.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_trees_updated}.
    /// CEP:SECURITY: capacities bounded.
    pub active: ActiveSet<'a>,
    /// CEP:WHAT: The shared substitution.
    /// CEP:WHY: Simplification and generation extend it trail-disciplined.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: baseline depth between saturate iterations.
    /// CEP:COST: see Substitution.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{demodulation_simplifies, resolution_fires}.
    /// CEP:SECURITY: bounds-checked.
    pub substitution: Substitution<'a>,
    /// CEP:WHAT: Input clause counter (the age source).
    /// CEP:WHY: Design 15.2: age is the birth order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_age.
    /// CEP:SECURITY: none.
    input_age: core::cell::Cell<u32>,
    /// CEP:WHAT: The arena the space was constructed over.
    /// CEP:WHY: The conjecture harvest (Spec 16) builds bounded mini search spaces over the SAME arena inside the loop; the field is the sanctioned handle (the store, passive, and active sets already borrow the arena internally, so this adds one reference, no ownership).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the arena outlives the space and every mini space derived from it.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    /// CEP:SECURITY: none.
    pub arena: &'a Arena,
    /// CEP:WHAT: The first proof-only clause id (the import watermark), or kInvalidClauseId before any import.
    /// CEP:WHY: The conjecture import's proof-only clauses (Spec 17 section 3) share the store's dense id space with staged clauses but must never be mistaken for axioms: the harvest's premise enumeration, the unit window, and the constructor-instance scan all stop at this watermark, so imported subproof clauses can neither seed candidates nor pollute later mini refutations (the Task 26 sev-0 repair; the watermark is monotone because proof ids only grow).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: set once by the first add_proof_clause; never reset.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{proof_watermark_bounds_harvest_scans, two_harvests_stay_sound}.
    /// CEP:SECURITY: soundness boundary of the conjecture feature.
    proof_base: core::cell::Cell<u64>,
    /// CEP:WHAT: The frozen conjecture symbol set (sorted, arena-backed), or None before the driver sets it (CEP-1035).
    /// CEP:WHY: Design 15.2 row 2's conjecture-distance strategy measures symbol overlap against the conjecture; the set is a CEP-1-style frozen input (set once before saturate, like the symbol table), stored as a sorted arena array so the per-push distance walk binary-searches it; None makes every distance 0 (the documented degenerate fairness, Spec 08 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: set before saturate when the ConjectureDistance strategy is selected; never mutated after set_conjecture_symbols.
    /// CEP:COST: 8 bytes plus the arena array.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{heap_orders_by_conjecture_distance, conjecture_distance_ignores_conjecture_symbols}.
    /// CEP:SECURITY: none.
    conjecture_symbols: core::cell::Cell<Option<&'a [core::cell::Cell<u32>]>>,
}

impl<'a> SearchSpace<'a> {
    /// CEP:WHAT: Constructs the search space with production capacities.
    /// CEP:WHY: Production entry point; the capacities are the named constants.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: returns SearchError on capacity exhaustion.
    /// CEP:ASSUMES: the arena has room (slot, tree, and pool arrays; about 120 MiB at maximum caps).
    /// CEP:COST: O(capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}.
    /// CEP:SECURITY: capacities validated before allocation.
    pub fn new(arena: &'a Arena, options: &SearchOptions) -> Result<SearchSpace<'a>, SearchError> {
        SearchSpace::new_with(
            arena,
            options,
            mapt_config::limits::kPassiveHeapCapacity,
            mapt_config::limits::kActiveSetCapacity,
            mapt_config::limits::kDiscriminationTreeNodes,
            mapt_config::limits::kDiscriminationTreeEntries,
            mapt_config::limits::kFeatureVectorPoolWords,
            mapt_config::limits::kClauseOffsetTableCapacity,
        )
    }

    /// CEP:WHAT: Constructs the search space with explicit capacities.
    /// CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production path; Phase 4 adds the clause-id side-table capacity so proof reconstruction and AVATAR ancestry can resolve parent ids on the production space while tests inject small tables.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: returns SearchError on exhaustion.
    /// CEP:ASSUMES: capacities >= 1.
    /// CEP:COST: O(capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops; security/phase3_bounds_test.rs::{passive_capacity_enforced, active_capacity_enforced}; unit/hot/clause_test.rs::side_table_capacity_enforced.
    /// CEP:SECURITY: bounds validated.
    /// CEP:WHAT: Clippy allowance for the eight explicit capacities (one per bounded substructure).
    /// CEP:WHY: CEP&CC 34.3 requires every capacity injectable on the production path; an options struct would hide which test uses which bound, so the parameter list is the documented interface.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs; security/phase4_bounds_test.rs.
    /// CEP:SECURITY: none.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with(
        arena: &'a Arena,
        options: &SearchOptions,
        passive_capacity: u32,
        active_capacity: u32,
        tree_nodes: u32,
        tree_entries: u32,
        pool_words: u32,
        id_offset_capacity: u32,
    ) -> Result<SearchSpace<'a>, SearchError> {
        Ok(SearchSpace {
            store: ClauseStore::new_with(arena, id_offset_capacity).map_err(SearchError::Clause)?,
            passive: PassiveHeap::new_with(arena, passive_capacity, options.strategy)?,
            active: ActiveSet::new_with(
                arena,
                active_capacity,
                tree_nodes,
                tree_entries,
                pool_words,
            )?,
            substitution: Substitution::new(arena),
            input_age: core::cell::Cell::new(0),
            arena,
            proof_base: core::cell::Cell::new(kInvalidClauseId),
            conjecture_symbols: core::cell::Cell::new(None),
        })
    }

    /// CEP:WHAT: Freezes the conjecture symbol set (design 15.2 row 2, CEP-1035): copies the ids into a sorted arena array consumed by the conjecture-distance weight.
    /// CEP:WHY: The distance walk binary-searches the set, so it is frozen sorted once before the search (CEP-1 discipline: inputs are frozen before the hot path); calling it twice replaces the set loudly by contract (the doc'd assume forbids it in production, and the deterministic rebuild keeps tests honest).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError on arena exhaustion.
    /// CEP:ASSUMES: called before saturate; symbol ids come from the frozen symbol table.
    /// CEP:COST: O(n log n) sort plus one arena allocation.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{heap_orders_by_conjecture_distance, conjecture_distance_ignores_conjecture_symbols}.
    /// CEP:SECURITY: none.
    pub fn set_conjecture_symbols(&self, symbols: &[u32]) -> Result<(), SearchError> {
        let range = self
            .arena
            .alloc_array::<core::cell::Cell<u32>>(symbols.len() as u32)
            .map_err(|_| SearchError::Passive(PassiveError::Full))?;
        let slot = self
            .arena
            .array_mut::<core::cell::Cell<u32>>(range)
            .map_err(|_| SearchError::Passive(PassiveError::Full))?;
        for (index, value) in symbols.iter().enumerate() {
            slot[index].set(*value);
        }
        // In-place insertion sort (CEP-0: no allocation, no Vec) so the frozen
        // form is canonical for the distance walk's binary search, independent
        // of the caller's input order (CEP&CC 38.10).
        for index in 1..symbols.len() {
            let key = slot[index].get();
            let mut position = index;
            while position > 0 && slot[position - 1].get() > key {
                slot[position].set(slot[position - 1].get());
                position -= 1;
            }
            slot[position].set(key);
        }
        let frozen = self
            .arena
            .array::<core::cell::Cell<u32>>(range)
            .map_err(|_| SearchError::Passive(PassiveError::Full))?;
        self.conjecture_symbols.set(Some(frozen));
        Ok(())
    }

    // CEP:WHAT: Pushes a clause into the passive set through the strategy's push path.
    // CEP:WHY: One branch point for the design 15.2 strategies (CEP-1035): the conjecture-distance strategy computes the distance once per clause and pushes through push_with_distance, every other strategy keeps the plain push - so no new work lands on the existing hot path (Law 1) and the priority is fixed at birth in both cases (determinism, CEP&CC 38.10); pub(crate) because the AVATAR controller's materialization paths push through the same discipline (a direct heap push under ConjectureDistance would rank the clause priority 0 and jump the queue).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates PassiveError (capacity).
    // CEP:ASSUMES: literals are the staged clause's literals (the distance walk reads their atoms).
    // CEP:COST: one enum compare for the non-conjecture strategies; the distance walk only under ConjectureDistance.
    // CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::heap_orders_by_conjecture_distance.
    // CEP:SECURITY: capacity bound.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn push_passive(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        clause_id: u64,
        ptr: ClausePtr,
        age: u32,
        weight: u32,
        literals: &[Literal],
    ) -> Result<(), PassiveError> {
        if options.strategy == SelectionStrategy::ConjectureDistance {
            let distance = SelectionWeight::conjecture_distance(
                context.terms,
                context.symbols,
                self.conjecture_symbols.get(),
                literals,
            );
            self.passive
                .push_with_distance(clause_id, ptr.as_u32(), distance)
        } else {
            self.passive.push(clause_id, ptr.as_u32(), age, weight)
        }
    }

    // CEP:WHAT: Marks a clause record with the set-of-support bit when the SOS option is on and the derivation licenses it (CEP-1035).
    // CEP:WHY: Design 15.2 row 5: supported clauses are the NegatedConjecture/ConjectureNegation seeds and every derivation descendant (a parent carries the mark); the mark rides the record's flag field (kClauseFlagSos, written through the sanctioned set_flag mutator) so clause count scales without a side table; the option-off path is a no-op (zero cost when the strategy is not selected - Law 1); pub(crate) because the AVATAR controller's materialization paths (activate_under_model, transfer_learnts, the supported-input variant) create passive-bound records through the same discipline.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError on unreadable parents or the flag write.
    // CEP:ASSUMES: parents are store ids of previously created records (monotonic ids: their flags are final).
    // CEP:COST: one rule compare plus, for derivations, one record read per parent; one flag write when the mark lands.
    // CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{sos_flag_marks_conjecture_seeds, sos_flag_inherits_through_parents}.
    // CEP:SECURITY: none.
    pub(crate) fn mark_sos(
        &self,
        options: &SearchOptions,
        ptr: ClausePtr,
        rule: InferenceRule,
        parents: &[u64; kMaxDerivationParents],
        parent_count: u8,
    ) -> Result<(), SearchError> {
        if !options.set_of_support {
            return Ok(());
        }
        let mut supported =
            rule == InferenceRule::NegatedConjecture || rule == InferenceRule::ConjectureNegation;
        if !supported {
            for parent_id in parents.iter().take(parent_count as usize) {
                if *parent_id == kInvalidClauseId {
                    continue;
                }
                let parent = self
                    .store
                    .clause_by_id(crate::ir::clause::ClauseId(*parent_id))
                    .map_err(SearchError::Clause)?;
                if parent.flags & kClauseFlagSos != 0 {
                    supported = true;
                    break;
                }
            }
        }
        if supported {
            self.store
                .set_flag(ptr, kClauseFlagSos)
                .map_err(SearchError::Clause)?;
        }
        Ok(())
    }

    // CEP:WHAT: Reads a clause's set-of-support mark by store id (CEP-1035).
    // CEP:WHY: The loop's selection restriction asks the flag of every popped clause; ids come from the passive heap and resolve through the store's id side table.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError on an unreadable record (the caller treats a missing flag as unsupported only after the read succeeded).
    // CEP:ASSUMES: the id is store-produced.
    // CEP:COST: one record read.
    // CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::sos_restriction_spares_nonsupport_clauses.
    // CEP:SECURITY: bounds-checked.
    fn clause_is_sos(&self, clause_id: u64) -> Result<bool, SearchError> {
        let record = self
            .store
            .clause_by_id(crate::ir::clause::ClauseId(clause_id))
            .map_err(SearchError::Clause)?;
        Ok(record.flags & kClauseFlagSos != 0)
    }

    /// CEP:WHAT: Adds one input clause: computes the selection flags, the selection weight, creates the record with the Input derivation, and pushes it into the passive set.
    /// CEP:WHY: Design 15.1's initial passive population; the empty input clause is pushed like any other (the loop detects it on pop and returns Theorem).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError (store bounds, flag computation, passive capacity).
    /// CEP:ASSUMES: literal atoms were interned by the caller's term store; the caller standardizes each clause's variables to a dense namespace (design 7.2 stage 7 discipline).
    /// CEP:COST: O(literals^2) flag comparisons plus the weight walk plus one store insert plus one heap push.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}; unit/hot/selection_test.rs::{maximality_computed, first_negative_selects}.
    /// CEP:SECURITY: store bounds enforced.
    pub fn add_input_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
    ) -> Result<u32, SearchError> {
        let derivation = DerivationStep {
            rule: InferenceRule::Input,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; kMaxDerivationParents],
            substitution: kInvalidSubstitutionOffset,
        };
        self.stage_and_push(context, options, literals, derivation)
    }

    /// CEP:WHAT: Returns the number of input clauses added.
    /// CEP:WHY: Diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
    /// CEP:SECURITY: none.
    pub fn input_count(&self) -> u32 {
        self.input_age.get()
    }

    /// CEP:WHAT: Adds one parentless theory clause (induction scheme) with an explicit rule.
    /// CEP:WHY: Revised build order Phase 4 (Spec 15): structural and well-founded induction schemes enter the passive set like inputs but carry their scheme rule so the proof walk and the TSTP writer present them as named theory axioms; the age comes from the shared input counter (the sanctioned allocation point, next_input_age's discipline).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError (store bounds, flag computation, passive capacity).
    /// CEP:ASSUMES: literal atoms were interned by the caller's term store; the rule is one of the parentless theory rules (StructuralInduction, WellFoundedInduction).
    /// CEP:COST: as add_input_clause (one staging pass, one store insert, one heap push).
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::{structural_scheme_clauses_match_clausification, schemes_enter_passive_set}.
    /// CEP:SECURITY: store bounds enforced.
    pub fn add_theory_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
        rule: InferenceRule,
    ) -> Result<u32, SearchError> {
        let derivation = DerivationStep {
            rule,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; kMaxDerivationParents],
            substitution: kInvalidSubstitutionOffset,
        };
        self.stage_and_push(context, options, literals, derivation)
    }

    /// CEP:WHAT: Adds one assumption clause (a conjecture candidate's negation) to this space.
    /// CEP:WHY: Spec 16 section 5: the mini-refutation premise must be distinguishable from axioms in the imported proof DAG, so it carries the ConjectureNegation rule; the shape is add_input_clause's with a different derivation label.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError.
    /// CEP:ASSUMES: literal atoms were interned by the caller's term store; called on the MINI space by the conjecture filter (the main search never adds assumptions).
    /// CEP:COST: as add_input_clause.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, unprovable_candidate_adds_nothing}.
    /// CEP:SECURITY: store bounds enforced.
    pub fn add_assumption_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
    ) -> Result<u32, SearchError> {
        let derivation = DerivationStep {
            rule: InferenceRule::ConjectureNegation,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; kMaxDerivationParents],
            substitution: kInvalidSubstitutionOffset,
        };
        self.stage_and_push(context, options, literals, derivation)
    }

    /// CEP:WHAT: Creates one proof-DAG clause without entering the passive set.
    /// CEP:WHY: Spec 17 section 3: the conjecture import replays a mini refutation into the main store clause by clause; the imported steps are proof-only (they never re-enter the search, or the main loop would saturate on its own lemmas' subproofs); the derivation is taken verbatim with the caller's translated parent ids, so the imported chain is exactly the mini chain.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError (store bounds, flag computation).
    /// CEP:ASSUMES: literal atoms were interned by the caller's term store; parent ids are valid main-store ids strictly older than the next id; the age is the mini clause's age.
    /// CEP:COST: one staging pass plus one store insert.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    /// CEP:SECURITY: store bounds enforced.
    pub fn add_proof_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
        age: u32,
        derivation: DerivationStep,
    ) -> Result<u32, SearchError> {
        let (staged, count, _weight) = self.stage_clause(context, options, literals)?;
        let (rule, parents, parent_count) =
            (derivation.rule, derivation.parents, derivation.parent_count);
        let ptr = self
            .store
            .new_clause(context.terms, &staged[..count], age, derivation)
            .map_err(SearchError::Clause)?;
        // Proof-only clauses still carry the set-of-support mark (CEP-1035):
        // imported ConjectureLemma derivations cite the imported negation
        // premise as a parent, and the parent's mark is what makes the lemma a
        // supported descendant.
        self.mark_sos(options, ptr, rule, &parents, parent_count)?;
        let id = self.store.clause(ptr).map_err(SearchError::Clause)?.id.0;
        // The import watermark: the first proof-only id. Monotone by the
        // store's dense id counter; every harvest scan stops here.
        if self.proof_base.get() == kInvalidClauseId {
            self.proof_base.set(id);
        }
        Ok(ptr.as_u32())
    }

    /// CEP:WHAT: Returns the proof-only watermark: the first imported clause's id, or the next unstaged id when no import has happened.
    /// CEP:WHY: The harvest's premise enumeration, unit window, and constructor-instance scan treat every id below this bound as harvest-visible and everything at or above it as import-private (Spec 16 section 3, the Task 26 sev-0 repair); before any import the bound is the next id, so the un-imported space behaves exactly as before.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called between clause creations (the returned bound is a snapshot; a concurrent creation only lowers what the caller sees, never raises it).
    /// CEP:COST: one load plus, before the first import, one next-id read.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{proof_watermark_bounds_harvest_scans, two_harvests_stay_sound}.
    /// CEP:SECURITY: the soundness boundary of the conjecture feature's id-space sharing.
    pub fn proof_base(&self) -> u64 {
        match self.proof_base.get() {
            kInvalidClauseId => self.store.next_clause_id().0,
            bound => bound,
        }
    }

    /// CEP:WHAT: Adds one derived clause with an explicit derivation into the passive set.
    /// CEP:WHY: Spec 16 section 6: a lemma proved by bounded refutation enters the main search through the normal passive path with the ConjectureLemma derivation (parents: imported negation premise and imported empty clause); the shape is add_input_clause's with the caller's derivation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SearchError.
    /// CEP:ASSUMES: literal atoms were interned by the caller's term store.
    /// CEP:COST: as add_input_clause.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, lemma_enters_passive_set}.
    /// CEP:SECURITY: store bounds enforced.
    pub fn add_derived_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
        derivation: DerivationStep,
    ) -> Result<u32, SearchError> {
        self.stage_and_push(context, options, literals, derivation)
    }

    // CEP:WHAT: Stages literals (bounds check, dedupe, selection flags, weight) for one clause creation.
    // CEP:WHY: The shared body of the add paths (input, theory, assumption, derived); staging is the production discipline of add_input_clause, extracted once so every Phase 4 (revised) path funnels through the identical checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError (TooManyLiterals, flag computation).
    // CEP:ASSUMES: as add_input_clause.
    // CEP:COST: O(literals^2) flag comparisons plus the weight walk.
    // CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set; unit/hot/conjecture_test.rs::lemma_enters_passive_set.
    // CEP:SECURITY: bounds enforced.
    fn stage_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
    ) -> Result<([Literal; kMaxClauseLiterals as usize], usize, u32), SearchError> {
        let mut staged: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        if literals.len() > staged.len() {
            return Err(SearchError::Clause(
                crate::ir::clause::ClauseError::TooManyLiterals,
            ));
        }
        for (index, literal) in literals.iter().enumerate() {
            staged[index] = *literal;
        }
        let deduped = dedupe_literals(&mut staged[..literals.len()]);
        if deduped > 0 {
            compute_selection_flags(context, options.selection, &mut staged[..deduped])
                .map_err(SearchError::Inference)?;
        }
        let weight = SelectionWeight::of(context.terms, context.symbols, &staged[..deduped]);
        Ok((staged, deduped, weight))
    }

    // CEP:WHAT: Runs the full staging pipeline and pushes the created clause into the passive set.
    // CEP:WHY: The body shared by add_input_clause, add_theory_clause, add_assumption_clause, and add_derived_clause: stage, create with the derivation, mark the set-of-support flag (CEP-1035: parentless theory rules are supported only through their rule seed), and push through the strategy's path (CEP-1035 conjecture distance); the age comes from the shared input counter.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError.
    // CEP:ASSUMES: as stage_clause.
    // CEP:COST: stage_clause plus one store insert, one flag scan, and one heap push.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction; unit/hot/induction_test.rs::schemes_enter_passive_set; unit/hot/strategy_selection_test.rs::sos_flag_marks_conjecture_seeds.
    // CEP:SECURITY: store bounds enforced.
    fn stage_and_push(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
        derivation: DerivationStep,
    ) -> Result<u32, SearchError> {
        let mut staged: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        if literals.len() > staged.len() {
            return Err(SearchError::Clause(
                crate::ir::clause::ClauseError::TooManyLiterals,
            ));
        }
        for (index, literal) in literals.iter().enumerate() {
            staged[index] = *literal;
        }
        let deduped = dedupe_literals(&mut staged[..literals.len()]);
        if deduped > 0 {
            compute_selection_flags(context, options.selection, &mut staged[..deduped])
                .map_err(SearchError::Inference)?;
        }
        let weight = SelectionWeight::of(context.terms, context.symbols, &staged[..deduped]);
        let age = self.next_input_age();
        let (rule, parents, parent_count) =
            (derivation.rule, derivation.parents, derivation.parent_count);
        let ptr = self
            .store
            .new_clause(context.terms, &staged[..deduped], age, derivation)
            .map_err(SearchError::Clause)?;
        self.mark_sos(options, ptr, rule, &parents, parent_count)?;
        let record = self.store.clause(ptr).map_err(SearchError::Clause)?;
        self.push_passive(
            context,
            options,
            record.id.0,
            ptr,
            age,
            weight,
            &staged[..deduped],
        )?;
        Ok(ptr.as_u32())
    }

    /// CEP:WHAT: Allocates the next input age (monotonic counter shared by input clauses and AVATAR component materializations).
    /// CEP:WHY: Materialized components (design 12.2 rule 3) enter the passive set like inputs and need the same monotone age discipline (design 15.2); the counter stays private to the space, so this is the single sanctioned allocation point.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: single-threaded space.
    /// CEP:COST: 1 load, 1 store.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: none.
    pub fn next_input_age(&self) -> u32 {
        let age = self.input_age.get();
        self.input_age.set(age + 1);
        age
    }
}

/// CEP:WHAT: Runs the given-clause loop to a terminal outcome, converting capacity-family errors to GaveUp(MemoryBudget).
/// CEP:WHY: Design 20.2 and the GaveUpReason::MemoryBudget documentation fix the loop's contract: a capacity or storage budget (passive full, active full, arena exhausted, clause budget) ENDS the search as GaveUp with the reason named, never as Err - a bound firing is a legal bounded outcome (CEP&CC Law 6), not a structural failure; before CEP-1056 the loop propagated those errors (arena exhaustion during rule materialization surfaced as Err after the honest-kind fix, clause-store and active-set capacity as Err since Phase 3), so long-running saturations crashed instead of stopping (tests/bug_first_negative_selection.rs); the wrapper keeps the conversion in one place so every current and future `?` inside the loop is covered and saturate_with_avatar inherits the behavior through its inner saturate call.
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(GaveUp(MemoryBudget)) when the inner loop returns a capacity-family SearchError; every other Err propagates; never panics.
/// CEP:ASSUMES: the inner loop's non-capacity errors are structural (corruption, caller bugs) and stay loud.
/// CEP:COST: one match per terminal error path; zero on Ok.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::arena_exhaustion_gives_up_memory_budget; tests/bug_first_negative_selection.rs (CEP-1056 regression).
/// CEP:SECURITY: the memory bound stays the denial-of-service boundary (CEP&CC 22.10).
pub fn saturate<F: Fn(u64) -> bool>(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    should_stop: &F,
    stats: &mut SearchStats,
) -> Result<SearchOutcome, SearchError> {
    match saturate_inner(space, context, options, should_stop, stats) {
        Ok(outcome) => Ok(outcome),
        Err(error) if is_memory_bound(&error) => {
            Ok(SearchOutcome::GaveUp(GaveUpReason::MemoryBudget))
        }
        Err(error) => Err(error),
    }
}

// CEP:WHAT: The capacity-family membership test over SearchError.
// CEP:WHY: The documented MemoryBudget members (design 20.2): arena or table exhaustion during rule materialization (Inference over ArenaFull, honest kinds since CEP-1056), clause-store capacity (arena, clause-id budget, id-offset side table), active-set capacity (slots, discrimination-tree nodes or entries, feature-vector pool), and the nested clause-store capacity inside active-set operations; structural variants (unreadable references, arity and parent bounds, out-of-range slots) stay Err - they are caller bugs or corruption, not capacity facts.
// CEP:STATUS: complete
// CEP:FAILURE: none; a pure classifier.
// CEP:ASSUMES: PassiveError capacity is handled inside drain_buffer (DrainStatus::PassiveFull) and never reaches this classifier.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::arena_exhaustion_gives_up_memory_budget.
// CEP:SECURITY: none.
fn is_memory_bound(error: &SearchError) -> bool {
    matches!(
        error,
        SearchError::Inference(InferenceError::Structural(SubstitutionError::ArenaFull))
            | SearchError::Clause(
                ClauseError::ArenaFull
                    | ClauseError::ClauseBudgetExceeded
                    | ClauseError::OffsetTableFull,
            )
            | SearchError::Active(ActiveError::SlotsFull)
            | SearchError::Active(ActiveError::Features(FeatureError::PoolFull))
            | SearchError::Active(ActiveError::Tree(
                IndexError::TreeFull | IndexError::EntryBudgetExceeded | IndexError::ArenaFull,
            ))
            | SearchError::Active(ActiveError::Store(
                ClauseError::ArenaFull
                    | ClauseError::ClauseBudgetExceeded
                    | ClauseError::OffsetTableFull,
            ))
    )
}

// CEP:WHAT: The given-clause loop body behind the capacity-converting saturate wrapper.
// CEP:WHY: Design 15.1 with the Phase 3 bounds: the injected stop callback (checked every kBudgetCheckInterval iterations) is the CEP-1005 time-budget mechanism and stays generic (no dyn, CEP-0 discipline) with the counter as its only input so tests inject deterministic predicates and the CEP-1 driver supplies wall time; the loop's step order (select, simplify, forward-subsume, backward-subsume, activate, generate) keeps the active array stable during one given clause's generation; deferred generation resumes across iterations through the in-progress state; the given clause's literals live in one fixed stack buffer for the whole loop (no allocation, no_std discipline).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError on structural failures; GaveUp on budget exhaustion; never panics; capacity-family errors are the wrapper's to convert.
// CEP:ASSUMES: the context's stores match the space's; the stop callback is deterministic for a fixed counter.
// CEP:COST: see file header; benches CEP-BENCH-0010/0011.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force, loop_refutes_pigeonhole}; fuzz/given_clause_fuzz_test.rs; bench CEP-BENCH-0010, CEP-BENCH-0011.
// CEP:SECURITY: all budgets enforced.
fn saturate_inner<F: Fn(u64) -> bool>(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    should_stop: &F,
    stats: &mut SearchStats,
) -> Result<SearchOutcome, SearchError> {
    let mut in_progress: Option<(u32, u64, GenerationCursor)> = None;
    let mut buffer = InferenceBuffer::new();
    let mut given: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let mut given_len: usize = 0;
    let mut iterations: u64 = 0;
    // CEP:WHAT: The simplification step chain buffer (CEP-1036, extended by CEP-1034).
    // CEP:WHY: Cleared per given clause; simplify_given records one snapshot per rewrite (demodulation, subsumption resolution, or condensation) and the park point stores one clause record per step so the derivation DAG carries the full simplification history for the kernel's exact replay (Spec 19).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: consumed in the same iteration it was filled (the park point runs before the next simplify).
    // CEP:COST: kMaxSimplifyRounds step records of stack.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    // CEP:SECURITY: none.
    let mut simplify_steps = SimplificationSteps::new();
    let mut chain_scratch: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    loop {
        // Budget checks (CEP-1005: every kBudgetCheckInterval iterations).
        if iterations > 0
            && iterations.is_multiple_of(kBudgetCheckInterval)
            && should_stop(iterations)
        {
            return Ok(SearchOutcome::GaveUp(GaveUpReason::TimeBudget));
        }
        iterations += 1;
        if stats.inferences >= options.inference_budget {
            return Ok(SearchOutcome::GaveUp(GaveUpReason::InferenceBudget));
        }
        // Conjecture harvest (revised build order Phase 4, Spec 16): a fixed
        // schedule (every kConjectureHarvestInterval iterations) with a fixed
        // total (kMaxConjectureHarvests); the harvest is a pure function of the
        // space state, so the loop stays deterministic (CEP&CC 38.10) and the
        // passive set it appends to is only read at the next select, so the
        // active-set consistency argument is untouched.
        if options.conjecture
            && stats.harvests < kMaxConjectureHarvests
            && iterations.is_multiple_of(kConjectureHarvestInterval)
        {
            crate::conjecture::harvest(space, context, options, stats);
        }
        if let Some((_given_offset, given_id, ref mut cursor)) = in_progress {
            // Deferred generation continues for the same given clause.
            let status = generate_step(
                context,
                &space.store,
                &space.active,
                &given[..given_len],
                given_id,
                cursor,
                &mut buffer,
            )?;
            stats.inferences += buffer.count as u64;
            stats.dropped += cursor.dropped;
            cursor.dropped = 0;
            match drain_buffer(space, context, options, &buffer, stats)? {
                DrainStatus::EmptyClause(refutation) => {
                    return Ok(SearchOutcome::Theorem { refutation })
                }
                DrainStatus::PassiveFull => {
                    return Ok(SearchOutcome::GaveUp(GaveUpReason::MemoryBudget))
                }
                DrainStatus::Drained => {}
            }
            if let crate::search::GenerationStatus::Complete = status {
                in_progress = None;
            }
            continue;
        }
        // Select the next given clause.
        let entry = match space.passive.pop() {
            Some(value) => value,
            None => return Ok(SearchOutcome::Saturated),
        };
        let given_offset = entry.offset;
        let given_id = entry.clause_id;
        given_len = read_given_into(space, given_offset, &mut given)?;
        if given_len == 0 {
            return Ok(SearchOutcome::Theorem {
                refutation: given_offset,
            });
        }
        // Simplify: tautology deletion, bounded demodulation, condensation, and
        // subsumption resolution against the active set (design 10.3 step 1).
        simplify_steps.count = 0;
        match simplify_given(
            space,
            context,
            options,
            given_id,
            &mut given,
            &mut given_len,
            stats,
            &mut simplify_steps,
        )? {
            SimplifyStatus::Discarded => {
                stats.given_processed += 1;
                continue;
            }
            SimplifyStatus::Kept => {}
        }
        // Defensive re-check after simplification: demodulation rewrites in
        // place and never removes literals, and condensation/SR deletions
        // (CEP-1034) record a chain step, so an empty buffer with NO recorded
        // chain is unreachable from a non-empty entry (the guard is kept as
        // defense in depth, deliberately). An empty buffer WITH a recorded
        // chain takes the chain path below: it parks the chain's last record
        // (the empty clause, e.g. a unit SR against a unit disequation) and
        // the next pop returns Theorem anchored at THAT record, whose
        // derivation chain reaches the axioms - returning the raw given offset
        // here would anchor the proof at a non-empty record.
        if given_len == 0 && simplify_steps.count == 0 {
            return Ok(SearchOutcome::Theorem {
                refutation: given_offset,
            });
        }
        // Forward/backward subsumption run only on a non-empty given: the
        // empty clause (a recorded SR chain's terminal, CEP-1034) is the
        // refutation itself - running backward subsumption with it would
        // delete the entire active set (the empty clause subsumes everything)
        // before the chain path parks the derivation.
        if given_len > 0 {
            // Forward subsumption: an active clause subsumes the given clause.
            if forward_subsumed(space, context, &given[..given_len])? {
                stats.forward_subsumed += 1;
                stats.given_processed += 1;
                continue;
            }
            // Backward subsumption: the given clause subsumes active clauses.
            backward_subsume(space, context, &given[..given_len], stats)?;
        }
        // Activate the given clause, or park a rewritten simplification chain back
        // to passive (the stored record is immutable; a rewritten clause is a new
        // record).
        if simplify_steps.count > 0 {
            // CEP:WHAT: The CEP-1036 chain path, extended by CEP-1034 to all three recorded simplification rules: one stored clause record per rewrite step.
            // CEP:WHY: Each record's derivation cites its own rule kind and parents ([previous, rule] for Demodulation and SubsumptionResolution, [previous] for Condensation), so the certified kernel replays each rule EXACTLY per step over the chain (Spec 19); the last record is the simplifier that re-enters the passive set, the intermediates are inert derivation anchors like the AvatarSplit originals; the pre-Phase-5 single-record park below remains as the defensive fallback for a clause rewritten without a recorded chain (corruption: its derivation cannot cite the rule, and the kernel rejects it as UnrecordedRule).
            // CEP:STATUS: complete
            // CEP:FAILURE: propagates SearchError on store, flag, or passive failures.
            // CEP:ASSUMES: the snapshots were restandardized + deduped at record time; the chain is contiguous from the given clause's id.
            // CEP:COST: one new_clause + one flags computation + one weight + one flag scan + one push per step.
            // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids; unit/hot/given_clause_test.rs::{condensation_simplifies_given, subsumption_resolution_simplifies_given}.
            // CEP:SECURITY: none.
            let mut previous_id = given_id;
            let mut last_ptr = ClausePtr::from_u32(given_offset);
            let mut last_age = 0u32;
            let mut last_count = 0usize;
            for step_index in 0..simplify_steps.count {
                let step = &simplify_steps.steps[step_index];
                let count = step.count as usize;
                for (target, source) in chain_scratch.iter_mut().zip(step.literals.iter()) {
                    *target = *source;
                }
                // The empty-clause chain step (a unit SR against a unit
                // disequation) skips flag computation like every empty record.
                if count > 0 {
                    compute_selection_flags(
                        context,
                        options.selection,
                        &mut chain_scratch[..count],
                    )
                    .map_err(SearchError::Inference)?;
                }
                let age = space.next_input_age();
                let (rule, parent_count, parents) = match step.rule {
                    InferenceRule::Condensation => (
                        InferenceRule::Condensation,
                        kUnaryRuleParents,
                        [
                            previous_id,
                            kInvalidClauseId,
                            kInvalidClauseId,
                            kInvalidClauseId,
                        ],
                    ),
                    rule => (
                        rule,
                        kBinaryRuleParents,
                        [
                            previous_id,
                            step.rule_id,
                            kInvalidClauseId,
                            kInvalidClauseId,
                        ],
                    ),
                };
                let derivation = DerivationStep {
                    rule,
                    parent_count,
                    reserved: 0,
                    parents,
                    substitution: kInvalidSubstitutionOffset,
                };
                let ptr = space
                    .store
                    .new_clause(context.terms, &chain_scratch[..count], age, derivation)
                    .map_err(SearchError::Clause)?;
                space.mark_sos(options, ptr, rule, &parents, parent_count)?;
                previous_id = space.store.clause(ptr).map_err(SearchError::Clause)?.id.0;
                last_ptr = ptr;
                last_age = age;
                last_count = count;
            }
            let last_step = &simplify_steps.steps[simplify_steps.count - 1];
            let weight =
                SelectionWeight::of(context.terms, context.symbols, &chain_scratch[..last_count]);
            let record = space.store.clause(last_ptr).map_err(SearchError::Clause)?;
            space.push_passive(
                context,
                options,
                record.id.0,
                last_ptr,
                last_age,
                weight,
                &chain_scratch[..last_step.count as usize],
            )?;
            stats.given_processed += 1;
            continue;
        }
        if given_is_stored(space, given_offset, &given[..given_len])? {
            space
                .active
                .insert(context.terms, given_offset, &given[..given_len])?;
        } else {
            // Defensive fallback (unreachable in production since CEP-1036: every
            // rewrite records a chain step, so a rewritten clause always takes the
            // chain path above); kept so an unforeseen rewrite path still parks the
            // clause instead of losing it. The single record cannot cite the
            // demodulating rule, so the certified kernel rejects the derivation as
            // UnrecordedRule (Spec 19) - the corruption is loud at proof time.
            let age = space.input_age.get();
            space.input_age.set(age + 1);
            // Restandardize the rewritten clause before storage: demodulation
            // can remove a middle variable (P(f(x0)) v Q(x1) under the rule
            // f(y)=a becomes P(a) v Q(x1), namespace {1} with a gap), and the
            // dense-namespace discipline the standardize-apart offset
            // arithmetic relies on requires [0, n) (Spec 07 section 2, the
            // same contract drain_buffer honors for rule conclusions).
            crate::inference::restandardize_clause(
                context.terms,
                context.symbols,
                &mut given[..given_len],
            )
            .map_err(SearchError::Inference)?;
            let deduped = dedupe_literals(&mut given[..given_len]);
            given_len = deduped;
            // Recompute the selection and maximality flags after
            // restandardize_clause rebuilt the literals: the rebuild constructs
            // fresh Literal records whose cached flags are false, and storing
            // them unflagged silently disables every ordering-eligible rule on
            // the parked demodulant when it is popped again (equality
            // resolution on a rewritten negative reflexive equation, ordered
            // resolution on the rewritten maximal side) - the Phase 4 (revised)
            // conjecture filter's symmetry proof exposed the loss; compute the
            // flags here so the parked record carries the same flags every
            // other stored clause has (Spec 08 section 3's staging contract).
            if given_len > 0 {
                compute_selection_flags(context, options.selection, &mut given[..given_len])
                    .map_err(SearchError::Inference)?;
            }
            let weight = SelectionWeight::of(context.terms, context.symbols, &given[..given_len]);
            let derivation = DerivationStep {
                rule: InferenceRule::Demodulation,
                parent_count: 1,
                reserved: 0,
                parents: [
                    given_id,
                    kInvalidClauseId,
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            };
            let ptr = space
                .store
                .new_clause(context.terms, &given[..given_len], age, derivation)
                .map_err(SearchError::Clause)?;
            let record = space.store.clause(ptr).map_err(SearchError::Clause)?;
            space.passive.push(record.id.0, ptr.as_u32(), age, weight)?;
            stats.given_processed += 1;
            continue;
        }
        stats.given_processed += 1;
        // Set-of-support restriction (design 15.2 row 5, CEP-1035): with the
        // option on, only conjecture descendants become given clauses. A
        // non-supported clause was simplified, subsumption-checked, and is now
        // ACTIVATED above (it serves as an inference partner for every later
        // given clause) but starts no generation - every inference involves at
        // least one supported clause, the classical SOS strategy (Wos, Robinson
        // & Carson 1965; Spec 08 section 7's completeness position).
        if options.set_of_support && !space.clause_is_sos(given_id)? {
            continue;
        }
        // Establish the in-progress generation state; the generation runs on the
        // next iteration through the in-progress branch.
        in_progress = Some((given_offset, given_id, GenerationCursor::new()));
    }
}

// CEP:WHAT: One recorded simplification rewrite step (CEP-1036 demodulation, extended by CEP-1034 to subsumption resolution and condensation): the restandardized, deduplicated snapshot of the clause after one simplification, with the simplifying rule clause's id and the rule kind.
// CEP:WHY: The certified kernel (Spec 19) replays demodulation, subsumption resolution, and condensation EXACTLY per step; that needs the rule's identity (the Phase 3/4 derivation recorded only the structural variant, ticket CEP-1036) and the kind (the three rules have distinct replay arms and parent shapes: demodulation and SR cite [previous, rule], condensation cites [previous] alone). The snapshot is restandardized + deduped at record time so the stored chain record equals the snapshot bit for bit, and the in-loop buffer keeps its own namespace for the next rewrite (all three rules are renaming-invariant, so the replay over the restandardized chain is sound).
// CEP:STATUS: complete
// CEP:FAILURE: none; a data record.
// CEP:ASSUMES: count <= kMaxClauseLiterals; rule_id != kInvalidClauseId for Demodulation and SubsumptionResolution (kInvalidClauseId is legal for Condensation, whose only parent is the chain predecessor); rule is one of the three recorded simplification rules.
// CEP:COST: kMaxClauseLiterals x 8 bytes of stack per step.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids; unit/hot/given_clause_test.rs::{condensation_simplifies_given, subsumption_resolution_simplifies_given}.
// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub(crate) struct SimplificationStep {
    /// CEP:WHAT: The post-rewrite clause snapshot (restandardized, deduplicated).
    /// CEP:WHY: The chain record's literals.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: slots beyond count are filler.
    /// CEP:COST: kMaxClauseLiterals x 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub literals: [Literal; kMaxClauseLiterals as usize],
    /// CEP:WHAT: The snapshot's literal count.
    /// CEP:WHY: Extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxClauseLiterals.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub count: u16,
    /// CEP:WHAT: The simplifying rule clause's store id (derivation parent 1).
    /// CEP:WHY: The kernel's exact per-step replay needs the rule; kInvalidClauseId makes the step unverifiable for Demodulation and SubsumptionResolution (UnrecordedRule) and is the legal Condensation shape (the clause simplifies itself).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the rule clause is live in the store when the id is valid.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub rule_id: u64,
    /// CEP:WHAT: The recorded rule kind (Demodulation, SubsumptionResolution, or Condensation).
    /// CEP:WHY: CEP-1034: the park point stores one record per step with the step's own rule label, and the kernel dispatches the replay arm on it; a rule outside the three recorded kinds would make the chain unverifiable and is rejected loudly at record time.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: record() fails loudly on a rule outside the recorded vocabulary.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte (enum copy).
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{condensation_simplifies_given, subsumption_resolution_simplifies_given}.
    /// CEP:SECURITY: none.
    pub rule: InferenceRule,
}

// CEP:WHAT: The per-simplify-call simplification step buffer (CEP-1036, extended by CEP-1034): one slot per simplify round.
// CEP:WHY: simplify_given performs at most one recorded simplification per round (the first successful demodulation, condensation, or subsumption resolution breaks the round), and the round count is kMaxSimplifyRounds, so the buffer capacity is exact and overflow is unreachable; saturate consumes the recorded chain right after the call by storing one clause record per step with the step's rule and parents, giving the derivation DAG the full simplification history the kernel replays.
// CEP:STATUS: complete
// CEP:FAILURE: none; the fixed arrays keep the buffer stack-allocated (no allocation in the hot loop).
// CEP:ASSUMES: one buffer per given clause iteration (cleared before each simplify_given call).
// CEP:COST: kMaxSimplifyRounds x (kMaxClauseLiterals x 8 + 12) bytes of stack.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
// CEP:SECURITY: none.
pub(crate) struct SimplificationSteps {
    /// CEP:WHAT: The recorded steps in rewrite order.
    /// CEP:WHY: The chain order is the replay order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: slots beyond count are filler.
    /// CEP:COST: kMaxSimplifyRounds step records.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub steps: [SimplificationStep; kMaxSimplifyRounds as usize],
    /// CEP:WHAT: The recorded step count.
    /// CEP:WHY: Extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= steps.len().
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub count: usize,
}

impl SimplificationSteps {
    // CEP:WHAT: Constructs an empty step buffer.
    // CEP:WHY: Explicit init with filler literals (the count governs reads).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    // CEP:SECURITY: none.
    pub fn new() -> SimplificationSteps {
        SimplificationSteps {
            steps: [SimplificationStep {
                literals: [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                    kMaxClauseLiterals as usize],
                count: 0,
                rule_id: kInvalidClauseId,
                rule: InferenceRule::Demodulation,
            }; kMaxSimplifyRounds as usize],
            count: 0,
        }
    }

    // CEP:WHAT: Records one simplification snapshot: restandardizes and dedupes a copy of the rewritten clause and stores it with the rule clause's id and the rule kind.
    // CEP:WHY: CEP-1036/CEP-1034: the stored chain record must equal the snapshot bit for bit (the kernel replays the production pipeline over it), so the restandardize + dedupe happens at record time, not at store time; the in-loop buffer keeps its own namespace because demodulation, subsumption resolution, and condensation are all renaming-invariant; a rule outside the recorded vocabulary fails loudly (a partial chain would be silently unverifiable).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError on restandardization failure; a full buffer or unrecorded rule kind fails loudly rather than recording a partial chain.
    // CEP:ASSUMES: literals.len() <= kMaxClauseLiterals; rule_id != kInvalidClauseId unless rule is Condensation.
    // CEP:COST: O(clause term nodes) restandardization plus O(n^2) dedupe.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids; unit/hot/given_clause_test.rs::{condensation_simplifies_given, subsumption_resolution_simplifies_given}.
    // CEP:SECURITY: none.
    pub fn record(
        &mut self,
        context: &InferenceContext<'_>,
        literals: &[Literal],
        rule_id: u64,
        rule: InferenceRule,
    ) -> Result<(), SearchError> {
        if self.count >= self.steps.len() {
            // Unreachable by the one-recorded-simplification-per-round invariant;
            // a partial chain would be silently unverifiable, so the failure is
            // loud instead.
            return Err(SearchError::Clause(
                crate::ir::clause::ClauseError::TooManyLiterals,
            ));
        }
        let recorded = matches!(
            rule,
            InferenceRule::Demodulation
                | InferenceRule::SubsumptionResolution
                | InferenceRule::Condensation
        );
        let rule_id_ok = rule == InferenceRule::Condensation || rule_id != kInvalidClauseId;
        if !recorded || !rule_id_ok {
            return Err(SearchError::Clause(
                crate::ir::clause::ClauseError::TooManyLiterals,
            ));
        }
        let slot = self.count;
        let step = &mut self.steps[slot];
        for (target, source) in step.literals.iter_mut().zip(literals.iter()) {
            *target = *source;
        }
        let count = literals.len();
        crate::inference::restandardize_clause(
            context.terms,
            context.symbols,
            &mut step.literals[..count],
        )
        .map_err(SearchError::Inference)?;
        // Dedupe (the loop's dedupe_literals semantics: drop exact (atom, polarity) repeats).
        let mut write: usize = 0;
        for read in 0..count {
            let duplicate = (0..write).any(|kept| {
                step.literals[kept].atom() == step.literals[read].atom()
                    && step.literals[kept].is_positive() == step.literals[read].is_positive()
            });
            if !duplicate {
                step.literals[write] = step.literals[read];
                write += 1;
            }
        }
        step.count = write as u16;
        step.rule_id = rule_id;
        step.rule = rule;
        self.count += 1;
        Ok(())
    }
}

// CEP:WHAT: Result of simplifying one given clause in the loop's buffer.
// CEP:WHY: A vocabulary type: Discarded (tautology) ends the round, Kept continues with the buffer's (possibly rewritten) literals.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{tautologies_discarded, demodulation_simplifies}.
// CEP:SECURITY: none.
enum SimplifyStatus {
    /// CEP:WHAT: The clause is redundant (tautology); discard it.
    /// CEP:WHY: Design 10.4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::tautologies_discarded.
    /// CEP:SECURITY: none.
    Discarded,
    /// CEP:WHAT: The clause survives (rewritten or unchanged) in the buffer.
    /// CEP:WHY: The loop continues with it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the buffer holds literal_count literals.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_simplifies.
    /// CEP:SECURITY: none.
    Kept,
}

// CEP:WHAT: Result of draining the generation buffer.
// CEP:WHY: The empty conclusion is the refutation and must surface immediately (not through a passive round-trip); a passive-capacity failure is a loud give-up.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, passive_overflow_stops}.
// CEP:SECURITY: none.
enum DrainStatus {
    /// CEP:WHAT: All buffered conclusions became passive clauses.
    /// CEP:WHY: The normal path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    Drained,
    /// CEP:WHAT: The buffer contained the empty clause; the payload is its record offset.
    /// CEP:WHY: Immediate refutation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the record exists.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
    /// CEP:SECURITY: none.
    EmptyClause(u32),
    /// CEP:WHAT: The passive set cannot take the buffered conclusions.
    /// CEP:WHY: Loud give-up (dropping buffered conclusions silently would corrupt the search).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    /// CEP:SECURITY: memory bound.
    PassiveFull,
}

// CEP:WHAT: Reads one clause's literals into the loop's fixed buffer; returns the literal count.
// CEP:WHY: The loop and generator consume literal slices; one reader keeps the inline/overflow split hidden (design 5.3) and the no_std discipline intact (no Vec).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError on unreadable records.
// CEP:ASSUMES: offset is store-produced; the buffer holds kMaxClauseLiterals slots.
// CEP:COST: O(literals).
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, resolution_fires}.
// CEP:SECURITY: bounds-checked.
fn read_given_into(
    space: &SearchSpace<'_>,
    offset: u32,
    buffer: &mut [Literal; kMaxClauseLiterals as usize],
) -> Result<usize, SearchError> {
    let clause = space
        .store
        .clause(crate::ir::clause::ClausePtr::from_u32(offset))
        .map_err(SearchError::Clause)?;
    let count = clause.literal_count as usize;
    if count > buffer.len() {
        return Err(SearchError::Clause(
            crate::ir::clause::ClauseError::TooManyLiterals,
        ));
    }
    for position in 0..clause.literal_count {
        buffer[position as usize] = space
            .store
            .literal(clause, position)
            .map_err(SearchError::Clause)?;
    }
    Ok(count)
}

// CEP:WHAT: Returns whether the stored record's literals equal the given literal slice.
// CEP:WHY: Decides between activating the stored record and creating a demodulant record.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError.
// CEP:ASSUMES: none.
// CEP:COST: O(literals).
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_simplifies.
// CEP:SECURITY: bounds-checked.
fn given_is_stored(
    space: &SearchSpace<'_>,
    offset: u32,
    literals: &[Literal],
) -> Result<bool, SearchError> {
    let clause = space
        .store
        .clause(crate::ir::clause::ClausePtr::from_u32(offset))
        .map_err(SearchError::Clause)?;
    if clause.literal_count as usize != literals.len() {
        return Ok(false);
    }
    for position in 0..clause.literal_count {
        let stored = space
            .store
            .literal(clause, position)
            .map_err(SearchError::Clause)?;
        if stored.atom() != literals[position as usize].atom()
            || stored.is_positive() != literals[position as usize].is_positive()
        {
            return Ok(false);
        }
    }
    Ok(true)
}

// CEP:WHAT: Simplifies the given clause in place: tautology deletion, then bounded rounds of demodulation against the active unit equations, condensation (CEP-1034), and subsumption resolution against the active set (CEP-1034).
// CEP:WHY: Design 10.3 step 1 with the CEP-1034 rows: a demodulation rewrite or a condensation/subsumption-resolution deletion recomputes the literal flags (with the configured selection function) because the surviving atoms carry new maximalities; every recorded simplification stores a chain step (with the simplifying rule clause's id and kind) so the park point can store the exact per-step derivation the kernel replays; the round count bounds the whole pass (kMaxSimplifyRounds).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; the substitution trail is unwound per rewrite.
// CEP:ASSUMES: literal_count >= 1 on entry; given_id is the given clause's store id (the condensation step's own parent).
// CEP:COST: O(rounds x (rules x positions + active x SR decision)), rounds bounded by kMaxSimplifyRounds; the SR scan runs behind the head-symbol prefilter and the attempt budget.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{tautologies_discarded, demodulation_simplifies, condensation_simplifies_given, subsumption_resolution_simplifies_given}.
// CEP:SECURITY: rounds bounded; the SR decision is attempt-bounded (kMaxSrMatchAttempts).
#[allow(clippy::too_many_arguments)]
fn simplify_given(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    given_id: u64,
    given: &mut [Literal; kMaxClauseLiterals as usize],
    literal_count: &mut usize,
    stats: &mut SearchStats,
    steps: &mut SimplificationSteps,
) -> Result<SimplifyStatus, SearchError> {
    if is_tautology(&given[..*literal_count]) {
        stats.tautologies += 1;
        return Ok(SimplifyStatus::Discarded);
    }
    let mut rewritten: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    for _round in 0..kMaxSimplifyRounds {
        let mut changed = false;
        let mut literal_index: usize = 0;
        while literal_index < *literal_count {
            let atom = given[literal_index].atom();
            let mut path: [u16; crate::inference::superposition::kMaxPathLength] =
                [0; crate::inference::superposition::kMaxPathLength];
            let mut path_len: u32 = 0;
            // Enter the literal at its first non-root position: rewriting
            // targets subterm positions (the atom root is never rewritten;
            // an atom without subterm positions has no demodulation site).
            if !crate::search::generate::advance_path(context.terms, atom, &mut path, &mut path_len)
            {
                literal_index += 1;
                continue;
            }
            while let Some(target) = crate::inference::superposition::subterm_at_public(
                context.terms,
                atom,
                &path[..path_len as usize],
            ) {
                // Query the rule tree with the subterm; unit rules only. The
                // payload buffer is bounded by kDemodulationPayloads: a
                // BufferTooSmall answer means more unit rules matched than the
                // buffer holds - the visible prefix is tried and the overflow
                // is COUNTED as a drop (Law 4: bounded drops are never
                // silent; the next simplify round retries with the rewritten
                // clause and typically reaches the rest).
                let mut payloads: [u64; kDemodulationPayloads] = [0; kDemodulationPayloads];
                let retrieved =
                    match space
                        .active
                        .rule_tree()
                        .retrieve(context.terms, target, &mut payloads)
                    {
                        Ok(value) => value,
                        Err(crate::index::IndexError::BufferTooSmall) => {
                            stats.dropped += 1;
                            payloads.len()
                        }
                        Err(error) => return Err(SearchError::Index(error)),
                    };
                let mut applied = false;
                for payload in payloads[..retrieved.min(payloads.len())].iter() {
                    let (offset, literal_position, unit) =
                        crate::search::active::unpack_payload(*payload);
                    if !unit {
                        continue;
                    }
                    let clause = match space
                        .store
                        .clause(crate::ir::clause::ClausePtr::from_u32(offset))
                    {
                        Ok(value) => value,
                        Err(_) => continue,
                    };
                    if literal_position >= clause.literal_count {
                        continue;
                    }
                    let rule_literal = match space.store.literal(clause, literal_position) {
                        Ok(value) => value,
                        Err(_) => continue,
                    };
                    let (rule_left, rule_right) = match unit_equation_sides(context, rule_literal) {
                        Some(value) => value,
                        None => continue,
                    };
                    let outcome = demodulate(
                        context,
                        &given[..*literal_count],
                        literal_index,
                        &path[..path_len as usize],
                        rule_left,
                        rule_right,
                        &mut rewritten,
                    )
                    .map_err(SearchError::Inference)?;
                    if let crate::inference::demodulation::DemodulationOutcome::Rewritten(count) =
                        outcome
                    {
                        given[..count].copy_from_slice(&rewritten[..count]);
                        compute_selection_flags(context, options.selection, &mut given[..count])
                            .map_err(SearchError::Inference)?;
                        // CEP-1036: record the rewrite snapshot (restandardized +
                        // deduped, with the rule clause's id) so the park point can
                        // store the exact per-step chain the kernel replays.
                        steps.record(
                            context,
                            &given[..count],
                            clause.id.0,
                            InferenceRule::Demodulation,
                        )?;
                        stats.demodulations += 1;
                        changed = true;
                        applied = true;
                        break;
                    }
                }
                if applied {
                    break;
                }
                if !crate::search::generate::advance_path(
                    context.terms,
                    atom,
                    &mut path,
                    &mut path_len,
                ) {
                    break;
                }
            }
            if changed {
                break;
            }
            literal_index += 1;
        }
        if !changed {
            // CEP-1034: with no demodulation site left, try condensation (the
            // clause against itself) and then subsumption resolution (an active
            // clause deleting one literal); a fired attempt keeps the round
            // going so the shorter clause demodulates further within the same
            // budget.
            let condensed = simplify_attempt_condensation(
                space,
                context,
                options,
                given_id,
                given,
                literal_count,
                stats,
                steps,
            )?;
            let resolved = if condensed {
                false
            } else {
                simplify_attempt_subsumption_resolution(
                    space,
                    context,
                    options,
                    given,
                    literal_count,
                    stats,
                    steps,
                )?
            };
            if !(condensed || resolved) {
                break;
            }
        }
        if is_tautology(&given[..*literal_count]) {
            stats.tautologies += 1;
            return Ok(SimplifyStatus::Discarded);
        }
    }
    Ok(SimplifyStatus::Kept)
}

// CEP:WHAT: The reserved head class of equality atoms in the SR prefilter (CEP-1034).
// CEP:WHY: The prefilter compares head classes; the equality pseudo-head (design 8.3: comparable with every predicate head) is its own class and must not collide with a real symbol id - real ids are bounded far below u32::MAX by kMaxSymbolCount.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kMaxSymbolCount < u32::MAX (static-asserted in config/limits.rs).
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs::sr_head_prefilter_soundness.
// CEP:SECURITY: none.
const kSrEqualityHead: u32 = u32::MAX;

// CEP:WHAT: Head-symbol class of one atom: the predicate symbol, the equality class for equality atoms, None for unreadable or variable atoms (the prefilter disables itself rather than guessing).
// CEP:WHY: A sound necessary condition bounds both the condensation attempt and the SR scan: a sigma-match between two literals keeps the head class (substitution changes arguments, never the head), so a condensation needs an opposite-polarity same-head pair inside the clause and an SR side literal's head must occur in the main premise.
// CEP:STATUS: complete
// CEP:FAILURE: None on an unreadable atom - callers degrade to the unfiltered path, never to a wrong rejection of a legal inference... (the condensation prefilter's None means "skip the attempt": the pair scan cannot prove a candidate exists; the SR prefilter's None disables the filter for the whole scan, which keeps every legal SR reachable).
// CEP:ASSUMES: atoms interned by the store.
// CEP:COST: one term view.
// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs::sr_head_prefilter_soundness.
// CEP:SECURITY: bounds-checked reads.
fn head_class(terms: &TermStore<'_>, atom: crate::ir::term::TermPtr) -> Option<u32> {
    let view = terms.term(atom).ok()?;
    match view.tag() {
        crate::ir::term::TermTag::Equality => Some(kSrEqualityHead),
        crate::ir::term::TermTag::Variable => None,
        _ => Some(view.symbol()),
    }
}

// CEP:WHAT: Whether the clause contains two literals whose atoms share the head class (the condensation prefilter, CEP-1034).
// CEP:WHY: Condensation (the Bachmair-Ganzinger instance condition, Spec 07 section 12) needs some clause literal to be a sigma-instance of another kept literal - sigma preserves the head, so a repeated head class inside the clause is a necessary condition; the pair scan is capped at the first 32 literals (sound truncation: clauses beyond the cap skip the prefilter and run the bounded decision directly); without a repeated head the bounded decision cannot fire and the attempt is skipped (a pure scan-bound win).
// CEP:STATUS: complete
// CEP:FAILURE: false only when no repeated head exists in the scanned window (the attempt is skipped, never a wrong simplification).
// CEP:ASSUMES: atoms interned; unreadable or variable atoms disable the prefilter (returns true conservatively).
// CEP:COST: O(min(n, 32)^2) head comparisons.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::condensation_simplifies_given; unit/hot/subsumption_resolution_test.rs::condensation_keeps_unmatched_clause.
// CEP:SECURITY: none.
fn has_repeated_head_pair(context: &InferenceContext<'_>, literals: &[Literal]) -> bool {
    const kCondensationScanLiterals: usize = 32;
    let scanned = literals.len().min(kCondensationScanLiterals);
    let mut heads: [Option<u32>; kCondensationScanLiterals] = [None; kCondensationScanLiterals];
    for (index, literal) in literals[..scanned].iter().enumerate() {
        heads[index] = head_class(context.terms, literal.atom());
    }
    for i in 0..scanned {
        for j in (i + 1)..scanned {
            let (left, right) = (heads[i], heads[j]);
            if left.is_none() || right.is_none() {
                // Unreadable or variable head: keep the decision reachable.
                return true;
            }
            if left == right {
                return true;
            }
        }
    }
    false
}

// CEP:WHAT: One condensation attempt against the given clause (CEP-1034): removes the first self-subsumption-resolution literal, records the chain step, and recounts.
// CEP:WHY: Design 10.1 condensation as a given-time simplification: the clause condenses to C \ {m'} when the self-SR conditions hold (Spec 07 section 12), which strictly strengthens it; the live buffer keeps its namespace (the rule is renaming-invariant) and the recorded snapshot is restandardized at record time for the kernel's per-step replay; the attempt runs behind the head-pair prefilter so the bounded decision only executes when a candidate pair exists.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; Ok(false) when condensation does not apply.
// CEP:ASSUMES: literal_count >= 2 for a fire (condensation_target rejects shorter clauses); the caller re-checks the empty-clause outcome after simplify.
// CEP:COST: the prefilter scan plus (when it passes) the attempt-bounded decision plus O(n) removal.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::condensation_simplifies_given; unit/cold/kernel_test.rs::condensation_replay_accepts_recorded_step.
// CEP:SECURITY: attempt-bounded.
#[allow(clippy::too_many_arguments)]
fn simplify_attempt_condensation(
    _space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    given_id: u64,
    given: &mut [Literal; kMaxClauseLiterals as usize],
    literal_count: &mut usize,
    stats: &mut SearchStats,
    steps: &mut SimplificationSteps,
) -> Result<bool, SearchError> {
    if *literal_count < 2 || !has_repeated_head_pair(context, &given[..*literal_count]) {
        return Ok(false);
    }
    let target =
        condensation_target(context, &given[..*literal_count]).map_err(SearchError::Inference)?;
    let position = match target {
        Some(value) => value,
        None => return Ok(false),
    };
    // Remove the resolution literal by compaction; the buffer keeps its own
    // namespace (removal may leave variable gaps - renaming-invariant for the
    // remaining in-buffer work, and the recorded snapshot is restandardized).
    let new_count = *literal_count - 1;
    for index in position..new_count {
        given[index] = given[index + 1];
    }
    compute_selection_flags(context, options.selection, &mut given[..new_count])
        .map_err(SearchError::Inference)?;
    *literal_count = new_count;
    stats.condensations += 1;
    steps.record(
        context,
        &given[..new_count],
        given_id,
        InferenceRule::Condensation,
    )?;
    Ok(true)
}

// CEP:WHAT: One subsumption-resolution pass over the active set (CEP-1034): the first active clause that subsumption-resolves the given clause deletes its resolution literal from the given clause.
// CEP:WHY: Design 10.1's subsumption resolution as given-time forward simplification (Riazanov 2003): the renamed active clause is the side premise, the given clause the main premise, and the deleted literal is the resolution literal; the scan cannot use the feature-vector dominance filter (the set-inclusion condition allows two side literals to map onto one main literal - the paper's S5 shape - which violates symbol-count dominance), so it runs behind a SOUND head-symbol prefilter instead: every side literal sigma-equals an exact main literal, so its head occurs in the main premise (clauses with more distinct head symbols than kSrHeadSymbols disable the prefilter - documented sound degradation); the decision itself is attempt-bounded (kMaxSrMatchAttempts).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; Ok(false) when no active clause subsumption-resolves the given clause.
// CEP:ASSUMES: the given clause is non-empty and not yet active; active slots are the frozen candidate source (the loop's invariant I4).
// CEP:COST: O(active) prefiltered scans plus one attempt-bounded decision per surviving candidate.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::subsumption_resolution_simplifies_given; unit/hot/subsumption_resolution_test.rs::sr_head_prefilter_soundness; unit/cold/kernel_test.rs::subsumption_resolution_replay_accepts_recorded_step.
// CEP:SECURITY: attempt-bounded; bounded by the active capacity.
#[allow(clippy::too_many_arguments)]
fn simplify_attempt_subsumption_resolution(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    given: &mut [Literal; kMaxClauseLiterals as usize],
    literal_count: &mut usize,
    stats: &mut SearchStats,
    steps: &mut SimplificationSteps,
) -> Result<bool, SearchError> {
    // The main premise's head-symbol set (bounded; overflow or an unreadable
    // head disables the prefilter for the whole scan).
    let mut heads: [u32; kSrHeadSymbols] = [0; kSrHeadSymbols];
    let mut head_count: usize = 0;
    let mut prefilter = true;
    for literal in given[..*literal_count].iter() {
        match head_class(context.terms, literal.atom()) {
            Some(head) => {
                if !heads[..head_count].contains(&head) {
                    if head_count < heads.len() {
                        heads[head_count] = head;
                        head_count += 1;
                    } else {
                        prefilter = false;
                        break;
                    }
                }
            }
            None => {
                prefilter = false;
                break;
            }
        }
    }
    let mut premise: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let mut raw: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let given_variables =
        crate::inference::count_clause_variables(context.terms, &given[..*literal_count])
            .map_err(SearchError::Inference)?;
    for slot_index in 0..space.active.len() {
        let slot = match space.active.slot(slot_index) {
            Some(value) => value,
            None => break,
        };
        let clause = match space.store.clause(ClausePtr::from_u32(slot.offset)) {
            Ok(value) => value,
            Err(_) => continue,
        };
        // Size guard: |side| <= |main| is a necessary SR condition.
        if clause.literal_count as usize > *literal_count {
            continue;
        }
        let mut side_ok = true;
        for position in 0..clause.literal_count {
            let literal = match space.store.literal(clause, position) {
                Ok(value) => value,
                Err(_) => {
                    side_ok = false;
                    break;
                }
            };
            if prefilter {
                match head_class(context.terms, literal.atom()) {
                    Some(head) if heads[..head_count].contains(&head) => {}
                    _ => {
                        side_ok = false;
                        break;
                    }
                }
            }
        }
        if !side_ok {
            continue;
        }
        for position in 0..clause.literal_count {
            match space.store.literal(clause, position) {
                Ok(value) => raw[position as usize] = value,
                Err(_) => {
                    return Err(SearchError::Clause(
                        crate::ir::clause::ClauseError::InvalidPointer,
                    ))
                }
            }
        }
        let renamed = crate::inference::rename_clause_apart(
            context.terms,
            context.symbols,
            &raw[..clause.literal_count as usize],
            given_variables as u32,
            &mut premise,
        );
        let premise_len = match renamed {
            Ok(_) => clause.literal_count as usize,
            Err(_) => continue,
        };
        let target =
            subsumption_resolves(context, &premise[..premise_len], &given[..*literal_count])
                .map_err(SearchError::Inference)?;
        if let Some(resolution) = target {
            let new_count = *literal_count - 1;
            for index in resolution..new_count {
                given[index] = given[index + 1];
            }
            // A unit SR against a unit disequation leaves the empty clause:
            // skip flag computation like every empty record (the loop's
            // post-simplify re-check takes the chain path).
            if new_count > 0 {
                compute_selection_flags(context, options.selection, &mut given[..new_count])
                    .map_err(SearchError::Inference)?;
            }
            *literal_count = new_count;
            stats.subsumption_resolutions += 1;
            steps.record(
                context,
                &given[..new_count],
                clause.id.0,
                InferenceRule::SubsumptionResolution,
            )?;
            return Ok(true);
        }
    }
    Ok(false)
}

// CEP:WHAT: Checks whether any active clause subsumes the given clause (forward subsumption) by an FV-filtered active scan.
// CEP:WHY: Design 10.3 step 1-2 and design 9.3's two-tier flow: the feature-vector filter (may_subsume) is the cheap first tier, and the matching-based subsumption check decides; the atom tree's flat-length retrieval cannot serve as the candidate tier (a stored p(x) is invisible to the query p(f(a)) although the former subsumes the latter - the tree is maintained for its documented index role and future iterator work, ticket CEP-1027), so the scan is the candidate source; the ACTIVE candidate is renamed into the given clause's variable window before the check.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError.
// CEP:ASSUMES: the given clause is non-empty.
// CEP:COST: O(active x subsumption check) with the FV filter pruning.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::forward_subsumption_discards; unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
// CEP:SECURITY: bounded by the active capacity.
fn forward_subsumed(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    given: &[Literal],
) -> Result<bool, SearchError> {
    let given_vector = space
        .active
        .features()
        .build(context.terms, given)
        .map_err(|error| SearchError::Active(ActiveError::Features(error)))?;
    let mut premise: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let mut raw: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let given_variables = crate::inference::count_clause_variables(context.terms, given)
        .map_err(SearchError::Inference)?;
    for slot_index in 0..space.active.len() {
        let slot = match space.active.slot(slot_index) {
            Some(value) => value,
            None => break,
        };
        if !space
            .active
            .features()
            .may_subsume(slot.features, given_vector)
        {
            continue;
        }
        let clause = match space
            .store
            .clause(crate::ir::clause::ClausePtr::from_u32(slot.offset))
        {
            Ok(value) => value,
            Err(_) => continue,
        };
        if clause.literal_count as usize > raw.len() {
            continue;
        }
        for position in 0..clause.literal_count {
            match space.store.literal(clause, position) {
                Ok(value) => raw[position as usize] = value,
                Err(_) => {
                    return Err(SearchError::Clause(
                        crate::ir::clause::ClauseError::InvalidPointer,
                    ))
                }
            }
        }
        let renamed = crate::inference::rename_clause_apart(
            context.terms,
            context.symbols,
            &raw[..clause.literal_count as usize],
            given_variables as u32,
            &mut premise,
        );
        let premise_len = match renamed {
            Ok(_) => clause.literal_count as usize,
            Err(_) => continue,
        };
        if subsumes(context, &premise[..premise_len], given).map_err(SearchError::Inference)? {
            return Ok(true);
        }
    }
    Ok(false)
}

// CEP:WHAT: Removes every active clause the given clause subsumes (backward subsumption).
// CEP:WHY: Design 10.1 backward subsumption; the given clause subsumes the active clause, so the ACTIVE side is renamed into the given's window; removal is by slot with swap-remove (the scan re-reads the moved entry by not advancing after a removal).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError.
// CEP:ASSUMES: the given clause is non-empty and not yet active.
// CEP:COST: O(active x subsumption check).
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::backward_subsumption_removes.
// CEP:SECURITY: bounded by the active capacity.
fn backward_subsume(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    given: &[Literal],
    stats: &mut SearchStats,
) -> Result<(), SearchError> {
    let given_vector = space
        .active
        .features()
        .build(context.terms, given)
        .map_err(|error| SearchError::Active(ActiveError::Features(error)))?;
    let mut premise: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let mut raw: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    let mut slot_index: u32 = 0;
    while slot_index < space.active.len() {
        let slot = match space.active.slot(slot_index) {
            Some(value) => value,
            None => break,
        };
        if !space
            .active
            .features()
            .may_subsume(given_vector, slot.features)
        {
            slot_index += 1;
            continue;
        }
        let clause = match space
            .store
            .clause(crate::ir::clause::ClausePtr::from_u32(slot.offset))
        {
            Ok(value) => value,
            Err(_) => {
                slot_index += 1;
                continue;
            }
        };
        if clause.literal_count as usize > raw.len() {
            slot_index += 1;
            continue;
        }
        for position in 0..clause.literal_count {
            match space.store.literal(clause, position) {
                Ok(value) => raw[position as usize] = value,
                Err(_) => {
                    slot_index += 1;
                    continue;
                }
            }
        }
        let given_variables = crate::inference::count_clause_variables(context.terms, given)
            .map_err(SearchError::Inference)?;
        let renamed = crate::inference::rename_clause_apart(
            context.terms,
            context.symbols,
            &raw[..clause.literal_count as usize],
            given_variables as u32,
            &mut premise,
        );
        let premise_len = match renamed {
            Ok(_) => clause.literal_count as usize,
            Err(_) => {
                slot_index += 1;
                continue;
            }
        };
        if subsumes(context, given, &premise[..premise_len]).map_err(SearchError::Inference)? {
            space
                .active
                .remove(context.terms, &space.store, slot_index)?;
            stats.backward_subsumed += 1;
            // The last slot moved into slot_index: do not advance (re-examine it).
            continue;
        }
        slot_index += 1;
    }
    Ok(())
}

// CEP:WHAT: Drains the generation buffer into the passive set (creating clause records with derivation steps).
// CEP:WHY: Design 15.1 step 6; tautologies are dropped (counted), the empty conclusion surfaces immediately as the refutation, and a passive-capacity failure is a loud give-up because dropping buffered conclusions silently would corrupt the search accounting.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(PassiveFull) on passive overflow; propagates other SearchErrors.
// CEP:ASSUMES: the buffered conclusions' literals are interned.
// CEP:COST: one store insert and one heap push per conclusion.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, inference_deferral_resumes, passive_overflow_stops, refutes_contradiction}.
// CEP:SECURITY: store bounds enforced.
fn drain_buffer(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    buffer: &InferenceBuffer,
    stats: &mut SearchStats,
) -> Result<DrainStatus, SearchError> {
    for entry in buffer.clauses[..buffer.count].iter() {
        let literals = &entry.literals[..entry.count as usize];
        if is_tautology(literals) {
            stats.tautologies += 1;
            stats.dropped += 1;
            continue;
        }
        if literals.is_empty() {
            // The empty conclusion: create the record and surface the refutation.
            let age = space.input_age.get();
            space.input_age.set(age + 1);
            let derivation = DerivationStep {
                rule: entry.rule,
                parent_count: if entry.parents[1] == kInvalidClauseId {
                    kUnaryRuleParents
                } else {
                    kBinaryRuleParents
                },
                reserved: 0,
                parents: [
                    entry.parents[0],
                    entry.parents[1],
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            };
            let (rule, parents, parent_count) =
                (derivation.rule, derivation.parents, derivation.parent_count);
            let ptr = space
                .store
                .new_clause(context.terms, &[], age, derivation)
                .map_err(SearchError::Clause)?;
            space.mark_sos(options, ptr, rule, &parents, parent_count)?;
            return Ok(DrainStatus::EmptyClause(ptr.as_u32()));
        }
        let mut staged: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        if literals.len() > staged.len() {
            stats.dropped += 1;
            continue;
        }
        for (index, literal) in literals.iter().enumerate() {
            staged[index] = *literal;
        }
        // Restandardize the conclusion into a dense variable namespace before
        // storage (Spec 07 section 2: the shared namespace may have gaps), then
        // drop duplicate literals (design 7.2 stage 10: resolution conclusions
        // routinely repeat a literal when both premises carry the same survivor).
        crate::inference::restandardize_clause(
            context.terms,
            context.symbols,
            &mut staged[..literals.len()],
        )
        .map_err(SearchError::Inference)?;
        let deduped = dedupe_literals(&mut staged[..literals.len()]);
        if deduped > 0 {
            compute_selection_flags(context, options.selection, &mut staged[..deduped])
                .map_err(SearchError::Inference)?;
        }
        let weight = SelectionWeight::of(context.terms, context.symbols, &staged[..deduped]);
        let age = space.input_age.get();
        space.input_age.set(age + 1);
        let derivation = DerivationStep {
            rule: entry.rule,
            parent_count: if entry.parents[1] == kInvalidClauseId {
                kUnaryRuleParents
            } else {
                kBinaryRuleParents
            },
            reserved: 0,
            parents: [
                entry.parents[0],
                entry.parents[1],
                kInvalidClauseId,
                kInvalidClauseId,
            ],
            substitution: kInvalidSubstitutionOffset,
        };
        let (rule, parents, parent_count) =
            (derivation.rule, derivation.parents, derivation.parent_count);
        let ptr = space
            .store
            .new_clause(context.terms, &staged[..deduped], age, derivation)
            .map_err(SearchError::Clause)?;
        space.mark_sos(options, ptr, rule, &parents, parent_count)?;
        let record = space.store.clause(ptr).map_err(SearchError::Clause)?;
        if space
            .push_passive(
                context,
                options,
                record.id.0,
                ptr,
                age,
                weight,
                &staged[..deduped],
            )
            .is_err()
        {
            return Ok(DrainStatus::PassiveFull);
        }
    }
    Ok(DrainStatus::Drained)
}

/// CEP:WHAT: Test probe for the forward-subsumption path (wraps forward_subsumed); pub because the integration tests live outside the crate, never called by production code.
/// CEP:WHY: The loop-internal helper is private; the database tests verify the filtered path (feature filter then matching) in isolation through this thin, documented projection - the loop-level behavior is covered by given_clause_test's forward_subsumption_discards; an internal SearchError is converted to false (the probe answers a yes/no question and the loop's own path surfaces the error loudly - the production forward_subsumed call has no such swallowing).
/// CEP:STATUS: complete
/// CEP:FAILURE: false on an internal error (test-surface behavior; production callers get the Err).
/// CEP:ASSUMES: the given clause is non-empty.
/// CEP:COST: as forward_subsumed.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
/// CEP:SECURITY: none.
pub fn saturate_probe_forward(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    given: &[Literal],
) -> bool {
    forward_subsumed(space, context, given).unwrap_or(false)
}
