// CEP:FILE: hot/search/given_clause.rs
// CEP:WHAT: The given-clause saturation loop (design 15.1) with the clause database (design 8.4), the selection weight function (design 15.3), simplification (demodulation, forward subsumption, tautology deletion - design 10.3 step 1), backward subsumption, bounded inference generation, and the design 20 budgets (CEP-1005).
// CEP:WHY: Design 26 Phase 3 build order: the loop is the ATP search - select from the passive set, move to the active set, simplify against the active set, discard the redundant, generate all inferences between the given clause and the active set, add the conclusions to the passive set, and terminate with Theorem on the empty clause, Saturated on an empty passive set, or GaveUp on a budget; the loop step order is fixed (select, simplify, forward-subsume, backward-subsume, activate, generate) so the active array never mutates during one given clause's generation (the generator's slot scan stays consistent); fairness follows from the strategy's priority function (Spec 08 section 4); the time budget is an injected should_stop callback checked every kBudgetCheckInterval iterations, which keeps the hot crate clock-free (the CEP-1 driver supplies wall time; tests supply deterministic stop predicates - the mechanism is what CEP-1005 demands); CounterSatisfiable needs model building (design 17, Phase 5) and Saturated is the honest Phase 3 terminal for satisfiable inputs.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns Result<SearchOutcome, SearchError>: capacity and structural failures surface loudly; GaveUp carries the budget reason; never panics.
// CEP:ASSUMES: One search space per arena; input clauses are added through add_input_clause (which computes flags and weights); the injected stop callback is pure w.r.t. its iteration counter (no hidden state).
// CEP:COST: per iteration: one passive pop O(log n), simplification (bounded demodulation rounds, FV-filtered subsumption), one active insertion, and generation steps (measured in bench CEP-BENCH-0010/0011); the loop is allocation-free after construction.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force, loop_refutes_pigeonhole}; fuzz/given_clause_fuzz_test.rs.
// CEP:SECURITY: every budget is enforced (inference count, clause budget, arena, capacities, injected time); the loop cannot run unbounded without the callback firing.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic for a fixed stop callback: selection, simplification, and generation are pure functions of the state; unit/hot/given_clause_test.rs::generation_is_deterministic and property/given_clause_property_test.rs::selection_is_deterministic verify the two-run discipline (identical conclusions and identical selection sequences on fresh double runs).
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 7 fixes the loop contract: the empty clause is derived only by sound inferences (Theorem is trustworthy), Saturated means every selected clause had all its budgeted inferences computed (fairness per the strategy's priority argument), and every GaveUp reason names its budget; the property tests verify the loop against the SAT solver and brute force on propositional problems.

use crate::inference::demodulation::{demodulate, unit_equation_sides};
use crate::inference::selection::compute_selection_flags;
use crate::inference::subsumption::{is_tautology, subsumes};
use crate::inference::{InferenceContext, SelectionFunction};
use crate::ir::clause::{ClauseStore, DerivationStep, InferenceRule};
use crate::ir::literal::Literal;
use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::TermStore;
use crate::memory::arena::Arena;
use crate::search::active::{ActiveError, ActiveSet};
use crate::search::generate::{generate_step, GenerationCursor, InferenceBuffer};
use crate::search::passive::{PassiveHeap, SelectionStrategy};
use crate::search::SearchError;
use crate::unification::substitution::Substitution;
use mapt_config::limits::{
    kBudgetCheckInterval, kConjectureHarvestInterval, kDefaultSymbolWeight, kInvalidClauseId,
    kInvalidSubstitutionOffset, kMaxClauseLiterals, kMaxConjectureHarvests, kMaxDerivationParents,
    kMaxInferences, kMaxSimplifyRounds, kSelectionVariableWeight,
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
}

impl SearchOptions {
    // CEP:WHAT: Production defaults.
    // CEP:WHY: One named place for the default configuration (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}.
    // CEP:SECURITY: none.
    pub fn new() -> SearchOptions {
        SearchOptions {
            strategy: SelectionStrategy::AgeWeightRatio,
            ordering: crate::inference::OrderingKind::Kbo,
            selection: SelectionFunction::None,
            inference_budget: kMaxInferences,
            conjecture: false,
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
    // CEP:WHAT: Computes the selection weight of one clause.
    // CEP:WHY: Design 15.3 with the default weights.
    // CEP:STATUS: complete
    // CEP:FAILURE: saturating add (see type header).
    // CEP:ASSUMES: literals interned by the store.
    // CEP:COST: O(total term nodes).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{selection_weight_counts_symbols, selection_weight_ignores_variables}.
    // CEP:SECURITY: depth-bounded.
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
}

impl<'a> SearchSpace<'a> {
    // CEP:WHAT: Constructs the search space with production capacities.
    // CEP:WHY: Production entry point; the capacities are the named constants.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns SearchError on capacity exhaustion.
    // CEP:ASSUMES: the arena has room (slot, tree, and pool arrays; about 120 MiB at maximum caps).
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}.
    // CEP:SECURITY: capacities validated before allocation.
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

    // CEP:WHAT: Constructs the search space with explicit capacities.
    // CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production path; Phase 4 adds the clause-id side-table capacity so proof reconstruction and AVATAR ancestry can resolve parent ids on the production space while tests inject small tables.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns SearchError on exhaustion.
    // CEP:ASSUMES: capacities >= 1.
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops; security/phase3_bounds_test.rs::{passive_capacity_enforced, active_capacity_enforced}; unit/hot/clause_test.rs::side_table_capacity_enforced.
    // CEP:SECURITY: bounds validated.
    // CEP:WHAT: Clippy allowance for the eight explicit capacities (one per bounded substructure).
    // CEP:WHY: CEP&CC 34.3 requires every capacity injectable on the production path; an options struct would hide which test uses which bound, so the parameter list is the documented interface.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: compile-time only.
    // CEP:EVIDENCE: security/phase3_bounds_test.rs; security/phase4_bounds_test.rs.
    // CEP:SECURITY: none.
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
        })
    }

    // CEP:WHAT: Adds one input clause: computes the selection flags, the selection weight, creates the record with the Input derivation, and pushes it into the passive set.
    // CEP:WHY: Design 15.1's initial passive population; the empty input clause is pushed like any other (the loop detects it on pop and returns Theorem).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError (store bounds, flag computation, passive capacity).
    // CEP:ASSUMES: literal atoms were interned by the caller's term store; the caller standardizes each clause's variables to a dense namespace (design 7.2 stage 7 discipline).
    // CEP:COST: O(literals^2) flag comparisons plus the weight walk plus one store insert plus one heap push.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::{refutes_contradiction, saturates_on_satisfiable}; unit/hot/selection_test.rs::{maximality_computed, first_negative_selects}.
    // CEP:SECURITY: store bounds enforced.
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

    // CEP:WHAT: Returns the number of input clauses added.
    // CEP:WHY: Diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction.
    // CEP:SECURITY: none.
    pub fn input_count(&self) -> u32 {
        self.input_age.get()
    }

    // CEP:WHAT: Adds one parentless theory clause (induction scheme) with an explicit rule.
    // CEP:WHY: Revised build order Phase 4 (Spec 15): structural and well-founded induction schemes enter the passive set like inputs but carry their scheme rule so the proof walk and the TSTP writer present them as named theory axioms; the age comes from the shared input counter (the sanctioned allocation point, next_input_age's discipline).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError (store bounds, flag computation, passive capacity).
    // CEP:ASSUMES: literal atoms were interned by the caller's term store; the rule is one of the parentless theory rules (StructuralInduction, WellFoundedInduction).
    // CEP:COST: as add_input_clause (one staging pass, one store insert, one heap push).
    // CEP:EVIDENCE: unit/hot/induction_test.rs::{structural_scheme_clauses_match_clausification, schemes_enter_passive_set}.
    // CEP:SECURITY: store bounds enforced.
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

    // CEP:WHAT: Adds one assumption clause (a conjecture candidate's negation) to this space.
    // CEP:WHY: Spec 16 section 5: the mini-refutation premise must be distinguishable from axioms in the imported proof DAG, so it carries the ConjectureNegation rule; the shape is add_input_clause's with a different derivation label.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError.
    // CEP:ASSUMES: literal atoms were interned by the caller's term store; called on the MINI space by the conjecture filter (the main search never adds assumptions).
    // CEP:COST: as add_input_clause.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, unprovable_candidate_adds_nothing}.
    // CEP:SECURITY: store bounds enforced.
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

    // CEP:WHAT: Creates one proof-DAG clause without entering the passive set.
    // CEP:WHY: Spec 17 section 3: the conjecture import replays a mini refutation into the main store clause by clause; the imported steps are proof-only (they never re-enter the search, or the main loop would saturate on its own lemmas' subproofs); the derivation is taken verbatim with the caller's translated parent ids, so the imported chain is exactly the mini chain.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError (store bounds, flag computation).
    // CEP:ASSUMES: literal atoms were interned by the caller's term store; parent ids are valid main-store ids strictly older than the next id; the age is the mini clause's age.
    // CEP:COST: one staging pass plus one store insert.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    // CEP:SECURITY: store bounds enforced.
    pub fn add_proof_clause(
        &self,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
        age: u32,
        derivation: DerivationStep,
    ) -> Result<u32, SearchError> {
        let (staged, count, _weight) = self.stage_clause(context, options, literals)?;
        let ptr = self
            .store
            .new_clause(context.terms, &staged[..count], age, derivation)
            .map_err(SearchError::Clause)?;
        let id = self.store.clause(ptr).map_err(SearchError::Clause)?.id.0;
        // The import watermark: the first proof-only id. Monotone by the
        // store's dense id counter; every harvest scan stops here.
        if self.proof_base.get() == kInvalidClauseId {
            self.proof_base.set(id);
        }
        Ok(ptr.as_u32())
    }

    // CEP:WHAT: Returns the proof-only watermark: the first imported clause's id, or the next unstaged id when no import has happened.
    // CEP:WHY: The harvest's premise enumeration, unit window, and constructor-instance scan treat every id below this bound as harvest-visible and everything at or above it as import-private (Spec 16 section 3, the Task 26 sev-0 repair); before any import the bound is the next id, so the un-imported space behaves exactly as before.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: called between clause creations (the returned bound is a snapshot; a concurrent creation only lowers what the caller sees, never raises it).
    // CEP:COST: one load plus, before the first import, one next-id read.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::{proof_watermark_bounds_harvest_scans, two_harvests_stay_sound}.
    // CEP:SECURITY: the soundness boundary of the conjecture feature's id-space sharing.
    pub fn proof_base(&self) -> u64 {
        match self.proof_base.get() {
            kInvalidClauseId => self.store.next_clause_id().0,
            bound => bound,
        }
    }

    // CEP:WHAT: Adds one derived clause with an explicit derivation into the passive set.
    // CEP:WHY: Spec 16 section 6: a lemma proved by bounded refutation enters the main search through the normal passive path with the ConjectureLemma derivation (parents: imported negation premise and imported empty clause); the shape is add_input_clause's with the caller's derivation.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError.
    // CEP:ASSUMES: literal atoms were interned by the caller's term store.
    // CEP:COST: as add_input_clause.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, lemma_enters_passive_set}.
    // CEP:SECURITY: store bounds enforced.
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
    // CEP:WHY: The body shared by add_input_clause, add_theory_clause, add_assumption_clause, and add_derived_clause: stage, create with the derivation, push; the age comes from the shared input counter.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError.
    // CEP:ASSUMES: as stage_clause.
    // CEP:COST: stage_clause plus one store insert plus one heap push.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::refutes_contradiction; unit/hot/induction_test.rs::schemes_enter_passive_set.
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
        let ptr = self
            .store
            .new_clause(context.terms, &staged[..deduped], age, derivation)
            .map_err(SearchError::Clause)?;
        let record = self.store.clause(ptr).map_err(SearchError::Clause)?;
        self.passive.push(record.id.0, ptr.as_u32(), age, weight)?;
        Ok(ptr.as_u32())
    }

    // CEP:WHAT: Allocates the next input age (monotonic counter shared by input clauses and AVATAR component materializations).
    // CEP:WHY: Materialized components (design 12.2 rule 3) enter the passive set like inputs and need the same monotone age discipline (design 15.2); the counter stays private to the space, so this is the single sanctioned allocation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: single-threaded space.
    // CEP:COST: 1 load, 1 store.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: none.
    pub fn next_input_age(&self) -> u32 {
        let age = self.input_age.get();
        self.input_age.set(age + 1);
        age
    }
}

// CEP:WHAT: Runs the given-clause loop to a terminal outcome.
// CEP:WHY: Design 15.1 with the Phase 3 bounds: the injected stop callback (checked every kBudgetCheckInterval iterations) is the CEP-1005 time-budget mechanism and stays generic (no dyn, CEP-0 discipline) with the counter as its only input so tests inject deterministic predicates and the CEP-1 driver supplies wall time; the loop's step order (select, simplify, forward-subsume, backward-subsume, activate, generate) keeps the active array stable during one given clause's generation; deferred generation resumes across iterations through the in-progress state; the given clause's literals live in one fixed stack buffer for the whole loop (no allocation, no_std discipline).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError on structural failures; GaveUp on budget exhaustion; never panics.
// CEP:ASSUMES: the context's stores match the space's; the stop callback is deterministic for a fixed counter.
// CEP:COST: see file header; benches CEP-BENCH-0010/0011.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force, loop_refutes_pigeonhole}; fuzz/given_clause_fuzz_test.rs; bench CEP-BENCH-0010, CEP-BENCH-0011.
// CEP:SECURITY: all budgets enforced.
pub fn saturate<F: Fn(u64) -> bool>(
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
    // CEP:WHAT: The demodulation step chain buffer (CEP-1036).
    // CEP:WHY: Cleared per given clause; simplify_given records one snapshot per rewrite and the park point stores one clause record per step so the derivation DAG carries the full rewrite history for the kernel's exact replay (Spec 19).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: consumed in the same iteration it was filled (the park point runs before the next simplify).
    // CEP:COST: kMaxSimplifyRounds step records of stack.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    // CEP:SECURITY: none.
    let mut demod_steps = DemodulationSteps::new();
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
        // Simplify: tautology deletion and bounded demodulation (design 10.3 step 1).
        demod_steps.count = 0;
        match simplify_given(
            space,
            context,
            options,
            &mut given,
            &mut given_len,
            stats,
            &mut demod_steps,
        )? {
            SimplifyStatus::Discarded => {
                stats.given_processed += 1;
                continue;
            }
            SimplifyStatus::Kept => {}
        }
        // Defensive re-check after simplification: demodulation rewrites in
        // place and never removes literals, so a clause that was non-empty at
        // entry stays non-empty here (the empty clause arrives through
        // SimplifyStatus::Discarded's drain path or the entry check above);
        // the guard is kept as defense in depth, deliberately.
        if given_len == 0 {
            return Ok(SearchOutcome::Theorem {
                refutation: given_offset,
            });
        }
        // Forward subsumption: an active clause subsumes the given clause.
        if forward_subsumed(space, context, &given[..given_len])? {
            stats.forward_subsumed += 1;
            stats.given_processed += 1;
            continue;
        }
        // Backward subsumption: the given clause subsumes active clauses.
        backward_subsume(space, context, &given[..given_len], stats)?;
        // Activate the given clause, or park a rewritten demodulant back to passive
        // (the stored record is immutable; a rewritten clause is a new record).
        if demod_steps.count > 0 {
            // CEP:WHAT: The CEP-1036 chain path: one stored clause record per rewrite step.
            // CEP:WHY: Each record's derivation cites parents [previous, rule] (the rule clause's id), so the certified kernel replays demodulation EXACTLY per step over the chain (Spec 19); the last record is the demodulant that re-enters the passive set, the intermediates are inert derivation anchors like the AvatarSplit originals; the pre-Phase-5 single-record park below remains as the defensive fallback for a clause rewritten without a recorded chain (corruption: its derivation cannot cite the rule, and the kernel rejects it as UnrecordedRule).
            // CEP:STATUS: complete
            // CEP:FAILURE: propagates SearchError on store or passive failures.
            // CEP:ASSUMES: the snapshots were restandardized + deduped at record time; the chain is contiguous from the given clause's id.
            // CEP:COST: one new_clause + one flags computation + one weight per step.
            // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
            // CEP:SECURITY: none.
            let mut previous_id = given_id;
            let mut last_ptr = crate::ir::clause::ClausePtr::from_u32(given_offset);
            let mut last_age = 0u32;
            for step_index in 0..demod_steps.count {
                let step = &demod_steps.steps[step_index];
                let count = step.count as usize;
                for (target, source) in chain_scratch.iter_mut().zip(step.literals.iter()) {
                    *target = *source;
                }
                compute_selection_flags(context, options.selection, &mut chain_scratch[..count])
                    .map_err(SearchError::Inference)?;
                let age = space.next_input_age();
                let derivation = DerivationStep {
                    rule: InferenceRule::Demodulation,
                    parent_count: 2,
                    reserved: 0,
                    parents: [
                        previous_id,
                        step.rule_id,
                        kInvalidClauseId,
                        kInvalidClauseId,
                    ],
                    substitution: kInvalidSubstitutionOffset,
                };
                let ptr = space
                    .store
                    .new_clause(context.terms, &chain_scratch[..count], age, derivation)
                    .map_err(SearchError::Clause)?;
                previous_id = space.store.clause(ptr).map_err(SearchError::Clause)?.id.0;
                last_ptr = ptr;
                last_age = age;
            }
            let last_count = demod_steps.steps[demod_steps.count - 1].count as usize;
            let weight =
                SelectionWeight::of(context.terms, context.symbols, &chain_scratch[..last_count]);
            let record = space.store.clause(last_ptr).map_err(SearchError::Clause)?;
            space
                .passive
                .push(record.id.0, last_ptr.as_u32(), last_age, weight)
                .map_err(SearchError::Passive)?;
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
        // Establish the in-progress generation state; the generation runs on the
        // next iteration through the in-progress branch.
        in_progress = Some((given_offset, given_id, GenerationCursor::new()));
    }
}

// CEP:WHAT: One recorded demodulation rewrite step (CEP-1036): the restandardized, deduplicated snapshot of the clause after one rewrite, with the demodulating rule clause's id.
// CEP:WHY: The certified kernel (Spec 19) replays demodulation EXACTLY per step; that needs the rule's identity (the Phase 3/4 derivation recorded only the structural variant, ticket CEP-1036) and the exact intermediate clause. The snapshot is restandardized + deduped at record time so the stored chain record equals the snapshot bit for bit, and the in-loop buffer keeps its own namespace for the next rewrite (demodulation is renaming-invariant, so the replay over the restandardized chain is sound).
// CEP:STATUS: complete
// CEP:FAILURE: none; a data record.
// CEP:ASSUMES: count <= kMaxClauseLiterals; rule_id != kInvalidClauseId.
// CEP:COST: kMaxClauseLiterals x 8 bytes of stack per step.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub(crate) struct DemodulationStep {
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
    /// CEP:WHAT: The demodulating rule clause's store id (derivation parent 1).
    /// CEP:WHY: The kernel's exact per-step replay needs the rule; kInvalidClauseId would make the step unverifiable (UnrecordedRule).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the rule clause is live in the store.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub rule_id: u64,
}

// CEP:WHAT: The per-simplify-call demodulation step buffer (CEP-1036): one slot per simplify round.
// CEP:WHY: simplify_given performs at most one rewrite per round (the first successful demodulate breaks the round), and the round count is kMaxSimplifyRounds, so the buffer capacity is exact and overflow is unreachable; saturate consumes the recorded chain right after the call by storing one clause record per step with parents [previous, rule], giving the derivation DAG the full rewrite history the kernel replays.
// CEP:STATUS: complete
// CEP:FAILURE: none; the fixed arrays keep the buffer stack-allocated (no allocation in the hot loop).
// CEP:ASSUMES: one buffer per given clause iteration (cleared before each simplify_given call).
// CEP:COST: kMaxSimplifyRounds x (kMaxClauseLiterals x 8 + 10) bytes of stack.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
// CEP:SECURITY: none.
pub(crate) struct DemodulationSteps {
    /// CEP:WHAT: The recorded steps in rewrite order.
    /// CEP:WHY: The chain order is the replay order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: slots beyond count are filler.
    /// CEP:COST: kMaxSimplifyRounds step records.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    /// CEP:SECURITY: none.
    pub steps: [DemodulationStep; kMaxSimplifyRounds as usize],
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

impl DemodulationSteps {
    // CEP:WHAT: Constructs an empty step buffer.
    // CEP:WHY: Explicit init with filler literals (the count governs reads).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    // CEP:SECURITY: none.
    pub fn new() -> DemodulationSteps {
        DemodulationSteps {
            steps: [DemodulationStep {
                literals: [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                    kMaxClauseLiterals as usize],
                count: 0,
                rule_id: kInvalidClauseId,
            }; kMaxSimplifyRounds as usize],
            count: 0,
        }
    }

    // CEP:WHAT: Records one rewrite snapshot: restandardizes and dedupes a copy of the rewritten clause and stores it with the rule clause's id.
    // CEP:WHY: CEP-1036: the stored chain record must equal the snapshot bit for bit (the kernel replays the production pipeline over it), so the restandardize + dedupe happens at record time, not at store time; the in-loop buffer keeps its own namespace because demodulation is renaming-invariant.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SearchError on restandardization failure; a full buffer is structurally unreachable (one rewrite per round, kMaxSimplifyRounds rounds) and fails loudly rather than recording a partial chain.
    // CEP:ASSUMES: literals.len() <= kMaxClauseLiterals; rule_id != kInvalidClauseId.
    // CEP:COST: O(clause term nodes) restandardization plus O(n^2) dedupe.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_chain_records_rule_ids.
    // CEP:SECURITY: none.
    pub fn record(
        &mut self,
        context: &InferenceContext<'_>,
        literals: &[Literal],
        rule_id: u64,
    ) -> Result<(), SearchError> {
        if self.count >= self.steps.len() || rule_id == kInvalidClauseId {
            // Unreachable by the one-rewrite-per-round invariant; a partial chain
            // would be silently unverifiable, so the failure is loud instead.
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

// CEP:WHAT: Simplifies the given clause in place: tautology deletion, then bounded demodulation rounds against the active unit equations.
// CEP:WHY: Design 10.3 step 1; a rewrite recomputes the literal flags (with the configured selection function) because the rewritten atoms have new maximalities.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; the substitution trail is unwound per rewrite.
// CEP:ASSUMES: literal_count >= 1 on entry.
// CEP:COST: O(rounds x rules x positions), rounds bounded by kMaxSimplifyRounds.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{tautologies_discarded, demodulation_simplifies}.
// CEP:SECURITY: rounds bounded.
fn simplify_given(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    given: &mut [Literal; kMaxClauseLiterals as usize],
    literal_count: &mut usize,
    stats: &mut SearchStats,
    steps: &mut DemodulationSteps,
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
                        steps.record(context, &given[..count], clause.id.0)?;
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
            break;
        }
        if is_tautology(&given[..*literal_count]) {
            stats.tautologies += 1;
            return Ok(SimplifyStatus::Discarded);
        }
    }
    Ok(SimplifyStatus::Kept)
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
            let ptr = space
                .store
                .new_clause(context.terms, &[], age, derivation)
                .map_err(SearchError::Clause)?;
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
        let ptr = space
            .store
            .new_clause(context.terms, &staged[..deduped], age, derivation)
            .map_err(SearchError::Clause)?;
        let record = space.store.clause(ptr).map_err(SearchError::Clause)?;
        if space
            .passive
            .push(record.id.0, ptr.as_u32(), age, weight)
            .is_err()
        {
            return Ok(DrainStatus::PassiveFull);
        }
    }
    Ok(DrainStatus::Drained)
}

// CEP:WHAT: Test probe for the forward-subsumption path (wraps forward_subsumed); pub because the integration tests live outside the crate, never called by production code.
// CEP:WHY: The loop-internal helper is private; the database tests verify the filtered path (feature filter then matching) in isolation through this thin, documented projection - the loop-level behavior is covered by given_clause_test's forward_subsumption_discards; an internal SearchError is converted to false (the probe answers a yes/no question and the loop's own path surfaces the error loudly - the production forward_subsumed call has no such swallowing).
// CEP:STATUS: complete
// CEP:FAILURE: false on an internal error (test-surface behavior; production callers get the Err).
// CEP:ASSUMES: the given clause is non-empty.
// CEP:COST: as forward_subsumed.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
// CEP:SECURITY: none.
pub fn saturate_probe_forward(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    given: &[Literal],
) -> bool {
    forward_subsumed(space, context, given).unwrap_or(false)
}
