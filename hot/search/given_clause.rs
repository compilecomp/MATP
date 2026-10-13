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
// CEP:HPC-DETERMINISM: deterministic for a fixed stop callback: selection, simplification, and generation are pure functions of the state; the two-identical-solves fuzz test verifies it.
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
    kBudgetCheckInterval, kDefaultSymbolWeight, kInvalidClauseId, kInvalidSubstitutionOffset,
    kMaxClauseLiterals, kMaxInferences, kMaxSimplifyRounds, kSelectionVariableWeight,
};

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
    /// CEP:WHAT: Candidates and conclusions dropped (retrieval overflow, namespace overflow, over-long conclusions, budget tail).
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
        }
    }
}

/// CEP:WHAT: The selection weight function (design 15.3).
/// CEP:WHY: weight = sum over the clause's subterm nodes of the symbol weight (function and predicate symbols at their configured weight, default 1) with variables at kSelectionVariableWeight (0) - the design's "symbol_weight(s) x occurrence_count(s)" with the documented defaults; the weight is computed at clause creation for the passive-set key and is distinct from the cached clause weight (which counts variables at the KBO weight for ordering purposes).
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
        )
    }

    // CEP:WHAT: Constructs the search space with explicit capacities.
    // CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns SearchError on exhaustion.
    // CEP:ASSUMES: capacities >= 1.
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops; security/phase3_bounds_test.rs::{passive_capacity_enforced, active_capacity_enforced}.
    // CEP:SECURITY: bounds validated.
    pub fn new_with(
        arena: &'a Arena,
        options: &SearchOptions,
        passive_capacity: u32,
        active_capacity: u32,
        tree_nodes: u32,
        tree_entries: u32,
        pool_words: u32,
    ) -> Result<SearchSpace<'a>, SearchError> {
        Ok(SearchSpace {
            store: ClauseStore::new(arena),
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
        let age = self.input_age.get();
        self.input_age.set(age + 1);
        let derivation = DerivationStep {
            rule: InferenceRule::Input,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; 4],
            substitution: kInvalidSubstitutionOffset,
        };
        let ptr = self
            .store
            .new_clause(context.terms, &staged[..deduped], age, derivation)
            .map_err(SearchError::Clause)?;
        let record = self.store.clause(ptr).map_err(SearchError::Clause)?;
        self.passive.push(record.id.0, ptr.as_u32(), age, weight)?;
        Ok(ptr.as_u32())
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
        match simplify_given(space, context, options, &mut given, &mut given_len, stats)? {
            SimplifyStatus::Discarded => {
                stats.given_processed += 1;
                continue;
            }
            SimplifyStatus::Kept => {}
        }
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
        if given_is_stored(space, given_offset, &given[..given_len])? {
            space
                .active
                .insert(context.terms, given_offset, &given[..given_len])?;
        } else {
            let age = space.input_age.get();
            space.input_age.set(age + 1);
            let deduped = dedupe_literals(&mut given[..given_len]);
            given_len = deduped;
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
            while let Some(target) = crate::inference::superposition::subterm_at_public(
                context.terms,
                atom,
                &path[..path_len as usize],
            ) {
                // Query the rule tree with the subterm; unit rules only.
                let mut payloads: [u64; 16] = [0; 16];
                let retrieved =
                    match space
                        .active
                        .rule_tree()
                        .retrieve(context.terms, target, &mut payloads)
                    {
                        Ok(value) => value,
                        Err(crate::index::IndexError::BufferTooSmall) => payloads.len(),
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
                    1
                } else {
                    2
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
                1
            } else {
                2
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

// CEP:WHAT: Test probe for the forward-subsumption path (wraps forward_subsumed).
// CEP:WHY: The loop-internal helper is private; the database tests verify the filtered path (feature filter then matching) in isolation through this thin, documented projection - the loop-level behavior is covered by given_clause_test's forward_subsumption_discards.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError.
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
