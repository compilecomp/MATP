// CEP:FILE: hot/search/mod.rs
// CEP:WHAT: Search module (design 15): the passive-set priority heap, the active set with its indexes, the bounded inference generator, and the given-clause saturation loop with budgets.
// CEP:WHY: Design 26 Phase 3 build order ("Given-clause loop (bounded)") over the Phase 2 engines and the Phase 3 inference rules: design 15.1 fixes the loop, 15.2 the selection strategies, 15.3 the weight function, 8.4 the clause database, and 10.3 the generation strategy; the loop enforces the design 20 budgets (kMaxInferences, the injected time budget checked every kBudgetCheckInterval iterations - CEP-1005) and returns the design 2.2 result vocabulary mapped onto SearchOutcome (Theorem, Saturated, GaveUp); CounterSatisfiable requires model building (design 17, Phase 5) and is therefore not a Phase 3 outcome.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring and the shared error vocabulary only.
// CEP:ASSUMES: one search per arena; the term store and symbol table are shared with the inference context.
// CEP:COST: compile-time only; per-component costs are documented in their files.
// CEP:EVIDENCE: unit/hot/search_db_test.rs; unit/hot/given_clause_test.rs; property/given_clause_property_test.rs; fuzz/given_clause_fuzz_test.rs; bench CEP-BENCH-0010, CEP-BENCH-0011.
// CEP:SECURITY: every budget is a named constant or an injected bound; all loops are bounded.
// CEP:HPC-DETERMINISM: deterministic end to end (verified by the two-identical-solves test in the fuzz suite); the injected time budget is the only nondeterminism source and returns GaveUp(Timeout), never a different answer.

pub mod active;
pub mod generate;
pub mod given_clause;
pub mod passive;

pub use active::{ActiveError, ActiveSet, ActiveSlot};
pub use generate::{
    GeneratedClause, GenerationCursor, GenerationPhase, GenerationStatus, InferenceBuffer,
};
pub use given_clause::{
    GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats, SelectionWeight,
};
pub use passive::{PassiveEntry, PassiveError, PassiveHeap, SelectionStrategy};

use crate::index::IndexError;
use crate::inference::InferenceError;
use crate::ir::clause::ClauseError;

/// CEP:WHAT: Error cases of the search layer.
/// CEP:WHY: CEP&CC Law 6 and 33.18: one composite vocabulary for the loop, flattening the component vocabularies with explicit From conversions; the search never panics and every capacity or structural failure surfaces as this type.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_capacity_enforced, capacity_enforced}; unit/hot/given_clause_test.rs::{per_clause_bound_enforced, passive_overflow_stops}.
/// CEP:SECURITY: capacity errors are the resource boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SearchError {
    /// CEP:WHAT: The passive heap capacity is exhausted.
    /// CEP:WHY: Loud bound (design 20.2: the search gives up, never loops).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    /// CEP:SECURITY: memory bound.
    Passive(PassiveError),
    /// CEP:WHAT: The active set capacity is exhausted.
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Active(ActiveError),
    /// CEP:WHAT: An index failure (tree capacity, term too large).
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated.
    /// CEP:SECURITY: memory bound.
    Index(IndexError),
    /// CEP:WHAT: An inference-rule structural failure.
    /// CEP:WHY: Loud propagation from the rules.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs.
    /// CEP:SECURITY: none.
    Inference(InferenceError),
    /// CEP:WHAT: A clause-store failure (arena exhausted, budget exceeded).
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    /// CEP:SECURITY: memory bound.
    Clause(ClauseError),
}

impl From<PassiveError> for SearchError {
    // CEP:WHAT: Converts passive-heap errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    // CEP:SECURITY: none.
    fn from(error: PassiveError) -> SearchError {
        SearchError::Passive(error)
    }
}

impl From<ActiveError> for SearchError {
    // CEP:WHAT: Converts active-set errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_capacity_enforced.
    // CEP:SECURITY: none.
    fn from(error: ActiveError) -> SearchError {
        SearchError::Active(error)
    }
}

impl From<IndexError> for SearchError {
    // CEP:WHAT: Converts index errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated.
    // CEP:SECURITY: none.
    fn from(error: IndexError) -> SearchError {
        SearchError::Index(error)
    }
}

impl From<InferenceError> for SearchError {
    // CEP:WHAT: Converts inference errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/inference_test.rs.
    // CEP:SECURITY: none.
    fn from(error: InferenceError) -> SearchError {
        SearchError::Inference(error)
    }
}

impl From<ClauseError> for SearchError {
    // CEP:WHAT: Converts clause-store errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::passive_overflow_stops.
    // CEP:SECURITY: none.
    fn from(error: ClauseError) -> SearchError {
        SearchError::Clause(error)
    }
}
