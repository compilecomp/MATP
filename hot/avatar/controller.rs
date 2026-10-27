// CEP:FILE: hot/avatar/controller.rs
// CEP:WHAT: The AVATAR controller (design 12): owns the abstraction SAT solver and the component table, splits input clauses, materializes components under the SAT model (model-guided selection), collects the component ancestry of first-order refutations, adds conflict clauses (conflict-driven backtracking), and drives saturate_with_avatar - the design 12.2 four-rule loop over the Phase 3 given-clause engine.
// CEP:WHY: Design 26 Phase 4 build order; Voronkov (CAV 2014): splitting replaces a clause C with variable-disjoint components C1..Cn guarded by assertion variables a1..an whose disjunction the abstraction solver maintains; the first-order search runs on model-true components only, a first-order refutation whose ancestry uses component set U yields the conflict clause not-a1 or ... or not-ak (sound because inputs + the components of U entail false), and an unsatisfiable abstraction proves the original problem unsatisfiable (every model of the original induces an abstraction model - Spec 12 Theorem 1); the Phase 4 protocol is MONOTONE-ACTIVATION (a materialized component never leaves the search: superset search is sound because every derived clause stays a consequence of the inputs, and complete because it subsumes the strict model-guided restriction - Spec 12 section 5), which avoids the generation-rollback machinery of design 22.2 (ticketed) while keeping every outcome sound: Theorem (direct refutation without components, or abstraction-unsat after conflicts), Saturated (passive empty with every component materialized, or every waiting component proven unassertable by assumption solves - Spec 12 section 6), GaveUp (named budgets).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: returns ControllerError (search, abstraction, or solver failures surface loudly); saturate_with_avatar maps every bounded stop to GaveUp with a named reason; never panics.
// CEP:ASSUMES: one controller per search space and arena; the abstraction solver declares at least the component-table capacity variables; the driver adds every input clause through add_input_clause (splitting inputs is the only split point - derived clauses are processed by the inner given-clause loop and re-split only through their eventual materialization as components of later splits is NOT performed, documented as the Phase 4 scope: only input clauses split, Spec 12 section 7).
// CEP:COST: one abstraction solve per round plus O(clause ids) ancestry scan per conflict plus component interning; the inner search costs are the Phase 3 loop's (bench CEP-BENCH-0010/0011).
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{controller_validates_solver_variables, split_inputs_create_components, unsplittable_inputs_pass_through, model_activates_components, refutes_split_pigeonhole, direct_refutation_bypasses_avatar, conflict_round_budget_enforced, model_rotation_budget_enforced, split_derivations_cite_original}; property/avatar_property_test.rs::{avatar_agrees_with_plain_saturation, avatar_refutations_check}.
// CEP:SECURITY: every capacity is a named bound (kAvatarComponentCapacity, kAvatarMaxConflictRounds, kAvatarMaxModelRotations, the ancestry bitset capacity); the ancestry scan is bounded by the clause-id side table.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic per round: the abstraction solver, component interning, activation order (slot order), and the inner loop are all deterministic; the round sequence is a pure function of the input.
// CEP:HPC-PASS-LEGALITY: Formal Spec 12 fixes the four rules (section 2), the splitting lemma (Lemma 1, section 3), the interning contract (section 4), the monotone-activation soundness and completeness arguments (Theorem 2 and section 5), the saturation theorem (Theorem 3, section 6), and the degradation policy (section 7); the property tests verify executably that avatar outcomes agree with plain saturation on propositional and small first-order problems.

use crate::sat::clause::{kSatClauseFlagDeleted, kSatClauseFlagLearnt};
use core::cell::Cell;
use mapt_config::limits::{
    kAvatarComponentCapacity, kAvatarComponentWordCapacity, kAvatarMaxAssertionSymbols,
    kAvatarMaxConflictRounds, kAvatarMaxModelRotations, kClauseOffsetTableCapacity,
    kInvalidClauseId, kInvalidClauseOffset, kLearningMaxFolLemmas, kLearningMaxLearntTransfers,
    kLearningMaxTransferLbd, kLearningMaxTransferLiterals, kMaxClauseLiterals,
    kMaxSatClauseLiterals, kSatMaxConflicts,
};

use crate::inference::{compute_selection_flags, InferenceContext};
use crate::ir::clause::{
    ClauseError, ClauseId, ClausePtr, ClauseStore, DerivationStep, InferenceRule,
};
use crate::ir::literal::{Literal, LiteralFlags};
use crate::ir::term::TermPtr;
use crate::memory::arena::Arena;
use crate::sat::cdcl::CdclError;
use crate::sat::literal::{SatLiteral, SatVar};
use crate::sat::restart::RestartPolicy;
use crate::sat::solver::{AssumptionOutcome, CdclSolver, SolveResult, SolverOptions};
use crate::search::given_clause::{
    saturate, GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats, SelectionWeight,
};

use super::component::{canonical_component_words, AvatarError, ComponentTable};
use super::splitter::{kMaxSplitComponents, try_split_with, SplitDecision};

// CEP:WHAT: Wraps a clause-store error into the controller vocabulary.
// CEP:WHY: The store's Result vocabulary (ClauseError) nests inside SearchError::Clause inside ControllerError::Search; one named wrapper per origin keeps every map_err auditable instead of repeating the construction inline (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none; a converter.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, split_derivations_cite_original}.
// CEP:SECURITY: none.
fn wrap_clause(error: crate::ir::clause::ClauseError) -> ControllerError {
    ControllerError::Search(crate::search::SearchError::Clause(error))
}

// CEP:WHAT: Wraps a selection-flags (inference) error into the controller vocabulary.
// CEP:WHY: As wrap_clause, for the selection pass over materialized literals.
// CEP:STATUS: complete
// CEP:FAILURE: none; a converter.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_activates_components.
// CEP:SECURITY: none.
fn wrap_inference(error: crate::inference::InferenceError) -> ControllerError {
    ControllerError::Search(crate::search::SearchError::Inference(error))
}

// CEP:WHAT: Wraps a passive-heap error into the controller vocabulary.
// CEP:WHY: As wrap_clause, for the component's passive push.
// CEP:STATUS: complete
// CEP:FAILURE: none; a converter.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_activates_components.
// CEP:SECURITY: none.
fn wrap_passive(error: crate::search::PassiveError) -> ControllerError {
    ControllerError::Search(crate::search::SearchError::Passive(error))
}

/// CEP:WHAT: Construction options of the AVATAR controller.
/// CEP:WHY: CEP&CC 34.3: every capacity and policy bound must be injectable so tests exercise the exhaustion paths at small scales on the production code path; one options record keeps the constructor surface stable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record (construction validates).
/// CEP:ASSUMES: sat_variables >= record_capacity; ancestry_bits <= kClauseOffsetTableCapacity.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{controller_validates_solver_variables, conflict_round_budget_enforced}.
/// CEP:SECURITY: the capacities are the denial-of-service bounds under test.
pub struct AvatarOptions {
    /// CEP:WHAT: Abstraction-solver variable count (must cover every component slot).
    /// CEP:WHY: Assertion variables are dense component slots (Spec 12 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: construction returns AvatarError::SolverVariables when sat_variables < record_capacity.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::controller_validates_solver_variables.
    /// CEP:SECURITY: bounds the solver's per-variable structures.
    pub sat_variables: u32,
    /// CEP:WHAT: Abstraction-solver restart policy.
    /// CEP:WHY: The abstraction is small; the policy mirrors the SAT engine default.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_activates_components.
    /// CEP:SECURITY: none.
    pub restart_policy: RestartPolicy,
    /// CEP:WHAT: Component-table record capacity (the assertion-variable space actually used).
    /// CEP:WHY: CEP&CC 34.3 injectable bound; production default kAvatarComponentCapacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: interning past it degrades to the unsplit clause.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, conflict_round_budget_enforced}.
    /// CEP:SECURITY: memory bound.
    pub record_capacity: u32,
    /// CEP:WHAT: Component-table canonical-word blob capacity.
    /// CEP:WHY: CEP&CC 34.3 injectable bound; production default kAvatarComponentWordCapacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: interning past it degrades to the unsplit clause.
    /// CEP:ASSUMES: >= record_capacity.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::word_budget_enforced.
    /// CEP:SECURITY: memory bound.
    pub word_capacity: u32,
    /// CEP:WHAT: Ancestry bitset capacity in bits (over clause ids).
    /// CEP:WHY: The conflict-ancestry scan marks clause ids; the bitset is a fixed arena allocation sized to the clause-id side table (the same unreachability argument: the arena exhausts first).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: ancestry scans over ids beyond the capacity return ControllerError::Avatar (mapped to GaveUp).
    /// CEP:ASSUMES: <= kClauseOffsetTableCapacity; >= 64.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: memory bound.
    pub ancestry_bits: u32,
    /// CEP:WHAT: Splitting gate: minimum literals per component.
    /// CEP:WHY: Design 12.3 kAvatarMinComponentSize; injectable per CEP&CC 34.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::min_component_size_gate.
    /// CEP:SECURITY: none.
    pub min_component_size: u16,
    /// CEP:WHAT: Abstraction-solver conflict budget per solve.
    /// CEP:WHY: Design 20.1 named-limit discipline for the abstraction engine (production default kSatMaxConflicts).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: abstraction solves return Indeterminate past the budget and saturate_with_avatar maps that to a GaveUp.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_activates_components.
    /// CEP:SECURITY: denial-of-service bound.
    pub conflict_budget: u64,
    /// CEP:WHAT: Maximum conflict-driven rounds (production default kAvatarMaxConflictRounds).
    /// CEP:WHY: CEP&CC 34.3: the round budget must be injectable so tests exercise the exhaustion path at small scales on the production code path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturate_with_avatar returns GaveUp(AvatarConflictBudget) past the budget.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub max_conflict_rounds: u32,
    /// CEP:WHAT: Maximum model-rotation attempts (production default kAvatarMaxModelRotations).
    /// CEP:WHY: CEP&CC 34.3 injectable bound; Spec 12 section 6 proves every waiting component is assertable in the monotone protocol (no conflict clause mentions a waiting component's variable), so rotations drain the waiting set one activation at a time and the budget is the defensive bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturate_with_avatar returns GaveUp(AvatarModelBudget) past the budget.
    /// CEP:ASSUMES: >= 0 (zero probes nothing - the exhaustion path under test).
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub max_model_rotations: u32,
    /// CEP:WHAT: Clause learning: the base symbol id of the reserved mapt_assertion_<i> block (Spec 18 section 3).
    /// CEP:WHY: The FOL copies of SAT-side clauses speak through the 0-ary assertion predicates reserved by SymbolTableBuilder::reserve_assertion_symbols; the controller maps SAT component slot i onto assertion atom base + i.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (construction validates the count bound).
    /// CEP:ASSUMES: the caller reserved the block and passed its base; learning is DISABLED while learning_symbol_count == 0.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::{conflict_lemma_staged_and_verifiable, learning_disabled_by_default}.
    /// CEP:SECURITY: none.
    pub learning_symbol_base: u32,
    /// CEP:WHAT: Clause learning: the reserved assertion-symbol count (Spec 18 section 3).
    /// CEP:WHY: The count bounds the slot-to-atom mapping (slots at or above it are unnameable, so lemma staging and transfer skip-and-count); zero disables learning (the default).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: construction returns InvalidOptions when the count exceeds kAvatarMaxAssertionSymbols.
    /// CEP:ASSUMES: <= kAvatarMaxAssertionSymbols; <= the abstraction solver's variable count.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::learning_disabled_by_default.
    /// CEP:SECURITY: symbol-space bound.
    pub learning_symbol_count: u32,
    /// CEP:WHAT: Clause learning: maximum staged FOL conflict lemmas (Spec 18 section 4; production default kLearningMaxFolLemmas).
    /// CEP:WHY: CEP&CC 34.3 injectable bound; the staging path skips and counts past it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 when learning is enabled.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_budget_enforced.
    /// CEP:SECURITY: staging-work bound.
    pub learning_max_lemmas: u32,
    /// CEP:WHAT: Clause learning: maximum transferred SAT learnt clauses (Spec 18 section 4; production default kLearningMaxLearntTransfers).
    /// CEP:WHY: CEP&CC 34.3 injectable bound; the transfer path skips and counts past it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 when learning is enabled.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::transfer_budget_enforced.
    /// CEP:SECURITY: transfer-work bound.
    pub learning_max_transfers: u32,
}

// CEP:WHAT: Production default options: full capacities, Luby restarts, the SAT conflict budget.
// CEP:WHY: The named constants are the production values (design 19.4: built before the hot path); tests override through the public fields.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the arena has room for the solver, table, and bitset (about 8 MiB).
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, refutes_split_pigeonhole}.
// CEP:SECURITY: none.
impl Default for AvatarOptions {
    // CEP:WHAT: Returns the production options.
    // CEP:WHY: Derived-default boilerplate avoided by the explicit constructor (CEP&CC 11.3 - the values name their sources).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    // CEP:SECURITY: none.
    fn default() -> AvatarOptions {
        AvatarOptions {
            sat_variables: kAvatarComponentCapacity,
            restart_policy: RestartPolicy::Luby,
            record_capacity: kAvatarComponentCapacity,
            word_capacity: kAvatarComponentWordCapacity,
            ancestry_bits: kClauseOffsetTableCapacity,
            min_component_size: mapt_config::limits::kAvatarMinComponentSize,
            conflict_budget: kSatMaxConflicts,
            max_conflict_rounds: kAvatarMaxConflictRounds,
            max_model_rotations: kAvatarMaxModelRotations,
            // Learning is disabled by default (Spec 18 section 3): the symbol
            // count is zero until the caller reserves the assertion block and
            // opts in; the budgets carry their production constants so an opt-in
            // options literal is bounded even when the caller forgets them.
            learning_symbol_base: 0,
            learning_symbol_count: 0,
            learning_max_lemmas: kLearningMaxFolLemmas,
            learning_max_transfers: kLearningMaxLearntTransfers,
        }
    }
}

/// CEP:WHAT: Error cases of the AVATAR controller: wraps the search, component, and solver vocabularies.
/// CEP:WHY: CEP&CC Law 6: one explicit failure vocabulary per component boundary; the driver matches on the origin without losing the inner error.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{controller_validates_solver_variables, split_inputs_create_components}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControllerError {
    /// CEP:WHAT: The inner search space failed.
    /// CEP:WHY: Clause-store, passive, active, and inference failures keep their Phase 3 vocabulary.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    /// CEP:SECURITY: none.
    Search(crate::search::SearchError),
    /// CEP:WHAT: The component table failed.
    /// CEP:WHY: Capacity and word-budget exhaustions keep their table vocabulary.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{capacity_enforced, word_budget_enforced}.
    /// CEP:SECURITY: none.
    Avatar(AvatarError),
    /// CEP:WHAT: The abstraction solver failed structurally.
    /// CEP:WHY: CDCL storage and attach failures keep their solver vocabulary.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::controller_validates_solver_variables.
    /// CEP:SECURITY: none.
    Solver(CdclError),
    /// CEP:WHAT: The controller options are inconsistent (solver variables below the record capacity, bitset capacity out of range).
    /// CEP:WHY: Construction-time validation with a named variant instead of a panic.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::controller_validates_solver_variables.
    /// CEP:SECURITY: input validation.
    InvalidOptions,
}

/// CEP:WHAT: The outcome of one controller input-add: the clause entered the space whole, or it split into components.
/// CEP:WHY: The driver and the tests must distinguish the two paths (split inputs never push the original into the passive set, design 12.2 rule 1).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: offsets are store-produced.
/// CEP:COST: enum copy with payload.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, unsplittable_inputs_pass_through}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddOutcome {
    /// CEP:WHAT: The clause was added unsplit; the payload is its record offset.
    /// CEP:WHY: Unsplittable clauses (single component, gate refusal, degradation) take the plain Phase 3 path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::unsplittable_inputs_pass_through.
    /// CEP:SECURITY: none.
    Added(u32),
    /// CEP:WHAT: The clause split; the payload is the original's record offset (retained inertly for proof reconstruction).
    /// CEP:WHY: The original never enters the search; its record anchors the components' AvatarSplit derivations (Spec 12 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the components are interned and their disjunction is in the abstraction.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, split_derivations_cite_original}.
    /// CEP:SECURITY: none.
    Split { original: u32 },
}

/// CEP:WHAT: The terminal outcome of the AVATAR saturation protocol.
/// CEP:WHY: Design 12.2: Theorem (with the refuting clause offset and whether the abstraction refutation closed it), Saturated (Spec 12 Theorem 3 conditions), or GaveUp with a named reason; mapping onto the design 2.2 vocabulary is the CEP-1 driver's job.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{refutes_split_pigeonhole, direct_refutation_bypasses_avatar, conflict_round_budget_enforced, model_rotation_budget_enforced}; property/avatar_property_test.rs::avatar_agrees_with_plain_saturation.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AvatarOutcome {
    /// CEP:WHAT: The empty clause was derived; the payload is its clause record offset and whether the abstraction unsatisfiability closed the case.
    /// CEP:WHY: via_avatar = false is a direct first-order refutation of the input clauses; via_avatar = true needed component assumptions and is justified by the abstraction refutation (Spec 12 Theorem 1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the refutation record exists.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{direct_refutation_bypasses_avatar, refutes_split_pigeonhole}.
    /// CEP:SECURITY: none.
    Theorem {
        /// CEP:WHAT: The refuting (empty) clause's record offset.
        /// CEP:WHY: Proof reconstruction starts here (design 18.2).
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 4 bytes.
        /// CEP:EVIDENCE: unit/cold/tstp_test.rs::formats_refutation_proof.
        /// CEP:SECURITY: none.
        refutation: u32,
        /// CEP:WHAT: Whether the refutation used split components (abstraction-closed).
        /// CEP:WHY: Drives the TSTP proof's presentation (Spec 14 section 5).
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 1 byte.
        /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
        /// CEP:SECURITY: none.
        via_avatar: bool,
    },
    /// CEP:WHAT: The search saturated: passive empty with every component materialized, or every waiting component proven unassertable (Spec 12 Theorem 3).
    /// CEP:WHY: The honest Phase 4 terminal for satisfiable inputs (model construction is Phase 5, design 17).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{saturates_when_waiting_drains, model_rotation_budget_enforced}.
    /// CEP:SECURITY: none.
    Saturated,
    /// CEP:WHAT: A named budget ended the search.
    /// CEP:WHY: Design 20.1/20.2 plus the two AVATAR budgets (conflict rounds, model rotations).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the stats carry the state at the stop.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{conflict_round_budget_enforced, model_rotation_budget_enforced}.
    /// CEP:SECURITY: denial-of-service bounds.
    GaveUp(GaveUpReason),
}

/// CEP:WHAT: The controller's measurement record.
/// CEP:WHY: Design 24 diagnostics; every counter is deterministic per run (CEP&CC 38.10).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: single-threaded updates.
/// CEP:COST: 10 Cells.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, refutes_split_pigeonhole}.
/// CEP:SECURITY: none.
#[derive(Debug, Default)]
pub struct AvatarStats {
    /// CEP:WHAT: Input clauses that split.
    /// CEP:WHY: Splitting-rate diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    /// CEP:SECURITY: none.
    pub splits: Cell<u32>,
    /// CEP:WHAT: Input clauses that stayed whole (including table-full degradations).
    /// CEP:WHY: Degradation visibility (CEP&CC Law 6 - never silent).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::unsplittable_inputs_pass_through.
    /// CEP:SECURITY: none.
    pub unsplit: Cell<u32>,
    /// CEP:WHAT: Components interned fresh.
    /// CEP:WHY: Abstraction-growth diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    /// CEP:SECURITY: none.
    pub components_fresh: Cell<u32>,
    /// CEP:WHAT: Components shared (re-interned).
    /// CEP:WHY: Component-sharing effectiveness (Voronkov 2014 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    /// CEP:SECURITY: none.
    pub components_shared: Cell<u32>,
    /// CEP:WHAT: Components materialized into the search.
    /// CEP:WHY: Model-activation diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_activates_components.
    /// CEP:SECURITY: none.
    pub activations: Cell<u32>,
    /// CEP:WHAT: Conflict clauses added to the abstraction.
    /// CEP:WHY: Conflict-driven-backtracking diagnostics (design 12.2 rule 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: none.
    pub conflicts: Cell<u32>,
    /// CEP:WHAT: Model-rotation assumption solves attempted.
    /// CEP:WHY: Rotation diagnostics (Spec 12 section 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
    /// CEP:SECURITY: none.
    pub rotations: Cell<u32>,
    /// CEP:WHAT: FOL conflict lemmas staged (Spec 18 section 4).
    /// CEP:WHY: Learning diagnostics; the staged lemma is a stored clause record, not a search clause.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
    /// CEP:SECURITY: none.
    pub learning_lemmas: Cell<u32>,
    /// CEP:WHAT: SAT learnt clauses transferred into FOL clauses (Spec 18 section 4).
    /// CEP:WHY: Learning diagnostics; a transferred lemma enters the passive set.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::transfer_learnts_enter_passive.
    /// CEP:SECURITY: none.
    pub learning_transfers: Cell<u32>,
    /// CEP:WHAT: Learning attempts skipped (budgets exhausted, slots unnameable, policy filters).
    /// CEP:WHY: CEP&CC Law 4: bounded skips are counted, never silent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: Cell load.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::{conflict_lemma_budget_enforced, transfer_policy_filters}.
    /// CEP:SECURITY: none.
    pub learning_skipped: Cell<u32>,
}

/// CEP:WHAT: The AVATAR controller: the abstraction solver, the component table, the ancestry bitset, and the protocol state.
/// CEP:WHY: Design 12.1's controller box: one owner of the ATP-SAT bridge state; the solver and table are pub so the driver can read models and the component table for proof extraction (design 12.4: no serialization, both engines share the arena).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ControllerError.
/// CEP:ASSUMES: single-threaded; one controller per space; the driver adds inputs only through add_input_clause.
/// CEP:COST: construction O(capacities); per-round costs as the file header.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs (the whole file); property/avatar_property_test.rs::avatar_agrees_with_plain_saturation.
/// CEP:SECURITY: all capacities named and validated.
pub struct AvatarController<'a> {
    /// CEP:WHAT: The abstraction SAT solver (proof recording off; Spec 12 section 8 documents why).
    /// CEP:WHY: Maintains the assertion-variable disjunctions and the conflict clauses; model_value drives activation; add_clause adds problem clauses (never reduced by the registry, so conflict bans are permanent).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: see CdclError.
    /// CEP:ASSUMES: variables >= component-table capacity.
    /// CEP:COST: see CdclSolver.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{model_activates_components, refutes_split_pigeonhole}.
    /// CEP:SECURITY: bounded by the solver's named budgets.
    pub solver: CdclSolver<'a>,
    /// CEP:WHAT: The component table.
    /// CEP:WHY: Interning, assertion variables, and materialization bookkeeping (design 12.2 rule 1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: see AvatarError.
    /// CEP:ASSUMES: one table per controller.
    /// CEP:COST: see ComponentTable.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs (the whole file).
    /// CEP:SECURITY: bounded capacities.
    pub components: ComponentTable<'a>,
    /// CEP:WHAT: Ancestry bitset over clause ids (one bit per id, capacity bits).
    /// CEP:WHY: The conflict-ancestry scan marks ids in one descending pass (parents precede children, Spec 12 section 5); the bitset is a fixed arena allocation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: ids beyond the capacity abort the scan loudly.
    /// CEP:ASSUMES: capacity <= kClauseOffsetTableCapacity (the arena exhausts first - same argument as the side table).
    /// CEP:COST: capacity/8 bytes; O(ids) scan per conflict.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: bounds-checked.
    ancestry: &'a [Cell<u64>],
    /// CEP:WHAT: Conflict-slot buffer (one entry per component record, the deduplicated used-slot list of the last ancestry scan).
    /// CEP:WHY: The conflict-ancestry result must live off the stack (256 KiB at the production capacity would stress worker-thread stacks); the arena buffer is written by plan_conflict and read by add_conflict_from_buffer (Spec 12 section 5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one scan at a time (single-threaded).
    /// CEP:COST: 4 bytes per record.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: bounds-checked.
    conflict_slots: &'a [Cell<u32>],
    /// CEP:WHAT: Splitting gate (minimum literals per component).
    /// CEP:WHY: Design 12.3 kAvatarMinComponentSize, injectable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::min_component_size_gate.
    /// CEP:SECURITY: none.
    min_component_size: u16,
    /// CEP:WHAT: Maximum conflict-driven rounds (injected; production default kAvatarMaxConflictRounds).
    /// CEP:WHY: CEP&CC 34.3 injectable protocol bound (Spec 12 section 5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturate_with_avatar returns GaveUp(AvatarConflictBudget) at the bound.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    max_conflict_rounds: u32,
    /// CEP:WHAT: Maximum model-rotation attempts (injected; production default kAvatarMaxModelRotations).
    /// CEP:WHY: CEP&CC 34.3 injectable protocol bound (Spec 12 section 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: saturate_with_avatar returns GaveUp(AvatarModelBudget) at the bound.
    /// CEP:ASSUMES: >= 0.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    max_model_rotations: u32,
    /// CEP:WHAT: The controller's stats.
    /// CEP:WHY: Design 24 diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: see AvatarStats.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, refutes_split_pigeonhole}.
    /// CEP:SECURITY: none.
    pub stats: AvatarStats,
    /// CEP:WHAT: The learning assertion base (Spec 18 section 3; snapshot of AvatarOptions::learning_symbol_base).
    /// CEP:WHY: SAT component slot i maps onto assertion atom base + i.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: meaningful only when learning_symbol_count > 0.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
    /// CEP:SECURITY: none.
    learning_symbol_base: u32,
    /// CEP:WHAT: The learning assertion count (0 disables learning; Spec 18 section 3).
    /// CEP:WHY: The slot-to-atom bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kAvatarMaxAssertionSymbols.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::learning_disabled_by_default.
    /// CEP:SECURITY: none.
    learning_symbol_count: u32,
    /// CEP:WHAT: The staged-lemma budget (Spec 18 section 4).
    /// CEP:WHY: CEP&CC 34.3 injectable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 when learning is enabled.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_budget_enforced.
    /// CEP:SECURITY: none.
    learning_max_lemmas: u32,
    /// CEP:WHAT: The transfer budget (Spec 18 section 4).
    /// CEP:WHY: CEP&CC 34.3 injectable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 when learning is enabled.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::transfer_budget_enforced.
    /// CEP:SECURITY: none.
    learning_max_transfers: u32,
    /// CEP:WHAT: The monotone transfer cursor: the registry entry index one past the last transferred entry.
    /// CEP:WHY: Spec 18 section 4: transfers enumerate registry entries beyond the cursor after unconditional solves; the cursor advances monotonically so every entry is considered at most once (deterministic, no rescans).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: single-threaded.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::transfer_learnts_enter_passive.
    /// CEP:SECURITY: none.
    transfer_cursor: Cell<u32>,
}

impl<'a> AvatarController<'a> {
    // CEP:WHAT: Constructs the controller with explicit options (solver, table, bitset).
    // CEP:WHY: CEP&CC 34.3 injectable capacities on the production path; validates sat_variables >= record_capacity and the bitset range before any allocation.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns InvalidOptions for inconsistent options and the wrapped table/solver errors for arena exhaustion.
    // CEP:ASSUMES: the arena has room for all substructures.
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{controller_validates_solver_variables, split_inputs_create_components}.
    // CEP:SECURITY: options validated before allocation.
    pub fn new_with(
        arena: &'a Arena,
        options: &AvatarOptions,
    ) -> Result<AvatarController<'a>, ControllerError> {
        if options.sat_variables < options.record_capacity
            || options.record_capacity == 0
            || options.ancestry_bits < 64
            || options.ancestry_bits > kClauseOffsetTableCapacity
            || !options.ancestry_bits.is_multiple_of(64)
        {
            return Err(ControllerError::InvalidOptions);
        }
        // Learning options (Spec 18 section 3): the reserved count must fit the
        // named assertion-symbol bound, and an enabled configuration carries
        // positive budgets.
        if options.learning_symbol_count > kAvatarMaxAssertionSymbols
            || (options.learning_symbol_count > 0
                && (options.learning_max_lemmas == 0 || options.learning_max_transfers == 0))
        {
            return Err(ControllerError::InvalidOptions);
        }
        let components =
            ComponentTable::new_with(arena, options.record_capacity, options.word_capacity)
                .map_err(ControllerError::Avatar)?;
        let mut solver_options =
            SolverOptions::new(options.sat_variables, options.restart_policy, false);
        solver_options.conflict_budget = options.conflict_budget;
        solver_options.record_proof = false;
        let solver =
            CdclSolver::new_advanced(arena, solver_options).map_err(ControllerError::Solver)?;
        let bitset_words = options.ancestry_bits / 64;
        let bitset_range = arena
            .alloc_array::<Cell<u64>>(bitset_words)
            .map_err(|_| ControllerError::Avatar(AvatarError::ComponentTableFull))?;
        let ancestry = arena
            .array::<Cell<u64>>(bitset_range)
            .map_err(|_| ControllerError::Avatar(AvatarError::ComponentTableFull))?;
        let conflict_range = arena
            .alloc_array::<Cell<u32>>(options.record_capacity)
            .map_err(|_| ControllerError::Avatar(AvatarError::ComponentTableFull))?;
        let conflict_slots = arena
            .array::<Cell<u32>>(conflict_range)
            .map_err(|_| ControllerError::Avatar(AvatarError::ComponentTableFull))?;
        Ok(AvatarController {
            solver,
            components,
            ancestry,
            conflict_slots,
            min_component_size: options.min_component_size,
            max_conflict_rounds: options.max_conflict_rounds,
            max_model_rotations: options.max_model_rotations,
            stats: AvatarStats::default(),
            learning_symbol_base: options.learning_symbol_base,
            learning_symbol_count: options.learning_symbol_count,
            learning_max_lemmas: options.learning_max_lemmas,
            learning_max_transfers: options.learning_max_transfers,
            transfer_cursor: Cell::new(0),
        })
    }

    // CEP:WHAT: Constructs the controller with production defaults.
    // CEP:WHY: The production entry point; the capacities are the named constants (AvatarOptions::default).
    // CEP:STATUS: complete
    // CEP:FAILURE: as new_with.
    // CEP:ASSUMES: the arena has about 8 MiB free beyond the search space.
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_inputs_create_components.
    // CEP:SECURITY: as new_with.
    pub fn new(arena: &'a Arena) -> Result<AvatarController<'a>, ControllerError> {
        AvatarController::new_with(arena, &AvatarOptions::default())
    }

    // CEP:WHAT: Adds one input clause: splits it when the gate passes, otherwise the plain Phase 3 path.
    // CEP:WHY: Design 12.2 rule 1 with the Spec 12 section 7 degradation policy: the original record is created (Input derivation, never pushed to passive - inert by construction) so the components' AvatarSplit derivations cite it; each component is restandardized to its own dense namespace, canonicalized, interned (sharing assertion variables across splits), and its assertion literal joins the split's disjunction a1 or ... or an (a problem clause - permanent, never registry-reduced); table-full and word-full degradations keep the clause whole (sound).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates ControllerError on structural failures; degradation is NOT a failure (counted in stats.unsplit).
    // CEP:ASSUMES: literal atoms were interned by the context's term store; the caller standardized the clause's variables densely; the space and the controller share one arena.
    // CEP:COST: one split decision plus per-component restandardize/canonicalize/intern plus one solver add_clause.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{split_inputs_create_components, unsplittable_inputs_pass_through, split_derivations_cite_original}.
    // CEP:SECURITY: all buffers bounded (kMaxClauseLiterals, kMaxSplitComponents).
    pub fn add_input_clause(
        &self,
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        literals: &[Literal],
    ) -> Result<AddOutcome, ControllerError> {
        if literals.len() > kMaxClauseLiterals as usize {
            return Err(ControllerError::Search(crate::search::SearchError::Clause(
                ClauseError::TooManyLiterals,
            )));
        }
        match try_split_with(context.terms, literals, self.min_component_size) {
            SplitDecision::Unsplittable => {
                space
                    .add_input_clause(context, options, literals)
                    .map_err(ControllerError::Search)?;
                self.stats.unsplit.set(self.stats.unsplit.get() + 1);
                Ok(AddOutcome::Added(0))
            }
            SplitDecision::Splittable(view) => {
                // Stage a copy for per-component extraction.
                let mut staged: [Literal; kMaxClauseLiterals as usize] =
                    [Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
                for (slot, literal) in staged.iter_mut().zip(literals.iter()) {
                    *slot = *literal;
                }
                // The original record: Input derivation, inert (never pushed to passive);
                // the store computes the record's weight at creation (design 5.3).
                let age = space.next_input_age();
                let original_derivation = DerivationStep {
                    rule: InferenceRule::Input,
                    parent_count: 0,
                    reserved: 0,
                    parents: [kInvalidClauseId; 4],
                    substitution: kInvalidClauseOffset,
                };
                let original = space
                    .store
                    .new_clause(
                        context.terms,
                        &staged[..literals.len()],
                        age,
                        original_derivation,
                    )
                    .map_err(wrap_clause)?;
                let original_id = space.store.clause(original).map_err(wrap_clause)?.id.0;
                // Intern every component; collect assertion literals.
                let mut assertion: [SatLiteral; kMaxSplitComponents] =
                    [SatLiteral::new(SatVar(0), true)
                        .map_err(|_| ControllerError::InvalidOptions)?;
                        kMaxSplitComponents];
                let mut words: [u32; kMaxClauseLiterals as usize] =
                    [0; kMaxClauseLiterals as usize];
                let mut component_literals: [Literal; kMaxClauseLiterals as usize] =
                    [Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
                for (component, assertion_slot) in assertion
                    .iter_mut()
                    .enumerate()
                    .take(view.component_count as usize)
                {
                    let mut count: usize = 0;
                    for (position, literal) in staged[..literals.len()].iter().enumerate() {
                        if view.literal_component[position] as usize == component {
                            component_literals[count] = *literal;
                            count += 1;
                        }
                    }
                    // Restandardize the component into its own dense namespace (interning identity).
                    crate::inference::restandardize_clause(
                        context.terms,
                        context.symbols,
                        &mut component_literals[..count],
                    )
                    .map_err(wrap_inference)?;
                    let word_count =
                        canonical_component_words(&component_literals[..count], &mut words);
                    match self.components.intern(&words[..word_count], original_id) {
                        Ok(interned) => {
                            if interned.fresh {
                                self.stats
                                    .components_fresh
                                    .set(self.stats.components_fresh.get() + 1);
                            } else {
                                self.stats
                                    .components_shared
                                    .set(self.stats.components_shared.get() + 1);
                            }
                            *assertion_slot = SatLiteral::new(
                                self.components.assertion_variable(interned.slot),
                                true,
                            )
                            .map_err(|_| ControllerError::InvalidOptions)?;
                        }
                        Err(AvatarError::ComponentTableFull)
                        | Err(AvatarError::WordBudgetExceeded) => {
                            // Sound degradation (Spec 12 section 7): keep the clause whole.
                            // The original record stays as the inert proof anchor; the plain
                            // clause joins the search through the standard path.
                            space
                                .add_input_clause(context, options, literals)
                                .map_err(ControllerError::Search)?;
                            self.stats.unsplit.set(self.stats.unsplit.get() + 1);
                            return Ok(AddOutcome::Added(0));
                        }
                        Err(error) => return Err(ControllerError::Avatar(error)),
                    }
                }
                // The abstraction clause: a1 or ... or an (problem clause, permanent).
                self.solver
                    .add_clause(&assertion[..view.component_count as usize])
                    .map_err(ControllerError::Solver)?;
                self.stats.splits.set(self.stats.splits.get() + 1);
                Ok(AddOutcome::Split {
                    original: original.as_u32(),
                })
            }
        }
    }

    // CEP:WHAT: Materializes every unmaterialized component whose assertion variable is true under the current model; returns the activation count.
    // CEP:WHY: Design 12.2 rule 3 (model-guided selection) under monotone activation (Spec 12 section 5): the component clause is created with the AvatarSplit derivation (parent = the first split's original), the literal component tags (CEP-1011), split_level = slot + 1, the selection flags, the weight, the next input age, and a passive push - the component enters the search exactly once.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates ControllerError; set_materialized is idempotent so a repeated activation is a no-op.
    // CEP:ASSUMES: the solver just returned Satisfiable (model_value is meaningful); the space and controller share one arena.
    // CEP:COST: O(components) scan plus O(literals) per activated component.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{model_activates_components, refutes_split_pigeonhole, split_derivations_cite_original}.
    // CEP:SECURITY: all reads bounds-checked.
    pub fn activate_under_model(
        &self,
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
    ) -> Result<u32, ControllerError> {
        let mut activated: u32 = 0;
        let mut component_literals: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        for slot in 0..self.components.component_count() {
            if self.components.materialized(slot).is_some() {
                continue;
            }
            if self.solver.model_value(slot) != Some(true) {
                continue;
            }
            let (word_start, word_count) = match self.components.word_extent(slot) {
                Some(extent) => extent,
                None => return Err(ControllerError::Avatar(AvatarError::InvalidClause)),
            };
            if word_count as usize > component_literals.len() {
                return Err(ControllerError::Avatar(AvatarError::InvalidClause));
            }
            for (index, literal_slot) in component_literals
                .iter_mut()
                .enumerate()
                .take(word_count as usize)
            {
                let word = self
                    .components
                    .word_at(word_start + index as u32)
                    .ok_or(ControllerError::Avatar(AvatarError::InvalidClause))?;
                let atom = TermPtr::from_u32(word >> 1);
                let polarity = (word & 1) == 1;
                let mut literal = Literal::new(atom, polarity);
                literal.set_avatar_component_tag((slot as u8) & LiteralFlags::kAvatarComponentMask);
                *literal_slot = literal;
            }
            let count = word_count as usize;
            let source_id = self
                .components
                .source_clause(slot)
                .ok_or(ControllerError::Avatar(AvatarError::InvalidClause))?;
            let derivation = DerivationStep {
                rule: InferenceRule::AvatarSplit,
                parent_count: 1,
                reserved: 0,
                parents: [
                    source_id,
                    kInvalidClauseId,
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidClauseOffset,
            };
            compute_selection_flags(context, options.selection, &mut component_literals[..count])
                .map_err(wrap_inference)?;
            let weight =
                SelectionWeight::of(context.terms, context.symbols, &component_literals[..count]);
            let age = space.next_input_age();
            let ptr = space
                .store
                .new_clause(context.terms, &component_literals[..count], age, derivation)
                .map_err(wrap_clause)?;
            space
                .store
                .set_split_level(ptr, (slot + 1) as u16)
                .map_err(wrap_clause)?;
            let record = space.store.clause(ptr).map_err(wrap_clause)?;
            space
                .passive
                .push(record.id.0, ptr.as_u32(), age, weight)
                .map_err(wrap_passive)?;
            self.components
                .set_materialized(slot, ptr.as_u32())
                .map_err(ControllerError::Avatar)?;
            self.stats.activations.set(self.stats.activations.get() + 1);
            activated += 1;
        }
        // The model is consumed: end its readability so the next add_clause sees
        // level 0 (the plain-solve exit path runs no epilogue - see CdclSolver::cancel).
        self.solver.cancel();
        Ok(activated)
    }

    // CEP:WHAT: Collects the component slots used by a refutation's derivation ancestry; returns the count written to out.
    // CEP:WHY: Design 12.2 rule 4: the conflict clause bans the conjunction of every component in the refutation's ancestry; the scan exploits monotonic clause ids (parents precede children) with one descending pass over the id range marking ancestors on the bitset and recording component clauses (split_level != 0) - Spec 12 section 5 proves the single pass correct.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns ControllerError::Avatar when a clause id exceeds the bitset capacity or a parent is unreadable.
    // CEP:ASSUMES: refutation is a store-produced offset; out has at least component_count slots.
    // CEP:COST: O(refutation id) bitset scan plus O(ancestry) record reads.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: ids bounded by the bitset capacity.
    pub fn plan_conflict(
        &self,
        store: &ClauseStore<'_>,
        refutation: u32,
    ) -> Result<usize, ControllerError> {
        for word in self.ancestry.iter() {
            word.set(0);
        }
        let root = store
            .clause(ClausePtr::from_u32(refutation))
            .map_err(|_| ControllerError::Avatar(AvatarError::InvalidClause))?;
        let max_id = root.id.0;
        let bit_capacity = (self.ancestry.len() as u64) * 64;
        if max_id < mapt_config::limits::kFirstClauseId
            || (max_id - mapt_config::limits::kFirstClauseId) >= bit_capacity
        {
            return Err(ControllerError::Avatar(AvatarError::InvalidClause));
        }
        let mark = |id: u64| -> Result<(), ControllerError> {
            let index = id - mapt_config::limits::kFirstClauseId;
            let word = self.ancestry.get((index / 64) as usize);
            let word = match word {
                Some(word) => word,
                None => return Err(ControllerError::Avatar(AvatarError::InvalidClause)),
            };
            let bits = word.get();
            word.set(bits | (1u64 << (index % 64)));
            Ok(())
        };
        let is_marked = |id: u64| -> Option<bool> {
            if id < mapt_config::limits::kFirstClauseId {
                return Some(false);
            }
            let index = id - mapt_config::limits::kFirstClauseId;
            let word = self.ancestry.get((index / 64) as usize)?;
            Some((word.get() >> (index % 64)) & 1 == 1)
        };
        mark(root.id.0)?;
        let mut used: usize = 0;
        let mut id = max_id;
        loop {
            if is_marked(id) == Some(true) {
                if let Ok(record) = store.clause_by_id(ClauseId(id)) {
                    if record.split_level != 0 && used < self.conflict_slots.len() {
                        self.conflict_slots[used].set((record.split_level - 1) as u32);
                        used += 1;
                    }
                    for parent in record.derivation.parents.iter() {
                        if *parent != kInvalidClauseId {
                            if *parent >= id {
                                // Parents precede children (monotonic ids); a violation is a
                                // corrupted derivation - fail loudly.
                                return Err(ControllerError::Avatar(AvatarError::InvalidClause));
                            }
                            mark(*parent)?;
                        }
                    }
                } else {
                    // An unresolvable ancestor id (record outside the side table) - fail loudly.
                    return Err(ControllerError::Avatar(AvatarError::InvalidClause));
                }
            }
            if id == mapt_config::limits::kFirstClauseId {
                break;
            }
            id -= 1;
        }
        // Deduplicate the used-slot list (insertion order preserved).
        let mut deduped: usize = 0;
        for index in 0..used {
            let slot = self.conflict_slots[index].get();
            let mut seen = false;
            for prior in 0..deduped {
                if self.conflict_slots[prior].get() == slot {
                    seen = true;
                    break;
                }
            }
            if !seen {
                self.conflict_slots[deduped].set(slot);
                deduped += 1;
            }
        }
        Ok(deduped)
    }

    // CEP:WHAT: Adds the conflict clause from the controller's conflict-slot buffer (the first `used` entries).
    // CEP:WHY: Design 12.2 rule 4 and Spec 12 Lemma 2: inputs + the components of U entail false, so every original-problem model falsifies the all-true-U assignment - the clause not-a1 or ... or not-ak is entailed and excludes at least the current model; problem-clause semantics keep the ban permanent (no registry reduction); reading the controller's own buffer avoids a stack copy and any truncation (a truncated ban would be UNSOUND - it must cover every used slot or fail loudly).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns AvatarError::InvalidClause when used exceeds kMaxSatClauseLiterals (the abstraction cannot host the clause - a loud stop, never a silent subset ban) and propagates the solver error.
    // CEP:ASSUMES: the buffer was filled by plan_conflict; entries are distinct slots < component_count.
    // CEP:COST: O(used) literal construction plus one add_clause.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: literal count bounded by kMaxSatClauseLiterals.
    pub fn add_conflict_from_buffer(&self, used: usize) -> Result<(), ControllerError> {
        if used > kMaxSatClauseLiterals as usize || used > self.conflict_slots.len() {
            return Err(ControllerError::Avatar(AvatarError::InvalidClause));
        }
        let mut literals: [SatLiteral; kMaxSatClauseLiterals as usize] =
            [SatLiteral::new(SatVar(0), true).map_err(|_| ControllerError::InvalidOptions)?;
                kMaxSatClauseLiterals as usize];
        for (literal_slot, index) in literals.iter_mut().zip(0..used) {
            let slot = self.conflict_slots[index].get();
            *literal_slot = SatLiteral::new(SatVar(slot), false)
                .map_err(|_| ControllerError::InvalidOptions)?;
        }
        self.solver
            .add_clause(&literals[..used])
            .map_err(ControllerError::Solver)?;
        self.stats.conflicts.set(self.stats.conflicts.get() + 1);
        Ok(())
    }

    // CEP:WHAT: Stages the FOL copy of the conflict clause from the controller's conflict-slot buffer (Spec 18 section 4): one stored SatLearn clause over 0-ary assertion atoms, anchored at the round's refutation.
    // CEP:WHY: The SAT ban clause (add_conflict_from_buffer) lives in the abstraction; the FOL copy records the same proposition in the derivation DAG as a SatLearn lemma (all-negative assertion atoms, one parent: the round's refuting empty clause), where the certified kernel verifies its shape (Spec 19); the lemma is STAGED (stored, never pushed to the passive set - the assertion atoms are foreign to the first-order search), the staging is all-or-nothing (a partial ban would be unsound), and every skip is counted (Law 4).
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) on every skip path (learning disabled, budget exhausted, unnameable slot, count bound); Err propagates store failures; never panics.
    // CEP:ASSUMES: the buffer was filled by plan_conflict; refutation_id is the refuting clause's store id; the caller reserved the assertion symbols and configured the controller with the block's base.
    // CEP:COST: O(used) atom interns plus one new_clause.
    // CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::{conflict_lemma_staged_and_verifiable, conflict_lemma_budget_enforced, learning_disabled_by_default}.
    // CEP:SECURITY: budgets bound the staging work.
    pub fn add_conflict_lemma_from_buffer(
        &self,
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
        used: usize,
        refutation_id: u64,
    ) -> Result<Option<u64>, ControllerError> {
        if self.learning_symbol_count == 0 {
            return Ok(None);
        }
        if self.stats.learning_lemmas.get() >= self.learning_max_lemmas
            || used == 0
            || used > kMaxClauseLiterals as usize
            || used > self.conflict_slots.len()
        {
            self.stats
                .learning_skipped
                .set(self.stats.learning_skipped.get() + 1);
            return Ok(None);
        }
        let mut literals: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        for (index, literal_slot) in literals.iter_mut().enumerate().take(used) {
            let slot = self.conflict_slots[index].get();
            if slot >= self.learning_symbol_count {
                // All-or-nothing: a partial ban clause would be unsound, so an
                // unnameable slot skips the whole staging (counted).
                self.stats
                    .learning_skipped
                    .set(self.stats.learning_skipped.get() + 1);
                return Ok(None);
            }
            let atom = context
                .terms
                .intern_pred(context.symbols, self.learning_symbol_base + slot, &[])
                .map_err(crate::inference::InferenceError::from)
                .map_err(wrap_inference)?;
            *literal_slot = Literal::new(atom, false);
        }
        let derivation = DerivationStep {
            rule: InferenceRule::SatLearn,
            parent_count: 1,
            reserved: 0,
            parents: [
                refutation_id,
                kInvalidClauseId,
                kInvalidClauseId,
                kInvalidClauseId,
            ],
            substitution: kInvalidClauseOffset,
        };
        let age = space.next_input_age();
        let ptr = space
            .store
            .new_clause(context.terms, &literals[..used], age, derivation)
            .map_err(wrap_clause)?;
        let record = space.store.clause(ptr).map_err(wrap_clause)?;
        self.stats
            .learning_lemmas
            .set(self.stats.learning_lemmas.get() + 1);
        Ok(Some(record.id.0))
    }

    // CEP:WHAT: Transfers the abstraction solver's new learnt clauses (registry entries beyond the monotone cursor) into FOL SatLearn clauses over assertion atoms (Spec 18 section 4).
    // CEP:WHY: Bidirectional learning (design 18 Feature A): the SAT engine's conflict-driven lemmas are consequences of the abstraction's problem clauses, so their FOL copies are sound recorded introductions; the transfer policy keeps only small, high-quality learnts (kLearningMaxTransferLiterals, kLearningMaxTransferLbd) whose variables are all nameable component slots, every transferred clause enters the passive set (the search may use the assertion atoms), the cursor advances monotonically so each registry entry is considered at most once, and every skip is counted (Law 4); the transferred clause's derivation is parentless SatLearn (the SAT engine's own DRAT discipline covers the SAT-side derivation).
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok on every skip path (counted in stats.learning_skipped); Err propagates store and passive failures; never panics.
    // CEP:ASSUMES: called after an unconditional solve (Satisfiable); single-threaded; learning enabled by the caller's options.
    // CEP:COST: O(new registry entries) header reads plus one new_clause + one passive push per transfer.
    // CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::{transfer_learnts_enter_passive, transfer_budget_enforced, transfer_policy_filters, learning_disabled_by_default}.
    // CEP:SECURITY: budgets bound the transfer work.
    pub fn transfer_learnts(
        &self,
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
    ) -> Result<(), ControllerError> {
        if self.learning_symbol_count == 0 {
            return Ok(());
        }
        let registry = self.solver.registry();
        let storage = self.solver.core().clauses();
        let mut cursor = self.transfer_cursor.get();
        let end = registry.entry_count();
        while cursor < end {
            if self.stats.learning_transfers.get() >= self.learning_max_transfers {
                // Budget exhausted: stop WITHOUT advancing the cursor past the
                // unprocessed entries (the next unconditional solve retries);
                // the deferred batch is counted as one bounded skip (Law 4).
                self.stats
                    .learning_skipped
                    .set(self.stats.learning_skipped.get() + 1);
                break;
            }
            let entry = match registry.entry(cursor) {
                Ok(value) => value,
                Err(_) => {
                    self.stats
                        .learning_skipped
                        .set(self.stats.learning_skipped.get() + 1);
                    cursor += 1;
                    continue;
                }
            };
            if entry.tombstone.get() {
                cursor += 1;
                continue;
            }
            let offset = entry.offset.get();
            let header = match storage.header(offset) {
                Ok(value) => value,
                Err(_) => {
                    self.stats
                        .learning_skipped
                        .set(self.stats.learning_skipped.get() + 1);
                    cursor += 1;
                    continue;
                }
            };
            let learnt = header.flags & kSatClauseFlagLearnt != 0;
            let deleted = header.flags & kSatClauseFlagDeleted != 0;
            let policy = header.lbd <= kLearningMaxTransferLbd
                && header.length as u64 <= kLearningMaxTransferLiterals as u64;
            if !learnt || deleted || !policy {
                self.stats
                    .learning_skipped
                    .set(self.stats.learning_skipped.get() + 1);
                cursor += 1;
                continue;
            }
            let mut literals: [Literal; kMaxClauseLiterals as usize] =
                [Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            let mut count: usize = 0;
            let mut nameable = true;
            for position in 0..header.length {
                let sat_literal = match storage.literal(offset, position) {
                    Ok(value) => value,
                    Err(_) => {
                        nameable = false;
                        break;
                    }
                };
                let slot = sat_literal.variable().0;
                if slot >= self.learning_symbol_count || count >= literals.len() {
                    nameable = false;
                    break;
                }
                let atom = context
                    .terms
                    .intern_pred(context.symbols, self.learning_symbol_base + slot, &[])
                    .map_err(crate::inference::InferenceError::from)
                    .map_err(wrap_inference)?;
                literals[count] = Literal::new(atom, sat_literal.is_positive());
                count += 1;
            }
            if !nameable || count == 0 {
                self.stats
                    .learning_skipped
                    .set(self.stats.learning_skipped.get() + 1);
                cursor += 1;
                continue;
            }
            let derivation = DerivationStep {
                rule: InferenceRule::SatLearn,
                parent_count: 0,
                reserved: 0,
                parents: [kInvalidClauseId; 4],
                substitution: kInvalidClauseOffset,
            };
            let age = space.next_input_age();
            let ptr = space
                .store
                .new_clause(context.terms, &literals[..count], age, derivation)
                .map_err(wrap_clause)?;
            let record = space.store.clause(ptr).map_err(wrap_clause)?;
            let weight = SelectionWeight::of(context.terms, context.symbols, &literals[..count]);
            space
                .passive
                .push(record.id.0, ptr.as_u32(), age, weight)
                .map_err(wrap_passive)?;
            self.stats
                .learning_transfers
                .set(self.stats.learning_transfers.get() + 1);
            cursor += 1;
        }
        self.transfer_cursor.set(cursor);
        Ok(())
    }

    // CEP:WHAT: Returns the number of unmaterialized (waiting) components.
    // CEP:WHY: The saturation decision (Spec 12 Theorem 3) and the rotation sweep need the waiting count.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(components).
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{saturates_when_waiting_drains, model_rotation_budget_enforced}.
    // CEP:SECURITY: none.
    pub fn waiting_count(&self) -> u32 {
        let mut waiting: u32 = 0;
        for slot in 0..self.components.component_count() {
            if self.components.materialized(slot).is_none() {
                waiting += 1;
            }
        }
        waiting
    }
}

// CEP:WHAT: Runs the AVATAR saturation protocol to a terminal outcome (design 12.2's four-rule loop over the Phase 3 engine).
// CEP:WHY: Spec 12 section 5 fixes the protocol: round start solves the abstraction and activates model-true waiting components (rule 3); the inner saturate runs the given-clause loop - a direct Theorem (empty ancestry) terminates immediately, a component-ancestry Theorem adds the conflict clause and re-solves (rule 4): abstraction-unsat closes the case as Theorem (Theorem 1), a new model re-activates and the search continues (monotone: previously materialized components stay, a superset of the strict model-guided search - sound and complete, Theorem 2); Saturated with no waiting components is the honest saturation, Saturated with waiting components triggers the bounded rotation sweep (assumption solves per waiting slot; every slot unassertable proves saturation sound - Theorem 3), rotation-exhaustion past the budget is a loud GaveUp; every other GaveUp reason propagates; the should_stop callback is checked between rounds with the round counter (the CEP-1 driver ignores the counter for wall time; tests use iteration predicates - the dual use is the CEP-1005 discipline).
// CEP:STATUS: complete
// CEP:FAILURE: propagates ControllerError on structural failures; GaveUp on every named budget; never panics.
// CEP:ASSUMES: the space, context, options, and controller share one arena; inputs were added through controller.add_input_clause; the stop callback is deterministic for a fixed counter.
// CEP:COST: one abstraction solve per round plus the Phase 3 loop costs per round plus O(ids) per conflict.
// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::{refutes_split_pigeonhole, direct_refutation_bypasses_avatar, conflict_round_budget_enforced, model_rotation_budget_enforced, saturates_when_waiting_drains}; property/avatar_property_test.rs::{avatar_agrees_with_plain_saturation, avatar_refutations_check}.
// CEP:SECURITY: all budgets enforced (kAvatarMaxConflictRounds, kAvatarMaxModelRotations, the inner loop's budgets).
pub fn saturate_with_avatar<F: Fn(u64) -> bool>(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    controller: &AvatarController<'_>,
    should_stop: &F,
    stats: &mut SearchStats,
) -> Result<AvatarOutcome, ControllerError> {
    // CEP:WHAT: Round counter (also the should_stop input between rounds).
    // CEP:WHY: The dual-use counter discipline (CEP-1005): wall-clock drivers ignore it, deterministic tests bound it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: bounded by kAvatarMaxConflictRounds plus the stop callback.
    // CEP:COST: 4 bytes.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
    // CEP:SECURITY: none.
    let mut rounds: u32 = 0;
    // CEP:WHAT: Rotation-attempt counter (cumulative across saturations).
    // CEP:WHY: The kAvatarMaxModelRotations bound is global to the run (Spec 12 section 6).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 4 bytes.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
    // CEP:SECURITY: none.
    let mut rotations: u32 = 0;
    // CEP:WHAT: The refutation of the latest conflict round (the Theorem anchor when the abstraction closes).
    // CEP:WHY: An abstraction-unsat result needs a first-order refutation record for proof reconstruction (design 18.2).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: Some exactly when at least one conflict clause exists.
    // CEP:COST: 4 bytes.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: none.
    let mut last_refutation: Option<u32> = None;
    // Initial round: solve the (initially positive-only) abstraction and activate its
    // model; every later round begins with a model adopted inline by the conflict or
    // rotation handling (the only continue paths), so no round-start re-solve is needed.
    match controller.solver.solve() {
        SolveResult::Satisfiable => {
            // Spec 18 section 4: transfer the abstraction's new learnts into
            // FOL lemmas after every unconditional solve, before activation.
            controller.transfer_learnts(space, context)?;
            controller.activate_under_model(space, context, options)?;
        }
        SolveResult::Unsatisfiable => {
            // Unreachable before any conflict clause exists (all-positive clauses admit
            // the all-true model); defensively stop loudly.
            return Ok(AvatarOutcome::GaveUp(GaveUpReason::AvatarConflictBudget));
        }
        SolveResult::Indeterminate(error) => {
            return Err(ControllerError::Solver(error));
        }
    }
    loop {
        if rounds > 0 && should_stop(rounds as u64) {
            return Ok(AvatarOutcome::GaveUp(GaveUpReason::TimeBudget));
        }
        rounds += 1;
        match saturate(space, context, options, should_stop, stats)
            .map_err(ControllerError::Search)?
        {
            SearchOutcome::Theorem { refutation } => {
                let used = controller.plan_conflict(&space.store, refutation)?;
                if used == 0 {
                    return Ok(AvatarOutcome::Theorem {
                        refutation,
                        via_avatar: false,
                    });
                }
                if rounds >= controller.max_conflict_rounds {
                    return Ok(AvatarOutcome::GaveUp(GaveUpReason::AvatarConflictBudget));
                }
                // CEP:WHAT: Build the conflict clause from the controller's deduplicated slot buffer.
                // CEP:WHY: The buffer holds the ancestry's component slots (Spec 12 Lemma 2).
                // CEP:STATUS: complete
                // CEP:FAILURE: propagates the solver error on add failure.
                // CEP:ASSUMES: the buffer was just written by plan_conflict.
                // CEP:COST: O(used).
                // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
                // CEP:SECURITY: none.
                controller.add_conflict_from_buffer(used)?;
                // Spec 18 section 4: stage the FOL copy of the ban clause,
                // anchored at this round's refuting clause (all-or-nothing;
                // skips counted inside).
                let refutation_id = space
                    .store
                    .clause(crate::ir::clause::ClausePtr::from_u32(refutation))
                    .map_err(wrap_clause)?
                    .id
                    .0;
                controller.add_conflict_lemma_from_buffer(space, context, used, refutation_id)?;
                match controller.solver.solve() {
                    SolveResult::Unsatisfiable => {
                        return Ok(AvatarOutcome::Theorem {
                            refutation,
                            via_avatar: true,
                        });
                    }
                    SolveResult::Satisfiable => {
                        last_refutation = Some(refutation);
                        // Spec 18 section 4: transfer after the unconditional
                        // solve; the conflict lemma was staged below when the
                        // ban was added.
                        controller.transfer_learnts(space, context)?;
                        controller.activate_under_model(space, context, options)?;
                        continue;
                    }
                    SolveResult::Indeterminate(error) => {
                        return Err(ControllerError::Solver(error));
                    }
                }
            }
            SearchOutcome::Saturated => {
                if controller.waiting_count() == 0 {
                    return Ok(AvatarOutcome::Saturated);
                }
                // Bounded rotation sweep (Spec 12 section 6): probe every waiting slot.
                let mut adopted = false;
                for slot in 0..controller.components.component_count() {
                    if controller.components.materialized(slot).is_some() {
                        continue;
                    }
                    if rotations >= controller.max_model_rotations {
                        break;
                    }
                    rotations += 1;
                    controller.stats.rotations.set(rotations);
                    let assumption = match SatLiteral::new(SatVar(slot), true) {
                        Ok(literal) => literal,
                        Err(_) => return Err(ControllerError::InvalidOptions),
                    };
                    match controller.solver.solve_with_assumptions(&[assumption]) {
                        AssumptionOutcome::Satisfiable => {
                            controller.activate_under_model(space, context, options)?;
                            adopted = true;
                            break;
                        }
                        AssumptionOutcome::UnsatUnderAssumptions => continue,
                        AssumptionOutcome::Unsatisfiable => {
                            // The formula alone is unsat: conflicts exist, so a refutation
                            // exists; close on it (structurally guaranteed Some here).
                            return Ok(match last_refutation {
                                Some(refutation) => AvatarOutcome::Theorem {
                                    refutation,
                                    via_avatar: true,
                                },
                                None => AvatarOutcome::GaveUp(GaveUpReason::AvatarConflictBudget),
                            });
                        }
                        AssumptionOutcome::Indeterminate(error) => {
                            return Err(ControllerError::Solver(error));
                        }
                    }
                }
                if adopted {
                    continue;
                }
                if controller.waiting_count() > 0 && rotations >= controller.max_model_rotations {
                    return Ok(AvatarOutcome::GaveUp(GaveUpReason::AvatarModelBudget));
                }
                // The sweep drained the waiting set (every probe adopted and activated):
                // the search saturated over the full materialized closure (Spec 12
                // Theorem 3 - the assertability lemma guarantees the sweep always
                // finds an adoptable model while waiting components remain).
                return Ok(AvatarOutcome::Saturated);
            }
            SearchOutcome::GaveUp(reason) => return Ok(AvatarOutcome::GaveUp(reason)),
        }
    }
}
