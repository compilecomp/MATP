// CEP:FILE: hot/sat/database.rs
// CEP:WHAT: SatCore: the composite SAT state bundling assignment store, trail, watch lists, and clause storage behind one API with clause attachment, assignment, and backtracking.
// CEP:WHY: Design 11.1 components S1-S6 are separate structures but one state machine: attachment writes watch links and enqueues units, assignment writes the trail and the value array, and backtracking must pop the trail and clear values atomically; bundling them in one type makes the invariants (one value per assigned variable, trail/assignment consistency, watch-list membership) local and property-testable, while the BCP engine (sat/bcp.rs) implements propagation as methods on this type with no FFI and no locks (design 12.4).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SatCoreError for every failure path (storage, trail, assignment, invariant violations); never panics.
// CEP:ASSUMES: Single-threaded use (Cell interior mutability); the arena outlives the core; all clauses added through add_clause get exactly one watch-list attachment.
// CEP:COST: initialization is O(variables); add_clause is O(length); propagation is measured at 54.90 cycles median per step (including the reason and level recording of assign_with_reason) in bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: unit/hot/sat_watch_test.rs; unit/hot/sat_trail_test.rs; unit/hot/sat_bcp_test.rs; property/bcp_property_test.rs; bench CEP-BENCH-0005.
// CEP:SECURITY: variable counts and literal ranges are validated at initialization and clause creation; backtracking clears exactly the popped assignments.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; all state transitions are index-ordered with no clocks or addresses.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: value_of_literal loads through two nested accessors; merging the arrays (value + reason in one struct-of-arrays row) is a measured Phase 2 follow-up; ticket CEP-1016.

use crate::memory::arena::Arena;
use crate::sat::assignment::{AssignmentError, AssignmentStore, SatValue, SatVarRaw};
use crate::sat::clause::{ClauseStorage, SatClauseError};
use crate::sat::literal::SatLiteral;
use crate::sat::trail::{SatTrail, SatTrailError};
use crate::sat::watch_lists::{WatchListError, WatchLists};
use mapt_config::limits::{kInvalidClauseOffset, kMaxSatVariables};

/// CEP:WHAT: Unified error type of the SAT core.
/// CEP:WHY: CEP&CC 33.18: component-specific error vocabulary; SatCore spans four subcomponents so it flattens their errors into one enum with explicit From conversions.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs covers every variant.
/// CEP:SECURITY: bounds are denial-of-service guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatCoreError {
    /// CEP:WHAT: Clause storage failure (see SatClauseError).
    Storage(SatClauseError),
    /// CEP:WHAT: Trail failure (see SatTrailError).
    Trail(SatTrailError),
    /// CEP:WHAT: Assignment store failure (see AssignmentError).
    Assignment(AssignmentError),
    /// CEP:WHAT: An internal invariant was violated (for example assigning an already-false literal).
    InvariantViolation,
}

impl From<SatClauseError> for SatCoreError {
    // CEP:WHAT: Converts storage errors.
    // CEP:WHY: Ergonomic ? propagation from storage calls.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: none.
    fn from(error: SatClauseError) -> SatCoreError {
        SatCoreError::Storage(error)
    }
}

impl From<SatTrailError> for SatCoreError {
    // CEP:WHAT: Converts trail errors.
    // CEP:WHY: Ergonomic ? propagation from trail calls.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    // CEP:SECURITY: none.
    fn from(error: SatTrailError) -> SatCoreError {
        SatCoreError::Trail(error)
    }
}

impl From<AssignmentError> for SatCoreError {
    // CEP:WHAT: Converts assignment errors.
    // CEP:WHY: Ergonomic ? propagation from assignment calls.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: none.
    fn from(error: AssignmentError) -> SatCoreError {
        SatCoreError::Assignment(error)
    }
}

/// CEP:WHAT: Outcome of attaching (or adding) a clause.
/// CEP:WHY: Unit clauses enqueue immediately, already-satisfied units need no action, and falsified units are immediate conflicts (design 11.1 S38 activation-literal discipline simplified for Phase 1); the caller must distinguish all four cases.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::{unit_clause_enqueues, falsified_unit_conflicts}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AttachOutcome {
    /// CEP:WHAT: Clause received two watch-list links.
    Attached(u32),
    /// CEP:WHAT: Unit clause; its literal was enqueued on the trail.
    UnitEnqueued(u32),
    /// CEP:WHAT: Unit clause already satisfied by the current assignment.
    AlreadySatisfied,
    /// CEP:WHAT: Unit clause already falsified by the current assignment.
    Conflict,
}

/// CEP:WHAT: The composite SAT core state.
/// CEP:WHY: See file header.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SatCoreError.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: see file header.
/// CEP:SECURITY: see file header.
pub struct SatCore<'a> {
    /// CEP:WHAT: Declared variable count.
    /// CEP:WHY: Bounds every literal variable (watch-head and value-array safety).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: clause creation rejects out-of-range variables.
    /// CEP:ASSUMES: fixed at initialization.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/literal_encoding_test.rs.
    /// CEP:SECURITY: validation bound.
    variables: u32,
    /// CEP:WHAT: Assignment store.
    /// CEP:WHY: Design 11.1 S1.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized for `variables`.
    /// CEP:COST: 1 byte per variable.
    /// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    /// CEP:SECURITY: bounds-checked.
    assignments: AssignmentStore<'a>,
    /// CEP:WHAT: Assignment trail with levels and queue head.
    /// CEP:WHY: Design 11.1 S5/S11/S15.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized at initialization.
    /// CEP:COST: 4 bytes per capacity entry.
    /// CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    /// CEP:SECURITY: bounds-checked.
    trail: SatTrail<'a>,
    /// CEP:WHAT: Watch-list heads.
    /// CEP:WHY: Design 11.1 S6, 11.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: two heads per variable.
    /// CEP:COST: 8 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    /// CEP:SECURITY: bounds-checked.
    watches: WatchLists<'a>,
    /// CEP:WHAT: Clause storage.
    /// CEP:WHY: Design 11.1 S3/S4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: arena-backed.
    /// CEP:COST: 16 bytes plus 4 per literal.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    /// CEP:SECURITY: bounds-checked.
    clauses: ClauseStorage<'a>,
    /// CEP:WHAT: Decision level per variable (0 = unassigned or root), Phase 2 conflict-analysis input (design 11.1 S15).
    /// CEP:WHY: First-UIP analysis must know, for every literal of the conflict clause, the level at which its variable was assigned; a flat array indexed by variable keeps that a single load (design 5.5 no-hash-map discipline) and cancelling clears it in lockstep with the value array.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (infallible reads return 0 for unassigned variables).
    /// CEP:ASSUMES: sized for `variables`; kept consistent with the value array by assign/decide/cancel_until.
    /// CEP:COST: 4 bytes per variable; 1 load per analysis step.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{reasons_recorded, cancel_clears_levels}.
    /// CEP:SECURITY: bounds-checked writes; reads clamped.
    levels: &'a [core::cell::Cell<u32>],
    /// CEP:WHAT: Antecedent (reason) clause offset per variable, kInvalidClauseOffset for decisions and reasonless root assignments made through assign (design 11.1 S18-S19 input).
    /// CEP:WHY: Conflict analysis resolves a propagated literal against its reason clause; recording the reason at assign time (BCP passes the propagating clause) is what makes the implication graph walkable in O(1) per variable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (kInvalidClauseOffset marks "no reason").
    /// CEP:ASSUMES: sized for `variables`; reason clauses are never deleted in Phase 2 (deletion policy is ticket CEP-1003, Phase 3).
    /// CEP:COST: 4 bytes per variable; 1 load per analysis resolution.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{reasons_recorded, root_assignment_has_no_reason}.
    /// CEP:SECURITY: bounds-checked writes; reads validated against storage on use.
    reasons: &'a [core::cell::Cell<u32>],
}

impl<'a> SatCore<'a> {
    // CEP:WHAT: Initializes the SAT core: validates the variable count, allocates and clears all state arrays.
    // CEP:WHY: Design 19.4 discipline: every thread-visible structure is fully built before the hot path; clearing gives provable initial invariants (all unassigned, all lists empty).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns SatCoreError::Assignment(AssignmentError::VariableOutOfRange) for zero or oversize variable counts and ArenaFull-mapped errors when arrays do not fit.
    // CEP:ASSUMES: 0 < variables <= kMaxSatVariables.
    // CEP:COST: O(variables + trail capacity) one-time.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::core_initializes.
    // CEP:SECURITY: variable count validated before any allocation.
    pub fn new(arena: &'a Arena, variables: u32) -> Result<SatCore<'a>, SatCoreError> {
        if variables == 0 || variables > kMaxSatVariables {
            return Err(SatCoreError::Assignment(
                AssignmentError::VariableOutOfRange,
            ));
        }
        let assignments = AssignmentStore::new(arena, variables)?;
        let trail = SatTrail::new(arena, variables)?;
        let watches = WatchLists::new(arena, variables).map_err(|error| {
            SatCoreError::Storage(match error {
                WatchListError::ArenaFull => SatClauseError::ArenaFull,
                WatchListError::VariableCountInvalid => SatClauseError::VariableOutOfRange,
            })
        })?;
        let clauses = ClauseStorage::new(arena, variables);
        let level_range = arena
            .alloc_array::<core::cell::Cell<u32>>(variables)
            .map_err(|_| SatCoreError::Storage(SatClauseError::ArenaFull))?;
        let levels = arena
            .array::<core::cell::Cell<u32>>(level_range)
            .map_err(|_| SatCoreError::Storage(SatClauseError::InvalidClauseOffset))?;
        let reason_range = arena
            .alloc_array::<core::cell::Cell<u32>>(variables)
            .map_err(|_| SatCoreError::Storage(SatClauseError::ArenaFull))?;
        let reasons = arena
            .array::<core::cell::Cell<u32>>(reason_range)
            .map_err(|_| SatCoreError::Storage(SatClauseError::InvalidClauseOffset))?;
        for index in 0..variables as usize {
            levels[index].set(0);
            reasons[index].set(kInvalidClauseOffset);
        }
        Ok(SatCore {
            variables,
            assignments,
            trail,
            watches,
            clauses,
            levels,
            reasons,
        })
    }

    // CEP:WHAT: Returns the declared variable count.
    // CEP:WHY: Bounds documentation and the verifier.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::core_initializes.
    // CEP:SECURITY: none.
    pub fn variable_count(&self) -> u32 {
        self.variables
    }

    // CEP:WHAT: Returns the three-valued value of a literal under the current assignment.
    // CEP:WHY: The single value-evaluation entry point shared by BCP, attach, and decisions; polarity-aware so callers never re-derive it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (out-of-range variables read as Unassigned by the store).
    // CEP:ASSUMES: literal variables are below the declared count.
    // CEP:COST: 1 load + 2 compares.
    // CEP:EVIDENCE: unit/hot/sat_literal_test.rs::value_evaluation.
    // CEP:SECURITY: none.
    pub fn value_of_literal(&self, literal: SatLiteral) -> SatValue {
        let value = self.assignments.value(SatVarRaw(literal.variable().0));
        match value {
            SatValue::Unassigned => SatValue::Unassigned,
            SatValue::True => {
                if literal.is_positive() {
                    SatValue::True
                } else {
                    SatValue::False
                }
            }
            SatValue::False => {
                if literal.is_positive() {
                    SatValue::False
                } else {
                    SatValue::True
                }
            }
        }
    }

    // CEP:WHAT: Assigns a literal true at the current level (trail push plus value write) with no antecedent clause.
    // CEP:WHY: The only sanctioned assignment path, so trail and values can never diverge (design 11.1 S5 invariant); the reasonless form serves decisions, root (level-0) assignments, and asserting literals of learnt unit clauses, all of which have no propagating clause.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvariantViolation when the literal is already false (caller bug surfaced loudly); propagates TrailFull and Assignment errors.
    // CEP:ASSUMES: callers assign only unassigned or true literals (BCP checks before calling; property-tested).
    // CEP:COST: 1 compare + 2 stores + trail push.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::propagation_drains_queue; unit/hot/sat_cdcl_test.rs::root_assignment_has_no_reason.
    // CEP:SECURITY: defensive invariant check retained in release.
    pub fn assign(&self, literal: SatLiteral) -> Result<(), SatCoreError> {
        self.assign_with_reason(literal, kInvalidClauseOffset)
    }

    // CEP:WHAT: Assigns a literal true at the current level, recording the antecedent clause for conflict analysis.
    // CEP:WHY: Design 11.1 S18/S19: the implication graph is walked through per-variable reason clauses; BCP records the propagating clause here, and learnt-clause assertion records the learnt clause, which is what makes first-UIP resolution sound (Formal Spec 06).
    // CEP:STATUS: complete
    // CEP:FAILURE: as assign(); the reason offset is stored unvalidated (validated when read by analysis).
    // CEP:ASSUMES: reason is a clause offset of this core's storage or kInvalidClauseOffset.
    // CEP:COST: as assign() plus 2 stores (level, reason).
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::reasons_recorded.
    // CEP:SECURITY: index bounds-checked.
    pub fn assign_with_reason(&self, literal: SatLiteral, reason: u32) -> Result<(), SatCoreError> {
        let variable = literal.variable().0 as usize;
        if variable >= self.levels.len() {
            return Err(SatCoreError::Assignment(
                AssignmentError::VariableOutOfRange,
            ));
        }
        match self.value_of_literal(literal) {
            SatValue::True => Ok(()),
            SatValue::False => Err(SatCoreError::InvariantViolation),
            SatValue::Unassigned => {
                self.trail.push_assignment(literal)?;
                let value = if literal.is_positive() {
                    SatValue::True
                } else {
                    SatValue::False
                };
                self.assignments
                    .set_value(SatVarRaw(literal.variable().0), value)?;
                self.levels[variable].set(self.trail.level());
                self.reasons[variable].set(reason);
                Ok(())
            }
        }
    }

    // CEP:WHAT: Returns the decision level at which a variable was assigned (0 when unassigned or root).
    // CEP:WHY: Conflict analysis and the learnt-clause backjump computation read the level of every literal (design 11.1 S15, S22).
    // CEP:STATUS: complete
    // CEP:FAILURE: none; out-of-range variables read as 0 (clamped, deterministic).
    // CEP:ASSUMES: variable below the declared count.
    // CEP:COST: 1 bounds check + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::reasons_recorded.
    // CEP:SECURITY: clamped read, no out-of-range access.
    pub fn level_of(&self, variable: u32) -> u32 {
        let index = variable as usize;
        if index >= self.levels.len() {
            return 0;
        }
        self.levels[index].get()
    }

    // CEP:WHAT: Returns the antecedent clause offset of a variable (kInvalidClauseOffset for decisions and root assignments).
    // CEP:WHY: Conflict analysis resolves propagated literals against their reasons (design 11.1 S19).
    // CEP:STATUS: complete
    // CEP:FAILURE: none; out-of-range variables read as no-reason (clamped, deterministic).
    // CEP:ASSUMES: variable below the declared count.
    // CEP:COST: 1 bounds check + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{reasons_recorded, root_assignment_has_no_reason}.
    // CEP:SECURITY: clamped read.
    pub fn reason_of(&self, variable: u32) -> u32 {
        let index = variable as usize;
        if index >= self.reasons.len() {
            return kInvalidClauseOffset;
        }
        self.reasons[index].get()
    }

    // CEP:WHAT: Opens a new decision level and assigns the decision literal.
    // CEP:WHY: Decision heuristics (Phase 2, S12) need the level structure now so BCP's level-relative behavior is testable.
    // CEP:STATUS: complete
    // CEP:FAILURE: as assign(), plus TooManyLevels.
    // CEP:ASSUMES: literal is unassigned.
    // CEP:COST: as assign() plus level push.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    // CEP:SECURITY: none.
    pub fn decide(&self, literal: SatLiteral) -> Result<(), SatCoreError> {
        if self.value_of_literal(literal) == SatValue::False {
            return Err(SatCoreError::InvariantViolation);
        }
        if self.value_of_literal(literal) == SatValue::True {
            return Ok(());
        }
        let variable = literal.variable().0 as usize;
        if variable >= self.levels.len() {
            return Err(SatCoreError::Assignment(
                AssignmentError::VariableOutOfRange,
            ));
        }
        self.trail.push_decision(literal)?;
        let value = if literal.is_positive() {
            SatValue::True
        } else {
            SatValue::False
        };
        self.assignments
            .set_value(SatVarRaw(literal.variable().0), value)?;
        self.levels[variable].set(self.trail.level());
        self.reasons[variable].set(kInvalidClauseOffset);
        Ok(())
    }

    // CEP:WHAT: Adds a clause and attaches it (watches for length >= 2, immediate enqueue for units).
    // CEP:WHY: Design 11.1 S3/S4/S6: one entry point keeps creation and attachment atomic so no unwatched clause can ever be observed by BCP.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates storage and assignment errors; returns AttachOutcome::Conflict for falsified units without error (a legitimate SAT outcome).
    // CEP:ASSUMES: literals are non-empty; duplicates and tautologies stored verbatim (sanitization is Phase 3).
    // CEP:COST: O(length).
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::{unit_clause_enqueues, falsified_unit_conflicts}; unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: length and variable bounds validated.
    pub fn add_clause(&self, literals: &[SatLiteral]) -> Result<AttachOutcome, SatCoreError> {
        let offset = self.clauses.new_clause(literals, false, 0)?;
        self.attach_clause(offset)
    }

    // CEP:WHAT: Adds a learnt clause and attaches it.
    // CEP:WHY: Design 11.1 S21: learnt clauses enter the same database with the learnt flag; the LBD is recorded for the future deletion policy (S23-S26).
    // CEP:STATUS: complete
    // CEP:FAILURE: as add_clause, plus LearntBudgetExceeded.
    // CEP:ASSUMES: Phase 2 conflict analysis produces the literals and LBD; Phase 1 exercises the path for budget enforcement.
    // CEP:COST: as add_clause.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::learnt_budget_enforced.
    // CEP:SECURITY: learnt budget bounded.
    pub fn add_learnt_clause(
        &self,
        literals: &[SatLiteral],
        lbd: u8,
    ) -> Result<AttachOutcome, SatCoreError> {
        let offset = self.clauses.new_clause(literals, true, lbd)?;
        self.attach_clause(offset)
    }

    // CEP:WHAT: Attaches an existing clause to the watch lists or enqueues its unit literal.
    // CEP:WHY: Design 11.3: exactly two watches for clauses of length >= 2, none for units; attachment is push-front on both lists.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates storage and assignment errors.
    // CEP:ASSUMES: the clause was created by this core's storage.
    // CEP:COST: O(1) plus possible unit enqueue.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: none.
    pub fn attach_clause(&self, offset: u32) -> Result<AttachOutcome, SatCoreError> {
        let header = self.clauses.header(offset)?;
        if header.length == 1 {
            let unit = self.clauses.literal(offset, 0)?;
            return match self.value_of_literal(unit) {
                SatValue::True => Ok(AttachOutcome::AlreadySatisfied),
                SatValue::False => Ok(AttachOutcome::Conflict),
                SatValue::Unassigned => {
                    self.assign_with_reason(unit, offset)?;
                    Ok(AttachOutcome::UnitEnqueued(offset))
                }
            };
        }
        let watch0 = self.clauses.literal(offset, 0)?;
        let watch1 = self.clauses.literal(offset, 1)?;
        let old0 = self.watches.head(watch0);
        self.clauses.set_next_in_watch(offset, 0, old0)?;
        self.watches.push_front(watch0, offset);
        let old1 = self.watches.head(watch1);
        self.clauses.set_next_in_watch(offset, 1, old1)?;
        self.watches.push_front(watch1, offset);
        Ok(AttachOutcome::Attached(offset))
    }

    // CEP:WHAT: Backtracks to a decision level, clearing the assignments of every popped literal.
    // CEP:WHY: Design 11.1 S22: backjumping must keep trail and value array consistent; clearing by walking the popped segment guarantees exactly the popped variables are unassigned.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; target levels are clamped by the trail.
    // CEP:ASSUMES: the trail holds each assigned variable at most once (property-tested).
    // CEP:COST: O(popped entries).
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::cancel_restores_assignments.
    // CEP:SECURITY: clamped level arithmetic.
    pub fn cancel_until(&self, level: u32) {
        let keep = self.trail.cancel_keep_index(level);
        let mut index = self.trail.len();
        while index > keep {
            index -= 1;
            if let Some(literal) = self.trail.literal_at(index) {
                let variable = literal.variable().0;
                let raw = SatVarRaw(variable);
                let cleared = self.assignments.set_value(raw, SatValue::Unassigned);
                debug_assert!(cleared.is_ok());
                let slot = variable as usize;
                if slot < self.levels.len() {
                    self.levels[slot].set(0);
                    self.reasons[slot].set(kInvalidClauseOffset);
                }
            }
        }
        self.trail.cancel_until(level);
    }

    // CEP:WHAT: Returns a reference to the trail (read access for BCP and tests).
    // CEP:WHY: BCP drains the queue through the trail; tests inspect levels.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    // CEP:SECURITY: read-only projection.
    pub fn trail(&self) -> &SatTrail<'a> {
        &self.trail
    }

    // CEP:WHAT: Returns a reference to the clause storage (read access for tests and the verifier).
    // CEP:WHY: Property tests verify watch invariants by reading headers and literals.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: property/bcp_property_test.rs.
    // CEP:SECURITY: read-only projection.
    pub fn clauses(&self) -> &ClauseStorage<'a> {
        &self.clauses
    }

    // CEP:WHAT: Returns a reference to the watch lists (read access for BCP and tests).
    // CEP:WHY: BCP reads heads and pushes new links through this projection, keeping the field private.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: read-only projection of the head array.
    pub fn watches(&self) -> &WatchLists<'a> {
        &self.watches
    }
}
