// CEP:FILE: hot/sat/solver.rs
// CEP:WHAT: The CDCL search loop: propagate, decide via VSIDS with saved phases, analyze conflicts (first UIP), learn, backjump, and restart, integrated over one SatCore, one analyzer, one VSIDS heap, one phase table, and one restart scheduler.
// CEP:WHY: Design 26 (Phase 2 build order: "SAT: CDCL (conflict analysis, learning, backjump)", "decision heuristic (VSIDS)", "restart strategy") and design 11: the loop is the composition point of S9-S24; every component is arena-backed and the loop itself performs no allocation, so the whole search is CEP-0; the loop is also the integration test vehicle (solve-vs-brute-force property tests) and the bench vehicle for per-conflict and per-decision cost evidence.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns Indeterminate(CdclError) on structural failures, the conflict budget, or over-long learnt clauses; Unsatisfiable on level-0 conflicts and falsified learnt units; Satisfiable when every variable is assigned. Never panics.
// CEP:ASSUMES: Clauses are added at level 0 before solve; single-threaded; the learnt-clause budget kSatMaxLearntClauses is enforced at creation (deletion policy is ticket CEP-1003, Phase 3), so exhausting it makes the solve Indeterminate rather than silent.
// CEP:COST: per iteration: one propagate (54.90 cycles median per step including reason and level recording, bench CEP-BENCH-0005) plus one decision (420.41 cycles median, bench CEP-BENCH-0009) plus per-conflict analysis and learning (697.42 cycles median, bench CEP-BENCH-0009); end-to-end PHP(3,4) refutation measured 5372.33 cycles per conflict on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0009, artifact benches/artifacts/cdcl_solve_per_conflict.json; the loop is allocation-free after construction.
// CEP:EVIDENCE: unit/hot/sat_solver_test.rs; property/cdcl_property_test.rs::{solve_agrees_with_brute_force, models_satisfy_formulas, learnt_clauses_are_entailed}; fuzz/cdcl_fuzz_test.rs; bench CEP-BENCH-0009.
// CEP:SECURITY: all state transitions go through the bounds-checked SatCore APIs; the conflict budget bounds adversarial workloads.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; decisions, propagation, analysis, learning, and restarts are all pure functions of the clause set and the arena state (CEP&CC 38.10), verified by the two-identical-solves test.
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 8 fixes the loop contract: the search terminates with Satisfiable only when every variable is assigned and BCP is at fixpoint (a model), with Unsatisfiable only after a conflict at level 0 (entailed by the empty resolvent), and CDCL with restarts and bounded learning terminates; the property tests verify both outcomes against a brute-force oracle.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: the loop re-reads trail state through accessors per iteration and the learnt buffer is copied per conflict; both are measurement-deferred micro-optimizations; ticket CEP-1032.

use crate::memory::arena::Arena;
use crate::sat::assignment::SatValue;
use crate::sat::bcp::PropagationOutcome;
use crate::sat::cdcl::{CdclError, ConflictAnalyzer};
use crate::sat::database::{AttachOutcome, SatCore};
use crate::sat::literal::{SatLiteral, SatVar};
use crate::sat::restart::{RestartPolicy, RestartScheduler};
use crate::sat::vsids::{PhaseTable, VsidsHeap};
use core::cell::Cell;
use mapt_config::limits::{kMaxSatClauseLiterals, kMaxSatVariables, kSatMaxConflicts};

/// CEP:WHAT: Outcome of one solve.
/// CEP:WHY: CEP&CC Law 6: the three SAT outcomes plus the explicit indeterminate result that carries the bounded-failure reason (budget, structure, over-long learnts); conflating Indeterminate with Unsatisfiable would be unsound (design 2.2 result vocabulary).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, empty_formula_is_satisfiable, conflict_budget_returns_indeterminate}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolveResult {
    /// CEP:WHAT: Every variable assigned and BCP at fixpoint; read the model with model_value.
    /// CEP:WHY: The satisfying outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: property/cdcl_property_test.rs::models_satisfy_formulas.
    /// CEP:SECURITY: none.
    Satisfiable,
    /// CEP:WHAT: A conflict at decision level 0 (or a falsified learnt unit at level 0).
    /// CEP:WHY: The refuting outcome (Spec 06 section 8).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: property/cdcl_property_test.rs::solve_agrees_with_brute_force.
    /// CEP:SECURITY: none.
    Unsatisfiable,
    /// CEP:WHAT: The search stopped on a bounded failure; the error identifies which bound.
    /// CEP:WHY: Design 20.2: exceeded limits are explicit results, never silent continuation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: none.
    Indeterminate(CdclError),
}

/// CEP:WHAT: The CDCL solver: SAT core, conflict analyzer, VSIDS heap, phase table, restart scheduler, and the conflict counter, composed into one search state machine.
/// CEP:WHY: Design 11.1 components S9-S24 compose into the loop of design 11.4/26; owning the substructures in one type keeps their invariants (heap membership mirrors assignments, phases mirror last assignments, restart counter mirrors conflicts) local and testable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SolveResult and CdclError.
/// CEP:ASSUMES: single-threaded; clauses added at level 0 before solve.
/// CEP:COST: construction is O(variables); the loop is allocation-free.
/// CEP:EVIDENCE: unit/hot/sat_solver_test.rs; property/cdcl_property_test.rs; fuzz/cdcl_fuzz_test.rs.
/// CEP:SECURITY: all substructure APIs are bounds-checked.
pub struct CdclSolver<'a> {
    /// CEP:WHAT: The SAT core (values, trail, watches, clauses, levels, reasons).
    /// CEP:WHY: Design 11.1 S1-S6.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: shared with no other owner.
    /// CEP:COST: see SatCore.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs.
    /// CEP:SECURITY: bounds-checked APIs.
    core: SatCore<'a>,
    /// CEP:WHAT: The conflict analyzer.
    /// CEP:WHY: Design 11.1 S18-S20.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized for the same variable count as the core.
    /// CEP:COST: 14 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs.
    /// CEP:SECURITY: bounds-checked.
    analyzer: ConflictAnalyzer<'a>,
    /// CEP:WHAT: The VSIDS decision heap.
    /// CEP:WHY: Design 11.1 S7/S12/S13.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: heap membership mirrors unassigned variables.
    /// CEP:COST: 16 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs.
    /// CEP:SECURITY: bounds-checked.
    vsids: VsidsHeap<'a>,
    /// CEP:WHAT: The phase-saving table.
    /// CEP:WHY: Design 11.1 S8/S14/S17.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: phases mirror last assignments.
    /// CEP:COST: 1 byte per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    /// CEP:SECURITY: bounds-checked.
    phases: PhaseTable<'a>,
    /// CEP:WHAT: The restart scheduler.
    /// CEP:WHY: Design 11.1 S16.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one conflict per note_conflict.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs.
    /// CEP:SECURITY: none.
    restarts: RestartScheduler,
    /// CEP:WHAT: Conflicts analyzed in this solve.
    /// CEP:WHY: The kSatMaxConflicts budget counter (design 20.1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: solve returns Indeterminate past the budget.
    /// CEP:ASSUMES: reset never happens (one solve per instance in Phase 2).
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: denial-of-service bound.
    conflicts: Cell<u64>,
    /// CEP:WHAT: Whether restarts clear the phase table.
    /// CEP:WHY: Design 11.1 S17: "Reset on restart (configurable)".
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::phase_reset_configuration.
    /// CEP:SECURITY: none.
    reset_phases_on_restart: bool,
    /// CEP:WHAT: Whether a level-0 clause addition reported an immediate conflict (a falsified unit).
    /// CEP:WHY: BCP never rescans unit clauses (they carry no watches), so a unit falsified by earlier level-0 assignments would otherwise be invisible to the propagation loop; the flag makes the refutation explicit (Law 6; Spec 06 section 8).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: solve returns Unsatisfiable once set.
    /// CEP:ASSUMES: set only by add_clause at level 0.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::unit_conflict_at_root_is_unsat.
    /// CEP:SECURITY: none.
    root_conflict: Cell<bool>,
}

impl<'a> CdclSolver<'a> {
    // CEP:WHAT: Constructs the solver: core, analyzer, VSIDS heap, phase table, and scheduler for the declared variable count and policy.
    // CEP:WHY: Design 19.4: every structure is fully built before the hot path; the restart policy and phase-reset flag are the two configuration points the design names for Phase 2 (design 11.1 S14/S16/S17).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns CdclError::Storage on arena exhaustion and invalid variable counts.
    // CEP:ASSUMES: 0 < variables <= kMaxSatVariables; the arena has room for all substructures.
    // CEP:COST: O(variables) one-time.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{empty_formula_is_satisfiable, construction_rejects_zero_variables}.
    // CEP:SECURITY: count validated before allocation.
    pub fn new(
        arena: &'a Arena,
        variables: u32,
        policy: RestartPolicy,
        reset_phases_on_restart: bool,
    ) -> Result<CdclSolver<'a>, CdclError> {
        if variables == 0 || variables > kMaxSatVariables {
            return Err(CdclError::Storage(
                crate::sat::database::SatCoreError::Assignment(
                    crate::sat::assignment::AssignmentError::VariableOutOfRange,
                ),
            ));
        }
        let core = SatCore::new(arena, variables)?;
        let analyzer = ConflictAnalyzer::new(arena, variables)?;
        let vsids = VsidsHeap::new(arena, variables).map_err(|_| {
            CdclError::Storage(crate::sat::database::SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        let phases = PhaseTable::new(arena, variables).map_err(|_| {
            CdclError::Storage(crate::sat::database::SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        Ok(CdclSolver {
            core,
            analyzer,
            vsids,
            phases,
            restarts: RestartScheduler::new(policy),
            conflicts: Cell::new(0),
            reset_phases_on_restart,
            root_conflict: Cell::new(false),
        })
    }

    // CEP:WHAT: Adds a problem clause at level 0 before solving.
    // CEP:WHY: The solver-owned entry point keeps the level-0 discipline in one place (analysis assumes clauses never appear mid-search).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SatCoreError (empty clause, bounds, budget); a falsified unit returns AttachOutcome::Conflict and the solve (or the caller) decides UNSAT.
    // CEP:ASSUMES: called before solve and only at level 0.
    // CEP:COST: as SatCore::add_clause.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, unit_conflict_at_root_is_unsat}.
    // CEP:SECURITY: validation in the core.
    pub fn add_clause(&self, literals: &[SatLiteral]) -> Result<AttachOutcome, CdclError> {
        if self.core.trail().level() != 0 {
            return Err(CdclError::Storage(
                crate::sat::database::SatCoreError::InvariantViolation,
            ));
        }
        let outcome = self.core.add_clause(literals).map_err(CdclError::from)?;
        if outcome == AttachOutcome::Conflict {
            // A unit clause falsified by existing level-0 assignments: the formula is
            // refuted at the root; BCP will never rescan it (units carry no watches),
            // so the solver records the refutation here (Spec 06 section 8).
            self.root_conflict.set(true);
        }
        Ok(outcome)
    }

    // CEP:WHAT: Returns the value of a variable after a Satisfiable solve.
    // CEP:WHY: Model extraction (design 11.1 S40 for the standalone case).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (None when unassigned, which cannot happen after Satisfiable).
    // CEP:ASSUMES: called after solve returned Satisfiable for meaningful results.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: property/cdcl_property_test.rs::models_satisfy_formulas.
    // CEP:SECURITY: clamped read.
    pub fn model_value(&self, variable: u32) -> Option<bool> {
        match self
            .core
            .value_of_literal(SatLiteral::new(SatVar(variable), true).ok()?)
        {
            SatValue::True => Some(true),
            SatValue::False => Some(false),
            SatValue::Unassigned => None,
        }
    }

    // CEP:WHAT: Returns the number of conflicts analyzed.
    // CEP:WHY: Budget introspection for tests and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    // CEP:SECURITY: none.
    pub fn conflicts(&self) -> u64 {
        self.conflicts.get()
    }

    // CEP:WHAT: Returns the number of restarts performed.
    // CEP:WHY: Restart introspection for tests.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero.
    // CEP:SECURITY: none.
    pub fn restarts_done(&self) -> u32 {
        self.restarts.restarts_done()
    }

    // CEP:WHAT: Returns a reference to the SAT core (read access for tests and future proof output).
    // CEP:WHY: Tests inspect trail, values, and learnt clauses without widening the solver API.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: read-only use.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero.
    // CEP:SECURITY: read-only projection.
    pub fn core(&self) -> &SatCore<'a> {
        &self.core
    }

    // CEP:WHAT: Runs the CDCL loop to Satisfiable, Unsatisfiable, or Indeterminate.
    // CEP:WHY: Spec 06 section 8: propagate to fixpoint; on conflict analyze, learn, backjump, and assert; on quiescence decide via VSIDS with the saved phase; restart at the scheduler's threshold; exhaustion of decision candidates with a fixpoint trail is a model, a level-0 conflict is a refutation.
    // CEP:STATUS: complete
    // CEP:FAILURE: see SolveResult; never panics.
    // CEP:ASSUMES: see file header (clauses at level 0, single-threaded).
    // CEP:COST: see file header; measured in bench CEP-BENCH-0009.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, pigeonhole_is_unsat, unit_conflict_at_root_is_unsat, restart_returns_to_level_zero, deterministic_across_repeated_solves}; property/cdcl_property_test.rs::{solve_agrees_with_brute_force, models_satisfy_formulas, learnt_clauses_are_entailed}; fuzz/cdcl_fuzz_test.rs.
    // CEP:SECURITY: bounded by the conflict budget and every substructure bound.
    pub fn solve(&self) -> SolveResult {
        if self.root_conflict.get() {
            return SolveResult::Unsatisfiable;
        }
        // Buffer init: from_encoding(0) is the positive literal of variable 0, a valid
        // filler entry; analysis writes the real literals before literal_count ever lets
        // the caller read them.
        let mut learnt_buffer: [SatLiteral; kMaxSatClauseLiterals as usize] =
            [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize];
        loop {
            let propagation = match self.core.propagate() {
                Ok(outcome) => outcome,
                Err(error) => return SolveResult::Indeterminate(CdclError::from(error)),
            };
            match propagation {
                PropagationOutcome::Conflict(conflict) => {
                    if self.core.trail().level() == 0 {
                        return SolveResult::Unsatisfiable;
                    }
                    let conflict_count = self.conflicts.get().saturating_add(1);
                    self.conflicts.set(conflict_count);
                    if conflict_count > kSatMaxConflicts {
                        return SolveResult::Indeterminate(CdclError::ConflictBudgetExceeded);
                    }
                    self.restarts.note_conflict();
                    self.vsids.decay();
                    let outcome = match self.analyzer.analyze(
                        &self.core,
                        &self.vsids,
                        conflict,
                        &mut learnt_buffer,
                    ) {
                        Ok(outcome) => outcome,
                        Err(error) => return SolveResult::Indeterminate(error),
                    };
                    let literals = &learnt_buffer[..outcome.literal_count as usize];
                    if outcome.literal_count == 1 {
                        // Unit learnt: backjump first so the unit is asserted at its level.
                        self.backtrack(outcome.backjump_level);
                        match self.core.add_learnt_clause(literals, outcome.lbd as u8) {
                            Ok(AttachOutcome::UnitEnqueued(_)) => {}
                            Ok(AttachOutcome::AlreadySatisfied) => {}
                            Ok(AttachOutcome::Conflict) => return SolveResult::Unsatisfiable,
                            Ok(AttachOutcome::Attached(_)) => {}
                            Err(error) => {
                                return SolveResult::Indeterminate(CdclError::from(error))
                            }
                        }
                    } else {
                        let attached = match self
                            .core
                            .add_learnt_clause(literals, outcome.lbd as u8)
                        {
                            Ok(AttachOutcome::Attached(offset)) => offset,
                            Ok(_) => {
                                // A multi-literal learnt always attaches (length >= 2
                                // never enqueues or conflicts at attach time); any other
                                // outcome is an internal inconsistency surfaced loudly.
                                return SolveResult::Indeterminate(CdclError::MalformedConflict);
                            }
                            Err(error) => {
                                return SolveResult::Indeterminate(CdclError::from(error))
                            }
                        };
                        self.backtrack(outcome.backjump_level);
                        if let Err(error) = self.core.assign_with_reason(learnt_buffer[0], attached)
                        {
                            return SolveResult::Indeterminate(CdclError::from(error));
                        }
                    }
                }
                PropagationOutcome::NoConflict => {
                    if self.restarts.should_restart() {
                        self.backtrack(0);
                        self.restarts.record_restart();
                        if self.reset_phases_on_restart {
                            self.phases.reset();
                        }
                        continue;
                    }
                    let decision = self.vsids.pick_unassigned(|variable| {
                        match SatLiteral::new(SatVar(variable), true) {
                            Ok(literal) => {
                                self.core.value_of_literal(literal) != SatValue::Unassigned
                            }
                            Err(_) => true,
                        }
                    });
                    match decision {
                        None => return SolveResult::Satisfiable,
                        Some(variable) => {
                            let positive = self.phases.phase(variable);
                            let literal = match SatLiteral::new(SatVar(variable), positive) {
                                Ok(literal) => literal,
                                Err(_) => {
                                    return SolveResult::Indeterminate(CdclError::Storage(
                                        crate::sat::database::SatCoreError::InvariantViolation,
                                    ))
                                }
                            };
                            if let Err(error) = self.core.decide(literal) {
                                return SolveResult::Indeterminate(CdclError::from(error));
                            }
                        }
                    }
                }
            }
        }
    }

    // CEP:WHAT: Backtracks to a level, saving phases and reinserting variables into the VSIDS heap for every popped assignment.
    // CEP:WHY: Design 11.1 S17 (save polarity) and the MiniSat heap discipline (unassigned variables return to the decision heap); walking the popped segment before core cancellation keeps the three structures consistent.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: level <= current level.
    // CEP:COST: O(popped entries).
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{restart_returns_to_level_zero, restart_preserves_learnts}; unit/hot/sat_vsids_test.rs::insert_after_backtrack.
    // CEP:SECURITY: clamped level arithmetic in the core.
    fn backtrack(&self, level: u32) {
        let keep = self.core.trail().cancel_keep_index(level);
        let mut index = self.core.trail().len();
        while index > keep {
            index -= 1;
            if let Some(literal) = self.core.trail().literal_at(index) {
                let variable = literal.variable().0;
                self.phases.save_phase(variable, literal.is_positive());
                self.vsids.insert(variable);
            }
        }
        self.core.cancel_until(level);
    }
}
