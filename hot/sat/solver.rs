// CEP:FILE: hot/sat/solver.rs
// CEP:WHAT: The CDCL search loop: propagate, decide via VSIDS with saved phases, analyze conflicts (first UIP), learn, backjump, and restart, integrated over one SatCore, one analyzer, one VSIDS heap, one phase table, and one restart scheduler; Phase 3 adds the enumerable clause registry with the learnt-deletion reduction policy, optional DRAT proof recording of the clause lifecycle, and assumption-based incremental solving with failed-core extraction (analyze_final).
// CEP:WHY: Design 26 (Phase 2 build order: CDCL analysis/learning/backjump, VSIDS, restarts; Phase 3 build order: "incremental solving + assumptions", "proof logging (DRAT)") and design 11: the loop is the composition point of S9-S43; every component is arena-backed and the loop itself performs no allocation, so the whole search is CEP-0; the loop is also the integration-test vehicle (solve-vs-brute-force property tests) and the bench vehicle for per-conflict and per-decision cost evidence.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns Indeterminate(CdclError) on structural failures, the conflict budget, proof-buffer exhaustion, or over-long learnt clauses; Unsatisfiable on level-0 conflicts and falsified learnt units; Satisfiable when every variable is assigned; UnsatUnderAssumptions when the refutation requires the pushed assumptions (the core is then readable via failed_assumptions). Never panics.
// CEP:ASSUMES: Clauses are added at level 0 before solve; single-threaded; assumption literals belong to declared variables and repeat at most kMaxAssumptions per call; learnt clauses learned during an assumption solve are deleted on that solve's exit (they may depend on the assumptions), so incremental solves of the base formula stay sound.
// CEP:COST: per iteration: one propagate (54.90 cycles median per step including reason and level recording, bench CEP-BENCH-0005) plus one decision (420.41 cycles median, bench CEP-BENCH-0009) plus per-conflict analysis and learning (697.42 cycles median, bench CEP-BENCH-0009); end-to-end PHP(3,4) refutation measured 5372.33 cycles per conflict on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0009, artifact benches/artifacts/cdcl_solve_per_conflict.json; registry bookkeeping adds one O(1) registration per learnt clause (bench CEP-BENCH-0010, artifact benches/artifacts/sat_registry_step.json) and proof recording, when enabled, one O(1) append per clause add and delete (the append primitive measured by bench CEP-BENCH-0013, artifact benches/artifacts/sat_drat_record.json); the loop is allocation-free after construction.
// CEP:EVIDENCE: unit/hot/sat_solver_test.rs; unit/hot/sat_registry_test.rs; unit/hot/sat_assumptions_test.rs; unit/hot/sat_proof_test.rs; property/cdcl_property_test.rs::{solve_agrees_with_brute_force, models_satisfy_formulas, learnt_clauses_are_entailed}; property/sat_incremental_property_test.rs; fuzz/cdcl_fuzz_test.rs; bench CEP-BENCH-0005, CEP-BENCH-0009, CEP-BENCH-0010, CEP-BENCH-0013.
// CEP:SECURITY: all state transitions go through the bounds-checked SatCore APIs; the conflict budget, the registry capacity, and the proof capacities bound adversarial workloads.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; decisions, propagation, analysis, learning, restarts, reduction, and proof recording are pure functions of the clause set and the arena state (CEP&CC 38.10), verified by property/cdcl_property_test.rs::two_identical_solves (identical result, conflict, restart, and proof-step counts across fresh double solves, with reduction firing and proof recording on).
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 5 fixes the loop contract (the search terminates with Satisfiable only at a model, with Unsatisfiable only after a level-0 refutation, and CDCL with restarts, bounded learning, and bounded deletion terminates) and Spec 06 section 9 fixes the reduction contract; Formal Spec 10 sections 3-5 fix the assumption contract (root levels, backjump clamping, and the analyze_final core); Formal Spec 11 fixes the proof-recording contract; all three are verified against brute-force oracles in the property tests.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: the loop re-reads trail state through accessors per iteration and the learnt buffer is copied per conflict; both are measurement-deferred micro-optimizations; ticket CEP-1032.

use crate::memory::arena::Arena;
use crate::sat::assignment::SatValue;
use crate::sat::bcp::PropagationOutcome;
use crate::sat::cdcl::{CdclError, ConflictAnalyzer};
use crate::sat::database::{AttachOutcome, SatCore, SatCoreError};
use crate::sat::literal::{SatLiteral, SatVar};
use crate::sat::proof::ProofRecorder;
use crate::sat::registry::ClauseRegistry;
use crate::sat::restart::{RestartPolicy, RestartScheduler};
use crate::sat::vsids::{PhaseTable, VsidsHeap};
use core::cell::Cell;
use mapt_config::limits::{
    kMaxAssumptions, kMaxSatClauseLiterals, kMaxSatVariables, kSatBceMaxClauseLength,
    kSatBceStackDepth, kSatExtEntryLiterals, kSatMaxConflicts, kSatMaxLearntClauses,
    kSatProofLiteralCapacity, kSatProofMapCapacity, kSatProofStepCapacity, kSatRegistryCapacity,
};

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

/// CEP:WHAT: Outcome of one assumption-based solve (design 11.1 S38/S39).
/// CEP:WHY: Incremental solving distinguishes "the formula alone is unsatisfiable" from "the formula conjoined with the pushed assumptions is unsatisfiable" - the latter carries a failed core whose negation the formula entails, which is exactly what AVATAR component splitting consumes (design 12.2); conflating the two would make unsound splits possible.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: the failed core is only meaningful after UnsatUnderAssumptions.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{satisfiable_under_assumptions, unsat_formula_returns_unsat, unsat_under_assumptions_yields_core}; property/sat_incremental_property_test.rs::assumption_solves_agree_with_brute_force.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssumptionOutcome {
    /// CEP:WHAT: The formula plus the assumptions is satisfiable; read the model with model_value.
    /// CEP:WHY: The satisfying outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: property/sat_incremental_property_test.rs::assumption_solves_agree_with_brute_force.
    /// CEP:SECURITY: none.
    Satisfiable,
    /// CEP:WHAT: The formula alone is unsatisfiable (level-0 refutation independent of the assumptions).
    /// CEP:WHY: The strongest refuting outcome; callers must not treat it as a failed assumption set.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::unsat_formula_returns_unsat.
    /// CEP:SECURITY: none.
    Unsatisfiable,
    /// CEP:WHAT: The formula conjoined with the assumptions is unsatisfiable; the failed core is readable via failed_assumptions.
    /// CEP:WHY: Spec 10: the core is a subset of the assumptions whose negation the formula entails.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{unsat_under_assumptions_yields_core, core_negation_is_entailed}; property/sat_incremental_property_test.rs::cores_are_valid.
    /// CEP:SECURITY: none.
    UnsatUnderAssumptions,
    /// CEP:WHAT: The search stopped on a bounded failure; the error identifies which bound.
    /// CEP:WHY: Design 20.2: exceeded limits are explicit results, never silent continuation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::assumption_count_enforced.
    /// CEP:SECURITY: none.
    Indeterminate(CdclError),
}

/// CEP:WHAT: Construction options of the CDCL solver: the Phase 2 parameters plus the Phase 3 registry and proof-recorder configuration.
/// CEP:WHY: CEP&CC 34.3: every capacity and policy bound must be injectable so tests exercise the exhaustion paths at small scales on the production code path; one options record keeps the constructor surface stable while the configuration grows per phase.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record.
/// CEP:ASSUMES: capacities >= 1, budget >= 1, trigger >= 1, increment > 0 when proof recording is on.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{capacity_enforced, reduction_trigger_enforced}; unit/hot/sat_proof_test.rs::capacity_enforced; unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
/// CEP:SECURITY: the capacities are the denial-of-service bounds under test.
pub struct SolverOptions {
    /// CEP:WHAT: Declared variable count (1..=kMaxSatVariables).
    /// CEP:WHY: Bounds every literal and sizes the per-variable arrays.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: construction rejects zero or oversize counts.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::construction_rejects_zero_variables.
    /// CEP:SECURITY: validation bound.
    pub variables: u32,
    /// CEP:WHAT: Restart policy (Luby or geometric).
    /// CEP:WHY: Design 11.5.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs.
    /// CEP:SECURITY: none.
    pub policy: RestartPolicy,
    /// CEP:WHAT: Whether restarts clear the phase table.
    /// CEP:WHY: Design 11.1 S17.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::phase_reset_configuration.
    /// CEP:SECURITY: none.
    pub reset_phases_on_restart: bool,
    /// CEP:WHAT: Conflict budget (production: kSatMaxConflicts).
    /// CEP:WHY: Design 20.1.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: solve returns Indeterminate past the budget.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: denial-of-service bound.
    pub conflict_budget: u64,
    /// CEP:WHAT: Clause-registry entry capacity (production: kSatRegistryCapacity).
    /// CEP:WHY: CEP-1003.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: clause registration errors at the bound.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    pub registry_capacity: u32,
    /// CEP:WHAT: Live-learnt count at which database reduction fires (production: kSatMaxLearntClauses).
    /// CEP:WHY: Design 11.6.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (the policy, not a failure bound).
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_trigger_enforced.
    /// CEP:SECURITY: none.
    pub reduction_trigger: u32,
    /// CEP:WHAT: Clause-activity bump increment (production: 1.0).
    /// CEP:WHY: Design 11.1 S24.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: > 0.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::activity_rescale_preserves_order.
    /// CEP:SECURITY: none.
    pub activity_increment: f64,
    /// CEP:WHAT: Whether to attach a DRAT proof recorder.
    /// CEP:WHY: Design 18 and 11.1 S41-S43; off by default because recording allocates arena memory and appends one step per clause mutation (benchmarks keep the Phase 2 cost profile; certificate-producing drivers enable it).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: proof recording errors surface as Indeterminate.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs; unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    /// CEP:SECURITY: bounded buffers.
    pub record_proof: bool,
    /// CEP:WHAT: Proof step capacity (production: kSatProofStepCapacity).
    /// CEP:WHY: S42.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: recording errors at the bound.
    /// CEP:ASSUMES: >= 1 when record_proof.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    pub proof_step_capacity: u32,
    /// CEP:WHAT: Proof map capacity (production: kSatProofMapCapacity).
    /// CEP:WHY: S42.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: recording errors at the bound.
    /// CEP:ASSUMES: >= 1 when record_proof.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    pub proof_map_capacity: u32,
    /// CEP:WHAT: Proof literal capacity (production: kSatProofLiteralCapacity).
    /// CEP:WHY: S42.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: recording errors at the bound.
    /// CEP:ASSUMES: >= 1 when record_proof.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    pub proof_literal_capacity: u32,
}

impl SolverOptions {
    /// CEP:WHAT: Production defaults for every option.
    /// CEP:WHY: One named place documents the default configuration (CEP&CC 11.3); every default is a named constant from config/limits.rs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs (the default constructors use these).
    /// CEP:SECURITY: none.
    pub fn new(variables: u32, policy: RestartPolicy, reset_phases_on_restart: bool) -> Self {
        SolverOptions {
            variables,
            policy,
            reset_phases_on_restart,
            conflict_budget: kSatMaxConflicts,
            registry_capacity: kSatRegistryCapacity,
            reduction_trigger: kSatMaxLearntClauses,
            activity_increment: 1.0,
            record_proof: false,
            proof_step_capacity: kSatProofStepCapacity,
            proof_map_capacity: kSatProofMapCapacity,
            proof_literal_capacity: kSatProofLiteralCapacity,
        }
    }
}

/// CEP:WHAT: The CDCL solver: SAT core, conflict analyzer, VSIDS heap, phase table, restart scheduler, the conflict counter, the clause registry with the reduction policy, the optional proof recorder, the failed-assumption core buffer, and the blocked-clause model-extension stack, composed into one search state machine.
/// CEP:WHY: Design 11.1 components S9-S43 compose into the loop of design 11.4/26; owning the substructures in one type keeps their invariants (heap membership mirrors assignments, phases mirror last assignments, restart counter mirrors conflicts, registry tombstones mirror storage deleted bits) local and testable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SolveResult, AssumptionOutcome, and CdclError.
/// CEP:ASSUMES: single-threaded; clauses added at level 0 outside solve.
/// CEP:COST: construction is O(variables + capacities); the loop is allocation-free.
/// CEP:EVIDENCE: unit/hot/sat_solver_test.rs; unit/hot/sat_assumptions_test.rs; property/cdcl_property_test.rs; fuzz/cdcl_fuzz_test.rs.
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
    /// CEP:WHAT: The conflict analyzer (first-UIP analysis, minimization, and final assumption-core analysis).
    /// CEP:WHY: Design 11.1 S18-S20; S38.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized for the same variable count as the core.
    /// CEP:COST: 14 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs; unit/hot/sat_assumptions_test.rs::failed_core_is_minimal_subset.
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
    /// CEP:WHAT: Conflicts analyzed in this solver's lifetime.
    /// CEP:WHY: The kSatMaxConflicts budget counter (design 20.1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: solve returns Indeterminate past the budget.
    /// CEP:ASSUMES: cumulative across solves (the budget bounds the solver, not the call).
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
    /// CEP:WHAT: Conflict budget for this solver (production: kSatMaxConflicts).
    /// CEP:WHY: Design 20.1/20.2: the explicit denial-of-service bound; the injectable option lets security tests exercise the exhaustion path at small scales while sharing the entire loop code (CEP&CC 34.3: test the mechanism, not a copy).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: solve returns Indeterminate(CdclError::ConflictBudgetExceeded) past the budget.
    /// CEP:ASSUMES: >= 1; fixed at construction.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: denial-of-service bound.
    conflict_budget: u64,
    /// CEP:WHAT: The enumerable clause registry with the reduction policy (CEP-1003).
    /// CEP:WHY: Design 11.1 S4/S24/S25/S26; always present so every added clause is registered from every construction path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: registration errors surface as Indeterminate(Registry).
    /// CEP:ASSUMES: paired with self.core's storage.
    /// CEP:COST: 20 bytes per registry entry at the configured capacity.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs.
    /// CEP:SECURITY: capacity bound.
    registry: ClauseRegistry<'a>,
    /// CEP:WHAT: The optional DRAT proof recorder.
    /// CEP:WHY: Design 11.1 S41/S42 and 18; None when proof recording is off (the default construction).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: recording errors surface as Indeterminate(Proof).
    /// CEP:ASSUMES: paired with self.core's storage.
    /// CEP:COST: 24 bytes per step plus 8 per map entry plus 4 per literal at the configured capacities.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs; unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    /// CEP:SECURITY: bounded buffers.
    proof: Option<ProofRecorder<'a>>,
    /// CEP:WHAT: The failed-assumption core buffer.
    /// CEP:WHY: S38: analyze_final writes the core here at UnsatUnderAssumptions; failed_assumptions() reads it back.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: capacity kMaxAssumptions.
    /// CEP:COST: 4 bytes per assumption.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{unsat_under_assumptions_yields_core, core_negation_is_entailed}.
    /// CEP:SECURITY: bounded.
    failed: &'a [Cell<SatLiteral>],
    /// CEP:WHAT: Length of the current failed core (0 outside UnsatUnderAssumptions).
    /// CEP:WHY: Core extent for failed_assumptions.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= failed.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::unsat_under_assumptions_yields_core.
    /// CEP:SECURITY: none.
    failed_count: Cell<u32>,
    /// CEP:WHAT: Registry entry boundary of a deferred assumption-solve cleanup (kInvalidPendingCleanup when none is pending).
    /// CEP:WHY: A Satisfiable assumption solve must leave the model readable (model_value) and therefore cannot backtrack immediately, but its learnt clauses may depend on the assumption units; the boundary defers the mandatory cleanup to the next solver interaction (Spec 10 section 5), keeping both the model contract and incremental soundness.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: only set after a Satisfiable assumption solve; cleared by flush_pending_cleanup.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{model_survives_satisfiable_assumption_solve, learnts_do_not_leak_across_solves}.
    /// CEP:SECURITY: none.
    pending_cleanup: Cell<u32>,
    /// CEP:WHAT: Deferred assumption proof steps (id and literal packed per slot) of a pending cleanup.
    /// CEP:WHY: The lazy cleanup must also remove the assumption units from the proof trace; the ids are stack-local in the solve call, so they are parked here (u64 packing: high 32 bits proof id, low 32 bits literal encoding).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by pending_cleanup_steps_count.
    /// CEP:COST: 8 bytes per assumption.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{model_survives_satisfiable_assumption_solve, repeated_assumption_solves_agree}.
    /// CEP:SECURITY: none.
    pending_cleanup_steps: &'a [Cell<u64>],
    /// CEP:WHAT: Number of deferred assumption proof steps.
    /// CEP:WHY: Extent of pending_cleanup_steps.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= pending_cleanup_steps.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::repeated_assumption_solves_agree.
    /// CEP:SECURITY: none.
    pending_cleanup_steps_count: Cell<u32>,
    /// CEP:WHAT: The model-extension stack: one inline entry per soundness-relevant preprocessing elimination — blocked clauses (BCE, design 11.1 S31) and eliminated variables (BVE, design 11.1 S32).
    /// CEP:WHY: Both deletions are equisatisfiable only, so a Satisfiable model of the preprocessed database must be extended: a blocked clause's blocking literal is overridden to true when the clause is unsatisfied (the blocked property makes the reverse-order reconstruction sound, Spec 09 section 11), and an eliminated variable is flipped to the side its deleted clauses demand (the resolvent argument shows at most one side can be falsified, Spec 09 section 12); the stack is written only by the sanctioned preprocessing path and read only by model_value; inline arena arrays keep the memory bounded by kSatBceStackDepth x kSatExtEntryLiterals.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: record returns CdclError on stack or stride overflow (the preprocessing pass pre-checks both and reports the honest budget status instead).
    /// CEP:ASSUMES: entries are append-only; the per-entry payload never exceeds kSatExtEntryLiterals cells.
    /// CEP:COST: (kSatExtEntryLiterals + 4) cells per entry, allocated once at construction.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_eliminates_blocked_clause, bce_model_extension_satisfies_original, bve_eliminates_variable, bve_model_extension_satisfies_original}.
    /// CEP:SECURITY: bounds-checked reads and writes.
    ext_literals: &'a [Cell<SatLiteral>],
    /// CEP:WHAT: Per-entry metadata: (kind, anchor, payload length, clause count) as four u64 cells per entry. Kind 0 = blocked clause (anchor = blocking-literal encoding, payload = the clause's literals); kind 1 = eliminated variable (anchor = the variable index, payload = the deleted clauses' flat literals with a length marker per clause).
    /// CEP:WHY: The kind dispatches the reconstruction rule; the anchor identifies the overridden variable or literal; the payload length gates the literal-slot reads.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by ext_depth; payloads <= kSatExtEntryLiterals cells.
    /// CEP:COST: 32 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_model_extension_satisfies_original, bve_model_extension_satisfies_original}.
    /// CEP:SECURITY: bounds-checked reads.
    ext_meta: &'a [Cell<u64>],
    /// CEP:WHAT: Number of recorded extension entries.
    /// CEP:WHY: Extent of the stack; append-only monotone.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kSatBceStackDepth.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bce_stack_overflow_stops.
    /// CEP:SECURITY: none.
    ext_depth: Cell<u32>,
}

// CEP:WHAT: Sentinel for "no deferred cleanup pending".
// CEP:WHY: A named constant instead of a bare u32::MAX (CEP&CC 11.3); never a valid registry entry index boundary because entry indices start at 0 and the sentinel exceeds kSatRegistryCapacity.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::learnts_do_not_leak_across_solves.
// CEP:SECURITY: none.
const kInvalidPendingCleanup: u32 = u32::MAX;

// CEP:WHAT: Model-extension stack entry kind: a blocked clause (BCE, design 11.1 S31).
// CEP:WHY: The kind dispatches model_value's reconstruction rule (Spec 09 section 11).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: distinct from kExtKindEliminatedVariable.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bce_model_extension_satisfies_original.
// CEP:SECURITY: none.
const kExtKindBlockedClause: u64 = 0;

// CEP:WHAT: Model-extension stack entry kind: an eliminated variable (BVE, design 11.1 S32).
// CEP:WHY: The kind dispatches model_value's reconstruction rule (Spec 09 section 12).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: distinct from kExtKindBlockedClause.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bve_model_extension_satisfies_original.
// CEP:SECURITY: none.
const kExtKindEliminatedVariable: u64 = 1;

// CEP:WHAT: Bit shift separating the proof id and the literal encoding in one packed pending-cleanup step.
// CEP:WHY: The deferred assumption-delete queue stores (id, literal) pairs in one u64; the layout must be named so pack and unpack cannot drift apart (CEP&CC 11.3 auditability).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: proof ids fit u32 and literal encodings fit u32 (both bounded by their own capacities).
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{failed_core_is_minimal_subset, learnts_do_not_leak_across_solves}.
// CEP:SECURITY: none.
const kPendingCleanupIdShift: u32 = 32;

// CEP:WHAT: Low-word mask extracting the literal encoding from a packed pending-cleanup step.
// CEP:WHY: The unpacking side of the named layout (kPendingCleanupIdShift is the packing side).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: literal encodings occupy the low 32 bits.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::failed_core_is_minimal_subset.
// CEP:SECURITY: none.
const kPendingCleanupLiteralMask: u64 = 0xFFFF_FFFF;

impl<'a> CdclSolver<'a> {
    /// CEP:WHAT: Constructs the solver with production defaults (registry on, proof off).
    /// CEP:WHY: Design 19.4: every structure is fully built before the hot path; the Phase 2 signature stays identical so existing callers keep their behavior (registry bookkeeping adds O(1) per clause and the trigger never fires below kSatMaxLearntClauses).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns CdclError on invalid variable counts and arena exhaustion.
    /// CEP:ASSUMES: 0 < variables <= kMaxSatVariables; the arena has room for all substructures.
    /// CEP:COST: O(variables + registry capacity) one-time.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{empty_formula_is_satisfiable, construction_rejects_zero_variables}.
    /// CEP:SECURITY: count validated before allocation.
    pub fn new(
        arena: &'a Arena,
        variables: u32,
        policy: RestartPolicy,
        reset_phases_on_restart: bool,
    ) -> Result<CdclSolver<'a>, CdclError> {
        CdclSolver::new_with_conflict_budget(
            arena,
            variables,
            policy,
            reset_phases_on_restart,
            kSatMaxConflicts,
        )
    }

    /// CEP:WHAT: Constructs the solver with an explicit conflict budget (the production constructor delegates with kSatMaxConflicts).
    /// CEP:WHY: Security tests must exercise the ConflictBudgetExceeded path at small, fast scales; the explicit-budget constructor keeps the loop code identical for both paths (CEP&CC 34.3: test the mechanism).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: as new().
    /// CEP:ASSUMES: budget >= 1.
    /// CEP:COST: as new().
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: denial-of-service bound enforcement.
    pub fn new_with_conflict_budget(
        arena: &'a Arena,
        variables: u32,
        policy: RestartPolicy,
        reset_phases_on_restart: bool,
        conflict_budget: u64,
    ) -> Result<CdclSolver<'a>, CdclError> {
        let mut options = SolverOptions::new(variables, policy, reset_phases_on_restart);
        options.conflict_budget = conflict_budget;
        CdclSolver::new_advanced(arena, options)
    }

    /// CEP:WHAT: Constructs the solver from full options (registry capacities, reduction trigger, activity increment, proof configuration).
    /// CEP:WHY: CEP&CC 34.3: every Phase 3 bound (registry capacity, reduction trigger, proof capacities) must be injectable on the production code path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns CdclError::Registry/Proof when the registry or recorder arrays do not fit the arena, and the Phase 2 construction failures otherwise.
    /// CEP:ASSUMES: see SolverOptions.
    /// CEP:COST: O(variables + capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{capacity_enforced, reduction_trigger_enforced}; unit/hot/sat_proof_test.rs::capacity_enforced; unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: every capacity validated before allocation.
    pub fn new_advanced(
        arena: &'a Arena,
        options: SolverOptions,
    ) -> Result<CdclSolver<'a>, CdclError> {
        if options.variables == 0 || options.variables > kMaxSatVariables {
            return Err(CdclError::Storage(SatCoreError::Assignment(
                crate::sat::assignment::AssignmentError::VariableOutOfRange,
            )));
        }
        let core = SatCore::new(arena, options.variables)?;
        let analyzer = ConflictAnalyzer::new(arena, options.variables)?;
        let vsids = VsidsHeap::new(arena, options.variables).map_err(|_| {
            CdclError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        let phases = PhaseTable::new(arena, options.variables).map_err(|_| {
            CdclError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        let registry = ClauseRegistry::new_with(
            arena,
            options.registry_capacity,
            options.reduction_trigger,
            options.activity_increment,
        )
        .map_err(CdclError::Registry)?;
        let proof = if options.record_proof {
            Some(
                ProofRecorder::new_with(
                    arena,
                    options.proof_step_capacity,
                    options.proof_map_capacity,
                    options.proof_literal_capacity,
                )
                .map_err(CdclError::Proof)?,
            )
        } else {
            None
        };
        let failed_range = arena
            .alloc_array::<Cell<SatLiteral>>(kMaxAssumptions)
            .map_err(|_| {
                CdclError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        let failed = arena.array::<Cell<SatLiteral>>(failed_range).map_err(|_| {
            CdclError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })?;
        let pending_range = arena
            .alloc_array::<Cell<u64>>(kMaxAssumptions)
            .map_err(|_| {
                CdclError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        let pending_cleanup_steps = arena.array::<Cell<u64>>(pending_range).map_err(|_| {
            CdclError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })?;
        let ext_literals_range = arena
            .alloc_array::<Cell<SatLiteral>>(kSatBceStackDepth * kSatExtEntryLiterals)
            .map_err(|_| {
                CdclError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        let ext_literals = arena
            .array::<Cell<SatLiteral>>(ext_literals_range)
            .map_err(|_| {
                CdclError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::InvalidClauseOffset,
                ))
            })?;
        let ext_meta_range = arena
            .alloc_array::<Cell<u64>>(kSatBceStackDepth * 4)
            .map_err(|_| {
                CdclError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        let ext_meta = arena.array::<Cell<u64>>(ext_meta_range).map_err(|_| {
            CdclError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })?;
        Ok(CdclSolver {
            core,
            analyzer,
            vsids,
            phases,
            restarts: RestartScheduler::new(options.policy),
            conflicts: Cell::new(0),
            reset_phases_on_restart: options.reset_phases_on_restart,
            root_conflict: Cell::new(false),
            conflict_budget: options.conflict_budget,
            registry,
            proof,
            failed,
            failed_count: Cell::new(0),
            pending_cleanup: Cell::new(kInvalidPendingCleanup),
            pending_cleanup_steps,
            pending_cleanup_steps_count: Cell::new(0),
            ext_literals,
            ext_meta,
            ext_depth: Cell::new(0),
        })
    }

    // CEP:WHAT: Flushes a deferred assumption-solve cleanup: backtracks to level 0, deletes the assumption-dependent learnt clauses, and removes the assumption units from the proof trace.
    // CEP:WHY: Spec 10 section 5: the cleanup is mandatory before any further solver interaction (the deferred learnts may depend on assumption units that no longer hold); parking it behind one explicit method keeps every entry point (add_clause, both solve entry points) sound with a single call.
    // CEP:STATUS: complete
    // CEP:FAILURE: registry and proof errors surface loudly.
    // CEP:ASSUMES: called at the top of every public mutator and solver entry point.
    // CEP:COST: O(pending learnts + pending assumptions).
    // CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{learnts_do_not_leak_across_solves, repeated_assumption_solves_agree, model_survives_satisfiable_assumption_solve}.
    // CEP:SECURITY: none.
    fn flush_pending_cleanup(&self) -> Result<(), CdclError> {
        let boundary = self.pending_cleanup.get();
        if boundary == kInvalidPendingCleanup {
            return Ok(());
        }
        self.backtrack(0);
        let proof = self.proof.as_ref();
        if let Err(error) = self
            .registry
            .delete_learnts_from(self.core.clauses(), boundary, proof)
        {
            self.pending_cleanup.set(kInvalidPendingCleanup);
            self.pending_cleanup_steps_count.set(0);
            return Err(CdclError::Registry(error));
        }
        if let Some(recorder) = proof {
            let count = self.pending_cleanup_steps_count.get();
            for slot in (0..count as usize).rev() {
                let packed = self.pending_cleanup_steps[slot].get();
                let id = (packed >> kPendingCleanupIdShift) as u32;
                let literal =
                    SatLiteral::from_encoding((packed & kPendingCleanupLiteralMask) as u32);
                if let Err(error) = recorder.record_assumption_delete(id, literal) {
                    self.pending_cleanup.set(kInvalidPendingCleanup);
                    self.pending_cleanup_steps_count.set(0);
                    return Err(CdclError::Proof(error));
                }
            }
        }
        self.pending_cleanup.set(kInvalidPendingCleanup);
        self.pending_cleanup_steps_count.set(0);
        Ok(())
    }

    /// CEP:WHAT: Adds a problem clause at level 0 before solving, registering it with the registry and recording its proof addition when enabled.
    /// CEP:WHY: The solver-owned entry point keeps the level-0 discipline in one place (analysis assumes clauses never appear mid-search) and makes registration and proof emission impossible to forget (S4/S41).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates SatCoreError (empty clause, bounds, budget) plus registry and proof capacity errors; a falsified unit returns AttachOutcome::Conflict and the solve (or the caller) decides UNSAT.
    /// CEP:ASSUMES: called before solve and only at level 0.
    /// CEP:COST: as SatCore::add_clause plus O(1) registration and one proof append.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, unit_conflict_at_root_is_unsat}; unit/hot/sat_registry_test.rs::registry_enumerates; unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    /// CEP:SECURITY: validation in the core.
    pub fn add_clause(&self, literals: &[SatLiteral]) -> Result<AttachOutcome, CdclError> {
        self.add_clause_with_kind(literals, true)
    }

    /// CEP:WHAT: Adds a derived clause at level 0 (preprocessing rewrites: deduplicated, strengthened, vivified replacements) with the derived-add proof step whose RUP justification the checker verifies.
    /// CEP:WHY: The axiom/derivation split (Spec 11 section 3): solver.add_clause marks problem clauses as axioms (justification skipped, correspondence with the caller-supplied formula verified); preprocessing replacements are consequences of the database and carry the RUP burden through the derived step kind; every other discipline (level-0 check, registration, attachment, root-conflict flagging) is the shared internal path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: as add_clause.
    /// CEP:ASSUMES: called at level 0; the clause is a consequence of the current database.
    /// CEP:COST: as add_clause.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{duplicates_removed, strengthening_rewrites, vivification_shortens_clause}; unit/cold/drat_checker_test.rs::derivation_steps_are_rup_verified.
    /// CEP:SECURITY: add-time validation.
    pub fn add_derived_clause(&self, literals: &[SatLiteral]) -> Result<AttachOutcome, CdclError> {
        self.add_clause_with_kind(literals, false)
    }

    // CEP:WHAT: Shared level-0 clause-addition path: creation, attachment, registration, proof recording (axiom or derived kind), and the falsified-unit refutation flag.
    // CEP:WHY: One implementation keeps the level-0 discipline, the registration, and the root-conflict semantics identical for axioms and derivations (CEP&CC Law 3); only the proof step kind differs.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SatCoreError (empty clause, bounds, budget) plus registry and proof capacity errors; a falsified unit returns AttachOutcome::Conflict and the solve (or the caller) decides UNSAT.
    // CEP:ASSUMES: called at level 0 only.
    // CEP:COST: as SatCore::add_clause plus O(1) registration and one proof append.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, unit_conflict_at_root_is_unsat}; unit/hot/sat_registry_test.rs::registry_enumerates; unit/hot/sat_proof_test.rs::{steps_recorded_in_order, axiom_steps_match_formula}.
    // CEP:SECURITY: validation in the core.
    fn add_clause_with_kind(
        &self,
        literals: &[SatLiteral],
        axiom: bool,
    ) -> Result<AttachOutcome, CdclError> {
        self.flush_pending_cleanup()?;
        if self.core.trail().level() != 0 {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        let offset = self
            .core
            .clauses()
            .new_clause(literals, false, 0)
            .map_err(SatCoreError::from)
            .map_err(CdclError::from)?;
        let outcome = self.core.attach_clause(offset).map_err(CdclError::from)?;
        self.registry
            .register(self.core.clauses(), offset)
            .map_err(CdclError::Registry)?;
        if let Some(recorder) = &self.proof {
            let recorded = if axiom {
                recorder.record_axiom_add(offset, literals)
            } else {
                recorder.record_add(offset, literals)
            };
            recorded.map_err(CdclError::Proof)?;
        }
        if outcome == AttachOutcome::Conflict {
            // A unit clause falsified by existing level-0 assignments: the formula is
            // refuted at the root; BCP will never rescan it (units carry no watches),
            // so the solver records the refutation here (Spec 06 section 8) and emits
            // the empty clause into an attached proof (Spec 11 section 4).
            self.root_conflict.set(true);
            if let Some(recorder) = &self.proof {
                recorder.record_empty_clause().map_err(CdclError::Proof)?;
            }
        }
        Ok(outcome)
    }

    /// CEP:WHAT: Returns the value of a variable after a Satisfiable solve, extended over the model-extension stack.
    /// CEP:WHY: Model extraction (design 11.1 S40) plus the preprocessing reconstruction (design 11.1 S31/S32, Spec 09 sections 11-12): BCE and BVE deletions are equisatisfiable only, so the search's model of the preprocessed database is extended by walking the stack newest-entry-first; an entry that "consumes" its anchor variable under the current assignment yields the override (blocked clause: blocking literal to true; eliminated variable: the side flip its deleted clauses demand), which the blocked property and the resolvent argument make sound against the entries already applied (Spec 09 sections 11-12).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (None when unassigned and unconsumed by the stack, which cannot happen after Satisfiable: the search assigns every variable).
    /// CEP:ASSUMES: called after solve returned Satisfiable for meaningful results; stack entries written only through the record methods.
    /// CEP:COST: one trail load without stack entries; O(stack x entry size) worst case with the reconstruction active.
    /// CEP:EVIDENCE: property/cdcl_property_test.rs::models_satisfy_formulas; unit/hot/sat_preprocess_test.rs::{bce_model_extension_satisfies_original, bve_model_extension_satisfies_original}.
    /// CEP:SECURITY: clamped read.
    pub fn model_value(&self, variable: u32) -> Option<bool> {
        let literal = SatLiteral::new(SatVar(variable), true).ok()?;
        let trail = match self.core.value_of_literal(literal) {
            SatValue::True => Some(true),
            SatValue::False => Some(false),
            SatValue::Unassigned => None,
        };
        match self.ext_override(variable, 0) {
            Some(value) => Some(value),
            None => trail,
        }
    }

    /// CEP:WHAT: Returns the number of recorded model-extension stack entries.
    /// CEP:WHY: The preprocessing pass checks the free depth before recording and reports the honest budget status instead of an error when the stack is full (Spec 09 sections 11-12); public read access matches the core/registry/proof accessors' test-and-preprocessing discipline.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bce_stack_overflow_stops.
    /// CEP:SECURITY: none.
    pub fn ext_entry_count(&self) -> u32 {
        self.ext_depth.get()
    }

    // CEP:WHAT: Records one BCE elimination onto the stack: the clause's sorted deduplicated literals plus its blocking literal.
    // CEP:WHY: The entry is the reconstruction input of model_value; the clause must be copied (not referenced by offset) because it is deleted from the database and the storage bytes are not a stable read surface (compaction, ticket CEP-1007, reclaims storage; Spec 09 section 11).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns CdclError::Storage(InvariantViolation) on stack overflow or on an empty/overlong literal slice; the caller pre-checks the free depth so the overflow path is the loud backstop, not the control flow.
    // CEP:ASSUMES: 1 <= literals.len() <= kSatBceMaxClauseLength; called from the preprocessing pass only.
    // CEP:COST: one entry copy.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_eliminates_blocked_clause, bce_stack_overflow_stops}.
    // CEP:SECURITY: bounds-checked writes.
    pub(crate) fn bce_record(
        &self,
        literals: &[SatLiteral],
        blocking: SatLiteral,
    ) -> Result<(), CdclError> {
        if literals.is_empty() || literals.len() > kSatBceMaxClauseLength as usize {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        self.ext_record(
            kExtKindBlockedClause,
            blocking.encoding() as u64,
            literals.len() as u32,
            literals,
        )
    }

    // CEP:WHAT: Records one BVE elimination onto the stack: the variable plus its deleted clauses as a flat length-marked payload.
    // CEP:WHY: The variable-flip reconstruction (Spec 09 section 12) needs every deleted clause to decide which side the model must satisfy; the payload stores the clauses themselves because they are deleted from the database.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns CdclError::Storage(InvariantViolation) on stack overflow, an empty clause list, a length/literal mismatch, or a payload beyond kSatExtEntryLiterals cells; the caller pre-checks the free depth and payload size (one length-marker cell plus the clause literals per clause) so the overflow path is the loud backstop.
    // CEP:ASSUMES: every clause contains the variable (positive or negative polarity); clause_lengths[i] matches the i-th literal run; called from the preprocessing pass only.
    // CEP:COST: one entry copy.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bve_model_extension_satisfies_original.
    // CEP:SECURITY: bounds-checked writes.
    pub(crate) fn bve_record(
        &self,
        variable: u32,
        clause_lengths: &[u32],
        literals: &[SatLiteral],
    ) -> Result<(), CdclError> {
        if clause_lengths.is_empty() {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        let mut literal_sum = 0usize;
        for length in clause_lengths.iter() {
            if *length == 0 {
                return Err(CdclError::Storage(SatCoreError::InvariantViolation));
            }
            literal_sum += *length as usize;
        }
        if literals.len() != literal_sum
            || literal_sum + clause_lengths.len() > kSatExtEntryLiterals as usize
        {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        // The payload is the flat length-marked clause list: one marker cell per
        // clause (the length stored as an opaque encoding) followed by the literals.
        let mut payload = [SatLiteral::from_encoding(0); kSatExtEntryLiterals as usize];
        let mut used = 0usize;
        let mut cursor = 0usize;
        for length in clause_lengths.iter() {
            payload[used] = SatLiteral::from_encoding(*length);
            used += 1;
            for slot in 0..*length as usize {
                payload[used] = literals[cursor + slot];
                used += 1;
            }
            cursor += *length as usize;
        }
        self.ext_record(
            kExtKindEliminatedVariable,
            variable as u64,
            clause_lengths.len() as u32,
            &payload[..used],
        )
    }

    // CEP:WHAT: Appends one entry: kind, anchor, payload length, and clause count into the meta slots and the payload into the entry's literal cells.
    // CEP:WHY: The single append path keeps the stack layout (kind, anchor, length, count) and its bound checks in one place (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns CdclError::Storage(InvariantViolation) on stack overflow or a payload beyond the entry stride.
    // CEP:ASSUMES: payload.len() <= kSatExtEntryLiterals; called by the two typed record methods only.
    // CEP:COST: one entry copy.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_eliminates_blocked_clause, bve_eliminates_variable}.
    // CEP:SECURITY: bounds-checked writes.
    fn ext_record(
        &self,
        kind: u64,
        anchor: u64,
        clause_count: u32,
        payload: &[SatLiteral],
    ) -> Result<(), CdclError> {
        let depth = self.ext_depth.get() as usize;
        if depth >= kSatBceStackDepth as usize || payload.len() > kSatExtEntryLiterals as usize {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        let base = depth * kSatExtEntryLiterals as usize;
        for (slot, literal) in payload.iter().enumerate() {
            self.ext_literals[base + slot].set(*literal);
        }
        self.ext_meta[depth * 4].set(kind);
        self.ext_meta[depth * 4 + 1].set(anchor);
        self.ext_meta[depth * 4 + 2].set(payload.len() as u64);
        self.ext_meta[depth * 4 + 3].set(clause_count as u64);
        self.ext_depth.set((depth + 1) as u32);
        Ok(())
    }

    // CEP:WHAT: Scans the stack from the newest entry down to `lower` (exclusive) and returns the override of the first entry that consumes `variable`, or None when no entry consumes it.
    // CEP:WHY: The reconstruction processes entries newest-first; the newest consuming entry's override is the effective value because newer entries are already applied and older ones are not (Spec 09 sections 11-12).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: lower <= ext_depth.
    // CEP:COST: O(stack depth) entries scanned; the nested satisfaction checks recurse with a strictly increasing lower bound, so the total is bounded by the stack depth squared.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_model_extension_satisfies_original, bve_model_extension_satisfies_original}.
    // CEP:SECURITY: bounds-checked reads.
    fn ext_override(&self, variable: u32, lower: usize) -> Option<bool> {
        let depth = self.ext_depth.get() as usize;
        let mut index = depth;
        while index > lower {
            index -= 1;
            let kind = self.ext_meta[index * 4].get();
            let anchor = self.ext_meta[index * 4 + 1].get();
            match kind {
                kExtKindBlockedClause => {
                    let blocking = SatLiteral::from_encoding(anchor as u32);
                    if blocking.variable().0 != variable {
                        continue;
                    }
                    if !self.ext_blocked_clause_satisfied(index) {
                        return Some(blocking.is_positive());
                    }
                }
                _ => {
                    if anchor != variable as u64 {
                        continue;
                    }
                    if let Some(flip) = self.ext_eliminated_variable_flip(index) {
                        return Some(flip);
                    }
                }
            }
        }
        None
    }

    // CEP:WHAT: Returns whether a blocked-clause entry's clause is satisfied under the trail plus the overrides of the entries NEWER than `index`.
    // CEP:WHY: The reconstruction at entry `index` sees exactly the trail and the newer entries' overrides; a satisfied entry does not consume its blocking variable, leaving that variable to the older entries and the trail (Spec 09 section 11).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: index < ext_depth and the entry is a blocked-clause entry.
    // CEP:COST: O(clause length) with nested override scans strictly bounded by the stack depth.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bce_model_extension_satisfies_original.
    // CEP:SECURITY: bounds-checked reads.
    fn ext_blocked_clause_satisfied(&self, index: usize) -> bool {
        let payload = self.entry_literals(index);
        payload
            .iter()
            .any(|literal| self.entry_literal_value(*literal, index))
    }

    // CEP:WHAT: Returns the side flip a deleted-variable entry demands under the trail plus the newer entries' overrides: true when a positive clause of the variable is falsified, false when a negative clause is falsified, None when every deleted clause is already satisfied.
    // CEP:WHY: Spec 09 section 12's flip rule: at most one side can be falsified under a model of the reduced database (a falsified clause on each side would falsify their resolvent, which the model satisfies), and flipping to the falsified side satisfies every clause of that side while the resolvent argument keeps the other side satisfied.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (both-sides-falsified is unreachable; the deterministic tie-break prefers the positive side if it were ever reached).
    // CEP:ASSUMES: index < ext_depth and the entry is an eliminated-variable entry.
    // CEP:COST: O(payload cells) with nested override scans strictly bounded by the stack depth.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bve_model_extension_satisfies_original.
    // CEP:SECURITY: bounds-checked reads.
    fn ext_eliminated_variable_flip(&self, index: usize) -> Option<bool> {
        let anchor = self.ext_meta[index * 4 + 1].get() as u32;
        let payload = self.entry_literals(index);
        let mut used = 0usize;
        let mut positive_falsified = false;
        let mut negative_falsified = false;
        for _ in 0..self.ext_meta[index * 4 + 3].get() {
            let length = payload[used].encoding() as usize;
            used += 1;
            let mut satisfied = false;
            for slot in 0..length {
                let literal = payload[used + slot];
                if self.entry_literal_value(literal, index) {
                    satisfied = true;
                }
            }
            used += length;
            if !satisfied {
                // The clause's polarity: it contains the anchor variable either as
                // the positive or the negative literal (BVE deletes exactly the
                // clauses containing the variable).
                let contains_positive = payload[used - length..used]
                    .iter()
                    .any(|literal| literal.variable().0 == anchor && literal.is_positive());
                if contains_positive {
                    positive_falsified = true;
                } else {
                    negative_falsified = true;
                }
            }
        }
        if positive_falsified {
            Some(true)
        } else if negative_falsified {
            Some(false)
        } else {
            None
        }
    }

    // CEP:WHAT: Copies an entry's payload cells out of the stack slice.
    // CEP:WHY: One read helper keeps the stride arithmetic and the bounds checks single-sourced.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (the payload length was validated at record time).
    // CEP:ASSUMES: index < ext_depth.
    // CEP:COST: one copy of up to kSatExtEntryLiterals cells.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::bce_model_extension_satisfies_original.
    // CEP:SECURITY: bounds-checked reads.
    fn entry_literals(&self, index: usize) -> [SatLiteral; kSatExtEntryLiterals as usize] {
        let base = index * kSatExtEntryLiterals as usize;
        let mut cells = [SatLiteral::from_encoding(0); kSatExtEntryLiterals as usize];
        let length = self.ext_meta[index * 4 + 2].get() as usize;
        for (slot, cell) in cells.iter_mut().enumerate().take(length) {
            *cell = self.ext_literals[base + slot].get();
        }
        cells
    }

    // CEP:WHAT: Resolves one payload literal's value: the trail value when assigned, otherwise the override of the entries newer than `index`.
    // CEP:WHY: The reconstruction at entry `index` must not consult older entries (they are not yet applied); one helper keeps that rule single-sourced for both entry kinds.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: one trail load plus, when unassigned, a nested override scan bounded by the stack depth.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{bce_model_extension_satisfies_original, bve_model_extension_satisfies_original}.
    // CEP:SECURITY: none.
    fn entry_literal_value(&self, literal: SatLiteral, index: usize) -> bool {
        match self.core.value_of_literal(literal) {
            SatValue::True => true,
            SatValue::False => false,
            SatValue::Unassigned => self
                .ext_override(literal.variable().0, index + 1)
                .map(|value| value == literal.is_positive())
                .unwrap_or(false),
        }
    }

    /// CEP:WHAT: Returns the number of conflicts analyzed.
    /// CEP:WHY: Budget introspection for tests and diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
    /// CEP:SECURITY: none.
    pub fn conflicts(&self) -> u64 {
        self.conflicts.get()
    }

    /// CEP:WHAT: Returns the number of restarts performed.
    /// CEP:WHY: Restart introspection for tests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero.
    /// CEP:SECURITY: none.
    pub fn restarts_done(&self) -> u32 {
        self.restarts.restarts_done()
    }

    /// CEP:WHAT: Returns a reference to the SAT core (read access for tests and preprocessing).
    /// CEP:WHY: Tests inspect trail, values, and learnt clauses; preprocessing enumerates clauses through the registry and the storage without widening the solver API.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: read-only use.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero; unit/hot/sat_preprocess_test.rs.
    /// CEP:SECURITY: read-only projection.
    pub fn core(&self) -> &SatCore<'a> {
        &self.core
    }

    /// CEP:WHAT: Returns a reference to the clause registry.
    /// CEP:WHY: Preprocessing and tests enumerate and delete clauses through the registry (CEP-1003).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: read-mostly; mutation only through the documented registry APIs.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs; unit/hot/sat_preprocess_test.rs.
    /// CEP:SECURITY: none.
    pub fn registry(&self) -> &ClauseRegistry<'a> {
        &self.registry
    }

    /// CEP:WHAT: Returns the attached proof recorder, if any.
    /// CEP:WHY: The cold writer and checker consume the recorded steps after solving.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: None when the solver was built without recording.
    /// CEP:ASSUMES: read-only use.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs; unit/cold/drat_writer_test.rs.
    /// CEP:SECURITY: none.
    pub fn proof(&self) -> Option<&ProofRecorder<'a>> {
        self.proof.as_ref()
    }

    /// CEP:WHAT: Copies the failed-assumption core of the last UnsatUnderAssumptions result into a caller buffer and returns its length.
    /// CEP:WHY: S38: the core is the AVATAR-facing answer of an assumption solve; the copy-out API keeps the hot crate allocation-free and safe (no slice transmute of the Cell buffer), and an empty result accompanies every other outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: truncates to the buffer length and returns the copied count (callers size the buffer with failed_assumption_count or pass kMaxAssumptions storage per the documented contract).
    /// CEP:ASSUMES: meaningful only after UnsatUnderAssumptions; out is caller-owned stack storage.
    /// CEP:COST: O(core length).
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{unsat_under_assumptions_yields_core, core_negation_is_entailed}; property/sat_incremental_property_test.rs::cores_are_valid.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn failed_assumptions_into(&self, out: &mut [SatLiteral]) -> usize {
        let count = self.failed_count.get() as usize;
        let copied = count.min(out.len()).min(self.failed.len());
        for (slot, target) in out.iter_mut().enumerate().take(copied) {
            *target = self.failed[slot].get();
        }
        copied
    }

    /// CEP:WHAT: Returns the length of the last failed-assumption core.
    /// CEP:WHY: Lets callers size the copy buffer without probing.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::unsat_under_assumptions_yields_core.
    /// CEP:SECURITY: none.
    pub fn failed_assumption_count(&self) -> u32 {
        self.failed_count.get()
    }

    /// CEP:WHAT: Runs the CDCL loop without assumptions to Satisfiable, Unsatisfiable, or Indeterminate.
    /// CEP:WHY: Spec 06 section 8: the Phase 2 contract unchanged; the empty assumption vector makes root_level 0 so every Phase 2 behavior (backjump to computed levels, restarts to level 0) is the degenerate case of the general loop.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: see SolveResult; never panics.
    /// CEP:ASSUMES: see file header (clauses at level 0, single-threaded).
    /// CEP:COST: see file header; measured in bench CEP-BENCH-0009.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, pigeonhole_is_unsat, unit_conflict_at_root_is_unsat, restart_returns_to_level_zero, deterministic_across_repeated_solves, conflict_budget_returns_indeterminate}; property/cdcl_property_test.rs::{solve_agrees_with_brute_force, models_satisfy_formulas, learnt_clauses_are_entailed}; fuzz/cdcl_fuzz_test.rs.
    /// CEP:SECURITY: bounded by the conflict budget and every substructure bound.
    /// CEP:WHAT: Backtracks the trail to level 0, ending the current model's readability.
    /// CEP:WHY: The AVATAR incremental loop (design 12.2 rule 4) reads the model after a Satisfiable plain solve, then adds conflict clauses before the next solve; add_clause requires level 0, and a plain (assumption-free) solve exits without the epilogue that assumption solves run, so the controller must cancel between reading the model and adding clauses - the model contract (read first, cancel after) is documented here once instead of duplicating trail surgery in every caller.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; backtracking to 0 is always legal (learnt clauses of a plain solve are assumption-free and stay).
    /// CEP:ASSUMES: the caller finished reading model_value.
    /// CEP:COST: one trail unwind (O(assignments)).
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: none.
    pub fn cancel(&self) {
        self.backtrack(0);
    }

    /// CEP:WHAT: The convenience wrapper: solve with no assumptions.
    /// CEP:WHY: The common call shape for one-shot formulas; identical to solve_with_assumptions over an empty assumption slice, so the result vocabulary and budget behavior match exactly (SolveResult, AssumptionOutcome).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: see SolveResult; never panics.
    /// CEP:ASSUMES: none.
    /// CEP:COST: as solve_with_assumptions.
    /// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::{trivially_satisfiable, empty_formula_is_satisfiable}.
    /// CEP:SECURITY: none.
    pub fn solve(&self) -> SolveResult {
        match self.solve_with_assumptions(&[]) {
            AssumptionOutcome::Satisfiable => SolveResult::Satisfiable,
            AssumptionOutcome::Unsatisfiable => SolveResult::Unsatisfiable,
            AssumptionOutcome::UnsatUnderAssumptions => {
                // With no assumptions pushed there are no assumption decisions, so a
                // root-region conflict is a level-0 refutation; the arm is unreachable
                // by construction and maps defensively to the refuting outcome.
                SolveResult::Unsatisfiable
            }
            AssumptionOutcome::Indeterminate(error) => SolveResult::Indeterminate(error),
        }
    }

    /// CEP:WHAT: Runs the CDCL loop under assumption literals pushed as the lowest decision levels: Satisfiable extends the assumptions, Unsatisfiable refutes the formula alone, UnsatUnderAssumptions refutes formula-plus-assumptions and leaves a failed core, Indeterminate reports a bounded failure.
    /// CEP:WHY: Design 11.1 S38/S39 and Spec 10: assumptions occupy decision levels 1..=root (each its own level so analyze_final can attribute conflicts), the search never backjumps below root, conflicts at or below root trigger final analysis instead of learning, and the epilogue backtracks to level 0, deletes every learnt clause of this call (they may depend on the assumptions), and removes the assumption proof units - which is what makes the next incremental call sound; the labeled-block structure guarantees the epilogue runs on every exit path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: see AssumptionOutcome; never panics.
    /// CEP:ASSUMES: assumptions reference declared variables; the formula's clauses were added at level 0; no more than kMaxAssumptions literals per call.
    /// CEP:COST: as solve() plus O(assumptions) push/pop and O(new learnts) cleanup.
    /// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{satisfiable_under_assumptions, unsat_formula_returns_unsat, unsat_under_assumptions_yields_core, failed_core_is_minimal_subset, repeated_assumption_solves_agree, learnts_do_not_leak_across_solves}; property/sat_incremental_property_test.rs::{assumption_solves_agree_with_brute_force, cores_are_valid}.
    /// CEP:SECURITY: bounded by the conflict budget, the assumption count, and every substructure bound.
    pub fn solve_with_assumptions(&self, assumptions: &[SatLiteral]) -> AssumptionOutcome {
        if assumptions.len() > kMaxAssumptions as usize {
            return AssumptionOutcome::Indeterminate(CdclError::TooManyAssumptions);
        }
        if let Err(error) = self.flush_pending_cleanup() {
            return AssumptionOutcome::Indeterminate(error);
        }
        self.failed_count.set(0);
        let entry_registry_index = self.registry.entry_count();
        let mut proof_assumption_ids: [(u32, SatLiteral); kMaxAssumptions as usize] =
            [(0, SatLiteral::from_encoding(0)); kMaxAssumptions as usize];
        let mut assumption_recorded: usize = 0;
        self.backtrack(0);
        if self.root_conflict.get() {
            return AssumptionOutcome::Unsatisfiable;
        }
        let outcome = 'search: {
            // Push phase (Spec 10 section 3): each assumption becomes its own decision
            // level; a falsified assumption takes the unit-seed final analysis; a
            // propagation conflict below the search region takes the conflict-seed
            // final analysis.
            for literal in assumptions.iter() {
                if let Some(recorder) = &self.proof {
                    match recorder.record_assumption_add(*literal) {
                        Ok(id) => {
                            proof_assumption_ids[assumption_recorded] = (id, *literal);
                            assumption_recorded += 1;
                        }
                        Err(error) => {
                            break 'search AssumptionOutcome::Indeterminate(CdclError::Proof(error))
                        }
                    }
                }
                match self.core.value_of_literal(*literal) {
                    SatValue::False => {
                        // Falsified by level-0 assignments or an earlier assumption:
                        // F entails the negation of the collected earlier assumptions
                        // or of nothing (level-0 cause), and conjoining this assumption
                        // refutes; the core is this assumption plus the responsible
                        // earlier ones (Spec 10 section 4, unit-seed case).
                        let seed = [*literal];
                        let mut walked: [SatLiteral; kMaxAssumptions as usize] =
                            [SatLiteral::from_encoding(0); kMaxAssumptions as usize];
                        let walked_count =
                            match self.analyzer.analyze_final(&self.core, &seed, &mut walked) {
                                Ok(value) => value,
                                Err(error) => {
                                    break 'search AssumptionOutcome::Indeterminate(error)
                                }
                            };
                        let mut core: [SatLiteral; kMaxAssumptions as usize] =
                            [SatLiteral::from_encoding(0); kMaxAssumptions as usize];
                        core[0] = *literal;
                        let mut core_len: usize = 1;
                        for value in walked[..walked_count].iter() {
                            if core_len >= core.len() {
                                break;
                            }
                            core[core_len] = *value;
                            core_len += 1;
                        }
                        self.record_core(&core[..core_len]);
                        if let Some(recorder) = &self.proof {
                            if let Err(error) = recorder.record_empty_clause() {
                                break 'search AssumptionOutcome::Indeterminate(CdclError::Proof(
                                    error,
                                ));
                            }
                        }
                        break 'search AssumptionOutcome::UnsatUnderAssumptions;
                    }
                    SatValue::True => {
                        // Already implied (level 0 or an earlier assumption): decide()
                        // records nothing new and the level structure is untouched.
                        continue;
                    }
                    SatValue::Unassigned => {}
                }
                if let Err(error) = self.core.decide(*literal) {
                    break 'search AssumptionOutcome::Indeterminate(CdclError::from(error));
                }
                match self.core.propagate() {
                    Ok(PropagationOutcome::NoConflict) => {}
                    Ok(PropagationOutcome::Conflict(conflict)) => {
                        break 'search self.root_region_conflict(conflict);
                    }
                    Err(error) => {
                        break 'search AssumptionOutcome::Indeterminate(CdclError::from(error))
                    }
                }
            }
            let root_level = self.core.trail().level();
            // Search phase: identical to Phase 2 except that backjumps and restarts
            // clamp to root_level and conflicts at or below root_level take the
            // final-analysis path instead of learning.
            let mut learnt_buffer: [SatLiteral; kMaxSatClauseLiterals as usize] =
                [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize];
            loop {
                let propagation = match self.core.propagate() {
                    Ok(value) => value,
                    Err(error) => break AssumptionOutcome::Indeterminate(CdclError::from(error)),
                };
                match propagation {
                    PropagationOutcome::Conflict(conflict) => {
                        let level = self.core.trail().level();
                        if level == 0 {
                            if let Some(recorder) = &self.proof {
                                if let Err(error) = recorder.record_empty_clause() {
                                    break AssumptionOutcome::Indeterminate(CdclError::Proof(
                                        error,
                                    ));
                                }
                            }
                            break AssumptionOutcome::Unsatisfiable;
                        }
                        if level <= root_level {
                            break self.root_region_conflict(conflict);
                        }
                        let conflict_count = self.conflicts.get().saturating_add(1);
                        self.conflicts.set(conflict_count);
                        if conflict_count > self.conflict_budget {
                            break AssumptionOutcome::Indeterminate(
                                CdclError::ConflictBudgetExceeded,
                            );
                        }
                        self.restarts.note_conflict();
                        self.vsids.decay();
                        let analysis = match self.analyzer.analyze(
                            &self.core,
                            &self.vsids,
                            conflict,
                            &mut learnt_buffer,
                        ) {
                            Ok(value) => value,
                            Err(error) => break AssumptionOutcome::Indeterminate(error),
                        };
                        let literals = &learnt_buffer[..analysis.literal_count as usize];
                        let lbd = analysis.lbd as u8;
                        if analysis.literal_count == 1 {
                            // Unit learnt: backjump first (clamped to the assumption
                            // root) so the unit attaches at its own level and enqueues
                            // (Spec 06 section 3; the Phase 2 order preserved).
                            self.backtrack(root_level.max(analysis.backjump_level));
                            let offset = match self.create_learnt(literals, lbd) {
                                Ok(value) => value,
                                Err(terminal) => break terminal,
                            };
                            if let Err(error) = self.registry.bump_activity(offset) {
                                break AssumptionOutcome::Indeterminate(CdclError::Registry(error));
                            }
                        } else {
                            // Multi-literal learnt: create, attach, backjump (clamped),
                            // then assert the UIP literal with the learnt clause as its
                            // reason (Spec 06 section 3; the Phase 2 order preserved).
                            let attached = match self.create_learnt(literals, lbd) {
                                Ok(value) => value,
                                Err(terminal) => break terminal,
                            };
                            self.backtrack(root_level.max(analysis.backjump_level));
                            if let Err(error) =
                                self.core.assign_with_reason(learnt_buffer[0], attached)
                            {
                                break AssumptionOutcome::Indeterminate(CdclError::from(error));
                            }
                            if let Err(error) = self.registry.bump_activity(attached) {
                                break AssumptionOutcome::Indeterminate(CdclError::Registry(error));
                            }
                        }
                        if let Err(error) = self.registry.bump_activity(conflict) {
                            break AssumptionOutcome::Indeterminate(CdclError::Registry(error));
                        }
                        // Database reduction after learning (design 11.6; Spec 06
                        // section 9); the conflict clause is locked during reduction.
                        match self
                            .registry
                            .reduce(&self.core, conflict, self.proof.as_ref())
                        {
                            Ok(_) => {}
                            Err(error) => {
                                break AssumptionOutcome::Indeterminate(CdclError::Registry(error))
                            }
                        }
                    }
                    PropagationOutcome::NoConflict => {
                        if self.restarts.should_restart() {
                            self.backtrack(root_level);
                            self.restarts.record_restart();
                            if self.reset_phases_on_restart {
                                self.phases.reset();
                            }
                            continue;
                        }
                        let decision =
                            self.vsids.pick_unassigned(|variable| {
                                match SatLiteral::new(SatVar(variable), true) {
                                    Ok(literal) => {
                                        self.core.value_of_literal(literal) != SatValue::Unassigned
                                    }
                                    Err(_) => true,
                                }
                            });
                        match decision {
                            None => break AssumptionOutcome::Satisfiable,
                            Some(variable) => {
                                let positive = self.phases.phase(variable);
                                let literal = match SatLiteral::new(SatVar(variable), positive) {
                                    Ok(value) => value,
                                    Err(_) => {
                                        break AssumptionOutcome::Indeterminate(CdclError::Storage(
                                            SatCoreError::InvariantViolation,
                                        ))
                                    }
                                };
                                if let Err(error) = self.core.decide(literal) {
                                    break AssumptionOutcome::Indeterminate(CdclError::from(error));
                                }
                            }
                        }
                    }
                }
            }
        };
        // Epilogue (Spec 10 section 5). Plain solves (no assumptions) keep the exact
        // Phase 2 contract: the model stays readable and the learnt clauses stay in
        // the database (they are entailed by the formula alone). Assumption solves
        // must remove the assumption-dependent learnts and the assumption proof
        // units; a Satisfiable outcome defers that cleanup so the model stays
        // readable (flush_pending_cleanup runs it at the next interaction), while
        // every other outcome cleans up immediately.
        if assumptions.is_empty() {
            return outcome;
        }
        if matches!(outcome, AssumptionOutcome::Satisfiable) {
            for (slot, (id, literal)) in proof_assumption_ids[..assumption_recorded]
                .iter()
                .enumerate()
            {
                self.pending_cleanup_steps[slot]
                    .set((*id as u64) << kPendingCleanupIdShift | literal.encoding() as u64);
            }
            self.pending_cleanup_steps_count
                .set(assumption_recorded as u32);
            self.pending_cleanup.set(entry_registry_index);
            return outcome;
        }
        self.backtrack(0);
        if let Err(error) = self.registry.delete_learnts_from(
            self.core.clauses(),
            entry_registry_index,
            self.proof.as_ref(),
        ) {
            return AssumptionOutcome::Indeterminate(CdclError::Registry(error));
        }
        if let Some(recorder) = &self.proof {
            for (id, literal) in proof_assumption_ids[..assumption_recorded].iter().rev() {
                if let Err(error) = recorder.record_assumption_delete(*id, *literal) {
                    return AssumptionOutcome::Indeterminate(CdclError::Proof(error));
                }
            }
        }
        outcome
    }

    // CEP:WHAT: Creates, registers, proof-records, and attaches one learnt clause; returns the clause offset or the terminal outcome for falsified-unit refutations.
    // CEP:WHY: One sanctioned creation path keeps registration and proof emission impossible to forget (S21/S41) for both the unit and the multi-literal branches of the loop; a learnt unit falsified at attach time is a level-0-style refutation of the current conjunction and carries the empty-clause proof step.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates CdclError (storage, registry, proof); returns the Indeterminate terminal for the refutation case with the empty clause already recorded.
    // CEP:ASSUMES: literals are non-empty and their variables are declared.
    // CEP:COST: O(length) creation plus O(1) registration and one proof append.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates; unit/hot/sat_proof_test.rs::steps_recorded_in_order; unit/hot/sat_solver_test.rs::pigeonhole_is_unsat.
    // CEP:SECURITY: creation bounds enforced by the storage.
    fn create_learnt(&self, literals: &[SatLiteral], lbd: u8) -> Result<u32, AssumptionOutcome> {
        let offset = self
            .core
            .clauses()
            .new_clause(literals, true, lbd)
            .map_err(|error| {
                AssumptionOutcome::Indeterminate(CdclError::from(SatCoreError::from(error)))
            })?;
        if let Err(error) = self.registry.register(self.core.clauses(), offset) {
            return Err(AssumptionOutcome::Indeterminate(CdclError::Registry(error)));
        }
        if let Some(recorder) = &self.proof {
            if let Err(error) = recorder.record_add(offset, literals) {
                return Err(AssumptionOutcome::Indeterminate(CdclError::Proof(error)));
            }
        }
        match self.core.attach_clause(offset) {
            Ok(AttachOutcome::Attached(value)) => Ok(value),
            Ok(AttachOutcome::UnitEnqueued(value)) => Ok(value),
            Ok(AttachOutcome::AlreadySatisfied) => Ok(offset),
            Ok(AttachOutcome::Conflict) => {
                // A learnt unit falsified at its level: the conjunction is refuted
                // (Spec 06 section 8); emit the empty clause into an attached proof.
                if let Some(recorder) = &self.proof {
                    if let Err(error) = recorder.record_empty_clause() {
                        return Err(AssumptionOutcome::Indeterminate(CdclError::Proof(error)));
                    }
                }
                Err(AssumptionOutcome::Unsatisfiable)
            }
            Err(error) => Err(AssumptionOutcome::Indeterminate(CdclError::from(error))),
        }
    }

    // CEP:WHAT: Handles a conflict at or below the assumption root level: final analysis over the conflict clause, core recording, empty-clause proof emission, and the UnsatUnderAssumptions (or Unsatisfiable for an empty core) outcome.
    // CEP:WHY: Spec 10 section 4: levels 1..=root are assumptions and cannot be undone, so learning is replaced by analyze_final; an empty core means every seed literal was level-0 entailed, i.e. the formula alone is refuted.
    // CEP:STATUS: complete
    // CEP:FAILURE: storage and proof errors surface as Indeterminate.
    // CEP:ASSUMES: the trail is intact at the conflict; called before any backtracking.
    // CEP:COST: one analyze_final pass.
    // CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{unsat_under_assumptions_yields_core, failed_core_is_minimal_subset, empty_core_means_unsat}.
    // CEP:SECURITY: bounded by the trail length.
    fn root_region_conflict(&self, conflict: u32) -> AssumptionOutcome {
        let header = match self.core.clauses().header(conflict) {
            Ok(value) => value,
            Err(error) => {
                return AssumptionOutcome::Indeterminate(CdclError::from(SatCoreError::from(error)))
            }
        };
        let mut seed: [SatLiteral; kMaxSatClauseLiterals as usize] =
            [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize];
        let mut seed_len: usize = 0;
        while seed_len < header.length as usize {
            match self.core.clauses().literal(conflict, seed_len as u32) {
                Ok(value) => {
                    seed[seed_len] = value;
                    seed_len += 1;
                }
                Err(error) => {
                    return AssumptionOutcome::Indeterminate(CdclError::from(SatCoreError::from(
                        error,
                    )))
                }
            }
        }
        let mut core: [SatLiteral; kMaxAssumptions as usize] =
            [SatLiteral::from_encoding(0); kMaxAssumptions as usize];
        let core_len = match self
            .analyzer
            .analyze_final(&self.core, &seed[..seed_len], &mut core)
        {
            Ok(value) => value,
            Err(error) => return AssumptionOutcome::Indeterminate(error),
        };
        let outcome = if core_len == 0 {
            AssumptionOutcome::Unsatisfiable
        } else {
            AssumptionOutcome::UnsatUnderAssumptions
        };
        self.record_core(&core[..core_len]);
        if let Some(recorder) = &self.proof {
            if let Err(error) = recorder.record_empty_clause() {
                return AssumptionOutcome::Indeterminate(CdclError::Proof(error));
            }
        }
        outcome
    }

    // CEP:WHAT: Stores a failed core into the solver's failed buffer.
    // CEP:WHY: failed_assumptions_into reads this buffer after the solve returns; recording at the analysis point keeps the core exact even though the epilogue backtracks.
    // CEP:STATUS: complete
    // CEP:FAILURE: cores longer than the buffer are truncated to the first kMaxAssumptions members (cannot happen: the core is a subset of at most kMaxAssumptions assumptions).
    // CEP:ASSUMES: core members are distinct assumptions.
    // CEP:COST: O(core length).
    // CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{unsat_under_assumptions_yields_core, core_negation_is_entailed}.
    // CEP:SECURITY: bounds-checked writes.
    fn record_core(&self, core: &[SatLiteral]) {
        let mut count: usize = 0;
        for literal in core.iter() {
            if count >= self.failed.len() {
                break;
            }
            self.failed[count].set(*literal);
            count += 1;
        }
        self.failed_count.set(count as u32);
    }

    // CEP:WHAT: Backtracks to a level, saving phases and reinserting every popped variable through one batched VSIDS wave.
    // CEP:WHY: Design 11.1 S17 (save polarity) and the MiniSat heap discipline (unassigned variables return to the decision structure); walking the popped segment before core cancellation keeps the three structures consistent. The wave is merged as one sorted batch per touched band (CEP-1030) instead of per-variable walks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: level <= current level.
    // CEP:COST: O(popped entries) for the phase pass plus O(W log W) wave sort and one merge walk per touched band.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero; unit/hot/sat_vsids_test.rs::{insert_after_backtrack, wave_insert_matches_oracle}.
    // CEP:SECURITY: clamped level arithmetic in the core.
    fn backtrack(&self, level: u32) {
        let keep = self.core.trail().cancel_keep_index(level);
        let old_len = self.core.trail().len();
        let mut index = old_len;
        while index > keep {
            index -= 1;
            if let Some(literal) = self.core.trail().literal_at(index) {
                self.phases
                    .save_phase(literal.variable().0, literal.is_positive());
            }
        }
        let keep_index = keep;
        self.vsids
            .insert_wave_iter((keep_index..old_len).rev().filter_map(|entry| {
                self.core
                    .trail()
                    .literal_at(entry)
                    .map(|literal| literal.variable().0)
            }));
        self.core.cancel_until(level);
    }
}
