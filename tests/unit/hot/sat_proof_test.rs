// CEP:FILE: tests/unit/hot/sat_proof_test.rs
// CEP:WHAT: Unit tests for the DRAT proof recorder: step ordering, id monotonicity, literal fidelity, deletion resolution, axiom/derived/assumption step kinds, empty-clause steps, the unmapped-deletion rejection, and the capacity bounds.
// CEP:WHY: Design 11.1 S41/S42 and Spec 11: the recorder is the certificate source; its buffer discipline (dense ids, ascending map, verbatim literals) is pinned here before the cold writer and checker tests consume recorded traces.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; injected proof capacities for the bound tests.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/proof.rs.
// CEP:SECURITY: the capacity bound is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::proof::{ProofError, ProofStepKind};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};

// CEP:WHAT: Test variable count.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 8;

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable clause construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Builds a proof-recording solver with injected capacities.
// CEP:WHY: One constructor for this file.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver with recorder.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_proof_solver(
    step_capacity: u32,
    map_capacity: u32,
    literal_capacity: u32,
) -> CdclSolver<'static> {
    let arena = make_arena(16_777_216);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.record_proof = true;
    options.proof_step_capacity = step_capacity;
    options.proof_map_capacity = map_capacity;
    options.proof_literal_capacity = literal_capacity;
    CdclSolver::new_advanced(arena, options).expect("solver")
}

// CEP:WHAT: Verifies problem clauses record as axiom steps in addition order.
// CEP:WHY: Spec 11 section 3: axioms seed the checker's database in formula order.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong kinds or order.
// CEP:ASSUMES: fresh recorder.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_axiom_add, step}.
// CEP:SECURITY: none.
#[test]
fn steps_recorded_in_order() {
    let solver = make_proof_solver(1024, 1024, 4096);
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("c1");
    solver.add_clause(&[lit(2, true)]).expect("c2");
    let recorder = solver.proof().expect("recorder");
    assert_eq!(recorder.step_count(), 2);
    let first = recorder.step(0).expect("step");
    assert_eq!(first.kind, ProofStepKind::AxiomAdd);
    assert_eq!(first.literal_count, 2);
    let second = recorder.step(1).expect("step");
    assert_eq!(second.kind, ProofStepKind::AxiomAdd);
    assert_eq!(second.literal_count, 1);
}

// CEP:WHAT: Verifies proof ids are dense, monotonic, and 1-based.
// CEP:WHY: Spec 11 section 2: stable identities for LRAT-style consumption.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on non-monotonic ids.
// CEP:ASSUMES: fresh recorder.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_add, kFirstProofId}.
// CEP:SECURITY: none.
#[test]
fn ids_are_monotonic() {
    let solver = make_proof_solver(1024, 1024, 4096);
    solver.add_clause(&[lit(0, true)]).expect("c1");
    solver.add_clause(&[lit(1, true)]).expect("c2");
    solver.add_clause(&[lit(2, true)]).expect("c3");
    let recorder = solver.proof().expect("recorder");
    let mut last = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).expect("step");
        assert!(step.proof_id > last);
        last = step.proof_id;
    }
    assert_eq!(last, 3);
}

// CEP:WHAT: Verifies step literals are stored verbatim.
// CEP:WHY: The blob extents must reproduce the added clauses exactly.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any literal mismatch.
// CEP:ASSUMES: fresh recorder.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_add, step_literal}.
// CEP:SECURITY: none.
#[test]
fn literals_stored_verbatim() {
    let solver = make_proof_solver(1024, 1024, 4096);
    let clause = [lit(0, true), lit(1, false), lit(2, true)];
    solver.add_clause(&clause).expect("c1");
    let recorder = solver.proof().expect("recorder");
    let step = recorder.step(0).expect("step");
    for (index, expected) in clause.iter().enumerate() {
        let stored = recorder.step_literal(step, index as u32).expect("literal");
        assert_eq!(stored.encoding(), expected.encoding());
    }
}

// CEP:WHAT: Verifies the offset-to-id map resolves deletions.
// CEP:WHY: Spec 11 section 3: deletions carry their addition's id.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong id.
// CEP:ASSUMES: clause added then deleted through the registry.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_delete, proof_id_of}.
// CEP:SECURITY: none.
#[test]
fn deletion_resolves_id() {
    let solver = make_proof_solver(1024, 1024, 4096);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let recorder = solver.proof().expect("recorder");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    assert_eq!(recorder.proof_id_of(offset), Some(1));
    // Deleting through the registry with proof notification.
    use mapt::hot::sat::registry::RegistryError;
    let result: Result<(), RegistryError> = (|| {
        recorder
            .record_delete(offset, solver.core().clauses())
            .map_err(RegistryError::from)?;
        solver.registry().delete(solver.core().clauses(), offset)?;
        Ok(())
    })();
    result.expect("delete");
    let last = recorder.step(1).expect("step");
    assert_eq!(last.kind, ProofStepKind::Delete);
    assert_eq!(last.proof_id, 1);
}

// CEP:WHAT: Verifies deletions of never-added offsets are rejected.
// CEP:WHY: Law 6: bookkeeping divergence is loud.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on success.
// CEP:ASSUMES: fresh recorder.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_delete, UnmappedOffset}.
// CEP:SECURITY: none.
#[test]
fn unmapped_deletion_rejected() {
    let solver = make_proof_solver(1024, 1024, 4096);
    let recorder = solver.proof().expect("recorder");
    // No clause was ever recorded: any offset is unmapped.
    let result = recorder.record_delete(12345, solver.core().clauses());
    assert!(matches!(result, Err(ProofError::UnmappedOffset)));
}

// CEP:WHAT: Verifies the step buffer capacity bound is loud.
// CEP:WHY: Law 6: never a silent truncation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when adds succeed past the bound.
// CEP:ASSUMES: step capacity 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_add, StepBufferFull} and config/limits.rs kSatProofStepCapacity.
// CEP:SECURITY: the memory bound under test.
#[test]
fn capacity_enforced() {
    let solver = make_proof_solver(2, 8, 64);
    solver.add_clause(&[lit(0, true)]).expect("c1");
    solver.add_clause(&[lit(1, true)]).expect("c2");
    // The third add exhausts the two-step buffer.
    assert!(solver.add_clause(&[lit(2, true)]).is_err());
}

// CEP:WHAT: Verifies assumption units record as paired hypothesis steps.
// CEP:WHY: Spec 11 section 3: assumption adds are hypotheses and their deletes mirror them.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on unpaired or wrongly-kinded steps.
// CEP:ASSUMES: one assumption solve.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_assumption_add, record_assumption_delete}.
// CEP:SECURITY: none.
#[test]
fn assumption_steps_pair_up() {
    let solver = make_proof_solver(1024, 1024, 4096);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let outcome = solver.solve_with_assumptions(&[lit(0, true)]);
    use mapt::hot::sat::solver::AssumptionOutcome;
    assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
    let recorder = solver.proof().expect("recorder");
    let mut adds = 0;
    let mut deletes = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).expect("step");
        match step.kind {
            ProofStepKind::AssumptionAdd => adds += 1,
            ProofStepKind::AssumptionDelete => deletes += 1,
            _ => {}
        }
    }
    // The Satisfiable outcome defers cleanup: the add is recorded, the delete parks
    // in the pending state until the next interaction; flush by a second solve.
    let _ = solver.solve_with_assumptions(&[]);
    let mut adds_after = 0;
    let mut deletes_after = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).expect("step");
        match step.kind {
            ProofStepKind::AssumptionAdd => adds_after += 1,
            ProofStepKind::AssumptionDelete => deletes_after += 1,
            _ => {}
        }
    }
    assert_eq!(adds, 1);
    assert_eq!(adds_after, 1);
    assert_eq!(deletes_after, 1);
    assert!(deletes_after >= deletes);
}

// CEP:WHAT: Verifies axiom steps match the formula clauses one-to-one.
// CEP:WHY: Spec 11 section 3: the trace-to-formula binding.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a mismatched axiom step.
// CEP:ASSUMES: two formula clauses in order.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::record_axiom_add; consumed by unit/cold/drat_checker_test.rs::axioms_seed_the_database.
// CEP:SECURITY: none.
#[test]
fn axiom_steps_match_formula() {
    let solver = make_proof_solver(1024, 1024, 4096);
    let formula: [[SatLiteral; 2]; 2] =
        [[lit(0, true), lit(1, false)], [lit(2, true), lit(3, true)]];
    for clause in formula.iter() {
        solver.add_clause(clause).expect("add");
    }
    let recorder = solver.proof().expect("recorder");
    for (index, clause) in formula.iter().enumerate() {
        let step = recorder.step(index as u32).expect("step");
        for (slot, expected) in clause.iter().enumerate() {
            let stored = recorder.step_literal(step, slot as u32).expect("literal");
            assert_eq!(stored.encoding(), expected.encoding());
        }
    }
}

// CEP:WHAT: Verifies the empty-clause terminal step is recorded on refutation.
// CEP:WHY: Spec 11 section 4: a DRAT refutation ends with the empty clause.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the last step is not the empty add.
// CEP:ASSUMES: a trivially contradictory formula.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/proof.rs::{record_empty_clause, add_clause} and hot/sat/solver.rs.
// CEP:SECURITY: none.
#[test]
fn empty_clause_step_recorded() {
    let solver = make_proof_solver(1024, 1024, 4096);
    solver.add_clause(&[lit(0, true)]).expect("unit");
    solver.add_clause(&[lit(0, false)]).expect("counter-unit");
    let outcome = solver.solve();
    assert!(matches!(
        outcome,
        mapt::hot::sat::solver::SolveResult::Unsatisfiable
    ));
    let recorder = solver.proof().expect("recorder");
    let last = recorder.step(recorder.step_count() - 1).expect("step");
    assert_eq!(last.kind, ProofStepKind::Add);
    assert_eq!(last.literal_count, 0);
}
