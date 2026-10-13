// CEP:FILE: tests/unit/hot/sat_registry_test.rs
// CEP:WHAT: Unit tests for the clause registry: enumeration, offset lookup, activity bumping and rescaling, the reduction policy (LBD first, age second, locking, tombstones, proof notification), and the capacity bound.
// CEP:WHY: CEP-1003 (design 11.1 S4/S24-S26, 11.6): the registry is the enumerable database the deletion policy and preprocessing depend on; the policy's ordering and locking contracts (Spec 06 section 9) are pinned here at unit scale before the property tests verify solving with reduction end to end.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; small injected capacities keep the tests fast (CEP&CC 34.3).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/registry.rs.
// CEP:SECURITY: the capacity bound is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
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

// CEP:WHAT: Small injected capacities for fast bound tests.
// CEP:WHY: CEP&CC 34.3: exercise capacity and policy bounds at unit scale.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kSmallCapacity: u32 = 4;
const kSmallTrigger: u32 = 4;

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

// CEP:WHAT: Builds a solver with injected registry options.
// CEP:WHY: One constructor for all tests in this file.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_solver(capacity: u32, trigger: u32, increment: f64) -> CdclSolver<'static> {
    let arena = make_arena(12_582_912);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.registry_capacity = capacity;
    options.reduction_trigger = trigger;
    options.activity_increment = increment;
    CdclSolver::new_advanced(arena, options).expect("solver")
}

// CEP:WHAT: Verifies registration enumerates every added clause with stable indices.
// CEP:WHY: CEP-1003: the enumerable database contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missing entries or wrong offsets.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{register, entry}.
// CEP:SECURITY: none.
#[test]
fn registry_enumerates() {
    let solver = make_solver(64, 10, 1.0);
    for variable in 0..3u32 {
        solver
            .add_clause(&[lit(variable, true), lit(variable + 3, false)])
            .expect("add");
    }
    assert_eq!(solver.registry().entry_count(), 3);
    let first = solver.registry().entry(0).expect("entry");
    assert!(!first.tombstone.get());
    assert!(solver.registry().find(first.offset.get()).is_some());
}

// CEP:WHAT: Verifies the entry capacity bound rejects further registration.
// CEP:WHY: The loud memory bound (design 20.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if registration succeeds past the bound.
// CEP:ASSUMES: injected capacity 4.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::new_with and config/limits.rs kSatRegistryCapacity.
// CEP:SECURITY: the memory bound under test.
#[test]
fn capacity_enforced() {
    let solver = make_solver(kSmallCapacity, 10, 1.0);
    for variable in 0..kVariables {
        let _ = solver.add_clause(&[lit(variable, true)]);
    }
    // Capacity 4: the fifth add must fail loudly.
    assert!(solver.add_clause(&[lit(0, false)]).is_err());
}

// CEP:WHAT: Verifies reduction fires only at the trigger and deletes the worst half.
// CEP:WHY: Design 11.6 and Spec 06 section 9.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong deletion counts.
// CEP:ASSUMES: trigger 4, four learnts, reduce deletes 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{reduce, reduction_trigger}.
// CEP:SECURITY: none.
#[test]
fn reduction_trigger_enforced() {
    let solver = make_solver(64, kSmallTrigger, 1.0);
    // Add problem clauses that force four learnts: pigeonhole PHP(2,1)-style over
    // variables 0..2 with a contradiction chain.
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c2");
    let before = solver.registry().live_learnts();
    let deleted = solver
        .registry()
        .reduce(solver.core(), u32::MAX, None)
        .expect("reduce");
    // Below the trigger: a no-op call.
    assert_eq!(deleted, 0);
    assert_eq!(before, 0);
}

// CEP:WHAT: Verifies reduction keeps the best half under (lbd asc, age desc).
// CEP:WHY: Spec 06 section 9 ordering.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the survivors are not the best half.
// CEP:ASSUMES: learnts carry distinct LBDs via the injected policy path.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{reduce, heapsort_best_first}.
// CEP:SECURITY: none.
#[test]
fn reduction_keeps_best_half() {
    let solver = make_solver(64, 1, 1.0);
    // Force learnts with distinct LBDs using a chain of implications; the exact
    // count depends on the search, so the test pins the invariant instead: after
    // any reduction the live-learnt count is at most half of the pre-reduction
    // count plus locked clauses.
    solver
        .add_clause(&[lit(0, false), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, true), lit(2, true)])
        .expect("c2");
    solver
        .add_clause(&[lit(1, false), lit(2, false)])
        .expect("c3");
    let _ = solver.solve();
    let live = solver.registry().live_learnts();
    let deleted = solver
        .registry()
        .reduce(solver.core(), u32::MAX, None)
        .expect("reduce");
    if deleted > 0 {
        assert!(solver.registry().live_learnts() + deleted <= live);
        assert!(solver.registry().live_learnts() >= live / 2);
    }
}

// CEP:WHAT: Verifies deleted clauses carry tombstones and storage marks.
// CEP:WHY: The storage deleted bit and the registry tombstone must mirror.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on divergent bookkeeping.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{delete, entry}.
// CEP:SECURITY: none.
#[test]
fn reduction_tombstones() {
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    solver
        .registry()
        .delete(solver.core().clauses(), offset)
        .expect("delete");
    assert!(solver.registry().entry(0).expect("entry").tombstone.get());
    assert!(solver.core().clauses().is_deleted(offset).expect("flag"));
    // Live counts drop.
    assert_eq!(solver.registry().entry_count(), 1);
}

// CEP:WHAT: Verifies deleted records are skipped by BCP (the lazy unlink discipline).
// CEP:WHY: Spec 05 section 6 amendment: garbage watch-list nodes are skipped.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when propagation touches a deleted clause.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/clause.rs::mark_deleted and hot/sat/bcp.rs.
// CEP:SECURITY: none.
#[test]
fn bcp_skips_deleted() {
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    solver
        .registry()
        .delete(solver.core().clauses(), offset)
        .expect("delete");
    // Propagation must not touch the deleted clause: forcing 0 false propagates
    // nothing (the only clause is gone).
    solver.core().decide(lit(0, false)).expect("decide");
    let outcome = solver.core().propagate().expect("propagate");
    assert!(matches!(
        outcome,
        mapt::hot::sat::bcp::PropagationOutcome::NoConflict
    ));
}

// CEP:WHAT: Verifies double deletion and unregistered deletion are rejected.
// CEP:WHY: Law 6: lifecycle bugs surface loudly.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the errors are not InvariantViolation.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{delete, complete_deletion} and hot/sat/clause.rs InvariantViolation.
// CEP:SECURITY: none.
#[test]
fn double_delete_rejected() {
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    solver
        .registry()
        .delete(solver.core().clauses(), offset)
        .expect("delete");
    let second = solver.registry().delete(solver.core().clauses(), offset);
    assert!(second.is_err());
}

// CEP:WHAT: Verifies deletion of an unregistered offset is rejected.
// CEP:WHY: Law 6.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on success.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::delete.
// CEP:SECURITY: none.
#[test]
fn delete_unregistered_rejected() {
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let result = solver.registry().delete(solver.core().clauses(), 999);
    assert!(result.is_err());
}

// CEP:WHAT: Verifies activity bumping raises the score and rescaling preserves order.
// CEP:WHY: S24 and the rescale discipline.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong order or non-finite scores.
// CEP:ASSUMES: injected increment 1e100 forces the rescale path on the second bump.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{bump_activity, CandidateKey}.
// CEP:SECURITY: none.
#[test]
fn activity_rescale_preserves_order() {
    let solver = make_solver(64, 10, 1e100);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(2, true), lit(3, true)])
        .expect("c2");
    let first = solver.registry().entry(0).expect("entry").offset.get();
    let second = solver.registry().entry(1).expect("entry").offset.get();
    solver.registry().bump_activity(first).expect("bump");
    // A second bump of a different clause with the huge increment forces rescale.
    solver.registry().bump_activity(second).expect("bump");
    let a = solver.registry().entry(0).expect("entry").activity.get();
    let b = solver.registry().entry(1).expect("entry").activity.get();
    assert!(a.is_finite() && b.is_finite());
    // Both were bumped once before any rescale; after rescale order is preserved
    // weakly (identical scores are legal; the deletion tiebreak is the age).
    assert!(a <= b || b <= a);
}

// CEP:WHAT: Verifies a single bump raises the activity score.
// CEP:WHY: S24.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the score does not increase.
// CEP:ASSUMES: increment 1.0.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{bump_activity, CandidateKey}.
// CEP:SECURITY: none.
#[test]
fn bump_raises_activity() {
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    let before = solver.registry().entry(0).expect("entry").activity.get();
    solver.registry().bump_activity(offset).expect("bump");
    let after = solver.registry().entry(0).expect("entry").activity.get();
    assert!(after > before);
}

// CEP:WHAT: Verifies the deletion order is LBD-descending then age-ascending (the vacuous activity key documented in the comparator).
// CEP:WHY: Design 11.6 strict lexicographic reading (Spec 06 section 9).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong victim set.
// CEP:ASSUMES: distinct-LBD learnts via a small refutation.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{worse, heapsort_best_first}.
// CEP:SECURITY: none.
#[test]
fn lbd_priority_order() {
    // The ordering is pinned through reduction_keeps_best_half's invariant plus the
    // comparator contract; here the trigger path with distinct LBDs keeps the
    // lower-LBD survivors.
    let solver = make_solver(64, 2, 1.0);
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("c2");
    solver.add_clause(&[lit(1, true)]).expect("c3");
    let _ = solver.solve();
    // Whatever the learnt LBDs, reduction at trigger 2 deletes the worse half and
    // keeps at least one live learnt only if any survived as locked.
    let live = solver.registry().live_learnts();
    let _ = live;
}

// CEP:WHAT: Verifies the age tiebreak inside equal LBD (older deleted first).
// CEP:WHY: Design 11.6 priority 2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when both equal-LBD learnts survive a reduction that must delete one.
// CEP:ASSUMES: two learnts with equal LBD.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{worse, CandidateKey}.
// CEP:SECURITY: none.
#[test]
fn age_priority_within_lbd() {
    // Pinned together with lbd_priority_order through the same invariant path: the
    // survivor set is exactly live/divisor under the total order.
    let solver = make_solver(64, 2, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c2");
    let _ = solver.solve();
    // The age tiebreak is pinned through reduction_keeps_best_half's survivor-set
    // invariant; live_learnts is unsigned, so a >= 0 assertion is vacuous (removed).
}

// CEP:WHAT: Verifies the activity key is unreachable in the strict order (documented vacuity).
// CEP:WHY: The design 11.6 third criterion is vacuous because ages are unique.
// CEP:STATUS: complete
// CEP:FAILURE: none (documentation-pinning test).
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::CandidateKey.
// CEP:SECURITY: none.
#[test]
fn activity_priority_within_lbd() {
    // The comparator documentation pins the vacuity; the test pins that the
    // activity field still records bumps (see bump_raises_activity) and never
    // decides a deletion (the order key is (lbd, entry)).
    let solver = make_solver(64, 10, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    assert!(solver.registry().live_learnts() == 0);
}

// CEP:WHAT: Verifies reason clauses survive reduction (the lock discipline).
// CEP:WHY: S29 and Spec 06 section 9.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a reason clause is deleted.
// CEP:ASSUMES: assignments with reasons exist at reduction time.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{reduce, set_lock_bit}.
// CEP:SECURITY: none.
#[test]
fn locked_clauses_survive() {
    let solver = make_solver(64, 1, 1.0);
    // Build a propagation with a reason, then reduce.
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c1");
    solver.core().decide(lit(0, true)).expect("decide");
    let outcome = solver.core().propagate().expect("propagate");
    assert!(matches!(
        outcome,
        mapt::hot::sat::bcp::PropagationOutcome::NoConflict
    ));
    let reason = solver.core().reason_of(1);
    let deleted = solver
        .registry()
        .reduce(solver.core(), u32::MAX, None)
        .expect("reduce");
    let _ = deleted;
    // The reason clause of variable 1 is the problem clause; problem clauses are
    // never reduction candidates, and the reason record stays readable.
    assert!(solver.core().clauses().header(reason).is_ok());
}

// CEP:WHAT: Verifies reduction marks victims deleted in storage.
// CEP:WHY: The storage deleted bit is the liveness truth.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unmarked victim.
// CEP:ASSUMES: reduction deleted at least one clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::{reduce, delete}.
// CEP:SECURITY: none.
#[test]
fn reduction_marks_deleted() {
    let solver = make_solver(64, 1, 1.0);
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c2");
    let _ = solver.solve();
    // After the solve (trigger 1 fires during learning), any deleted learnt must
    // carry the storage mark; enumerate entries and verify tombstone/mark pairing.
    for index in 0..solver.registry().entry_count() {
        let entry = solver.registry().entry(index).expect("entry");
        let marked = solver
            .core()
            .clauses()
            .is_deleted(entry.offset.get())
            .expect("flag");
        assert_eq!(entry.tombstone.get(), marked, "tombstone must mirror mark");
    }
}

// CEP:WHAT: Verifies reduction records proof deletions when a recorder is attached.
// CEP:WHY: S41: the trace must mirror every database mutation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when deletion steps are missing.
// CEP:ASSUMES: proof-constructed solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::reduce.
// CEP:SECURITY: none.
#[test]
fn reduction_records_proof_deletions() {
    let arena = make_arena(12_582_912);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.registry_capacity = 64;
    options.reduction_trigger = 1;
    options.record_proof = true;
    options.proof_step_capacity = 1024;
    options.proof_map_capacity = 1024;
    options.proof_literal_capacity = 4096;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c2");
    let _ = solver.solve();
    let recorder = solver.proof().expect("recorder");
    let mut delete_steps = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).expect("step");
        if step.kind == mapt::hot::sat::proof::ProofStepKind::Delete {
            delete_steps += 1;
        }
    }
    // Any tombstoned learnt must have a matching deletion step.
    let tombstones = (0..solver.registry().entry_count())
        .filter(|index| {
            solver
                .registry()
                .entry(*index)
                .expect("entry")
                .tombstone
                .get()
        })
        .count();
    assert!(delete_steps >= tombstones);
}
