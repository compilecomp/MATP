// CEP:FILE: tests/unit/hot/sat_vsids_test.rs
// CEP:WHAT: Unit tests for the VSIDS heap and phase table: construction, bumping, decay, rescaling, tie-breaking, pick discipline, backtracking reinsertion, and phase round trips.
// CEP:WHY: CEP&CC 32.8 and Formal Spec 06 section 6: the decision heuristic drives the search; a nondeterministic or wrong heap order changes proofs and can loop the search.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/vsids.rs.
// CEP:SECURITY: variable bounds are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::vsids::{PhaseTable, VsidsError, VsidsHeap};
use mapt_config::limits::{kMaxSatVariables, kSatDefaultPhasePositive, kSatVsidsActivityCeiling};

// CEP:WHAT: Default test variable count.
// CEP:WHY: Named constant for the heap fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFixtureVariables: u32 = 16;

// CEP:WHAT: Constructs a VSIDS heap fixture.
// CEP:WHY: Shared setup.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one arena.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_heap() -> VsidsHeap<'static> {
    let arena = make_arena(1_048_576);
    VsidsHeap::new(arena, kFixtureVariables).expect("heap")
}

// CEP:WHAT: Verifies construction rejects zero and oversize variable counts.
// CEP:WHY: Law 6: bounds violations are loud.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an invalid count is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs new.
// CEP:SECURITY: memory bounds.
#[test]
fn construction_rejects_bad_counts() {
    let arena = make_arena(1_048_576);
    assert_eq!(
        VsidsHeap::new(arena, 0).err(),
        Some(VsidsError::VariableCountInvalid)
    );
    let arena2 = make_arena(1_048_576);
    assert_eq!(
        VsidsHeap::new(arena2, kMaxSatVariables + 1).err(),
        Some(VsidsError::VariableCountInvalid)
    );
}

// CEP:WHAT: Verifies the initial pick is the lowest-index variable (zero activities, index tie-break).
// CEP:WHY: Determinism of the decision order from a fresh heap (CEP&CC 38.10).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a different first pick.
// CEP:ASSUMES: fresh heap.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs new and pick_unassigned.
// CEP:SECURITY: none.
#[test]
fn initial_pick_is_lowest_index() {
    let heap = make_heap();
    assert_eq!(heap.pick_unassigned(|_| false), Some(0));
    assert_eq!(heap.pick_unassigned(|_| false), Some(1));
}

// CEP:WHAT: Verifies bumping raises activity and reorders picks.
// CEP:WHY: S12/S13: conflicts must steer future decisions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the bumped variable is not picked first.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs bump.
// CEP:SECURITY: none.
#[test]
fn bump_raises_activity() {
    let heap = make_heap();
    assert_eq!(heap.activity(5), 0.0);
    heap.bump(5);
    assert!(heap.activity(5) > 0.0);
    heap.bump(5);
    assert_eq!(heap.pick_unassigned(|_| false), Some(5));
}

// CEP:WHAT: Verifies the decay grows the increment by 100 / kSatVsidsDecayPercent.
// CEP:WHY: S13: the geometric increment implements recency bias.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on the wrong growth factor.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs decay.
// CEP:SECURITY: none.
#[test]
fn decay_grows_increment() {
    let heap = make_heap();
    let before = heap.increment();
    heap.decay();
    let after = heap.increment();
    let expected = before * 100.0 / mapt_config::limits::kSatVsidsDecayPercent as f64;
    assert!(
        (after - expected).abs() < 1e-12,
        "decay must grow the increment by 100/{}",
        mapt_config::limits::kSatVsidsDecayPercent
    );
}

// CEP:WHAT: Verifies rescaling keeps every score finite and preserves order.
// CEP:WHY: The f64-overflow discipline: above the ceiling all scores and the increment shrink by the rescale factor, an order-preserving operation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on non-finite scores or order flips.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs decay.
// CEP:SECURITY: none.
#[test]
fn rescale_keeps_scores_finite() {
    let heap = make_heap();
    // Push variable 3 above variable 7 in activity, then force many decays until the
    // increment passes the ceiling and a rescale happens.
    for _ in 0..3 {
        heap.bump(3);
    }
    heap.bump(7);
    let higher_before = heap.activity(3);
    let lower_before = heap.activity(7);
    assert!(higher_before > lower_before);
    let mut decays: u32 = 0;
    while heap.increment() <= kSatVsidsActivityCeiling && decays < 5_000 {
        heap.decay();
        decays += 1;
    }
    assert!(
        heap.increment() <= kSatVsidsActivityCeiling,
        "the increment must be rescaled below the ceiling"
    );
    assert!(heap.activity(3).is_finite());
    assert!(heap.activity(7).is_finite());
    assert!(
        heap.activity(3) > heap.activity(7),
        "rescaling must preserve the activity order"
    );
}

// CEP:WHAT: Verifies activity ties are broken by the smaller variable index.
// CEP:WHY: CEP&CC 38.10: the heap key must be total for reproducible search.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a nondeterministic order.
// CEP:ASSUMES: equal activities.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs key_greater.
// CEP:SECURITY: none.
#[test]
fn ties_broken_by_index() {
    let heap = make_heap();
    heap.bump(9);
    heap.bump(4);
    heap.bump(12);
    // All three have equal activity (one bump each): picks must be 4, 9, 12.
    assert_eq!(heap.pick_unassigned(|_| false), Some(4));
    assert_eq!(heap.pick_unassigned(|_| false), Some(9));
    assert_eq!(heap.pick_unassigned(|_| false), Some(12));
}

// CEP:WHAT: Verifies pick_unassigned skips and discards assigned variables.
// CEP:WHY: The MiniSat lazy-removal discipline: assigned tops leave the heap permanently until backtracking reinserts them.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an assigned variable is returned.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs pick_unassigned.
// CEP:SECURITY: none.
#[test]
fn pick_skips_assigned() {
    let heap = make_heap();
    heap.bump(2);
    // Variables 0 and 1 are assigned: the pick must skip them and return 2.
    assert_eq!(heap.pick_unassigned(|variable| variable < 2), Some(2));
    // After 2 is picked (and assigned by the caller), the next unassigned is 3.
    assert_eq!(heap.pick_unassigned(|variable| variable < 3), Some(3));
}

// CEP:WHAT: Verifies backtracking reinsertion restores previously assigned variables.
// CEP:WHY: The heap invariant: every unassigned variable is in the heap.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a reinserted variable is never picked.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs insert.
// CEP:SECURITY: none.
#[test]
fn insert_after_backtrack() {
    let heap = make_heap();
    assert_eq!(heap.pick_unassigned(|_| false), Some(0));
    assert_eq!(heap.pick_unassigned(|_| false), Some(1));
    // Simulate a backtrack: variables 0 and 1 become unassigned again.
    heap.insert(0);
    heap.insert(1);
    // Double insert is a no-op.
    heap.insert(0);
    assert_eq!(heap.pick_unassigned(|_| false), Some(0));
    assert_eq!(heap.pick_unassigned(|_| false), Some(1));
    assert_eq!(heap.pick_unassigned(|_| false), Some(2));
}

// CEP:WHAT: Verifies the phase table defaults, round trip, and reset.
// CEP:WHY: S14/S17: phase selection and reset on restart.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong polarity.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs PhaseTable.
// CEP:SECURITY: none.
#[test]
fn phase_table_roundtrip() {
    let arena = make_arena(1_048_576);
    let phases = PhaseTable::new(arena, kFixtureVariables).expect("phases");
    assert_eq!(
        phases.phase(3),
        kSatDefaultPhasePositive,
        "unset entries fall back to the default phase"
    );
    phases.save_phase(3, true);
    phases.save_phase(4, false);
    assert!(phases.phase(3));
    assert!(!phases.phase(4));
    phases.reset();
    assert_eq!(phases.phase(3), kSatDefaultPhasePositive);
    assert_eq!(phases.phase(4), kSatDefaultPhasePositive);
}

// CEP:WHAT: Verifies the phase default constant name used by the test.
// CEP:WHY: Companion assertion so the default is pinned in one place.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatDefaultPhasePositive.
// CEP:SECURITY: none.
#[test]
fn saved_phase_defaults_to_constant() {
    let arena = make_arena(1_048_576);
    let phases = PhaseTable::new(arena, kFixtureVariables).expect("phases");
    for variable in 0..kFixtureVariables {
        assert_eq!(phases.phase(variable), kSatDefaultPhasePositive);
    }
}
