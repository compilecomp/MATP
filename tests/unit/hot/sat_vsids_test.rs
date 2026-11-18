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

use common::{make_arena, DeterministicRng};
use mapt::hot::sat::vsids::{PhaseTable, VsidsError, VsidsHeap};
use mapt_config::limits::{
    kMaxSatVariables, kSatDefaultPhasePositive, kSatVsidsActivityCeiling, kSatVsidsDecayPercent,
    kSatVsidsRescaleFactor,
};

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

// CEP:WHAT: Fuzz fixture size for the two-level bucket heap tests.
// CEP:WHY: Large enough to spread activities over hundreds of ladder bands, small enough for the oracle's linear-scan argmax.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzVariables: u32 = 64;

// CEP:WHAT: Constructs a VSIDS heap fixture with a given variable count.
// CEP:WHY: Shared setup for the fuzz harnesses.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena sized for the two-level arrays.
// CEP:COST: one arena.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_heap_n(variables: u32) -> VsidsHeap<'static> {
    let arena = make_arena(4_194_304);
    VsidsHeap::new(arena, variables).expect("heap")
}

// CEP:WHAT: Reference oracle mirroring the normative Spec 06 section 6 semantics: per-variable activities, membership flags, and the geometric increment with its rescale; pick is a linear argmax over (activity desc, index asc).
// CEP:WHY: The two-level bucket heap must be behaviorally indistinguishable from the normative order; the oracle is the independent definition the differential tests compare against.
// CEP:STATUS: complete
// CEP:FAILURE: the fuzz tests fail loudly on any pick or activity divergence.
// CEP:ASSUMES: mirrors the exact arithmetic of hot/sat/vsids.rs (same f64 operations in the same order, so results are bitwise identical).
// CEP:COST: linear scans; test-only.
// CEP:EVIDENCE: used by ladder_matches_oracle_under_fuzz and wave_insert_matches_oracle.
// CEP:SECURITY: none.
struct Oracle {
    activities: Vec<f64>,
    present: Vec<bool>,
    increment: f64,
}

impl Oracle {
    // CEP:WHAT: Creates an oracle with all variables present and zero activities.
    // CEP:WHY: Matches VsidsHeap::new's initial state.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: linear.
    // CEP:EVIDENCE: used by the fuzz tests.
    // CEP:SECURITY: none.
    fn new(variables: u32) -> Oracle {
        Oracle {
            activities: vec![0.0; variables as usize],
            present: vec![true; variables as usize],
            increment: 1.0,
        }
    }

    // CEP:WHAT: Mirrors VsidsHeap::bump (activity update only; membership unchanged).
    // CEP:WHY: The heap re-bands present variables and updates absent ones' scores; the membership effect is identical in both.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: used by the fuzz tests.
    // CEP:SECURITY: none.
    fn bump(&mut self, variable: u32) {
        self.activities[variable as usize] += self.increment;
    }

    // CEP:WHAT: Mirrors VsidsHeap::decay including the rescale branch.
    // CEP:WHY: Same growth factor, same ceiling, same order-preserving multiply, and the same flush: a product below the smallest normal is stored as exactly 0.0, matching the normative flush semantics (a score below the ladder is zero, so the bottom band ties by index).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: linear on rescale.
    // CEP:EVIDENCE: used by ladder_matches_oracle_under_fuzz and wave_insert_matches_oracle.
    // CEP:SECURITY: none.
    fn decay(&mut self) {
        self.increment *= 100.0 / kSatVsidsDecayPercent as f64;
        if self.increment > kSatVsidsActivityCeiling {
            for score in self.activities.iter_mut() {
                let scaled = *score * kSatVsidsRescaleFactor;
                *score = if scaled < f64::MIN_POSITIVE {
                    0.0
                } else {
                    scaled
                };
            }
            self.increment *= kSatVsidsRescaleFactor;
        }
    }

    // CEP:WHAT: Mirrors pick_unassigned: argmax over (activity desc, index asc) among present variables, then removal.
    // CEP:WHY: The normative decision rule, implemented independently of the bucket structure.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: ties keep the first (lowest-index) candidate, matching the total key.
    // CEP:COST: linear.
    // CEP:EVIDENCE: used by the fuzz tests.
    // CEP:SECURITY: none.
    fn pick(&mut self) -> Option<u32> {
        let mut best: Option<usize> = None;
        for index in 0..self.activities.len() {
            if !self.present[index] {
                continue;
            }
            match best {
                None => best = Some(index),
                Some(current) => {
                    if self.activities[index] > self.activities[current] {
                        best = Some(index);
                    }
                }
            }
        }
        best.map(|index| {
            self.present[index] = false;
            index as u32
        })
    }

    // CEP:WHAT: Mirrors insert (present flag set; already-present stays present).
    // CEP:WHY: The heap's insert is a no-op for present variables; the flag semantics match.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: used by the fuzz tests.
    // CEP:SECURITY: none.
    fn insert(&mut self, variable: u32) {
        self.present[variable as usize] = true;
    }

    // CEP:WHAT: Mirrors insert_wave_iter (a set union; duplicates collapse).
    // CEP:WHY: The heap's wave deduplicates through the pending marker; the set union is the same semantics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: linear in the wave.
    // CEP:EVIDENCE: used by wave_insert_matches_oracle.
    // CEP:SECURITY: none.
    fn wave(&mut self, variables: &[u32]) {
        for variable in variables {
            self.present[*variable as usize] = true;
        }
    }
}

// CEP:WHAT: Drives one decay burst in lockstep: repeated decay on both the heap and the oracle until the increment crosses the activity ceiling, which is the decay that performs exactly one rescale.
// CEP:WHY: The rescale is the rare rebuild path; a burst must terminate (the increment only drops via the rescale, so a ceiling-based while-loop re-enters forever) and must apply the identical decay sequence to both sides.
// CEP:STATUS: complete
// CEP:FAILURE: none (the increment grows monotonically by 100/95 per decay and is bitwise identical on both sides, so both cross together).
// CEP:ASSUMES: heap and oracle increments are bitwise identical before the burst.
// CEP:COST: ~4800 decay calls per burst, one rescale.
// CEP:EVIDENCE: used by the differential fuzz and underflow_flush_ties_by_index.
// CEP:SECURITY: none.
fn decay_burst_lockstep(heap: &VsidsHeap, oracle: &mut Oracle) {
    let mut guard = 0usize;
    loop {
        let before = heap.increment();
        heap.decay();
        oracle.decay();
        if heap.increment() < before {
            // The only shrinking step is the rescale's multiply by 1e-100: exactly one
            // rescale has happened.
            break;
        }
        guard += 1;
        assert!(
            guard < 100_000,
            "the burst never reached the rescale ceiling"
        );
    }
}

// CEP:WHAT: Shared differential fuzz harness: drives the heap and the oracle through the same deterministic operation sequence and asserts identical picks and bitwise-identical activities.
// CEP:WHY: CEP-1030's correctness claim is behavioral equivalence with the normative order; a fixed-seed differential run over thousands of mixed operations (bump, decay, rescale burst, pick, insert, wave) is the strongest available evidence short of the release bench.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on the first divergent pick or activity.
// CEP:ASSUMES: the oracle mirrors the heap's f64 arithmetic operation-for-operation.
// CEP:COST: offline; a few million oracle scans worst case.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs CEP:EVIDENCE.
// CEP:SECURITY: none.
fn run_differential_fuzz(seed: u64, use_waves: bool, iterations: usize) {
    let heap = make_heap_n(kFuzzVariables);
    let mut oracle = Oracle::new(kFuzzVariables);
    let mut rng = DeterministicRng::new(seed);
    for _ in 0..iterations {
        let roll = rng.below(100);
        if roll < 45 {
            let variable = rng.below(kFuzzVariables as u64) as u32;
            heap.bump(variable);
            oracle.bump(variable);
        } else if roll < 60 {
            heap.decay();
            oracle.decay();
        } else if roll < 66 {
            // Rescale burst: one full increment growth cycle, exercising the rare rebuild.
            decay_burst_lockstep(&heap, &mut oracle);
        } else if roll < 86 {
            let got = heap.pick_unassigned(|_| false);
            let want = oracle.pick();
            assert_eq!(got, want, "pick diverged from the normative order");
        } else if roll < 93 && use_waves {
            let mut wave: Vec<u32> = Vec::new();
            for _ in 0..rng.below(8) {
                wave.push(rng.below(kFuzzVariables as u64) as u32);
            }
            heap.insert_wave_iter(wave.iter().copied());
            oracle.wave(&wave);
        } else {
            let variable = rng.below(kFuzzVariables as u64) as u32;
            heap.insert(variable);
            oracle.insert(variable);
        }
        if rng.below(97) == 0 {
            for variable in 0..kFuzzVariables as usize {
                assert_eq!(
                    heap.activity(variable as u32),
                    oracle.activities[variable],
                    "activity mirror diverged for variable {variable}"
                );
            }
        }
    }
}

// CEP:WHAT: Differential fuzz over bumps, decays, rescale bursts, picks, and inserts (no waves).
// CEP:WHY: The bucket ladder must decide exactly like the normative (activity, index) oracle across band boundaries and rescales.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any pick or activity divergence.
// CEP:ASSUMES: fixed seed keeps the run reproducible (CEP&CC 28.3).
// CEP:COST: offline.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs (band lookup, unlink/link, pick cursor).
// CEP:SECURITY: none.
#[test]
fn ladder_matches_oracle_under_fuzz() {
    run_differential_fuzz(0x5EED_1030, false, 4_000);
}

// CEP:WHAT: Differential fuzz with batched wave insertions interleaved with picks, including duplicate and already-present wave members.
// CEP:WHY: The wave merge must preserve the exact key order; duplicate and present members must collapse deterministically.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any pick divergence.
// CEP:ASSUMES: fixed seed.
// CEP:COST: offline.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs (insert_wave_iter, merge_wave_group, heapsort).
// CEP:SECURITY: none.
#[test]
fn wave_insert_matches_oracle() {
    run_differential_fuzz(0x5EED_1031, true, 4_000);
}

// CEP:WHAT: Verifies that four rescale cycles flush a once-bumped score to exactly zero and that the flushed variable ties back into index order.
// CEP:WHY: The rescale factor is 1e-100, so a score of 1.0 underflows after four rescales; the flushed variable must rejoin the zero band and pick in index order, matching the binary heap's tie-break.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the flush is wrong or the tie order breaks.
// CEP:ASSUMES: kSatVsidsRescaleFactor = 1e-100; activities are never subnormal before the flush.
// CEP:COST: ~19200 decay calls, each O(1) except four O(variables + bands) rebuilds.
// CEP:EVIDENCE: cited by hot/sat/vsids.rs rescale_buckets (phase B).
// CEP:SECURITY: none.
#[test]
fn underflow_flush_ties_by_index() {
    let heap = make_heap_n(kFixtureVariables);
    let mut oracle = Oracle::new(kFixtureVariables);
    heap.bump(5);
    oracle.bump(5);
    for _ in 0..3 {
        decay_burst_lockstep(&heap, &mut oracle);
        assert!(
            heap.activity(5) > 0.0,
            "the score must still be positive before the fourth rescale"
        );
    }
    decay_burst_lockstep(&heap, &mut oracle);
    assert_eq!(
        heap.activity(5),
        0.0,
        "the fourth rescale must flush the score"
    );
    for variable in 0..kFixtureVariables {
        assert_eq!(
            heap.pick_unassigned(|_| false),
            Some(variable),
            "flushed variables must tie in index order"
        );
    }
    assert_eq!(heap.pick_unassigned(|_| false), None);
}
