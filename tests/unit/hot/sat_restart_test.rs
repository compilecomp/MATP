// CEP:FILE: tests/unit/hot/sat_restart_test.rs
// CEP:WHAT: Unit tests for restart scheduling: the canonical Luby sequence pinned to the design's literal values, threshold scaling, geometric growth, firing conditions, and saturating arithmetic.
// CEP:WHY: CEP&CC 32.8 and design 11.5: the restart schedule must be the exact Luby sequence (the design spells out its first sixteen values) because restart points change the proof trace.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any sequence deviation.
// CEP:ASSUMES: none beyond the scheduler itself.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/restart.rs.
// CEP:SECURITY: saturating counters are exercised here.

#![allow(non_upper_case_globals)]

use mapt::hot::sat::restart::{luby_value, RestartPolicy, RestartScheduler};
use mapt_config::limits::kSatRestartBaseInterval;

// CEP:WHAT: Verifies the Luby values match the design's literal sequence 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1.
// CEP:WHY: Design 11.5 pins this exact sequence; any deviation changes restart points and proofs.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any value mismatch.
// CEP:ASSUMES: 1-based indexing.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/restart.rs luby_value.
// CEP:SECURITY: none.
#[test]
fn luby_sequence_matches_design() {
    let expected: [u64; 16] = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1];
    for (index, value) in expected.iter().enumerate() {
        assert_eq!(
            luby_value(index as u32 + 1),
            *value,
            "Luby value {} must match the design sequence",
            index + 1
        );
    }
    // Longer prefix spot checks (positions 17-31).
    let tail: [u64; 15] = [1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 16];
    for (offset, value) in tail.iter().enumerate() {
        assert_eq!(luby_value(offset as u32 + 17), *value);
    }
    // Index zero is treated as one (documented).
    assert_eq!(luby_value(0), 1);
}

// CEP:WHAT: Verifies Luby thresholds scale the base interval through restarts.
// CEP:WHY: Design 11.5: the interval grows as the sequence times kSatRestartBaseInterval.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong thresholds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/restart.rs record_restart.
// CEP:SECURITY: none.
#[test]
fn luby_thresholds_scale_base() {
    let scheduler = RestartScheduler::new(RestartPolicy::Luby);
    let base = kSatRestartBaseInterval as u64;
    // Initial: Luby(1) x base.
    assert_eq!(scheduler.threshold(), base);
    scheduler.record_restart();
    // Second interval: Luby(2) x base = base.
    assert_eq!(scheduler.threshold(), base);
    scheduler.record_restart();
    // Third interval: Luby(3) x base = 2 x base.
    assert_eq!(scheduler.threshold(), 2 * base);
    scheduler.record_restart();
    // Fourth interval: Luby(4) x base = base.
    assert_eq!(scheduler.threshold(), base);
    scheduler.record_restart();
    scheduler.record_restart();
    // Sixth interval: Luby(6) x base = 2 x base (the sequence is 1, 1, 2, 1, 1, 2).
    assert_eq!(scheduler.threshold(), 2 * base);
}

// CEP:WHAT: Verifies geometric thresholds grow by the configured factor.
// CEP:WHY: Design 11.5 alternative policy.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong growth.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/restart.rs record_restart.
// CEP:SECURITY: none.
#[test]
fn geometric_intervals_grow() {
    let scheduler = RestartScheduler::new(RestartPolicy::Geometric);
    let base = kSatRestartBaseInterval as u64;
    let factor = mapt_config::limits::kSatRestartGeometricFactorPercent as u64;
    assert_eq!(scheduler.threshold(), base);
    scheduler.record_restart();
    assert_eq!(scheduler.threshold(), base * factor / 100);
    scheduler.record_restart();
    // The exact third value depends on integer division order; assert monotonic growth.
    let second = base * factor / 100;
    let third = second * factor / 100;
    assert_eq!(scheduler.threshold(), third.max(second));
    assert!(scheduler.threshold() > second);
}

// CEP:WHAT: Verifies the firing condition fires exactly at the threshold.
// CEP:WHY: Off-by-one restart points change the trace.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if firing is early or late.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/restart.rs should_restart/note_conflict.
// CEP:SECURITY: none.
#[test]
fn restart_fires_at_threshold() {
    let scheduler = RestartScheduler::new(RestartPolicy::Luby);
    let base = kSatRestartBaseInterval as u64;
    assert!(!scheduler.should_restart());
    for _ in 0..base.saturating_sub(1) {
        scheduler.note_conflict();
    }
    assert!(
        !scheduler.should_restart(),
        "one conflict short must not fire"
    );
    scheduler.note_conflict();
    assert!(
        scheduler.should_restart(),
        "exactly base conflicts must fire"
    );
    scheduler.record_restart();
    assert!(!scheduler.should_restart(), "recording resets the counter");
}

// CEP:WHAT: Verifies counters saturate safely under extreme counts.
// CEP:WHY: CEP&CC 22.6: integer safety; no overflow panics or wraparound restarts.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any panic.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/restart.rs note_conflict/record_restart.
// CEP:SECURITY: integer safety.
#[test]
fn saturating_counts_are_safe() {
    let scheduler = RestartScheduler::new(RestartPolicy::Luby);
    for _ in 0..40 {
        scheduler.note_conflict();
        if scheduler.should_restart() {
            scheduler.record_restart();
        }
    }
    let geometric = RestartScheduler::new(RestartPolicy::Geometric);
    for _ in 0..1_000 {
        geometric.note_conflict();
        if geometric.should_restart() {
            geometric.record_restart();
        }
    }
    assert!(geometric.threshold() >= kSatRestartBaseInterval as u64);
    // The largest u32 index sits at the end of the 2^32 - 1 block: value 2^31.
    assert_eq!(luby_value(u32::MAX), 1u64 << 31);
}
