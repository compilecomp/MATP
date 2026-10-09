// CEP:FILE: hot/sat/restart.rs
// CEP:WHAT: Restart scheduling: the canonical Luby sequence (Luby, Sinclair & Zuckerman 1993) scaled by the base interval, with the geometric alternative, tracked as pure arithmetic state with no arrays.
// CEP:WHY: Design 11.5 fixes the restart contract: "MAPT uses the Luby sequence ... by default. The restart interval grows as 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ... The base interval is a named constant (kSatRestartBaseInterval). ... Geometric restarts are available as an alternative"; restarts bound the cost of bad search branches and the scheduler must be deterministic (CEP&CC 38.10) because restart points change the proof trace.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: All operations are infallible (saturating arithmetic, no allocation, no indexing); the scheduler never panics.
// CEP:ASSUMES: One scheduler per solver; note_conflict is called once per analyzed conflict; record_restart exactly when a restart is performed.
// CEP:COST: constant-time queries and updates; the Luby value computation is O(log index) at restart time only.
// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_sequence_matches_design, luby_thresholds_scale_base, geometric_intervals_grow, restart_fires_at_threshold, saturating_counts_are_safe}.
// CEP:SECURITY: none; no untrusted input reaches the scheduler.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the sequence is a pure function of the restart count and all arithmetic is saturating integer math.
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 7 fixes the restart contract: the k-th restart occurs after Luby(k+1) x kSatRestartBaseInterval conflicts (geometric: base x factor^k), the sequence grows without bound so restarts cannot livelock the search, and the unit test pins the first sixteen Luby values to the design's literal sequence.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: the scheduler is a counter compare per conflict and an O(log k) Luby recomputation per restart; no cheaper deterministic schedule state exists.

use mapt_config::limits::{kSatRestartBaseInterval, kSatRestartGeometricFactorPercent};

// CEP:WHAT: Percent scale for the geometric growth division.
// CEP:WHY: The threshold grows by factor/100; the scale is named once (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::geometric_intervals_grow.
// CEP:SECURITY: none.
const kPercentScale: u64 = 100;

// CEP:WHAT: Luby block growth base: the block size sequence is 1, 3, 7, ... (2*size + 1).
// CEP:WHY: Named constants for the block arithmetic (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::luby_sequence_matches_design.
// CEP:SECURITY: none.
const kLubyBlockBase: u64 = 2;
/// CEP:WHAT: Sequence-index offset converting the stored restart count to the next Luby interval (count + 2).
/// CEP:WHY: Named offset instead of an inline 2 (CEP&CC 11.3); Spec 06 section 7 fixes the indexing.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 1-based Luby indexing.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::luby_thresholds_scale_base.
/// CEP:SECURITY: none.
const kFirstLubyIndex: u32 = 2;
/// CEP:WHAT: Halving divisor of the Luby block size during descent.
/// CEP:WHY: See kLubyBlockBase.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::luby_sequence_matches_design.
/// CEP:SECURITY: none.
const kLubyBlockDivisor: u64 = 2;
/// CEP:WHAT: Bit width of u64; Luby values are powers of two up to this shift width.
/// CEP:WHY: The shift bound prevents shift-overflow on extreme indices (CEP&CC 22.6).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: u64 is 64 bits (pinned by the target ABI).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::saturating_counts_are_safe.
/// CEP:SECURITY: integer safety.
const kU64ShiftWidth: u32 = 64;

/// CEP:WHAT: Available restart policies (design 11.5).
/// CEP:WHY: Luby is the default and geometric the documented alternative; a closed enum forbids arbitrary schedules (CEP&CC Law 5 vocabulary discipline).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: exactly two policies in Phase 2.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RestartPolicy {
    /// CEP:WHAT: Canonical Luby sequence scaled by the base interval (default).
    /// CEP:WHY: Design 11.5 default.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::luby_sequence_matches_design.
    /// CEP:SECURITY: none.
    Luby,
    /// CEP:WHAT: Geometric growth by kSatRestartGeometricFactorPercent per restart.
    /// CEP:WHY: Design 11.5 alternative.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::geometric_intervals_grow.
    /// CEP:SECURITY: none.
    Geometric,
}

/// CEP:WHAT: Restart scheduler: policy, conflict counter, and the current conflict threshold for the next restart.
/// CEP:WHY: Design 11.1 S16; the state is three scalars so construction needs no arena and the scheduler stays the cheapest per-conflict bookkeeping in the solver.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none (saturating arithmetic everywhere; thresholds stop growing at u64 saturation).
/// CEP:ASSUMES: driven by the solver loop once per conflict and once per restart.
/// CEP:COST: 1 compare per conflict, O(log k) per restart.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs; unit/hot/sat_solver_test.rs::{restart_returns_to_level_zero, restart_preserves_learnts}.
/// CEP:SECURITY: none.
pub struct RestartScheduler {
    /// CEP:WHAT: Configured policy.
    /// CEP:WHY: Selects the threshold sequence.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow}.
    /// CEP:SECURITY: none.
    policy: RestartPolicy,
    /// CEP:WHAT: Conflicts since the last restart.
    /// CEP:WHY: The firing condition compares this against the threshold.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (saturating increment).
    /// CEP:ASSUMES: monotonic between restarts.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::restart_fires_at_threshold.
    /// CEP:SECURITY: none.
    conflicts_since_restart: core::cell::Cell<u64>,
    /// CEP:WHAT: Number of restarts performed (the sequence index minus one).
    /// CEP:WHY: Selects the next Luby value or geometric factor exponent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (saturating increment).
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow}.
    /// CEP:SECURITY: none.
    restarts_done: core::cell::Cell<u32>,
    /// CEP:WHAT: Conflict threshold for the next restart.
    /// CEP:WHY: Precomputed so the per-conflict check is one compare.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (saturating updates).
    /// CEP:ASSUMES: grows without bound until saturation.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{restart_fires_at_threshold, saturating_counts_are_safe}.
    /// CEP:SECURITY: none.
    threshold: core::cell::Cell<u64>,
}

impl RestartScheduler {
    // CEP:WHAT: Constructs a scheduler with the first threshold of its policy.
    // CEP:WHY: The first Luby interval is 1 x base and the first geometric interval is base, so both policies share the same initial threshold (design 11.5).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: kSatRestartBaseInterval >= 1 (statically asserted in config).
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow}.
    // CEP:SECURITY: none.
    pub fn new(policy: RestartPolicy) -> RestartScheduler {
        let base = kSatRestartBaseInterval as u64;
        RestartScheduler {
            policy,
            conflicts_since_restart: core::cell::Cell::new(0),
            restarts_done: core::cell::Cell::new(0),
            threshold: core::cell::Cell::new(base),
        }
    }

    // CEP:WHAT: Returns the configured policy.
    // CEP:WHY: Diagnostics and solver construction cross-checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs.
    // CEP:SECURITY: none.
    pub fn policy(&self) -> RestartPolicy {
        self.policy
    }

    // CEP:WHAT: Returns the current conflict threshold.
    // CEP:WHY: Test introspection of the schedule.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow}.
    // CEP:SECURITY: none.
    pub fn threshold(&self) -> u64 {
        self.threshold.get()
    }

    // CEP:WHAT: Records one analyzed conflict.
    // CEP:WHY: The solver calls this once per conflict so the firing condition stays a pure compare.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (saturating).
    // CEP:ASSUMES: called at most once per conflict.
    // CEP:COST: 1 add.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs::restart_fires_at_threshold.
    // CEP:SECURITY: none.
    pub fn note_conflict(&self) {
        let next = self.conflicts_since_restart.get().saturating_add(1);
        self.conflicts_since_restart.set(next);
    }

    // CEP:WHAT: Returns true when the restart condition is met.
    // CEP:WHY: The per-conflict firing test (design 11.1 S16).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the solver acts on true immediately.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs::restart_fires_at_threshold.
    // CEP:SECURITY: none.
    pub fn should_restart(&self) -> bool {
        self.conflicts_since_restart.get() >= self.threshold.get()
    }

    // CEP:WHAT: Advances the schedule after a performed restart.
    // CEP:WHY: Design 11.5: the interval sequence advances (Luby index or geometric factor) and the conflict counter resets; saturating arithmetic keeps the threshold finite forever.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: called exactly once per restart.
    // CEP:COST: O(log k) for the Luby recomputation.
    // CEP:EVIDENCE: unit/hot/sat_restart_test.rs::{luby_thresholds_scale_base, geometric_intervals_grow, saturating_counts_are_safe}.
    // CEP:SECURITY: none.
    pub fn record_restart(&self) {
        let done = self.restarts_done.get();
        self.conflicts_since_restart.set(0);
        self.restarts_done.set(done.saturating_add(1));
        let next_threshold = match self.policy {
            RestartPolicy::Luby => {
                // Interval for the upcoming restart number (done + 1, 0-based) is
                // Luby(done + 2) x base (Spec 06 section 7); the +2 converts the stored
                // count to the 1-based sequence index of the NEXT interval.
                let index = done.saturating_add(kFirstLubyIndex);
                luby_value(index).saturating_mul(kSatRestartBaseInterval as u64)
            }
            RestartPolicy::Geometric => {
                let factor = kSatRestartGeometricFactorPercent as u64;
                let grown = self
                    .threshold
                    .get()
                    .saturating_mul(factor)
                    .checked_div(kPercentScale)
                    .unwrap_or(u64::MAX);
                grown.max(self.threshold.get())
            }
        };
        self.threshold.set(next_threshold);
    }

    // CEP:WHAT: Returns the number of restarts performed.
    // CEP:WHY: Diagnostics and solver tests.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_solver_test.rs::restart_returns_to_level_zero.
    // CEP:SECURITY: none.
    pub fn restarts_done(&self) -> u32 {
        self.restarts_done.get()
    }
}

// CEP:WHAT: Computes the canonical Luby sequence value at a 1-based index: 1, 1, 2, 1, 1, 2, 4, 1, ...
// CEP:WHY: Design 11.5 pins this exact sequence; the iterative block-finding formulation (Luby, Sinclair & Zuckerman 1993, standard SAT-solver presentation) avoids recursion and floating point so the schedule is integer-deterministic.
// CEP:STATUS: complete
// CEP:FAILURE: none (index 0 is treated as index 1, documented; values saturate at the u64 shift bound).
// CEP:ASSUMES: index >= 1 in intended use.
// CEP:COST: O(log index).
// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::luby_sequence_matches_design.
// CEP:SECURITY: none.
pub fn luby_value(index: u32) -> u64 {
    if index == 0 {
        return 1;
    }
    // Zero-based position inside the sequence.
    let mut position: u64 = index as u64 - 1;
    let mut size: u64 = 1;
    let mut sequence: u32 = 0;
    while size < position + 1 {
        size = kLubyBlockBase * size + 1;
        sequence += 1;
    }
    while size - 1 != position {
        size = (size - 1) / kLubyBlockDivisor;
        if sequence == 0 {
            return 1;
        }
        sequence -= 1;
        position %= size;
    }
    if sequence >= kU64ShiftWidth {
        return u64::MAX;
    }
    1u64 << sequence
}
