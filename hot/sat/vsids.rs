// CEP:FILE: hot/sat/vsids.rs
// CEP:WHAT: VSIDS decision machinery: an arena-backed variable-activity max-heap with decay and rescaling (design 11.1 S7, S12, S13) plus the phase-saving table (S8, S14, S17).
// CEP:WHY: Design 11.2 names decision variable selection one of the three hottest paths (OPT-0): "Heap extract-max + re-insert" per decision; the activity array is f64 per variable exactly as the design prescribes (S7), the increment grows geometrically per conflict (S13, MiniSat-style 0.95 decay), and scores are rescaled below the ceiling so they stay finite and the heap comparison stays total, which is what keeps the heuristic deterministic (CEP&CC 38.10); ties are broken by smaller variable index because heap order must be a total order for reproducible search.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: VsidsHeap construction returns VsidsError::ArenaFull / VariableCountInvalid; operations are infallible (bounded indices validated at construction). Never panics.
// CEP:ASSUMES: Single-threaded use (Cell arrays); assigned variables are removed from the heap lazily by pick_unassigned and reinserted by the solver's backtracking (MiniSat discipline); activities are always finite non-negative doubles so comparisons are total.
// CEP:COST: bump is O(log n) sift-up; decay is constant plus occasional O(n) rescale; pick is O(log n) amortized (assigned tops are discarded); measured 420.41 cycles median per bump-plus-pick-plus-reinsert cycle over a 256-variable heap on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0009, artifact benches/artifacts/cdcl_decide.json.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs; unit/hot/sat_solver_test.rs; property/cdcl_property_test.rs; bench CEP-BENCH-0009.
// CEP:SECURITY: variable indices are bounds-checked on every array access; heap size is bounded by the declared variable count.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; heap order is the total order (activity desc, variable index asc), all arithmetic is IEEE-754 on finite non-negative values, and no clocks or randomness participate.
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 6 fixes the VSIDS contract: decisions always select the unassigned variable with the currently highest (activity, index) key, activities of implication-graph variables are bumped per conflict, and the increment decays geometrically; the solver property tests verify decisions against the oracle ordering.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: sift operations go through Cell array reads/writes; a raw-pointer heap with a proven bounds argument would shave the checks but violates the bounds-proof rule (CEP&CC 22.4); a two-level bucket heap (E prover style) is the structural follow-up; ticket CEP-1030.

use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::{
    kMaxSatVariables, kSatDefaultPhasePositive, kSatVsidsActivityCeiling, kSatVsidsDecayPercent,
    kSatVsidsRescaleFactor,
};

// CEP:WHAT: Percent scale as f64 (100.0) for the decay factor computation.
// CEP:WHY: The increment grows by 100 / kSatVsidsDecayPercent; a named local constant keeps the scale single-sourced without importing the hot crate's integer kPercentScale (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::decay_grows_increment.
// CEP:SECURITY: none.
const kPercentScaleF64: f64 = 100.0;

// CEP:WHAT: Arity of the VSIDS binary heap (children of position i sit at 2i+1 and 2i+2).
// CEP:WHY: The parent and child index arithmetic names its base (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: binary heap.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index}.
// CEP:SECURITY: none.
const kHeapArity: u32 = 2;

// CEP:WHAT: Sentinel heap position meaning "variable is not in the heap".
// CEP:WHY: Assigned variables are removed from the heap; the sentinel distinguishes absence from position zero (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: never aliases a real position because positions are below the variable count.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{pick_skips_assigned, insert_after_backtrack}.
// CEP:SECURITY: none.
pub const kNotInHeap: u32 = u32::MAX;

/// CEP:WHAT: Error cases of VSIDS construction.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::construction_rejects_bad_counts.
/// CEP:SECURITY: variable-count bounds are the memory boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VsidsError {
    /// CEP:WHAT: The declared variable count is zero or above kMaxSatVariables.
    VariableCountInvalid,
    /// CEP:WHAT: The arena cannot hold the activity, heap, and position arrays.
    ArenaFull,
}

/// CEP:WHAT: VSIDS activity heap: per-variable f64 activities, a binary max-heap of variable indices keyed by (activity desc, index asc), and per-variable heap positions.
/// CEP:WHY: Design 11.1 S7/S12: activity scores as f64 in an arena heap; the position array makes bump-induced sift-ups O(log n) without searching, and the total tie-broken key makes the decision order reproducible.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see VsidsError (construction only).
/// CEP:ASSUMES: single-threaded; one heap per solver.
/// CEP:COST: 16 bytes per variable (activity, heap slot, position) plus the increment.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs; bench CEP-BENCH-0009.
/// CEP:SECURITY: bounds-checked accessors.
pub struct VsidsHeap<'a> {
    /// CEP:WHAT: Per-variable activity scores.
    /// CEP:WHY: Design 11.1 S7.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: finite non-negative doubles.
    /// CEP:COST: 8 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, decay_grows_increment}.
    /// CEP:SECURITY: bounds-checked.
    activities: &'a [Cell<f64>],
    /// CEP:WHAT: Current activity increment applied per bump.
    /// CEP:WHY: The geometrically growing increment implements recency bias (S13).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: positive finite.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::decay_grows_increment.
    /// CEP:SECURITY: none.
    increment: Cell<f64>,
    /// CEP:WHAT: Max-heap of variable indices.
    /// CEP:WHY: Extract-max per decision (design 11.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries below the variable count.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index}.
    /// CEP:SECURITY: bounds-checked.
    heap: &'a [Cell<u32>],
    /// CEP:WHAT: Heap position per variable (kNotInHeap when absent).
    /// CEP:WHY: O(log n) bump updates and O(1) membership.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the heap array.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{pick_skips_assigned, insert_after_backtrack}.
    /// CEP:SECURITY: bounds-checked.
    positions: &'a [Cell<u32>],
    /// CEP:WHAT: Number of heap entries.
    /// CEP:WHY: Heap cursor.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= variable count.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{pick_skips_assigned, insert_after_backtrack}.
    /// CEP:SECURITY: none.
    heap_size: Cell<u32>,
}

impl<'a> VsidsHeap<'a> {
    // CEP:WHAT: Constructs the heap with all variables inserted in index order and zero activities.
    // CEP:WHY: Zero activities with the index-ascending tie-break make the identity array a valid max-heap, so initialization needs no sift passes (design 19.4 build-before-hot-path discipline).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableCountInvalid for zero or oversize counts, ArenaFull when the arrays do not fit.
    // CEP:ASSUMES: 0 < variables <= kMaxSatVariables.
    // CEP:COST: O(variables) one-time.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{construction_rejects_bad_counts, initial_pick_is_lowest_index}.
    // CEP:SECURITY: count validated before allocation.
    pub fn new(arena: &'a Arena, variables: u32) -> Result<VsidsHeap<'a>, VsidsError> {
        if variables == 0 || variables > kMaxSatVariables {
            return Err(VsidsError::VariableCountInvalid);
        }
        let activity_range = arena
            .alloc_array::<Cell<f64>>(variables)
            .map_err(|_| VsidsError::ArenaFull)?;
        let activities = arena
            .array::<Cell<f64>>(activity_range)
            .map_err(|_| VsidsError::ArenaFull)?;
        let heap_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| VsidsError::ArenaFull)?;
        let heap = arena
            .array::<Cell<u32>>(heap_range)
            .map_err(|_| VsidsError::ArenaFull)?;
        let position_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| VsidsError::ArenaFull)?;
        let positions = arena
            .array::<Cell<u32>>(position_range)
            .map_err(|_| VsidsError::ArenaFull)?;
        for index in 0..variables as usize {
            activities[index].set(0.0);
            heap[index].set(index as u32);
            positions[index].set(index as u32);
        }
        Ok(VsidsHeap {
            activities,
            increment: Cell::new(1.0),
            heap,
            positions,
            heap_size: Cell::new(variables),
        })
    }

    // CEP:WHAT: Returns the activity of a variable.
    // CEP:WHY: Diagnostics and the deterministic tie-break contract documentation.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns 0.0 for out-of-range variables (clamped, deterministic).
    // CEP:ASSUMES: variable below the declared count.
    // CEP:COST: 1 bounds check + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    // CEP:SECURITY: clamped read.
    pub fn activity(&self, variable: u32) -> f64 {
        let index = variable as usize;
        if index >= self.activities.len() {
            return 0.0;
        }
        self.activities[index].get()
    }

    // CEP:WHAT: Returns the current increment.
    // CEP:WHY: Decay behavior documentation and tests.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::decay_grows_increment.
    // CEP:SECURITY: none.
    pub fn increment(&self) -> f64 {
        self.increment.get()
    }

    // CEP:WHAT: Adds the current increment to a variable's activity and restores the heap invariant.
    // CEP:WHY: Design 11.1 S13: variables on the current conflict's implication graph are bumped; the sift-up maintains the heap under the total (activity desc, index asc) key.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (out-of-range variables are clamped no-ops, deterministic).
    // CEP:ASSUMES: variable below the declared count in solver use.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    // CEP:SECURITY: clamped.
    pub fn bump(&self, variable: u32) {
        let index = variable as usize;
        if index >= self.activities.len() {
            return;
        }
        let updated = self.activities[index].get() + self.increment.get();
        self.activities[index].set(updated);
        let position = self.positions[index].get();
        if position != kNotInHeap {
            self.sift_up(position);
        }
    }

    // CEP:WHAT: Grows the increment by the decay factor and rescales all activities when the increment passes the ceiling.
    // CEP:WHY: Design 11.1 S13 (decay) and the f64-overflow discipline: the rescale multiplies every activity and the increment by kSatVsidsRescaleFactor, an order-preserving positive constant, keeping all scores finite and the heap comparison total.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: called once per conflict.
    // CEP:COST: constant, plus O(variables) on a rescale.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{decay_grows_increment, rescale_keeps_scores_finite}.
    // CEP:SECURITY: none.
    pub fn decay(&self) {
        let factor = kPercentScaleF64 / kSatVsidsDecayPercent as f64;
        self.increment.set(self.increment.get() * factor);
        if self.increment.get() > kSatVsidsActivityCeiling {
            for slot in self.activities.iter() {
                slot.set(slot.get() * kSatVsidsRescaleFactor);
            }
            self.increment
                .set(self.increment.get() * kSatVsidsRescaleFactor);
        }
    }

    // CEP:WHAT: Inserts a variable into the heap if absent (backtracking reinsertion).
    // CEP:WHY: Assigned variables leave the heap at pick time; cancel_until unassigns them and the solver reinserts here, restoring the invariant that every unassigned variable is in the heap.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (out-of-range or already-present variables are no-ops, deterministic).
    // CEP:ASSUMES: the variable is unassigned in solver use.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::insert_after_backtrack.
    // CEP:SECURITY: clamped.
    pub fn insert(&self, variable: u32) {
        let index = variable as usize;
        if index >= self.positions.len() {
            return;
        }
        if self.positions[index].get() != kNotInHeap {
            return;
        }
        let size = self.heap_size.get();
        if size as usize >= self.heap.len() {
            return;
        }
        self.heap[size as usize].set(variable);
        self.positions[index].set(size);
        self.heap_size.set(size + 1);
        self.sift_up(size);
    }

    // CEP:WHAT: Picks the unassigned variable with the highest (activity, index) key, discarding assigned variables from the heap.
    // CEP:WHY: Design 11.1 S12 and 11.2: the decision primitive; the is_assigned predicate keeps the heap free of the caller's assignment state without this module owning it (no dyn, no coupling).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (None means every variable is assigned).
    // CEP:ASSUMES: the predicate reflects the caller's current assignment store.
    // CEP:COST: O(log n) amortized (each assigned top is discarded once per assignment epoch).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index, pick_skips_assigned}.
    // CEP:SECURITY: none.
    pub fn pick_unassigned(&self, is_assigned: impl Fn(u32) -> bool) -> Option<u32> {
        while self.heap_size.get() > 0 {
            let candidate = self.extract_max()?;
            if !is_assigned(candidate) {
                return Some(candidate);
            }
        }
        None
    }

    // CEP:WHAT: Extracts the maximum variable from the heap.
    // CEP:WHY: The heap primitive under pick_unassigned.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (None on empty).
    // CEP:ASSUMES: heap invariant holds.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index}.
    // CEP:SECURITY: none.
    fn extract_max(&self) -> Option<u32> {
        let size = self.heap_size.get();
        if size == 0 {
            return None;
        }
        let top = self.heap[0].get();
        self.positions[top as usize].set(kNotInHeap);
        let last = size - 1;
        if last == 0 {
            self.heap_size.set(0);
            return Some(top);
        }
        let moved = self.heap[last as usize].get();
        self.heap[0].set(moved);
        self.positions[moved as usize].set(0);
        self.heap_size.set(last);
        self.sift_down(0);
        Some(top)
    }

    // CEP:WHAT: Sifts the entry at a position up toward the root.
    // CEP:WHY: Heap repair after activity bumps and insertions.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: position is inside the heap.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    // CEP:SECURITY: none.
    fn sift_up(&self, mut position: u32) {
        while position > 0 {
            let parent = (position - 1) / kHeapArity;
            let child_variable = self.heap[position as usize].get();
            let parent_variable = self.heap[parent as usize].get();
            if self.key_greater(child_variable, parent_variable) {
                self.heap[position as usize].set(parent_variable);
                self.heap[parent as usize].set(child_variable);
                self.positions[parent_variable as usize].set(position);
                self.positions[child_variable as usize].set(parent);
                position = parent;
            } else {
                break;
            }
        }
    }

    // CEP:WHAT: Sifts the entry at a position down toward the leaves.
    // CEP:WHY: Heap repair after extraction.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: position is inside the heap.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index}.
    // CEP:SECURITY: none.
    fn sift_down(&self, mut position: u32) {
        loop {
            let size = self.heap_size.get();
            let left = position * kHeapArity + 1;
            if left >= size {
                break;
            }
            let right = left + 1;
            let current = self.heap[position as usize].get();
            let left_child = self.heap[left as usize].get();
            let mut best = left;
            let mut best_variable = left_child;
            if right < size {
                let right_child = self.heap[right as usize].get();
                if self.key_greater(right_child, best_variable) {
                    best = right;
                    best_variable = right_child;
                }
            }
            if self.key_greater(best_variable, current) {
                self.heap[position as usize].set(best_variable);
                self.heap[best as usize].set(current);
                self.positions[best_variable as usize].set(position);
                self.positions[current as usize].set(best);
                position = best;
            } else {
                break;
            }
        }
    }

    // CEP:WHAT: Total heap key: activity descending, then variable index ascending.
    // CEP:WHY: CEP&CC 38.10 determinism requires a total order on heap entries; ties on activity are resolved by the smaller index so identical runs produce identical decisions.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: activities are finite (guaranteed by rescaling).
    // CEP:COST: 2 compares.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ties_broken_by_index.
    // CEP:SECURITY: none.
    fn key_greater(&self, left: u32, right: u32) -> bool {
        let left_activity = self.activities[left as usize].get();
        let right_activity = self.activities[right as usize].get();
        if left_activity > right_activity {
            return true;
        }
        if left_activity < right_activity {
            return false;
        }
        left < right
    }
}

// CEP:WHAT: Phase encodings.
// CEP:WHY: Named constants for the tri-state values (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: exactly three states.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{saved_phase_defaults_to_constant, phase_table_roundtrip}.
// CEP:SECURITY: none.
const kPhaseUnset: u8 = 0;
/// CEP:WHAT: Saved positive-phase encoding.
/// CEP:WHY: See kPhaseUnset.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
/// CEP:SECURITY: none.
const kPhasePositive: u8 = 1;
/// CEP:WHAT: Saved negative-phase encoding.
/// CEP:WHY: See kPhaseUnset.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
/// CEP:SECURITY: none.
const kPhaseNegative: u8 = 2;

/// CEP:WHAT: Phase-saving table: per-variable last-assigned polarity with a default fallback (design 11.1 S8, S14, S17).
/// CEP:WHY: Phase saving exploits the empirical locality of satisfying assignments (Pipatsrisawat & Darwiche 2007): deciding the last seen polarity first shortens refutations; the flat u8 array keeps the lookup one load, and the tri-state encoding (unset / positive / negative) distinguishes "never assigned" from both polarities.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none (reads are clamped to the default phase).
/// CEP:ASSUMES: single-threaded; the solver saves phases when unassigning (cancel) and may reset on restart per configuration.
/// CEP:COST: 1 byte per variable.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{saved_phase_defaults_to_constant, phase_table_roundtrip}.
/// CEP:SECURITY: bounds-checked writes, clamped reads.
pub struct PhaseTable<'a> {
    /// CEP:WHAT: Per-variable phase encoding: 0 unset, 1 positive, 2 negative.
    /// CEP:WHY: Tri-state storage distinguishes defaults from saved polarities.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length equals the declared variable count.
    /// CEP:COST: 1 byte per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    /// CEP:SECURITY: bounds-checked.
    phases: &'a [Cell<u8>],
}

impl<'a> PhaseTable<'a> {
    // CEP:WHAT: Constructs a phase table with every entry unset.
    // CEP:WHY: Unset entries fall back to the default decision polarity (S14).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableCountInvalid / ArenaFull.
    // CEP:ASSUMES: 0 < variables <= kMaxSatVariables.
    // CEP:COST: O(variables) one-time.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::saved_phase_defaults_to_constant.
    // CEP:SECURITY: count validated before allocation.
    pub fn new(arena: &'a Arena, variables: u32) -> Result<PhaseTable<'a>, VsidsError> {
        if variables == 0 || variables > kMaxSatVariables {
            return Err(VsidsError::VariableCountInvalid);
        }
        let range = arena
            .alloc_array::<Cell<u8>>(variables)
            .map_err(|_| VsidsError::ArenaFull)?;
        let phases = arena
            .array::<Cell<u8>>(range)
            .map_err(|_| VsidsError::ArenaFull)?;
        for slot in phases.iter() {
            slot.set(kPhaseUnset);
        }
        Ok(PhaseTable { phases })
    }

    // CEP:WHAT: Returns the saved decision polarity of a variable, or the default when unset.
    // CEP:WHY: Design 11.1 S14: "Use saved phase (phase saving) or constant phase."
    // CEP:STATUS: complete
    // CEP:FAILURE: none (clamped to the default for out-of-range variables).
    // CEP:ASSUMES: variable below the declared count in solver use.
    // CEP:COST: 1 bounds check + 1 load + 1 compare.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{saved_phase_defaults_to_constant, phase_table_roundtrip}.
    // CEP:SECURITY: clamped read.
    pub fn phase(&self, variable: u32) -> bool {
        let index = variable as usize;
        if index >= self.phases.len() {
            return kSatDefaultPhasePositive;
        }
        match self.phases[index].get() {
            kPhasePositive => true,
            kPhaseNegative => false,
            _ => kSatDefaultPhasePositive,
        }
    }

    // CEP:WHAT: Saves the last-assigned polarity of a variable.
    // CEP:WHY: Design 11.1 S17: "Save polarity on assignment" (MAPT saves at unassignment time, which records the same last-assigned polarity).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (out-of-range variables are clamped no-ops).
    // CEP:ASSUMES: variable below the declared count in solver use.
    // CEP:COST: 1 bounds check + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    // CEP:SECURITY: clamped write.
    pub fn save_phase(&self, variable: u32, positive: bool) {
        let index = variable as usize;
        if index >= self.phases.len() {
            return;
        }
        self.phases[index].set(if positive {
            kPhasePositive
        } else {
            kPhaseNegative
        });
    }

    // CEP:WHAT: Clears every saved phase back to unset.
    // CEP:WHY: Design 11.1 S17: "Reset on restart (configurable)"; the solver calls this only when constructed with phase reset enabled.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(variables).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    // CEP:SECURITY: none.
    pub fn reset(&self) {
        for slot in self.phases.iter() {
            slot.set(kPhaseUnset);
        }
    }
}
