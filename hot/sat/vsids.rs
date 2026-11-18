// CEP:FILE: hot/sat/vsids.rs
// CEP:WHAT: VSIDS decision machinery: a two-level bucket heap over a static geometric activity ladder with a sparse band-node pool (design 11.1 S7, S12, S13; ticket CEP-1030) plus the phase-saving table (S8, S14, S17).
// CEP:WHY: Design 11.2 names decision variable selection one of the three hottest paths (OPT-0). The binary heap this module previously shipped sifts on every bump and reinsertion; the two-level structure (E-prover TBucket style) replaces sift trees with bucket lists: level 1 is a STATIC ladder of activity bands derived by pure bit inspection of the f64 score (biased exponent selects the band, the top mantissa bits the sub-band - the map is strictly monotone, so band order is score order; band 0 is the bottom band of zero scores), level 2 is a per-band doubly-linked member list kept sorted by the exact normative key (activity desc, variable index asc). The per-band bookkeeping lives in a sparse pool of band nodes (id, head, tail, length, occupied-list links) sized by the variable count and kept in one occupied-band linked list sorted by descending band id: the decision pick reads the head node's chain tail in O(1) - the head node is the highest non-empty band, so its minimum-index member is the normative maximum - and no cursor array or per-band array of ladder-span size exists (the fixed 269 KiB per heap of the first cut starved arena-sharing callers that build many small spaces; the pool scales with the variable count instead). Unlink is O(1) via the per-variable prev/next arrays; bump relinks into the new band with a walk over that band's members in index-adjacent memory order; the backtracking wave is sorted once and merged per band. The normative decision order of Spec 06 section 6 is preserved exactly: bands partition the positive scores into disjoint ascending ranges, so the global maximum is the first occupied band's minimum-index member, and within a band the exact (activity, index) key orders the list. The rescale multiplies every score by an order-preserving constant and rebuilds the occupied list by run splitting with no sort (positive bands re-chained in descending source order, which is the key order; scores flushed to exactly zero are re-chained in index order, matching the tie-break). No clocks, no randomness; every operation is a pure function of the operation history (CEP&CC 38.10).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: VsidsHeap construction returns VsidsError::ArenaFull / VariableCountInvalid; operations are infallible (bounded indices validated at construction and clamped on access; the band pool is sized by the variable count and the occupied-node count is bounded by the member count, so pool exhaustion is unreachable - if it were reached anyway, the affected variable stays unlinked and the search misses that decision, a documented incompleteness that never misapplies an inference). Never panics.
// CEP:ASSUMES: Single-threaded use (Cell arrays); assigned variables are unlinked from their band by pick_unassigned and relinked by the solver's backtracking wave (MiniSat discipline); activities are finite non-negative doubles (the rescale keeps them below the ceiling), so the key comparison is total; scores are never negative and never subnormal (increments start at 1.0 and only grow), so the ladder's bottom band covers every non-positive score.
// CEP:COST: 24 bytes per variable (activity, band slot, prev, next, wave slot) plus a 24-byte band node per pool slot with 2 x variables slots (the occupied count is bounded by the member count, and the rescale's transient overlap of old and new nodes is bounded by the same argument with free-as-processed reclamation); bump is O(1) unlink plus an O(b) walk over the destination band's members (b = band occupancy; the walk reads the activities array in variable-index order, which is contiguous) after an O(o) descent of the occupied-node list from its head (bumped variables rise, so the destination is near the head); pick is O(1); decay is O(1) plus the rare rescale at O(variables + occupied-node list work) with no sort; the backtracking wave is one heapsort of the wave plus one merge walk per touched band, O(W log W + sum of band sizes) replacing W binary-heap sift-ups of O(W log variables). Worst cases are documented: a bump into a band holding b members walks O(b); the zero band can hold every variable, so waves that reinsert never-bumped variables walk it once per wave. Replaces the previous per-operation O(log variables) sift pair (bench CEP-BENCH-0009 measured the binary heap; re-measurement of this structure is pending, see doc/tickets.md CEP-1030).
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs (including the differential oracle fuzz tests ladder_matches_oracle_under_fuzz and wave_insert_matches_oracle); unit/hot/sat_solver_test.rs; property/cdcl_property_test.rs.
// CEP:SECURITY: variable indices are bounds-checked on every array access; band and wave storage are bounded by the declared variable count.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the decision order is the total order (activity desc, variable index asc), band computation is pure bit arithmetic on IEEE-754 doubles, heapsorts run over deterministic inputs, and no clocks or randomness participate.
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 6 fixes the VSIDS contract: decisions always select the unassigned variable with the currently highest (activity, index) key, activities of implication-graph variables are bumped per conflict, and the increment decays geometrically; the two-level structure implements the same contract (the Spec 06 amendment delivered with CEP-1030 records the structure and its invariants). The solver property tests verify decisions against the oracle ordering.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: the band walk is O(band occupancy) where the binary heap paid O(log variables); in the collision-heavy regime (many variables share a score band) the walk beats the sift's scattered heap/position accesses, in the spread regime it can lose, and the occupied-node descent is O(occupied bands) per new band. Per-band sorted arrays would binary-search the insertion point but reintroduce the packed-partition shift problem; a fat-node or skip-list band remains future work. Raw-pointer variants that shave the bounds checks are barred by the bounds-proof rule (CEP&CC 22.4).

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

/// CEP:WHAT: Sentinel meaning "no node" in the occupied-band list and the free list, and "end of chain" in the per-variable links.
/// CEP:WHY: One sentinel serves the three list roles because real node slots and variable indices never approach u32::MAX (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: node slots and variable indices are below kMaxSatVariables * 2.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{pick_skips_assigned, insert_after_backtrack}.
/// CEP:SECURITY: none.
pub const kNotInHeap: u32 = u32::MAX;

// CEP:WHAT: Sentinel band-slot value marking a variable collected into the current wave but not yet linked.
// CEP:WHY: insert_wave_iter must reject a variable collected twice into one wave (the trail yields unique variables, but the API is public); the pending marker is distinguishable from both 0 (unlinked) and real slots.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kWavePending never aliases a real slot+1 value.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle (duplicate entries are exercised).
// CEP:SECURITY: none.
const kWavePending: u32 = u32::MAX;

// CEP:WHAT: Sentinel node-band value marking a freed band node.
// CEP:WHY: The rescale walks a captured chain of node slots; a slot may have been freed and reused by a new band node, and the dead marker lets the walk skip it (freed nodes carry no members, so re-processing would at worst be a no-op, but skipping keeps the accounting exact).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: real band ids are below kVsidsBandIdBound, far below u32::MAX.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ladder_matches_oracle_under_fuzz (rescale bursts mid-fuzz).
// CEP:SECURITY: none.
const kDeadBand: u32 = u32::MAX;

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
    /// CEP:WHAT: The arena cannot hold the activity, band-slot, link, wave, and node-pool arrays.
    ArenaFull,
}

/// CEP:WHAT: VSIDS two-level bucket heap: per-variable f64 activities, the static band ladder evaluated by bit inspection, per-variable band membership with doubly-linked list pointers, and a sparse pool of band nodes threaded into one occupied-band list sorted by descending band id, keyed by the total order (activity desc, variable index asc).
/// CEP:WHY: Design 11.1 S7/S12 and ticket CEP-1030: decision selection must return the highest (activity, index) key; the ladder makes band lookup bit-arithmetic, the per-band lists make unlink O(1) and pick O(1), and the sparse node pool keeps the per-heap footprint proportional to the variable count instead of the ladder span.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see VsidsError (construction only).
/// CEP:ASSUMES: single-threaded; one heap per solver.
/// CEP:COST: 24 bytes per variable plus a 24-byte node per pool slot with two slots per variable (see the file CEP:COST).
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs; property/cdcl_property_test.rs.
/// CEP:SECURITY: bounds-checked accessors.
pub struct VsidsHeap<'a> {
    /// CEP:WHAT: Per-variable activity scores.
    /// CEP:WHY: Design 11.1 S7: activity scores as f64.
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
    /// CEP:WHAT: Band-node pool slot per variable, stored as slot + 1; 0 = unlinked (picked or never linked), kWavePending = collected into the current wave.
    /// CEP:WHY: O(1) band-node lookup on unlink and the membership flag in one array.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the pool and the lists.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::pick_skips_assigned.
    /// CEP:SECURITY: bounds-checked.
    band_slot: &'a [Cell<u32>],
    /// CEP:WHAT: Previous variable in the band chain (kNotInHeap = chain head).
    /// CEP:WHY: The doubly-linked chain makes unlink O(1) without scanning.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with next and the node heads.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::insert_after_backtrack.
    /// CEP:SECURITY: bounds-checked.
    prev: &'a [Cell<u32>],
    /// CEP:WHAT: Next variable in the band chain (kNotInHeap = chain tail).
    /// CEP:WHY: O(1) unlink and O(1) chain-tail pick.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with prev and the node tails.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::insert_after_backtrack.
    /// CEP:SECURITY: bounds-checked.
    next: &'a [Cell<u32>],
    /// CEP:WHAT: Wave buffer (one u32 per variable) used by insert_wave_iter.
    /// CEP:WHY: The backtracking wave is sorted once and merged per band, replacing per-variable walks.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length equals the declared variable count (a wave never exceeds it).
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle.
    /// CEP:SECURITY: bounds-checked.
    scratch: &'a [Cell<u32>],
    /// CEP:WHAT: Band id of each pool node (kDeadBand when the node is free).
    /// CEP:WHY: The occupied list is ordered by band id and the pick walks its head.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one node per occupied band.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    /// CEP:SECURITY: bounds-checked.
    node_band: &'a [Cell<u32>],
    /// CEP:WHAT: First variable of each node's band chain (carries the band's maximum key).
    /// CEP:WHY: New members and the merge walk read the chain head.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the chains.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::initial_pick_is_lowest_index.
    /// CEP:SECURITY: bounds-checked.
    node_head: &'a [Cell<u32>],
    /// CEP:WHAT: Last variable of each node's band chain (carries the band's minimum key).
    /// CEP:WHY: The pick pops the chain tail in O(1) (the chain stores indices descending, so the tail is the smallest index).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the chains.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::initial_pick_is_lowest_index.
    /// CEP:SECURITY: bounds-checked.
    node_tail: &'a [Cell<u32>],
    /// CEP:WHAT: Member count of each node's band chain.
    /// CEP:WHY: Empty nodes are freed immediately, keeping the occupied count bounded by the member count.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: equals the chain length.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::pick_skips_assigned.
    /// CEP:SECURITY: bounds-checked.
    node_len: &'a [Cell<u32>],
    /// CEP:WHAT: Occupied-list previous node of each pool node (kNotInHeap = list head).
    /// CEP:WHY: O(1) node removal when a band empties.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the occupied list.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: cited by unlink (exercised by pick_skips_assigned).
    /// CEP:SECURITY: bounds-checked.
    node_prev: &'a [Cell<u32>],
    /// CEP:WHAT: Occupied-list next node of each pool node, doubling as the free-list link for freed nodes.
    /// CEP:WHY: One link field serves both roles because a freed node is in exactly one of the two lists.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent with the occupied list or the free list.
    /// CEP:COST: 4 bytes per pool slot.
    /// CEP:EVIDENCE: cited by unlink and rescale_buckets.
    /// CEP:SECURITY: bounds-checked.
    node_next: &'a [Cell<u32>],
    /// CEP:WHAT: Head of the occupied-band list (the highest non-empty band).
    /// CEP:WHY: The pick reads its chain tail; the list replaces any cursor array.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: nodes are sorted by descending band id.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    /// CEP:SECURITY: none.
    list_head: Cell<u32>,
    /// CEP:WHAT: Head of the temporary band-node list used only inside the rescale.
    /// CEP:WHY: New band nodes created during the rescale must stay out of the occupied list that the rescale's captured-chain walk traverses - a node spliced into the walked list could be revisited and self-splice, losing its members. The temporary list is threaded through node_next and merged back after the walk.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: always kNotInHeap outside rescale_bands.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ladder_matches_oracle_under_fuzz (rescale bursts mid-fuzz).
    /// CEP:SECURITY: none.
    rescale_temp: Cell<u32>,
    /// CEP:WHAT: Head of the band-node free list.
    /// CEP:WHY: Node allocation and reclamation are O(1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: threaded through node_next.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: cited by unlink and find_or_create_node.
    /// CEP:SECURITY: none.
    node_free: Cell<u32>,
}

impl<'a> VsidsHeap<'a> {
    /// CEP:WHAT: Constructs the heap with all variables linked into the bottom band (band 0) in index order and zero activities.
    /// CEP:WHY: Zero activities tie under the total key, so the index-ordered chain is the sorted order and construction needs no comparisons (design 19.4 build-before-hot-path discipline); the single occupied node is the whole list.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns VariableCountInvalid for zero or oversize counts, ArenaFull when the arrays do not fit.
    /// CEP:ASSUMES: 0 < variables <= kMaxSatVariables.
    /// CEP:COST: O(variables) one-time.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{construction_rejects_bad_counts, initial_pick_is_lowest_index}.
    /// CEP:SECURITY: count validated before allocation.
    pub fn new(arena: &'a Arena, variables: u32) -> Result<VsidsHeap<'a>, VsidsError> {
        if variables == 0 || variables > kMaxSatVariables {
            return Err(VsidsError::VariableCountInvalid);
        }
        let slots = variables * 2;
        let activity_range = arena
            .alloc_array::<Cell<f64>>(variables)
            .map_err(|_| VsidsError::ArenaFull)?;
        let activities = arena
            .array::<Cell<f64>>(activity_range)
            .map_err(|_| VsidsError::ArenaFull)?;
        let band_slot = Self::alloc_u32(arena, variables)?;
        let prev = Self::alloc_u32(arena, variables)?;
        let next = Self::alloc_u32(arena, variables)?;
        let scratch = Self::alloc_u32(arena, variables)?;
        let node_band = Self::alloc_u32(arena, slots)?;
        let node_head = Self::alloc_u32(arena, slots)?;
        let node_tail = Self::alloc_u32(arena, slots)?;
        let node_len = Self::alloc_u32(arena, slots)?;
        let node_prev = Self::alloc_u32(arena, slots)?;
        let node_next = Self::alloc_u32(arena, slots)?;
        // Free list: all slots threaded in ascending order; slot 0 is taken for band 0 below.
        for index in 0..slots as usize {
            node_band[index].set(kDeadBand);
            node_next[index].set(if index + 1 < slots as usize {
                (index + 1) as u32
            } else {
                kNotInHeap
            });
            node_head[index].set(kNotInHeap);
            node_tail[index].set(kNotInHeap);
            node_len[index].set(0);
            node_prev[index].set(kNotInHeap);
        }
        node_band[0].set(0);
        node_head[0].set(0);
        node_tail[0].set(variables - 1);
        node_len[0].set(variables);
        node_prev[0].set(kNotInHeap);
        node_next[0].set(kNotInHeap);
        for index in 0..variables as usize {
            activities[index].set(0.0);
            band_slot[index].set(1);
            // Index-ascending chain through band 0: next grows, prev shrinks.
            next[index].set(if index + 1 < variables as usize {
                (index + 1) as u32
            } else {
                kNotInHeap
            });
            prev[index].set(if index > 0 {
                (index - 1) as u32
            } else {
                kNotInHeap
            });
        }
        Ok(VsidsHeap {
            activities,
            increment: Cell::new(1.0),
            band_slot,
            prev,
            next,
            scratch,
            node_band,
            node_head,
            node_tail,
            node_len,
            node_prev,
            node_next,
            list_head: Cell::new(0),
            rescale_temp: Cell::new(kNotInHeap),
            node_free: Cell::new(1),
        })
    }

    /// CEP:WHAT: Returns the activity of a variable.
    /// CEP:WHY: Diagnostics and the deterministic tie-break contract documentation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: returns 0.0 for out-of-range variables (clamped, deterministic).
    /// CEP:ASSUMES: variable below the declared count.
    /// CEP:COST: 1 bounds check + 1 load.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    /// CEP:SECURITY: clamped read.
    pub fn activity(&self, variable: u32) -> f64 {
        let index = variable as usize;
        if index >= self.activities.len() {
            return 0.0;
        }
        self.activities[index].get()
    }

    /// CEP:WHAT: Returns the current increment.
    /// CEP:WHY: Decay behavior documentation and tests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::decay_grows_increment.
    /// CEP:SECURITY: none.
    pub fn increment(&self) -> f64 {
        self.increment.get()
    }

    /// CEP:WHAT: Adds the current increment to a variable's activity and re-bands it.
    /// CEP:WHY: Design 11.1 S13: variables on the current conflict's implication graph are bumped; an in-band variable is unlinked in O(1) and relinked into its new band by one walk. The ladder is strictly monotone, so the new band is at or above the old one and the occupied-node descent is short.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (out-of-range variables are clamped no-ops, deterministic).
    /// CEP:ASSUMES: variable below the declared count in solver use.
    /// CEP:COST: O(1) unlink + O(occupied-list descent) + O(b) band walk (b = destination band occupancy).
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    /// CEP:SECURITY: clamped.
    pub fn bump(&self, variable: u32) {
        let index = variable as usize;
        if index >= self.activities.len() {
            return;
        }
        let updated = self.activities[index].get() + self.increment.get();
        self.activities[index].set(updated);
        if self.band_slot[index].get() != 0 && self.band_slot[index].get() != kWavePending {
            self.unlink(variable);
            self.link(variable, Self::level_of_activity(updated));
        }
    }

    /// CEP:WHAT: Grows the increment by the decay factor and rescales all activities when the increment passes the ceiling.
    /// CEP:WHY: Design 11.1 S13 (decay) and the f64-overflow discipline: the rescale multiplies every activity and the increment by kSatVsidsRescaleFactor, an order-preserving positive constant, keeping all scores finite and the key comparison total. Every product below the smallest normal is flushed to exactly zero, so the stored scores satisfy "band 0 means 0.0" as an invariant of the values themselves.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called once per conflict; the increment never enters the subnormal range (the rescale returns it to the normal scale).
    /// CEP:COST: O(1), plus the rare rescale at O(variables) plus occupied-list work with no sort (positive bands are rebuilt by run splitting; flushed zero scores are re-chained in index order).
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{decay_grows_increment, rescale_keeps_scores_finite, underflow_flush_ties_by_index}.
    /// CEP:SECURITY: none.
    pub fn decay(&self) {
        let factor = kPercentScaleF64 / kSatVsidsDecayPercent as f64;
        self.increment.set(self.increment.get() * factor);
        if self.increment.get() > kSatVsidsActivityCeiling {
            // Flush, not round: a product in the subnormal range is nonzero but maps to
            // band 0 (biased exponent 0), and the bottom-band rebuild orders band 0 by
            // index, which is the key order only for exact zeros. Clamping subnormal
            // products to 0.0 here keeps the flush semantics the ladder is designed
            // around - a score below the ladder is exactly zero (design 11.1 S13 note).
            for slot in self.activities.iter() {
                let scaled = slot.get() * kSatVsidsRescaleFactor;
                slot.set(if scaled < f64::MIN_POSITIVE {
                    0.0
                } else {
                    scaled
                });
            }
            self.increment
                .set(self.increment.get() * kSatVsidsRescaleFactor);
            self.rescale_bands();
        }
    }

    /// CEP:WHAT: Inserts a variable into its activity's band if absent (backtracking reinsertion, single-variable form).
    /// CEP:WHY: Assigned variables leave the structure at pick time; cancel_until unassigns them and the solver relinks them (the batched form insert_wave_iter is the hot path). Double insert is a no-op.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (out-of-range or already-present variables are no-ops, deterministic).
    /// CEP:ASSUMES: the variable is unassigned in solver use.
    /// CEP:COST: O(occupied-list descent) + O(b) band walk.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::insert_after_backtrack.
    /// CEP:SECURITY: clamped.
    pub fn insert(&self, variable: u32) {
        let index = variable as usize;
        if index >= self.band_slot.len() {
            return;
        }
        let state = self.band_slot[index].get();
        if state != 0 {
            return;
        }
        let band = Self::level_of_activity(self.activities[index].get());
        self.link(variable, band);
    }

    /// CEP:WHAT: Inserts a batch of variables (the backtracking wave), sorted once and merged one walk per touched band.
    /// CEP:WHY: cancel_until unassigns a whole trail segment; merging the sorted wave into each band's sorted list costs O(W log W + band sizes) instead of W independent O(b) walks. Out-of-range, already-present, and duplicate variables are dropped deterministically.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (an empty wave is a no-op).
    /// CEP:ASSUMES: the iterator yields each variable at most once per call for meaningful dedup (duplicates are still handled by the pending marker).
    /// CEP:COST: O(W log W) heapsort over the wave + O(band size) merge per touched band.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle; hot/sat/solver.rs backtrack.
    /// CEP:SECURITY: bounds-checked collection into the wave buffer.
    pub fn insert_wave_iter(&self, variables: impl Iterator<Item = u32>) {
        // CEP:WHAT: Collect the wave into the scratch buffer with duplicate rejection.
        // CEP:WHY: The pending marker in band_slot makes a repeated yield visible; the buffer is exactly variable-count sized, so the wave always fits.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: O(W).
        // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle.
        // CEP:SECURITY: bounds-checked.
        let mut count: usize = 0;
        for variable in variables {
            let index = variable as usize;
            if index >= self.band_slot.len() {
                continue;
            }
            if self.band_slot[index].get() != 0 {
                continue;
            }
            self.band_slot[index].set(kWavePending);
            self.scratch[count].set(variable);
            count += 1;
        }
        if count == 0 {
            return;
        }
        Self::heapsort_ascending_by_key(&self.scratch[..count], self.activities);
        // CEP:WHAT: Merge the sorted wave into the touched bands, one descending run per band.
        // CEP:WHY: The ascending sort groups equal-band members contiguously (the ladder is monotone in the score); walking each group backward yields the band's descending key order, which merges with the band chain in one pass.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: level_of_activity is monotone (band order follows score order).
        // CEP:COST: O(W) grouping + O(band size) per touched band.
        // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle.
        // CEP:SECURITY: none.
        let mut group_start = 0usize;
        while group_start < count {
            let band = Self::level_of_activity(
                self.activities[self.scratch[group_start].get() as usize].get(),
            );
            let mut group_end = group_start;
            while group_end < count
                && Self::level_of_activity(
                    self.activities[self.scratch[group_end].get() as usize].get(),
                ) == band
            {
                group_end += 1;
            }
            self.merge_wave_group(group_start, group_end, band);
            group_start = group_end;
        }
    }

    /// CEP:WHAT: Picks the unassigned variable with the highest (activity, index) key, discarding assigned variables from the structure.
    /// CEP:WHY: Design 11.1 S12 and 11.2: the decision primitive. The occupied list's head node is the highest non-empty band and its chain stores indices descending, so its tail is the band's minimum index - the global maximum under the total key; the is_assigned predicate keeps the structure free of the caller's assignment state without this module owning it (no dyn, no coupling).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (None means every variable is assigned).
    /// CEP:ASSUMES: the predicate reflects the caller's current assignment store.
    /// CEP:COST: O(1) per pick; emptied nodes are reclaimed in O(1).
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{bump_raises_activity, ties_broken_by_index, pick_skips_assigned}.
    /// CEP:SECURITY: none.
    pub fn pick_unassigned(&self, is_assigned: impl Fn(u32) -> bool) -> Option<u32> {
        while self.list_head.get() != kNotInHeap {
            let node = self.list_head.get();
            // The chain stores keys descending, so its head carries the band's maximum
            // key - and the head node is the highest non-empty band, so this is the
            // normative global maximum.
            let candidate = self.node_head[node as usize].get();
            self.unlink(candidate);
            if !is_assigned(candidate) {
                return Some(candidate);
            }
        }
        None
    }

    // CEP:WHAT: Maps an activity score to its ladder band by pure bit inspection.
    // CEP:WHY: The band must be a strictly monotone function of the score so band order equals score order (the pick correctness argument); biased exponent selects the band, the top mantissa bits select the sub-band, zero/subnormal scores map to the bottom band. The band id space is (biased + 53) * 8 + (mantissa >> 49 & 7) for biased 1..2046, i.e. ids 424..16799 plus the bottom band 0 - the ids are pure arithmetic and index no array, so no ladder-span storage exists.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (non-positive and NaN scores clamp to the bottom band deterministically; NaN is caught explicitly because it compares false against everything and would otherwise compute an out-of-range band).
    // CEP:ASSUMES: IEEE-754 binary64; activities are finite.
    // CEP:COST: 4 bit operations.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ladder_matches_oracle_under_fuzz (band boundaries crossed as scores spread).
    // CEP:SECURITY: none.
    fn level_of_activity(activity: f64) -> u32 {
        // NaN compares false against everything, so it is caught explicitly: falling
        // through would compute band (0x7FF + 53) * 8, far above any real band.
        if activity.is_nan() || activity <= 0.0 {
            return 0;
        }
        let bits = activity.to_bits();
        let biased = ((bits >> 52) & 0x7FF) as u32;
        if biased == 0 {
            return 0;
        }
        (biased + 53) * 8 + ((bits >> 49) as u32 & 7)
    }

    // CEP:WHAT: Allocates and validates one Cell<u32> arena array.
    // CEP:WHY: The heap construction allocates ten u32 arrays; one helper keeps the ArenaFull mapping single-sourced.
    // CEP:STATUS: complete
    // CEP:FAILURE: ArenaFull when the arena cannot hold the array.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation plus validation.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::construction_rejects_bad_counts (ArenaFull path).
    // CEP:SECURITY: the arena is the memory boundary.
    fn alloc_u32(arena: &'a Arena, count: u32) -> Result<&'a [Cell<u32>], VsidsError> {
        let range = arena
            .alloc_array::<Cell<u32>>(count)
            .map_err(|_| VsidsError::ArenaFull)?;
        arena
            .array::<Cell<u32>>(range)
            .map_err(|_| VsidsError::ArenaFull)
    }

    // CEP:WHAT: Returns a band node's slot from the temporary rescale list, reusing the existing node for that band id or carving one from the free list.
    // CEP:WHY: Nodes created during the rescale must stay out of the occupied list that the captured-chain walk traverses; the temporary list is threaded through node_next and merged back after the walk.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns kNotInHeap if the free list is exhausted (see find_or_create_node).
    // CEP:ASSUMES: called only inside rescale_bands.
    // CEP:COST: O(temporary-list descent).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ladder_matches_oracle_under_fuzz.
    // CEP:SECURITY: none.
    fn find_or_create_temp(&self, band: u32) -> u32 {
        let mut previous: u32 = kNotInHeap;
        let mut current = self.rescale_temp.get();
        while current != kNotInHeap {
            let slot = current as usize;
            let node_band = self.node_band[slot].get();
            if node_band == band {
                return current;
            }
            if node_band < band {
                break;
            }
            previous = current;
            current = self.node_next[slot].get();
        }
        let slot = self.node_free.get();
        if slot == kNotInHeap {
            return kNotInHeap;
        }
        self.node_free.set(self.node_next[slot as usize].get());
        self.node_band[slot as usize].set(band);
        self.node_head[slot as usize].set(kNotInHeap);
        self.node_tail[slot as usize].set(kNotInHeap);
        self.node_len[slot as usize].set(0);
        self.node_next[slot as usize].set(current);
        // The temporary list must be fully doubly-linked: after phase C merges it into
        // the occupied list, free_node unlinks through node_prev, so a stale
        // kNotInHeap predecessor on a mid-list node would make the node look like the
        // list head and corrupt list_head when it is reclaimed.
        self.node_prev[slot as usize].set(previous);
        if previous == kNotInHeap {
            self.rescale_temp.set(slot);
        } else {
            self.node_next[previous as usize].set(slot);
        }
        if current != kNotInHeap {
            self.node_prev[current as usize].set(slot);
        }
        slot
    }

    // CEP:WHAT: Unlinks an in-band variable from its band chain in O(1) and reclaims the band node when the chain empties.
    // CEP:WHY: Bump re-banding, pick removal, and wave collection share the primitive; the occupied-node count stays bounded by the member count because empty nodes are reclaimed here.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the variable is linked (band_slot is a real slot).
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::pick_skips_assigned.
    // CEP:SECURITY: none.
    fn unlink(&self, variable: u32) {
        let index = variable as usize;
        let slot = (self.band_slot[index].get() - 1) as usize;
        let predecessor = self.prev[index].get();
        let successor = self.next[index].get();
        if predecessor != kNotInHeap {
            self.next[predecessor as usize].set(successor);
        } else {
            self.node_head[slot].set(successor);
        }
        if successor != kNotInHeap {
            self.prev[successor as usize].set(predecessor);
        } else {
            self.node_tail[slot].set(predecessor);
        }
        let remaining = self.node_len[slot].get() - 1;
        self.node_len[slot].set(remaining);
        self.band_slot[index].set(0);
        if remaining == 0 {
            self.free_node(slot as u32);
        }
    }

    // CEP:WHAT: Returns a band node's slot, reusing the existing node for that band id or carving one from the free list and inserting it into the occupied list at its sorted position.
    // CEP:WHY: The occupied list must stay sorted by descending band id so its head is the decision maximum.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns kNotInHeap if the free list is exhausted; the caller leaves the variable unlinked (documented incompleteness - the bound "occupied nodes <= members <= variables" makes this unreachable in legitimate operation).
    // CEP:ASSUMES: band ids are unique per node.
    // CEP:COST: O(occupied-list descent from the head).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::bump_raises_activity.
    // CEP:SECURITY: none.
    fn find_or_create_node(&self, band: u32) -> u32 {
        let mut previous: u32 = kNotInHeap;
        let mut current = self.list_head.get();
        while current != kNotInHeap {
            let slot = current as usize;
            let node_band = self.node_band[slot].get();
            if node_band == band {
                return current;
            }
            if node_band < band {
                break;
            }
            previous = current;
            current = self.node_next[slot].get();
        }
        let slot = self.node_free.get();
        if slot == kNotInHeap {
            return kNotInHeap;
        }
        // Detach from the free list.
        self.node_free.set(self.node_next[slot as usize].get());
        self.node_band[slot as usize].set(band);
        self.node_head[slot as usize].set(kNotInHeap);
        self.node_tail[slot as usize].set(kNotInHeap);
        self.node_len[slot as usize].set(0);
        // Insert into the occupied list before `current`.
        self.node_prev[slot as usize].set(previous);
        self.node_next[slot as usize].set(current);
        if previous == kNotInHeap {
            self.list_head.set(slot);
        } else {
            self.node_next[previous as usize].set(slot);
        }
        if current != kNotInHeap {
            self.node_prev[current as usize].set(slot);
        }
        slot
    }

    // CEP:WHAT: Returns a band node to the free list, removing it from the occupied list and marking it dead.
    // CEP:WHY: Empty nodes must not linger: the occupied count is bounded by the member count only if empty nodes are reclaimed eagerly; the dead marker lets the rescale's captured-chain walk skip reused slots.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the node's chain is empty.
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::pick_skips_assigned.
    // CEP:SECURITY: none.
    fn free_node(&self, slot: u32) {
        let index = slot as usize;
        let previous = self.node_prev[index].get();
        let successor = self.node_next[index].get();
        if previous == kNotInHeap {
            self.list_head.set(successor);
        } else {
            self.node_next[previous as usize].set(successor);
        }
        if successor != kNotInHeap {
            self.node_prev[successor as usize].set(previous);
        }
        self.node_band[index].set(kDeadBand);
        self.node_head[index].set(kNotInHeap);
        self.node_tail[index].set(kNotInHeap);
        self.node_len[index].set(0);
        self.node_prev[index].set(kNotInHeap);
        self.node_next[index].set(self.node_free.get());
        self.node_free.set(slot);
    }

    // CEP:WHAT: Links a variable into a band's chain at its exact key position.
    // CEP:WHY: The band chain must stay sorted by (activity desc, index asc) so the chain tail is the band minimum and the pick is exact.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; if the band node cannot be allocated the variable stays unlinked (documented incompleteness).
    // CEP:ASSUMES: the variable is unlinked (band_slot == 0).
    // CEP:COST: O(occupied-list descent) + O(b) chain walk (contiguous index-order activity reads).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ties_broken_by_index.
    // CEP:SECURITY: none.
    fn link(&self, variable: u32, band: u32) {
        let slot = self.find_or_create_node(band);
        if slot == kNotInHeap {
            return;
        }
        let index = variable as usize;
        let mut predecessor: u32 = kNotInHeap;
        let mut current = self.node_head[slot as usize].get();
        while current != kNotInHeap && self.key_greater(current, variable) {
            predecessor = current;
            current = self.next[current as usize].get();
        }
        let successor = current;
        self.prev[index].set(predecessor);
        self.next[index].set(successor);
        if predecessor != kNotInHeap {
            self.next[predecessor as usize].set(variable);
        } else {
            self.node_head[slot as usize].set(variable);
        }
        if successor != kNotInHeap {
            self.prev[successor as usize].set(variable);
        } else {
            self.node_tail[slot as usize].set(variable);
        }
        self.node_len[slot as usize].set(self.node_len[slot as usize].get() + 1);
        self.band_slot[index].set(slot + 1);
    }

    // CEP:WHAT: Total heap key: activity descending, then variable index ascending.
    // CEP:WHY: CEP&CC 38.10 determinism requires a total order on members; ties on activity are resolved by the smaller index so identical runs produce identical decisions.
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

    // CEP:WHAT: Rebuilds the occupied-band list after the rescale multiplied every activity.
    // CEP:WHY: The multiply preserves the exact activity order, so each occupied band's chain splits into runs whose new band ids descend along the chain; splicing every run into its new band's node while walking the occupied list from the head (descending band ids) appends runs to each target in descending activity order, which is the key order. Scores flushed to exactly zero tie under the key and are re-chained in index order by the bottom-band pass, matching the binary heap's tie-break.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: activities are already multiplied; the ladder is monotone; the walk follows a captured next-node chain so splices and frees during the walk cannot loop it; a freed-and-reused slot reached by the captured chain holds a new node whose members are already final, so its run is a keep and the node is not freed.
    // CEP:COST: O(variables) plus O(occupied-list work) with no sort.
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{rescale_keeps_scores_finite, underflow_flush_ties_by_index, ladder_matches_oracle_under_fuzz}.
    // CEP:SECURITY: none.
    fn rescale_bands(&self) {
        // CEP:WHAT: Phase A: walk the occupied list over a captured chain and re-band every member.
        // CEP:WHY: Descending source order makes the run-splice order the key order; freeing each emptied node as it is processed keeps the pool within its bound.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: a positive node's members all move (the factor is 1e-100, strictly below every positive score's band); band 0's node is skipped (its members are already at band 0 and the bottom-band pass re-chains them in index order); a keep-run (new band == the node's own band) arises only for reached-but-reused new nodes and stays in place.
        // CEP:COST: O(members) plus O(1) per run splice and per emptied node.
        // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::rescale_keeps_scores_finite.
        // CEP:SECURITY: none.
        let mut node = self.list_head.get();
        while node != kNotInHeap {
            let captured_next = self.node_next[node as usize].get();
            let node_band = self.node_band[node as usize].get();
            if node_band != 0 && node_band != kDeadBand {
                let first = self.node_head[node as usize].get();
                // A node reached by the captured chain either still holds its original
                // members (an old positive node: every member moves, because the factor
                // 1e-100 sends every positive score strictly below its own band) or is a
                // new node created during this same rescale whose slot was freed and
                // reused (its members are already final). The first member's computed
                // band distinguishes the cases: equal to the node's band means final.
                if first != kNotInHeap
                    && Self::level_of_activity(self.activities[first as usize].get()) != node_band
                {
                    let mut current = first;
                    let mut run_head: u32 = kNotInHeap;
                    let mut run_tail: u32 = kNotInHeap;
                    let mut run_band: u32 = 0;
                    let mut run_len: u32 = 0;
                    while current != kNotInHeap {
                        let next_current = self.next[current as usize].get();
                        let new_band =
                            Self::level_of_activity(self.activities[current as usize].get());
                        if run_head != kNotInHeap && new_band != run_band {
                            // Close the run: detach it from the source chain and splice
                            // it into its new band's node. Positive targets live in the
                            // temporary rescale list (never in the walked list); flushed
                            // targets splice into the live band-0 node (the bottom-band
                            // pass below re-chains it in index order).
                            self.next[run_tail as usize].set(kNotInHeap);
                            let target = if run_band == 0 {
                                self.find_or_create_node(0)
                            } else {
                                self.find_or_create_temp(run_band)
                            };
                            if target != kNotInHeap {
                                self.append_run(target, run_head, run_tail, run_len);
                            }
                            run_head = kNotInHeap;
                        }
                        if run_head == kNotInHeap {
                            run_head = current;
                            run_tail = current;
                            run_band = new_band;
                            run_len = 1;
                        } else {
                            self.next[run_tail as usize].set(current);
                            self.prev[current as usize].set(run_tail);
                            run_tail = current;
                            run_len += 1;
                        }
                        current = next_current;
                    }
                    if run_head != kNotInHeap {
                        self.next[run_tail as usize].set(kNotInHeap);
                        let target = if run_band == 0 {
                            self.find_or_create_node(0)
                        } else {
                            self.find_or_create_temp(run_band)
                        };
                        if target != kNotInHeap {
                            self.append_run(target, run_head, run_tail, run_len);
                        }
                    }
                    // Every member moved: the node is empty and returns to the pool.
                    self.node_head[node as usize].set(kNotInHeap);
                    self.node_tail[node as usize].set(kNotInHeap);
                    self.node_len[node as usize].set(0);
                    self.free_node(node);
                }
            }
            node = captured_next;
        }
        // CEP:WHAT: Phase B: rebuild band 0's chain (every zero score) in index order.
        // CEP:WHY: Never-bumped and flushed scores all tie at exactly 0.0, and the key orders ties by smaller index, so a single index-ascending pass rebuilds the sorted chain without a sort; flushed members were spliced into band 0's node during phase A in source order, which this pass replaces with the key order.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: decay clamps every rescale product below the smallest normal to exactly 0.0, so bottom-band members are exactly 0.0 and the scan condition (activity == 0.0) is exact.
        // CEP:COST: O(variables).
        // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::underflow_flush_ties_by_index.
        // CEP:SECURITY: none.
        // Band 0's node is located, never created here: a linked zero-scored member
        // always sits in a band-0 node (the member-band invariant), so an absent
        // band-0 node means no zero members exist, and creating the node anyway would
        // leave an empty node in the occupied list - pick would then unlink
        // kNotInHeap out of it.
        let mut zero_slot: u32 = kNotInHeap;
        let mut probe = self.list_head.get();
        while probe != kNotInHeap {
            if self.node_band[probe as usize].get() == 0 {
                zero_slot = probe;
                break;
            }
            probe = self.node_next[probe as usize].get();
        }
        if zero_slot != kNotInHeap {
            self.node_head[zero_slot as usize].set(kNotInHeap);
            self.node_tail[zero_slot as usize].set(kNotInHeap);
            self.node_len[zero_slot as usize].set(0);
            let mut last: u32 = kNotInHeap;
            for index in 0..self.activities.len() {
                // Members of band 0 are exactly the linked zero-scored variables; picked
                // variables carry band_slot 0 and positive members carry other slots.
                let state = self.band_slot[index].get();
                if state == 0 || state == kWavePending {
                    continue;
                }
                let member_node = (state - 1) as usize;
                if self.node_band[member_node].get() != 0 || self.activities[index].get() != 0.0 {
                    continue;
                }
                let variable = index as u32;
                if last == kNotInHeap {
                    self.node_head[zero_slot as usize].set(variable);
                    self.prev[index].set(kNotInHeap);
                } else {
                    self.next[last as usize].set(variable);
                    self.prev[index].set(last);
                }
                last = variable;
                self.node_len[zero_slot as usize].set(self.node_len[zero_slot as usize].get() + 1);
            }
            if last != kNotInHeap {
                self.next[last as usize].set(kNotInHeap);
                self.node_tail[zero_slot as usize].set(last);
            }
        }
        // CEP:WHAT: Phase C: splice the temporary list (sorted by descending band id, all ids above 0) back onto the occupied list behind band 0's node.
        // CEP:WHY: The occupied list must be complete and sorted before the next pick; the walk kept new nodes off it.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: the temporary list is sorted descending and holds no band-0 node (band 0 targets use the live list).
        // CEP:COST: O(new nodes).
        // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::ladder_matches_oracle_under_fuzz.
        // CEP:SECURITY: none.
        let temp_head = self.rescale_temp.get();
        if temp_head != kNotInHeap {
            let mut temp_tail = temp_head;
            while self.node_next[temp_tail as usize].get() != kNotInHeap {
                temp_tail = self.node_next[temp_tail as usize].get();
            }
            let live_head = self.list_head.get();
            if live_head == kNotInHeap {
                self.list_head.set(temp_head);
            } else {
                self.node_next[temp_tail as usize].set(live_head);
                self.node_prev[live_head as usize].set(temp_tail);
                // The live list's head at this point is band 0's node (every positive
                // old node was processed and freed during the walk), which sits BELOW
                // every temporary node, so the merged list's head is the temporary
                // list's head - list_head must move to it or the positive bands stay
                // orphaned from the occupied list (unpickable and unvisitable).
                self.list_head.set(temp_head);
            }
            self.rescale_temp.set(kNotInHeap);
        }
    }

    // CEP:WHAT: Appends one contiguous run (head..tail, given length) to the tail of a target band node's chain.
    // CEP:WHY: The rescale assembles each new band from runs in key order; the run's internal chain is intact, so the splice is O(1).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the run is detached from its source chain; the target's current tail precedes the run in key order (descending source order).
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::rescale_keeps_scores_finite.
    // CEP:SECURITY: none.
    fn append_run(&self, target: u32, head: u32, tail: u32, length: u32) {
        let index = target as usize;
        let current_tail = self.node_tail[index].get();
        if current_tail == kNotInHeap {
            self.node_head[index].set(head);
            self.prev[head as usize].set(kNotInHeap);
        } else {
            self.next[current_tail as usize].set(head);
            self.prev[head as usize].set(current_tail);
        }
        self.node_tail[index].set(tail);
        self.next[tail as usize].set(kNotInHeap);
        self.node_len[index].set(self.node_len[index].get() + length);
        // Stamp every member's band slot to the target node.
        let mut cursor = head;
        while cursor != kNotInHeap {
            self.band_slot[cursor as usize].set(target + 1);
            cursor = self.next[cursor as usize].get();
        }
    }

    // CEP:WHAT: Merges one wave group (a descending-key run of the scratch buffer) into a band's chain.
    // CEP:WHY: The wave merge must produce the exact key order; weaving two descending sequences in one pass relinks every touched member exactly once.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; if the band node cannot be allocated the group stays unlinked (documented incompleteness).
    // CEP:ASSUMES: the group's members are consecutive in scratch and sorted descending by key; the band chain is sorted descending by key.
    // CEP:COST: O(band size + group size).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle.
    // CEP:SECURITY: none.
    fn merge_wave_group(&self, group_start: usize, group_end: usize, band: u32) {
        let slot = self.find_or_create_node(band);
        if slot == kNotInHeap {
            return;
        }
        let mut list_current = self.node_head[slot as usize].get();
        let mut run_index = group_end;
        let mut built_head: u32 = kNotInHeap;
        let mut built_tail: u32 = kNotInHeap;
        let mut built_len: u32 = 0;
        // Descending merge: the run is walked backward (scratch is ascending by key).
        while list_current != kNotInHeap || run_index > group_start {
            let take_from_list = if list_current == kNotInHeap {
                false
            } else if run_index == group_start {
                true
            } else {
                let run_variable = self.scratch[run_index - 1].get();
                self.key_greater(list_current, run_variable)
            };
            let member = if take_from_list {
                let member = list_current;
                list_current = self.next[member as usize].get();
                member
            } else {
                run_index -= 1;
                self.scratch[run_index].get()
            };
            if built_tail == kNotInHeap {
                built_head = member;
                self.prev[member as usize].set(kNotInHeap);
            } else {
                self.next[built_tail as usize].set(member);
                self.prev[member as usize].set(built_tail);
            }
            built_tail = member;
            built_len += 1;
        }
        if built_tail != kNotInHeap {
            self.next[built_tail as usize].set(kNotInHeap);
            self.node_head[slot as usize].set(built_head);
            self.node_tail[slot as usize].set(built_tail);
            self.node_len[slot as usize].set(built_len);
        }
        // Stamp every member's band slot to the node.
        let mut cursor = built_head;
        while cursor != kNotInHeap {
            self.band_slot[cursor as usize].set(slot + 1);
            cursor = self.next[cursor as usize].get();
        }
    }

    // CEP:WHAT: Deterministic heapsort of a scratch slice ascending by the (activity desc, index asc) key.
    // CEP:WHY: The wave merge needs the wave in the band chains' key order; the sort is pure and allocation-free, over the pre-allocated wave buffer.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: activities are finite; the slice length is bounded by the variable count.
    // CEP:COST: O(W log W).
    // CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::wave_insert_matches_oracle.
    // CEP:SECURITY: none.
    fn heapsort_ascending_by_key(slice: &[Cell<u32>], activities: &[Cell<f64>]) {
        let length = slice.len();
        if length < 2 {
            return;
        }
        let key_greater = |left: u32, right: u32| -> bool {
            let left_activity = activities[left as usize].get();
            let right_activity = activities[right as usize].get();
            if left_activity > right_activity {
                return true;
            }
            if left_activity < right_activity {
                return false;
            }
            left < right
        };
        // Build a max-heap on the key; popping the max to the end yields ascending order.
        let mut start = length / 2;
        while start > 0 {
            start -= 1;
            let mut root = start;
            loop {
                let child = root * 2 + 1;
                if child >= length {
                    break;
                }
                let mut best = child;
                if child + 1 < length && key_greater(slice[child + 1].get(), slice[child].get()) {
                    best = child + 1;
                }
                if key_greater(slice[best].get(), slice[root].get()) {
                    let a = slice[root].get();
                    let b = slice[best].get();
                    slice[root].set(b);
                    slice[best].set(a);
                    root = best;
                } else {
                    break;
                }
            }
        }
        let mut end = length;
        while end > 1 {
            end -= 1;
            let a = slice[0].get();
            let b = slice[end].get();
            slice[0].set(b);
            slice[end].set(a);
            let mut root = 0usize;
            loop {
                let child = root * 2 + 1;
                if child >= end {
                    break;
                }
                let mut best = child;
                if child + 1 < end && key_greater(slice[child + 1].get(), slice[child].get()) {
                    best = child + 1;
                }
                if key_greater(slice[best].get(), slice[root].get()) {
                    let x = slice[root].get();
                    let y = slice[best].get();
                    slice[root].set(y);
                    slice[best].set(x);
                    root = best;
                } else {
                    break;
                }
            }
        }
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
    /// CEP:WHAT: Constructs a phase table with every entry unset.
    /// CEP:WHY: Unset entries fall back to the default decision polarity (S14).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns VariableCountInvalid / ArenaFull.
    /// CEP:ASSUMES: 0 < variables <= kMaxSatVariables.
    /// CEP:COST: O(variables) one-time.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::saved_phase_defaults_to_constant.
    /// CEP:SECURITY: count validated before allocation.
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

    /// CEP:WHAT: Returns the saved decision polarity of a variable, or the default when unset.
    /// CEP:WHY: Design 11.1 S14: "Use saved phase (phase saving) or constant phase."
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (clamped to the default for out-of-range variables).
    /// CEP:ASSUMES: variable below the declared count in solver use.
    /// CEP:COST: 1 bounds check + 1 load + 1 compare.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::{saved_phase_defaults_to_constant, phase_table_roundtrip}.
    /// CEP:SECURITY: clamped read.
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

    /// CEP:WHAT: Saves the last-assigned polarity of a variable.
    /// CEP:WHY: Design 11.1 S17: "Save polarity on assignment" (MAPT saves at unassignment time, which records the same last-assigned polarity).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (out-of-range variables are clamped no-ops).
    /// CEP:ASSUMES: variable below the declared count in solver use.
    /// CEP:COST: 1 bounds check + 1 store.
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    /// CEP:SECURITY: clamped write.
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

    /// CEP:WHAT: Clears every saved phase back to unset.
    /// CEP:WHY: Design 11.1 S17: "Reset on restart (configurable)"; the solver calls this only when constructed with phase reset enabled.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(variables).
    /// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::phase_table_roundtrip.
    /// CEP:SECURITY: none.
    pub fn reset(&self) {
        for slot in self.phases.iter() {
            slot.set(kPhaseUnset);
        }
    }
}
