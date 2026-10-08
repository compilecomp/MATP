// CEP:FILE: hot/sat/trail.rs
// CEP:WHAT: SAT trail: flat literal stack with decision-level markers and the BCP propagation queue cursor.
// CEP:WHY: Design 11.1 S5/S15: the trail is the assignment stack that BCP drains (qhead) and conflict analysis walks (Phase 2); level markers give non-chronological backtracking its rewind points; flat arena arrays keep push/pop at one store and index arithmetic with zero allocation.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SatTrailError::TrailFull when the trail capacity is reached, TooManyLevels at the level bound; cancel_until clamps the target level. Never panics.
// CEP:ASSUMES: A variable is assigned at most once between backtracks, so the trail never holds duplicates of the same variable (property-tested); level starts are monotonic; the arena outlives the trail.
// CEP:COST: push is 2 compares + 2 stores; pop-driven cancel is O(popped) with one store per entry; pushes are exercised inside the propagation measurement (44.5 cycles median per step) in bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: unit/hot/sat_trail_test.rs; property/bcp_property_test.rs; bench CEP-BENCH-0005.
// CEP:SECURITY: capacity and level bounds are explicit errors; no unbounded growth.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; stack discipline with monotonic cursors.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: a trail push must bounds-check once, store the literal, bump the cursor; disassembly (artifact disasm_sat.txt) shows cmp+mov+add with no calls.

use crate::memory::arena::Arena;
use crate::sat::literal::SatLiteral;
use core::cell::Cell;
use mapt_config::limits::kSatTrailCapacity;

/// CEP:WHAT: Error cases of the trail.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_trail_test.rs covers every variant.
/// CEP:SECURITY: capacity bounds are denial-of-service guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatTrailError {
    /// CEP:WHAT: The literal stack is full (kSatTrailCapacity).
    TrailFull,
    /// CEP:WHAT: The level array is full (kMaxDecisionLevels).
    TooManyLevels,
    /// CEP:WHAT: The trail was not initialized (empty arrays).
    NotInitialized,
}

/// CEP:WHAT: The SAT assignment trail.
/// CEP:WHY: See file header; bundles the literal stack, the level-start stack, and the propagation queue head.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SatTrailError.
/// CEP:ASSUMES: sized once at initialization.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
/// CEP:SECURITY: bounded arrays, checked pushes.
pub struct SatTrail<'a> {
    /// CEP:WHAT: Assigned-literal stack (packed encodings).
    /// CEP:WHY: Design 11.1 S5.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: capacity kSatTrailCapacity.
    /// CEP:COST: 4 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    /// CEP:SECURITY: bounds-checked.
    literals: &'a [Cell<u32>],
    /// CEP:WHAT: Level-start indices; level i covers [level_starts[i], len).
    /// CEP:WHY: Design 11.1 S15 decision level tracking.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: capacity kMaxDecisionLevels + 1; entry 0 is always 0 (level 0 = root).
    /// CEP:COST: 4 bytes per level.
    /// CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    /// CEP:SECURITY: bounds-checked.
    level_starts: &'a [Cell<u32>],
    /// CEP:WHAT: Number of entries on the literal stack.
    /// CEP:WHY: Stack cursor.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kSatTrailCapacity.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    /// CEP:SECURITY: none.
    length: Cell<u32>,
    /// CEP:WHAT: Number of open levels.
    /// CEP:WHY: Level cursor; level() is this minus one.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 after initialization.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    /// CEP:SECURITY: none.
    level_count: Cell<u32>,
    /// CEP:WHAT: Propagation queue head (index of the next trail entry to process).
    /// CEP:WHY: Design 11.1 S11: BCP drains the trail in FIFO order through this cursor; separating it from length lets callers distinguish assigned from processed.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: qhead <= length.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::propagation_drains_queue.
    /// CEP:SECURITY: none.
    qhead: Cell<u32>,
}

impl<'a> SatTrail<'a> {
    // CEP:WHAT: Allocates and initializes the trail for a declared variable count.
    // CEP:WHY: Level 0 (root) must exist before any assignment so propagation at level 0 is representable; arrays are cleared for deterministic state; sizing by the variable count is sound because a variable is assigned at most once between backtracks (design 11.1 S5), so the trail never holds more entries than variables and levels never outnumber assignments plus one.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns NotInitialized when arena allocation fails or the variable count is zero or above kSatTrailCapacity.
    // CEP:ASSUMES: arena has room for both arrays.
    // CEP:COST: O(variables) one-time clear.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::initial_state; property/bcp_property_test.rs exercises many cores in one process.
    // CEP:SECURITY: cleared arrays, no uninitialized reads; capacity bounded by the declared count.
    pub fn new(arena: &'a Arena, variable_count: u32) -> Result<SatTrail<'a>, SatTrailError> {
        if variable_count == 0 || variable_count > kSatTrailCapacity {
            return Err(SatTrailError::NotInitialized);
        }
        let literal_range = arena
            .alloc_array::<Cell<u32>>(variable_count)
            .map_err(|_| SatTrailError::NotInitialized)?;
        let literals = arena
            .array::<Cell<u32>>(literal_range)
            .map_err(|_| SatTrailError::NotInitialized)?;
        for slot in literals.iter() {
            slot.set(0);
        }
        let level_range = arena
            .alloc_array::<Cell<u32>>(variable_count + 1)
            .map_err(|_| SatTrailError::NotInitialized)?;
        let level_starts = arena
            .array::<Cell<u32>>(level_range)
            .map_err(|_| SatTrailError::NotInitialized)?;
        for slot in level_starts.iter() {
            slot.set(0);
        }
        Ok(SatTrail {
            literals,
            level_starts,
            length: Cell::new(0),
            level_count: Cell::new(1),
            qhead: Cell::new(0),
        })
    }

    // CEP:WHAT: Appends an assignment at the current level.
    // CEP:WHY: BCP enqueues forced literals; decisions are enqueued through push_decision.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TrailFull at capacity.
    // CEP:ASSUMES: the literal's variable is unassigned (caller discipline, property-tested).
    // CEP:COST: 1 compare + 2 stores.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::push_and_read_back.
    // CEP:SECURITY: bounds-checked.
    pub fn push_assignment(&self, literal: SatLiteral) -> Result<(), SatTrailError> {
        let length = self.length.get();
        if length >= self.literals.len() as u32 {
            return Err(SatTrailError::TrailFull);
        }
        self.literals[length as usize].set(literal.encoding());
        self.length.set(length + 1);
        Ok(())
    }

    // CEP:WHAT: Opens a new decision level and appends the decision literal.
    // CEP:WHY: Level markers are the rewind points for non-chronological backtracking (design 11.1 S22 uses them in Phase 2).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TooManyLevels at the level bound and TrailFull at capacity.
    // CEP:ASSUMES: as push_assignment.
    // CEP:COST: 2 compares + 4 stores.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    // CEP:SECURITY: bounds-checked.
    pub fn push_decision(&self, literal: SatLiteral) -> Result<(), SatTrailError> {
        let levels = self.level_count.get();
        if levels >= self.level_starts.len() as u32 {
            return Err(SatTrailError::TooManyLevels);
        }
        let length = self.length.get();
        if length >= self.literals.len() as u32 {
            return Err(SatTrailError::TrailFull);
        }
        self.level_starts[levels as usize].set(length);
        self.level_count.set(levels + 1);
        self.literals[length as usize].set(literal.encoding());
        self.length.set(length + 1);
        Ok(())
    }

    // CEP:WHAT: Returns the entry at an index.
    // CEP:WHY: BCP reads the queue; conflict analysis (Phase 2) walks the stack.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns None for out-of-range indices (BCP treats None as queue end).
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::push_and_read_back.
    // CEP:SECURITY: bounds check retained in release.
    pub fn literal_at(&self, index: u32) -> Option<SatLiteral> {
        if index >= self.length.get() {
            return None;
        }
        Some(SatLiteral::from_encoding(
            self.literals[index as usize].get(),
        ))
    }

    // CEP:WHAT: Returns the current stack length.
    // CEP:WHY: Queue-end detection and backtracking bookkeeping.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
    // CEP:SECURITY: none.
    pub fn len(&self) -> u32 {
        self.length.get()
    }

    // CEP:WHAT: Returns true when the trail holds no assignments.
    // CEP:WHY: Complements len() for empty-state checks; clippy requires the pair.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::initial_state.
    // CEP:SECURITY: none.
    pub fn is_empty(&self) -> bool {
        self.length.get() == 0
    }

    // CEP:WHAT: Returns the current decision level.
    // CEP:WHY: Level-relative operations and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: at least the root level exists.
    // CEP:COST: 1 load + 1 subtract.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    // CEP:SECURITY: none.
    pub fn level(&self) -> u32 {
        self.level_count.get() - 1
    }

    // CEP:WHAT: Returns the index of the first entry of the current level.
    // CEP:WHY: Backtracking pops to this index.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 2 loads.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::levels.
    // CEP:SECURITY: none.
    pub fn current_level_start(&self) -> u32 {
        self.level_starts[self.level_count.get() as usize - 1].get()
    }

    // CEP:WHAT: Returns the propagation queue head.
    // CEP:WHY: BCP consumes assignments below qhead and stops at equality with len.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::propagation_drains_queue.
    // CEP:SECURITY: none.
    pub fn qhead(&self) -> u32 {
        self.qhead.get()
    }

    // CEP:WHAT: Advances the queue head (one assignment consumed).
    // CEP:WHY: BCP step primitive; separated from reads for auditability.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; clamped internally to len.
    // CEP:ASSUMES: caller checked qhead < len.
    // CEP:COST: 1 compare + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::propagation_drains_queue.
    // CEP:SECURITY: none.
    pub fn advance_qhead(&self) {
        let next = self.qhead.get() + 1;
        if next <= self.length.get() {
            self.qhead.set(next);
        }
    }

    // CEP:WHAT: Returns the trail index where a level begins.
    // CEP:WHY: Backtracking computes the popped segment from the target level's start; the accessor keeps the level array private.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; levels beyond the current level clamp to the current level's start.
    // CEP:ASSUMES: level <= current level for meaningful results.
    // CEP:COST: 1 compare + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::cancel_until.
    // CEP:SECURITY: clamped index, no out-of-range access.
    pub fn level_start(&self, level: u32) -> u32 {
        let clamped = level.min(self.level_count.get() - 1);
        self.level_starts[clamped as usize].get()
    }

    // CEP:WHAT: Returns the trail length that backtracking to a target level keeps.
    // CEP:WHY: Cancelling to level L keeps levels 0 through L; the kept prefix ends where level L+1 begins, so the keep index is level_starts[L+1]; targets at or above the current level are no-ops that keep the whole trail.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: level_starts is monotonic.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::cancel_until; unit/hot/sat_bcp_test.rs::cancel_restores_assignments.
    // CEP:SECURITY: clamped arithmetic, no underflow.
    pub fn cancel_keep_index(&self, target_level: u32) -> u32 {
        let current = self.level_count.get() - 1;
        if target_level >= current {
            return self.length.get();
        }
        self.level_starts[(target_level + 1) as usize].get()
    }

    // CEP:WHAT: Pops every entry above the target level and rewinds the queue head.
    // CEP:WHY: Design 11.1 S22 backjumping support; the assignment store is cleared by the caller (SatCore) which owns both structures.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; targets at or above the current level are no-ops (documented, deterministic).
    // CEP:ASSUMES: the caller clears assignment values for popped literals using cancel_keep_index before calling this.
    // CEP:COST: O(1); the caller performs the O(popped) value clears.
    // CEP:EVIDENCE: unit/hot/sat_trail_test.rs::cancel_until.
    // CEP:SECURITY: clamped arithmetic, no underflow.
    pub fn cancel_until(&self, target_level: u32) {
        let keep = self.cancel_keep_index(target_level);
        let current = self.level_count.get() - 1;
        if target_level >= current {
            return;
        }
        self.length.set(keep);
        self.level_count.set(target_level + 1);
        if self.qhead.get() > keep {
            self.qhead.set(keep);
        }
    }
}
