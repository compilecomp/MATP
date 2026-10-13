// CEP:FILE: hot/sat/registry.rs
// CEP:WHAT: Clause registry: the enumerable SAT clause database (dense arena entries for problem and learnt clauses with tombstones) plus the learnt-clause deletion policy (LBD first, then age, then activity) and clause-activity bumping with rescaling.
// CEP:WHY: Design 11.1 S4 ("clause database: arena-backed, generation-tagged") requires an enumerable database - Phase 2 clauses were reachable only through watch lists, which cannot enumerate units or deletion candidates; CEP-1003 (Phase 3) names the registry as the precondition for the deletion policy (S25/S26), and SAT preprocessing depends on the same enumeration (S30-S37); deletion marks records with the storage deleted bit (lazy watch-list unlinking, Spec 05 section 6 amendment) while the registry tombstone keeps the entry bookkeeping sound, and the fixed-density entry layout is co-designed with future compaction (S27, ticket CEP-1007) by never reusing entry indices.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns RegistryError (Full at the entry capacity, Storage for unreadable clause records, InvariantViolation for lifecycle misuse such as double deletion); never panics.
// CEP:ASSUMES: Single-threaded use; all registered offsets came from the same ClauseStorage the reduction is driven against; entries are appended in strictly ascending clause-offset order (arena bump allocation guarantees it; the offset binary search relies on it); the storage deleted bit is the single source of truth for liveness - the tombstone mirrors it.
// CEP:COST: registration is O(1) plus one header read; lookup by offset is O(log entries); bump_activity is O(1) with an O(entries) rescale at the 1e100 ceiling (rare); reduction is O(variables + live-learnts x log live-learnts) and fires at most once per learnt-budget window, so the amortized per-conflict cost is one registration plus one activity bump; measured in bench CEP-BENCH-0013, artifact benches/artifacts/sat_registry_step.json.
// CEP:EVIDENCE: unit/hot/sat_registry_test.rs; unit/hot/sat_preprocess_test.rs; property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability; bench CEP-BENCH-0013.
// CEP:SECURITY: the entry capacity is a memory-exhaustion bound; every scan is bounded by a named capacity; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; heapsort under a total key (entry indices are unique), index-ordered scans, no clocks or addresses (CEP&CC 38.10).
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 section 9 fixes the deletion contract: deletion never removes a clause that is the current reason of an assigned variable or the active conflict clause (locking, S29), the survivors are the best live/divisor entries under the design 11.6 total order (LBD ascending, age descending - the strict-lexicographic reading in which the activity key is vacuous because ages are unique, documented in the comparator), and deletions preserve the solver invariants because BCP skips deleted records and surviving reasons never point at deleted clauses; the property tests verify end-to-end that solving with reduction enabled agrees with brute force.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: reduction re-reads headers per comparison for the LBD instead of caching LBD in registry entries; caching is deferred pending measurement on reduction-heavy workloads; ticket CEP-1032.

use crate::memory::arena::Arena;
use crate::sat::clause::{
    kSatClauseFlagDeleted, kSatClauseFlagLearnt, kSatClauseFlagLocked, ClauseStorage,
    SatClauseError,
};
use crate::sat::database::SatCore;
use mapt_config::limits::{
    kInvalidClauseOffset, kSatClauseActivityCeiling, kSatClauseActivityRescaleFactor,
    kSatLearntReduceDivisor, kSatMaxLearntClauses, kSatRegistryCapacity,
};

/// CEP:WHAT: Error cases of the clause registry.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the registry never panics and never silently drops bookkeeping.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{capacity_enforced, double_delete_rejected}.
/// CEP:SECURITY: capacity errors are the memory-exhaustion boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistryError {
    /// CEP:WHAT: The entry capacity is exhausted.
    /// CEP:WHY: Bounded registry memory (design 20.1); loud failure instead of unbounded growth.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Full,
    /// CEP:WHAT: A clause record read or write failed.
    /// CEP:WHY: Reduction and enumeration read headers and literals through the storage API; unreadable offsets are surfaced, never guessed past.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_marks_deleted.
    /// CEP:SECURITY: bounds-checked reads.
    Storage(SatClauseError),
    /// CEP:WHAT: A proof-recorder failure while recording a deletion (capacity or bookkeeping).
    /// CEP:WHY: Reduction and assumption-solve cleanup record proof deletions as they delete; recorder failures must surface through the registry's Result without being conflated with storage failures (CEP&CC 33.18 closed vocabulary; the solver maps this variant back to CdclError::Proof).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_records_proof_deletions.
    /// CEP:SECURITY: capacity errors are the resource boundary.
    Proof(crate::sat::proof::ProofError),
    /// CEP:WHAT: A lifecycle call contradicted the tombstone or ordering state (double delete, delete of an unregistered offset, out-of-order registration).
    /// CEP:WHY: CEP&CC Law 6: registry bookkeeping bugs surface loudly.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{double_delete_rejected, delete_unregistered_rejected}.
    /// CEP:SECURITY: rejects corrupted bookkeeping.
    InvariantViolation,
}

impl From<SatClauseError> for RegistryError {
    // CEP:WHAT: Converts storage errors into the registry vocabulary.
    // CEP:WHY: CEP&CC 33.18: one explicit translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_marks_deleted.
    // CEP:SECURITY: none.
    fn from(error: SatClauseError) -> RegistryError {
        RegistryError::Storage(error)
    }
}

impl From<crate::sat::proof::ProofError> for RegistryError {
    // CEP:WHAT: Converts proof-recorder errors into the registry vocabulary.
    // CEP:WHY: Reduction and cleanup drive proof deletion recording; CEP&CC 33.18 keeps the vocabulary closed with one explicit translation point (the solver maps the variant back to CdclError::Proof).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_records_proof_deletions.
    // CEP:SECURITY: none.
    fn from(error: crate::sat::proof::ProofError) -> RegistryError {
        RegistryError::Proof(error)
    }
}

/// CEP:WHAT: One registry entry: the clause offset, the activity score, and the tombstone bit.
/// CEP:WHY: Design 11.1 S24 (activity) and CEP-1003 (enumerable offsets and tombstone unlinking); the fixed 16-byte record keeps the array dense for future compaction (S27) and index-stable so entry indices double as clause age (monotonic registration order).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: offsets are ascending across appends; activity is finite (rescaled at the ceiling).
/// CEP:COST: 16 bytes per entry.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{registry_enumerates, activity_rescale_preserves_order}.
/// CEP:SECURITY: private mutation discipline; all writes go through the registry.
#[repr(C)]
pub struct RegistryEntry {
    /// CEP:WHAT: Clause activity score (bumped when the clause participates in a conflict).
    /// CEP:WHY: Design 11.1 S24 and 11.6 deletion priority 3; f64 with the same rescale discipline as the VSIDS heap keeps scores finite and the ordering total; the f64 leads the record so the 16-byte layout packs without interior padding.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 0; rescaled before exceeding kSatClauseActivityCeiling.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::activity_rescale_preserves_order.
    /// CEP:SECURITY: none.
    pub activity: core::cell::Cell<f64>,
    /// CEP:WHAT: Clause offset in the shared storage.
    /// CEP:WHY: The identity the deletion policy and enumeration hand to the storage layer.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: created by the storage this registry is used with.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
    /// CEP:SECURITY: bounds-checked on every storage use.
    pub offset: core::cell::Cell<u32>,
    /// CEP:WHAT: Tombstone bit (entry no longer refers to a live clause).
    /// CEP:WHY: CEP-1003 wording: tombstone unlinking; the entry stays (indices are stable age identifiers) but is skipped by enumeration and reduction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: mirrors the storage deleted bit.
    /// CEP:COST: 1 byte plus padding.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_tombstones, registry_enumerates}.
    /// CEP:SECURITY: none.
    pub tombstone: core::cell::Cell<bool>,
}

// CEP:WHAT: Registry entry layout pin.
// CEP:WHY: The entry array is part of the enumerable-database memory contract shared with future compaction (CEP-1007) and diagnostics; drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<RegistryEntry>() == 16);

/// CEP:WHAT: Sort key of one reduction candidate: (lbd, activity, entry index).
/// CEP:WHY: The deletion policy (design 11.6) orders candidates by LBD, then activity, then age; packing the three fields in one Copy record keeps the heapsort allocation-free and its comparator a pure function (no dyn, no captures, CEP-0 discipline); the entry index is unique so the order is total.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: activity is finite.
/// CEP:COST: 16 bytes.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{lbd_priority_order, age_priority_within_lbd}.
/// CEP:SECURITY: none.
#[derive(Clone, Copy)]
struct CandidateKey {
    /// CEP:WHAT: Literal Block Distance of the candidate clause.
    /// CEP:WHY: Deletion priority 1 (higher deleted first).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: from the clause header.
    /// CEP:COST: 1 byte plus padding.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::lbd_priority_order.
    /// CEP:SECURITY: none.
    lbd: u8,
    /// CEP:WHAT: Entry index (registration age) of the candidate.
    /// CEP:WHY: Deletion priority 2 (older deleted first among same LBD) and the total-order tiebreak; the design's third criterion (activity, design 11.6) is structurally unreachable in the strict lexicographic order because ages are unique - the activity score itself stays recorded on the registry entry (S24) and is documented in the comparator.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: unique per candidate.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::age_priority_within_lbd.
    /// CEP:SECURITY: none.
    entry: u32,
}

// CEP:WHAT: Reduction candidate layout pin.
// CEP:WHY: The scratch is a fixed arena array; size drift changes the memory budget silently otherwise (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_keeps_best_half.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<CandidateKey>() == 8);

/// CEP:WHAT: The clause registry: entry array, live counters, reduction trigger, and the heapsort scratch for the deletion policy.
/// CEP:WHY: Design 11.1 S4/S24/S25/S26 and 11.6; owning the entry array, the scratch, and the counters in one type makes the invariants (ascending offsets, tombstone mirrors storage, live counters exact) local and testable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see RegistryError.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs; property/sat_preprocess_property_test.rs.
/// CEP:SECURITY: capacity bounded.
pub struct ClauseRegistry<'a> {
    /// CEP:WHAT: Dense entry array (capacity entries).
    /// CEP:WHY: The enumerable database; entry index is the registration age.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: appended in ascending offset order.
    /// CEP:COST: 16 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
    /// CEP:SECURITY: bounds-checked accesses.
    entries: &'a [RegistryEntry],
    /// CEP:WHAT: Number of entries ever appended (next entry index).
    /// CEP:WHY: Dense allocation cursor; never decreases (indices are stable age ids).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: registration errors at the array capacity.
    /// CEP:ASSUMES: <= entries.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{registry_enumerates, capacity_enforced}.
    /// CEP:SECURITY: capacity bound.
    next_entry: core::cell::Cell<u32>,
    /// CEP:WHAT: Live (non-tombstoned) entry count.
    /// CEP:WHY: Enumeration bound and diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kept exact by register/delete.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_tombstones, registry_enumerates}.
    /// CEP:SECURITY: none.
    live_entries: core::cell::Cell<u32>,
    /// CEP:WHAT: Live learnt-clause count.
    /// CEP:WHY: The reduction trigger input (design 11.6: delete when the database exceeds the learnt budget).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kept exact by register/delete.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_keeps_best_half, reduction_trigger_enforced}.
    /// CEP:SECURITY: none.
    live_learnts: core::cell::Cell<u32>,
    /// CEP:WHAT: Live-learnt count at which reduction fires.
    /// CEP:WHY: Production uses kSatMaxLearntClauses (design 11.6); tests inject small triggers (CEP&CC 34.3: test the mechanism).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1; fixed at construction.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_trigger_enforced.
    /// CEP:SECURITY: none.
    reduction_trigger: u32,
    /// CEP:WHAT: Activity bump increment.
    /// CEP:WHY: The per-conflict activity delta; 1.0 in production, injectable for fast rescale-path tests (same discipline as the VSIDS decay).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: > 0; fixed at construction.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::activity_rescale_preserves_order.
    /// CEP:SECURITY: none.
    activity_increment: f64,
    /// CEP:WHAT: Heapsort scratch: sort keys of live learnt candidates.
    /// CEP:WHY: The deletion policy sorts candidates under the total order; a flat scratch array keeps reduction allocation-free.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized to the entry capacity; used only inside reduce.
    /// CEP:COST: 8 bytes per candidate.
    /// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_keeps_best_half.
    /// CEP:SECURITY: none.
    scratch: &'a [core::cell::Cell<CandidateKey>],
}

impl<'a> ClauseRegistry<'a> {
    // CEP:WHAT: Constructs the registry with the default capacity, trigger, and increment.
    // CEP:WHY: Production entry point; the named constants are the documented defaults.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns RegistryError::Full-mapped errors when the arrays do not fit the arena.
    // CEP:ASSUMES: the arena has room for capacity x 20 bytes.
    // CEP:COST: O(capacity) one-time arena allocation and clear.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
    // CEP:SECURITY: capacity validated before allocation.
    pub fn new(arena: &'a Arena) -> Result<ClauseRegistry<'a>, RegistryError> {
        ClauseRegistry::new_with(arena, kSatRegistryCapacity, kSatMaxLearntClauses, 1.0)
    }

    // CEP:WHAT: Constructs the registry with explicit capacity, reduction trigger, and activity increment.
    // CEP:WHY: CEP&CC 34.3: security and policy tests must exercise the capacity bound, the trigger, and the rescale path at small, fast scales while sharing the production code path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Full-mapped errors when the arrays do not fit; rejects zero capacity, zero trigger, or non-positive increment.
    // CEP:ASSUMES: capacity >= 1, trigger >= 1, increment > 0.
    // CEP:COST: O(capacity) one-time.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{capacity_enforced, reduction_trigger_enforced, activity_rescale_preserves_order}; security/phase3_bounds_test.rs::registry_capacity_enforced.
    // CEP:SECURITY: bounds validated before allocation.
    pub fn new_with(
        arena: &'a Arena,
        capacity: u32,
        reduction_trigger: u32,
        activity_increment: f64,
    ) -> Result<ClauseRegistry<'a>, RegistryError> {
        if capacity == 0 || reduction_trigger == 0 || activity_increment <= 0.0 {
            return Err(RegistryError::InvariantViolation);
        }
        let entry_range = arena
            .alloc_array::<RegistryEntry>(capacity)
            .map_err(|_| RegistryError::Full)?;
        let entries = arena
            .array::<RegistryEntry>(entry_range)
            .map_err(|_| RegistryError::Full)?;
        for entry in entries.iter() {
            entry.offset.set(kInvalidClauseOffset);
            entry.activity.set(0.0);
            entry.tombstone.set(false);
        }
        let scratch_range = arena
            .alloc_array::<core::cell::Cell<CandidateKey>>(capacity)
            .map_err(|_| RegistryError::Full)?;
        let scratch = arena
            .array::<core::cell::Cell<CandidateKey>>(scratch_range)
            .map_err(|_| RegistryError::Full)?;
        Ok(ClauseRegistry {
            entries,
            next_entry: core::cell::Cell::new(0),
            live_entries: core::cell::Cell::new(0),
            live_learnts: core::cell::Cell::new(0),
            reduction_trigger,
            activity_increment,
            scratch,
        })
    }

    // CEP:WHAT: Registers a clause (problem or learnt, decided by the storage header) and returns the entry index.
    // CEP:WHY: CEP-1003: every clause entering the database becomes enumerable; the solver calls this from its add_clause and add_learnt_clause wrappers so registration cannot be forgotten.
    // CEP:STATUS: complete
    // CEP:FAILURE: Full at the capacity; Storage when the header is unreadable; InvariantViolation when the offset breaks the ascending-order invariant or is already deleted.
    // CEP:ASSUMES: offset is a live clause of the paired storage; offsets are registered in creation order.
    // CEP:COST: O(1) plus one header read for the learnt bit.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{registry_enumerates, capacity_enforced}.
    // CEP:SECURITY: capacity bound.
    pub fn register(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<u32, RegistryError> {
        let header = storage.header(offset)?;
        if header.flags & kSatClauseFlagDeleted != 0 {
            return Err(RegistryError::InvariantViolation);
        }
        let index = self.next_entry.get();
        if index as usize >= self.entries.len() {
            return Err(RegistryError::Full);
        }
        if index > 0 && self.entries[index as usize - 1].offset.get() >= offset {
            return Err(RegistryError::InvariantViolation);
        }
        let entry = &self.entries[index as usize];
        entry.offset.set(offset);
        entry.activity.set(0.0);
        entry.tombstone.set(false);
        self.next_entry.set(index + 1);
        self.live_entries.set(self.live_entries.get() + 1);
        if header.flags & kSatClauseFlagLearnt != 0 {
            self.live_learnts.set(self.live_learnts.get() + 1);
        }
        Ok(index)
    }

    // CEP:WHAT: Binary-searches the entry index of a clause offset.
    // CEP:WHY: Deletion and activity bumping arrive by offset; entries are ascending by offset so the search is O(log n) with no side arrays.
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) when the offset was never registered.
    // CEP:ASSUMES: ascending-offset invariant (enforced at register).
    // CEP:COST: O(log entries) compares.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{registry_enumerates, delete_unregistered_rejected}.
    // CEP:SECURITY: none.
    pub fn find(&self, offset: u32) -> Option<u32> {
        let count = self.next_entry.get() as usize;
        let mut low: usize = 0;
        let mut high: usize = count;
        while low < high {
            let mid = low + (high - low) / 2;
            let value = self.entries[mid].offset.get();
            if value < offset {
                low = mid + 1;
            } else if value > offset {
                high = mid;
            } else {
                return Some(mid as u32);
            }
        }
        None
    }

    // CEP:WHAT: Permanently deletes a registered clause: storage deleted mark, entry tombstone, counter updates.
    // CEP:WHY: The single sanctioned permanent-deletion path (S25) so the storage bit and the tombstone can never diverge; proof notification stays with the caller (the solver records the deletion before calling this).
    // CEP:STATUS: complete
    // CEP:FAILURE: InvariantViolation for unregistered or already-deleted offsets; Storage for unreadable records.
    // CEP:ASSUMES: offset is live and registered.
    // CEP:COST: O(log entries) find plus O(1) marking.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_tombstones, double_delete_rejected, delete_unregistered_rejected}.
    // CEP:SECURITY: loud lifecycle failures.
    pub fn delete(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<(), RegistryError> {
        let index = self.find(offset).ok_or(RegistryError::InvariantViolation)?;
        let entry = &self.entries[index as usize];
        if entry.tombstone.get() {
            return Err(RegistryError::InvariantViolation);
        }
        let flags = storage.header_flags(offset)?;
        storage.mark_deleted(offset)?;
        entry.tombstone.set(true);
        self.live_entries.set(self.live_entries.get() - 1);
        if flags & kSatClauseFlagLearnt != 0 {
            self.live_learnts.set(self.live_learnts.get() - 1);
        }
        Ok(())
    }

    // CEP:WHAT: Bumps the activity of a registered clause, rescaling all scores when the ceiling would be exceeded.
    // CEP:WHY: Design 11.1 S24 and 11.6 priority 3; the rescale keeps scores finite and the order total (same discipline as the VSIDS heap, ceiling x factor <= 1).
    // CEP:STATUS: complete
    // CEP:FAILURE: InvariantViolation for unregistered or tombstoned offsets.
    // CEP:ASSUMES: called on live entries only.
    // CEP:COST: O(1) per bump; O(entries) on rescale (amortized negligible: the ceiling is 1e100).
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{bump_raises_activity, activity_rescale_preserves_order}.
    // CEP:SECURITY: none.
    pub fn bump_activity(&self, offset: u32) -> Result<(), RegistryError> {
        let index = self.find(offset).ok_or(RegistryError::InvariantViolation)?;
        let entry = &self.entries[index as usize];
        if entry.tombstone.get() {
            return Err(RegistryError::InvariantViolation);
        }
        let next = entry.activity.get() + self.activity_increment;
        if next > kSatClauseActivityCeiling {
            let used = self.next_entry.get() as usize;
            for other in self.entries[..used].iter() {
                other
                    .activity
                    .set(other.activity.get() * kSatClauseActivityRescaleFactor);
            }
        } else {
            entry.activity.set(next);
        }
        Ok(())
    }

    // CEP:WHAT: Returns the live-learnt count (the reduction trigger input).
    // CEP:WHY: The solver asks after learning whether reduction is due (design 11.6).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_trigger_enforced.
    // CEP:SECURITY: none.
    pub fn live_learnts(&self) -> u32 {
        self.live_learnts.get()
    }

    // CEP:WHAT: Returns the reduction trigger threshold.
    // CEP:WHY: Budget introspection for the solver loop and tests.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::reduction_trigger_enforced.
    // CEP:SECURITY: none.
    pub fn reduction_trigger(&self) -> u32 {
        self.reduction_trigger
    }

    // CEP:WHAT: Returns the number of entries ever appended.
    // CEP:WHY: Enumeration bound for callers (preprocessing, diagnostics).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
    // CEP:SECURITY: none.
    pub fn entry_count(&self) -> u32 {
        self.next_entry.get()
    }

    // CEP:WHAT: Returns the entry record at an index (tombstones included).
    // CEP:WHY: Enumeration API for preprocessing and tests; the caller filters tombstones.
    // CEP:STATUS: complete
    // CEP:FAILURE: InvariantViolation for out-of-range indices (loud, never a panic).
    // CEP:ASSUMES: index < entry_count.
    // CEP:COST: 1 bounds check.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::registry_enumerates.
    // CEP:SECURITY: bounds-checked.
    pub fn entry(&self, index: u32) -> Result<&RegistryEntry, RegistryError> {
        let slot = index as usize;
        if slot >= self.next_entry.get() as usize {
            return Err(RegistryError::InvariantViolation);
        }
        Ok(&self.entries[slot])
    }

    // CEP:WHAT: Runs one database reduction when the trigger is reached: locks reason clauses and the active conflict clause, sorts live unlocked learnts best-first under the design 11.6 total order, deletes the worst live - live/divisor (recording proof deletions first when a recorder is attached), then unlocks.
    // CEP:WHY: Design 11.6 and CEP-1003: bounded learnt database with the three-criteria priority; locking implements S29 (clauses involved in conflict analysis are not deleted); the deterministic heapsort makes the victim set a pure function of the database state (CEP&CC 38.10); the proof notification happens inside the deletion loop so the trace can never miss a database mutation (S41).
    // CEP:STATUS: complete
    // CEP:FAILURE: Storage and InvariantViolation surface loudly; returns Ok(0) when the trigger is not reached (a no-op call is not an error).
    // CEP:ASSUMES: called between conflicts with a quiescent core (no analysis in progress); conflict_offset may be kInvalidClauseOffset when reduction runs outside a conflict (for example from preprocessing).
    // CEP:COST: O(variables) lock marking + O(live log live) heapsort + O(deleted) storage marks; see file header for amortization.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_keeps_best_half, locked_clauses_survive, reduction_trigger_enforced, reduction_marks_deleted, bcp_skips_deleted, reduction_records_proof_deletions}; property/cdcl_property_test.rs::solve_agrees_with_brute_force with reduction enabled via the injected trigger.
    // CEP:SECURITY: all scans are bounded by named capacities.
    pub fn reduce(
        &self,
        core: &SatCore<'_>,
        conflict_offset: u32,
        proof: Option<&crate::sat::proof::ProofRecorder<'_>>,
    ) -> Result<u32, RegistryError> {
        if self.live_learnts.get() < self.reduction_trigger {
            return Ok(0);
        }
        // Lock marking (S29): every reason clause of an assigned variable plus the
        // active conflict clause is locked for the duration of the reduction; locked
        // clauses can never appear as victims, so no surviving reason ever points at
        // a deleted record and no in-flight analysis loses its conflict clause.
        let variables = core.variable_count();
        for variable in 0..variables {
            let reason = core.reason_of(variable);
            if reason != kInvalidClauseOffset {
                self.set_lock_bit(core.clauses(), reason)?;
            }
        }
        let conflict_locked = conflict_offset != kInvalidClauseOffset;
        if conflict_locked {
            self.set_lock_bit(core.clauses(), conflict_offset)?;
        }
        // Collect live, unlocked, learnt candidates into the scratch (one header read
        // per candidate per reduction supplies both the learnt/lock bits and the LBD).
        let mut count: usize = 0;
        let total = self.next_entry.get() as usize;
        for index in 0..total {
            let entry = &self.entries[index];
            if entry.tombstone.get() {
                continue;
            }
            let header = core.clauses().header(entry.offset.get())?;
            if header.flags & kSatClauseFlagLearnt == 0 {
                continue;
            }
            if header.flags & kSatClauseFlagLocked != 0 {
                continue;
            }
            self.scratch[count].set(CandidateKey {
                lbd: header.lbd,
                entry: index as u32,
            });
            count += 1;
        }
        self.heapsort_best_first(count);
        // Keep the best live/divisor; delete the rest (the worst tail), recording each
        // deletion in the proof trace before the storage mark (S41: steps are emitted as
        // clauses are deleted).
        let keep = count / kSatLearntReduceDivisor as usize;
        let mut deleted: u32 = 0;
        for slot in keep..count {
            let index = self.scratch[slot].get().entry;
            let offset = self.entries[index as usize].offset.get();
            if let Some(recorder) = proof {
                recorder.record_delete(offset, core.clauses())?;
            }
            self.delete(core.clauses(), offset)?;
            deleted += 1;
        }
        // Unlock epilogue: clear every lock bit we may have set (reasons re-derived
        // the same way; a deleted record keeps a readable header, so clearing is safe).
        for variable in 0..variables {
            let reason = core.reason_of(variable);
            if reason != kInvalidClauseOffset {
                self.clear_lock_bit(core.clauses(), reason)?;
            }
        }
        if conflict_locked {
            self.clear_lock_bit(core.clauses(), conflict_offset)?;
        }
        Ok(deleted)
    }

    // CEP:WHAT: Deletes every live learnt clause registered at or after the given entry index (recording proof deletions first when a recorder is attached) and returns the deleted count.
    // CEP:WHY: Assumption solves may learn clauses that depend on the temporary assumption units; keeping them would corrupt later incremental solves of the base formula, so solve_with_assumptions snapshots entry_count at entry and deletes everything learnt since on exit (deletion is always sound; the failed core is extracted before cleanup); the entry-index boundary is exact because offsets and entry indices are both monotonic.
    // CEP:STATUS: complete
    // CEP:FAILURE: Storage and Proof errors surface loudly.
    // CEP:ASSUMES: the core is at level 0 (no assignment may reference a victim as its reason - backtrack first); entry_index <= entry_count.
    // CEP:COST: O(entries - entry_index) with one map lookup and one header read per candidate.
    // CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{learnts_do_not_leak_across_solves, repeated_assumption_solves_agree}.
    // CEP:SECURITY: bounded scan.
    pub fn delete_learnts_from(
        &self,
        storage: &ClauseStorage<'_>,
        entry_index: u32,
        proof: Option<&crate::sat::proof::ProofRecorder<'_>>,
    ) -> Result<u32, RegistryError> {
        if entry_index > self.next_entry.get() {
            return Err(RegistryError::InvariantViolation);
        }
        let mut deleted: u32 = 0;
        let mut index = entry_index;
        while index < self.next_entry.get() {
            let entry = &self.entries[index as usize];
            index += 1;
            if entry.tombstone.get() {
                continue;
            }
            let flags = storage.header_flags(entry.offset.get())?;
            if flags & kSatClauseFlagLearnt == 0 {
                continue;
            }
            if let Some(recorder) = proof {
                recorder.record_delete(entry.offset.get(), storage)?;
            }
            self.delete(storage, entry.offset.get())?;
            deleted += 1;
        }
        Ok(deleted)
    }

    // CEP:WHAT: Completes the deletion of a clause already isolated by the raw storage deleted mark: proof notification stays with the caller; this sets the tombstone and counters only.
    // CEP:WHY: Vivification isolates its candidate with the raw mark before knowing whether a shortened replacement exists; when it does, the permanent deletion must finish the already-marked record instead of double-marking (mark_deleted rejects double marks), so the registry exposes the completion half of the deletion protocol (CEP-1003 wording: tombstone unlinking after isolation).
    // CEP:STATUS: complete
    // CEP:FAILURE: InvariantViolation for unregistered or already-tombstoned offsets or a record whose deleted bit is not set; Storage for unreadable records.
    // CEP:ASSUMES: the caller recorded the proof deletion first and the storage deleted bit is set.
    // CEP:COST: O(log entries) find plus O(1) bookkeeping.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::vivification_shortens_clause.
    // CEP:SECURITY: loud lifecycle failures.
    pub fn complete_deletion(
        &self,
        storage: &ClauseStorage<'_>,
        offset: u32,
    ) -> Result<(), RegistryError> {
        let index = self.find(offset).ok_or(RegistryError::InvariantViolation)?;
        let entry = &self.entries[index as usize];
        if entry.tombstone.get() {
            return Err(RegistryError::InvariantViolation);
        }
        let flags = storage.header_flags(offset)?;
        if flags & kSatClauseFlagDeleted == 0 {
            return Err(RegistryError::InvariantViolation);
        }
        entry.tombstone.set(true);
        self.live_entries.set(self.live_entries.get() - 1);
        if flags & kSatClauseFlagLearnt != 0 {
            self.live_learnts.set(self.live_learnts.get() - 1);
        }
        Ok(())
    }

    // CEP:WHAT: Sets the lock bit on a clause header.
    // CEP:WHY: S29 lock discipline during reduction; one idempotent flag write.
    // CEP:STATUS: complete
    // CEP:FAILURE: Storage errors propagate.
    // CEP:ASSUMES: offset is a live record.
    // CEP:COST: one header read plus one flag write.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::locked_clauses_survive.
    // CEP:SECURITY: bounds-checked.
    fn set_lock_bit(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<(), RegistryError> {
        let flags = storage.header_flags(offset)?;
        storage.set_header_flags(offset, flags | kSatClauseFlagLocked)?;
        Ok(())
    }

    // CEP:WHAT: Clears the lock bit on a clause header.
    // CEP:WHY: Reduction epilogue; keeps the bit free for the next round.
    // CEP:STATUS: complete
    // CEP:FAILURE: Storage errors propagate.
    // CEP:ASSUMES: offset is a readable record (may be deleted - unlocking after deletion is harmless because the record is skipped everywhere).
    // CEP:COST: one header read plus one flag write.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::locked_clauses_survive.
    // CEP:SECURITY: bounds-checked.
    fn clear_lock_bit(
        &self,
        storage: &ClauseStorage<'_>,
        offset: u32,
    ) -> Result<(), RegistryError> {
        let flags = storage.header_flags(offset)?;
        storage.set_header_flags(offset, flags & !kSatClauseFlagLocked)?;
        Ok(())
    }

    // CEP:WHAT: Deterministic in-place heapsort of the scratch candidates best-first under the total order (lbd asc, age desc).
    // CEP:WHY: no_std forbids the standard sort (allocation and unstable ordering are both banned); heapsort is deterministic, allocation-free, and O(n log n) worst case; "best-first ascending" places the worst candidates at the tail, which is exactly the victim segment reduce deletes; the order is total because entry indices are unique.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (keys are pre-fetched; no storage reads inside the sort).
    // CEP:ASSUMES: scratch[..count] holds candidate keys.
    // CEP:COST: O(count log count) comparisons, no allocation.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_keeps_best_half, lbd_priority_order, age_priority_within_lbd}.
    // CEP:SECURITY: bounded by the scratch capacity.
    fn heapsort_best_first(&self, count: usize) {
        if count < 2 {
            return;
        }
        let mut start = count / 2;
        loop {
            if start == 0 {
                break;
            }
            start -= 1;
            self.sift_down(start, count);
        }
        let mut end = count;
        while end > 1 {
            end -= 1;
            let head = self.scratch[0].get();
            let tail = self.scratch[end].get();
            self.scratch[0].set(tail);
            self.scratch[end].set(head);
            self.sift_down(0, end);
        }
    }

    // CEP:WHAT: Sift-down helper of the heapsort (max-heap on "badness": a parent is worse than its children, so the worst candidate bubbles to the root and is swapped to the tail).
    // CEP:WHY: Classic bottom-up heapsort inner loop, isolated for auditability; the comparator is a pure function of the two keys (no captures, no dyn).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: root < end.
    // CEP:COST: O(log end) comparisons.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{lbd_priority_order, age_priority_within_lbd, activity_priority_within_lbd}.
    // CEP:SECURITY: bounded loops.
    fn sift_down(&self, root: usize, end: usize) {
        let mut node = root;
        loop {
            let mut candidate = node;
            let left = node * 2 + 1;
            let right = node * 2 + 2;
            if left < end && self.worse(self.scratch[left].get(), self.scratch[candidate].get()) {
                candidate = left;
            }
            if right < end && self.worse(self.scratch[right].get(), self.scratch[candidate].get()) {
                candidate = right;
            }
            if candidate == node {
                return;
            }
            let held = self.scratch[node].get();
            let moved = self.scratch[candidate].get();
            self.scratch[node].set(moved);
            self.scratch[candidate].set(held);
            node = candidate;
        }
    }

    // CEP:WHAT: Deletion-order comparator: true when left is a worse candidate than right (higher LBD; on LBD ties older age).
    // CEP:WHY: Design 11.6 priority list verbatim (LBD desc, age asc, activity asc); the age field (unique entry index) already decides every LBD tie, so the third criterion (activity) is structurally unreachable in the strict lexicographic reading - the design's own ordering makes it vacuous, which is documented here instead of silently reordering the keys (the activity score stays recorded for S24 and becomes decisive only if the age key is ever relaxed); the unique-index comparison makes the order total, so the heapsort output is deterministic.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: keys carry unique entry indices.
    // CEP:COST: 1-2 comparisons.
    // CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{lbd_priority_order, age_priority_within_lbd}.
    // CEP:SECURITY: none.
    fn worse(&self, left: CandidateKey, right: CandidateKey) -> bool {
        if left.lbd != right.lbd {
            return left.lbd > right.lbd;
        }
        left.entry < right.entry
    }
}
