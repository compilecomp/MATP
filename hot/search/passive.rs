// CEP:FILE: hot/search/passive.rs
// CEP:WHAT: The passive set (design 8.4): a flat binary min-heap of pending clauses keyed by the selection strategy's priority with clause-id tiebreak, supporting the design 15.2 strategies (age/weight ratio, weight-only, age-only).
// CEP:WHY: Design 8.4: the passive set is a priority queue ordered by (age, weight, clause id) implemented as a flat arena array with O(log n) insertion and extraction and no allocation per insertion; design 15.2 names three deterministic strategies - the default age/weight ratio (priority = age * scale / weight in u64 fixed point: old light clauses win, and because age grows monotonically with the birth order while weights are positive, every clause's priority is fixed at birth, so finitely many clauses can precede any given one under bounded weight growth and selection is fair up to that documented bound), weight-only, and age-only (trivially fair breadth-first); the clause-id tiebreak makes the heap order total and the selection deterministic (CEP&CC 38.10), which is what the design's fairness claim (15.1) and the determinism gate rely on.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SearchError::PassiveFull at the capacity; never panics.
// CEP:ASSUMES: Clause ids are strictly increasing across pushes (the clause store's monotonic counter); priorities are computed once at push and never recomputed.
// CEP:COST: push and pop are O(log n) swaps of 24-byte entries; measured within bench CEP-BENCH-0011, artifact benches/artifacts/atp_passive_step.json.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_weight, heap_orders_by_age, tie_breaks_by_clause_id, capacity_enforced}; property/given_clause_property_test.rs::selection_is_deterministic.
// CEP:SECURITY: capacity is a memory-exhaustion bound.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the total heap key (priority, clause id) makes the pop order a pure function of the push sequence.
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 4 fixes the priority functions and the fairness argument (age-monotone priorities with positive weights admit only finitely many predecessors per clause under bounded weight growth; age-only is unconditionally fair), and the heap invariants (parent key <= child keys) are property-tested.

use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::{kPassiveHeapCapacity, kSelectionRatioScale};

// CEP:WHAT: Arity of the passive heap's binary heap (children of index i sit at 2i+1 and 2i+2).
// CEP:WHY: The parent and child index arithmetic names its base (CEP&CC 11.3), matching the VSIDS and registry heap discipline.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, tie_breaks_by_clause_id}.
// CEP:SECURITY: none.
const kPassiveHeapArity: usize = 2;

/// CEP:WHAT: The default selection strategy (the design 15.2 default row).
/// CEP:WHY: SearchOptions derives Default; the documented default is the age/weight ratio.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
/// CEP:SECURITY: none.
impl Default for SelectionStrategy {
    // CEP:WHAT: The default strategy (AgeWeightRatio).
    // CEP:WHY: Design 15.2 row 1 is the default.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    // CEP:SECURITY: none.
    fn default() -> Self {
        SelectionStrategy::AgeWeightRatio
    }
}

/// CEP:WHAT: Selection strategy of the given-clause loop (design 15.2).
/// CEP:WHY: The strategy fixes the priority function; three deterministic strategies are delivered and the remaining two of design 15.2 (conjecture distance, set of support) are ticketed with owners (CEP-1035).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: fixed for the lifetime of one search.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_weight, heap_orders_by_age}.
/// CEP:SECURITY: none.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectionStrategy {
    /// CEP:WHAT: Minimum age/weight ratio (the design default).
    /// CEP:WHY: Design 15.2 row 1.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: weights >= 1 (the weight function guarantees this: every symbol carries at least the default weight).
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    /// CEP:SECURITY: none.
    AgeWeightRatio,
    /// CEP:WHAT: Minimum weight.
    /// CEP:WHY: Design 15.2 row 3; not fair in isolation (documented in Spec 08 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_weight.
    /// CEP:SECURITY: none.
    WeightOnly,
    /// CEP:WHAT: Minimum age (breadth-first).
    /// CEP:WHY: Design 15.2 row 4; trivially fair.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_age.
    /// CEP:SECURITY: none.
    AgeOnly,
}

// CEP:WHAT: Error cases of the passive heap.
// CEP:WHY: CEP&CC Law 6 vocabulary; the heap never panics.
// CEP:STATUS: complete
// CEP:FAILURE: none; this type IS the failure vocabulary.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::capacity_enforced.
// CEP:SECURITY: capacity is the memory boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassiveError {
    /// CEP:WHAT: The heap capacity is exhausted.
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::capacity_enforced; security/phase3_bounds_test.rs::passive_capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Full,
}

/// CEP:WHAT: One passive-set entry: the computed priority, the clause id (total tiebreak), and the clause offset.
/// CEP:WHY: Design 8.4: the key is (priority, clause_id) so the order is total and deterministic; the offset addresses the clause record for the pop consumer; 24 bytes keeps entries copyable for heap swaps.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: ids unique and monotonic across pushes.
/// CEP:COST: 24 bytes.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, tie_breaks_by_clause_id}.
/// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub struct PassiveEntry {
    /// CEP:WHAT: Strategy priority (smaller pops first).
    /// CEP:WHY: The heap key's first component.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: computed at push.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_weight, heap_orders_by_age}.
    /// CEP:SECURITY: none.
    pub priority: u64,
    /// CEP:WHAT: Clause id (smaller = older = pops first on priority ties).
    /// CEP:WHY: Total-order tiebreak (design 8.4 "ties are broken by clause ID").
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: unique.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::tie_breaks_by_clause_id.
    /// CEP:SECURITY: none.
    pub clause_id: u64,
    /// CEP:WHAT: Clause record offset.
    /// CEP:WHY: The pop consumer reads the clause through the store.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: produced by the clause store.
    /// CEP:COST: 4 bytes plus padding.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    /// CEP:SECURITY: bounds-checked on use.
    pub offset: u32,
}

/// CEP:WHAT: The passive-set min-heap.
/// CEP:WHY: Design 8.4; a flat arena array with sift-up/sift-down keeps insertion and extraction allocation-free and cache-friendly.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see PassiveError.
/// CEP:ASSUMES: single-threaded; the strategy is fixed at construction.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs; property/given_clause_property_test.rs::selection_is_deterministic.
/// CEP:SECURITY: capacity bounded.
pub struct PassiveHeap<'a> {
    /// CEP:WHAT: Entry array (heap order).
    /// CEP:WHY: Flat storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: push errors at the capacity.
    /// CEP:ASSUMES: entries[..count] is a valid min-heap.
    /// CEP:COST: 24 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, capacity_enforced}.
    /// CEP:SECURITY: capacity bound.
    entries: &'a [Cell<PassiveEntry>],
    /// CEP:WHAT: Number of live entries.
    /// CEP:WHY: Heap extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= entries.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    /// CEP:SECURITY: bounds checks on every access.
    count: Cell<u32>,
    /// CEP:WHAT: The selection strategy.
    /// CEP:WHY: Fixes the priority function.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed at construction.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_weight, heap_orders_by_age}.
    /// CEP:SECURITY: none.
    strategy: SelectionStrategy,
}

impl<'a> PassiveHeap<'a> {
    // CEP:WHAT: Constructs the heap with the default capacity and the given strategy.
    // CEP:WHY: Production entry point.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Full when the array does not fit the arena.
    // CEP:ASSUMES: arena has room for kPassiveHeapCapacity entries.
    // CEP:COST: O(capacity) one-time allocation.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    // CEP:SECURITY: capacity validated before allocation.
    pub fn new(
        arena: &'a Arena,
        strategy: SelectionStrategy,
    ) -> Result<PassiveHeap<'a>, PassiveError> {
        PassiveHeap::new_with(arena, kPassiveHeapCapacity, strategy)
    }

    // CEP:WHAT: Constructs the heap with an explicit capacity.
    // CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Full when the array does not fit; rejects zero capacity.
    // CEP:ASSUMES: capacity >= 1.
    // CEP:COST: O(capacity) one-time.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::capacity_enforced; security/phase3_bounds_test.rs::passive_capacity_enforced.
    // CEP:SECURITY: bounds validated.
    pub fn new_with(
        arena: &'a Arena,
        capacity: u32,
        strategy: SelectionStrategy,
    ) -> Result<PassiveHeap<'a>, PassiveError> {
        if capacity == 0 {
            return Err(PassiveError::Full);
        }
        let range = arena
            .alloc_array::<Cell<PassiveEntry>>(capacity)
            .map_err(|_| PassiveError::Full)?;
        let entries = arena
            .array::<Cell<PassiveEntry>>(range)
            .map_err(|_| PassiveError::Full)?;
        Ok(PassiveHeap {
            entries,
            count: Cell::new(0),
            strategy,
        })
    }

    // CEP:WHAT: Computes the strategy priority of one clause.
    // CEP:WHY: The priority is fixed at birth (age = birth order, weight = the selection weight function's value), which is what makes the order deterministic and the fairness argument of Spec 08 section 4 applicable.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (weight 0 saturates to priority age * scale - documented, cannot occur because the weight function's minimum is the default symbol weight of 1).
    // CEP:ASSUMES: age and weight are the clause's birth values.
    // CEP:COST: one multiply and one divide.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, heap_orders_by_weight, heap_orders_by_age}.
    // CEP:SECURITY: none.
    pub fn priority_of(&self, age: u32, weight: u32) -> u64 {
        match self.strategy {
            SelectionStrategy::AgeWeightRatio => {
                let denominator = if weight == 0 { 1 } else { weight as u64 };
                (age as u64).saturating_mul(kSelectionRatioScale) / denominator
            }
            SelectionStrategy::WeightOnly => weight as u64,
            SelectionStrategy::AgeOnly => age as u64,
        }
    }

    // CEP:WHAT: Pushes a clause into the heap.
    // CEP:WHY: The passive-set insertion (design 8.4); sift-up restores the heap invariant.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Full at the capacity.
    // CEP:ASSUMES: clause_id strictly greater than every pushed id.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, capacity_enforced}.
    // CEP:SECURITY: capacity bound.
    pub fn push(
        &self,
        clause_id: u64,
        offset: u32,
        age: u32,
        weight: u32,
    ) -> Result<(), PassiveError> {
        let next = self.count.get() as usize;
        if next >= self.entries.len() {
            return Err(PassiveError::Full);
        }
        self.entries[next].set(PassiveEntry {
            priority: self.priority_of(age, weight),
            clause_id,
            offset,
        });
        self.count.set(self.count.get() + 1);
        self.sift_up(next);
        Ok(())
    }

    // CEP:WHAT: Pops the best entry (minimum (priority, clause_id)).
    // CEP:WHY: The given-clause selection step (design 15.1 step 1).
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) when the heap is empty (the search is saturated).
    // CEP:ASSUMES: none.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, tie_breaks_by_clause_id}.
    // CEP:SECURITY: none.
    pub fn pop(&self) -> Option<PassiveEntry> {
        let count = self.count.get() as usize;
        if count == 0 {
            return None;
        }
        let best = self.entries[0].get();
        let last = count - 1;
        self.entries[0].set(self.entries[last].get());
        self.count.set(last as u32);
        if last > 0 {
            self.sift_down(0);
        }
        Some(best)
    }

    // CEP:WHAT: Returns the number of pending clauses.
    // CEP:WHY: Saturation detection and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_ratio.
    // CEP:SECURITY: none.
    pub fn len(&self) -> u32 {
        self.count.get()
    }

    // CEP:WHAT: Returns whether the heap holds no pending clauses.
    // CEP:WHY: The len/is_empty pair discipline (CEP&CC lint); the loop's saturation check and the tests read it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::heap_orders_by_key.
    // CEP:SECURITY: none.
    pub fn is_empty(&self) -> bool {
        self.count.get() == 0
    }

    // CEP:WHAT: Sift-up helper (min-heap on (priority, clause_id)).
    // CEP:WHY: Restores the invariant after push.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: entries[..count] is a heap except possibly at index.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, tie_breaks_by_clause_id}.
    // CEP:SECURITY: none.
    fn sift_up(&self, mut index: usize) {
        while index > 0 {
            let parent = (index - 1) / kPassiveHeapArity;
            let child_entry = self.entries[index].get();
            let parent_entry = self.entries[parent].get();
            if (child_entry.priority, child_entry.clause_id)
                < (parent_entry.priority, parent_entry.clause_id)
            {
                self.entries[index].set(parent_entry);
                self.entries[parent].set(child_entry);
                index = parent;
            } else {
                return;
            }
        }
    }

    // CEP:WHAT: Sift-down helper (min-heap on (priority, clause_id)).
    // CEP:WHY: Restores the invariant after pop.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: entries[..count] is a heap except possibly at index.
    // CEP:COST: O(log n).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_ratio, tie_breaks_by_clause_id}.
    // CEP:SECURITY: none.
    fn sift_down(&self, mut index: usize) {
        let count = self.count.get() as usize;
        loop {
            let mut best = index;
            let left = index * kPassiveHeapArity + 1;
            let right = left + 1;
            if left < count {
                let left_entry = self.entries[left].get();
                let best_entry = self.entries[best].get();
                if (left_entry.priority, left_entry.clause_id)
                    < (best_entry.priority, best_entry.clause_id)
                {
                    best = left;
                }
            }
            if right < count {
                let right_entry = self.entries[right].get();
                let best_entry = self.entries[best].get();
                if (right_entry.priority, right_entry.clause_id)
                    < (best_entry.priority, best_entry.clause_id)
                {
                    best = right;
                }
            }
            if best == index {
                return;
            }
            let held = self.entries[index].get();
            let moved = self.entries[best].get();
            self.entries[index].set(moved);
            self.entries[best].set(held);
            index = best;
        }
    }
}
