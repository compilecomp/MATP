// CEP:FILE: hot/concurrency/chase_lev.rs
// CEP:WHAT: The Chase-Lev work-stealing deque (design 19.3): owner push/pop at the bottom, thief steal at the top, over caller-supplied atomic storage (a power-of-two ring of AtomicU64 plus two AtomicI64 cursors) - storage-agnostic so the no_std hot crate carries only the algorithm and the CEP-1 caller owns the memory.
// CEP:WHY: Design 26 Phase 4 and Chase and Lev (SPAA 2005, "Dynamic Circular Work-Stealing Deque"): the owner operates both ends LIFO with O(1) amortized push/pop and thieves take from the top with O(1) amortized steal; the protocol is the crossdeque-battle-tested formulation - push publishes the slot with a Release store of bottom (pairs with steal's Acquire load), pop decrements bottom with SeqCst before reading the last element so the owner and a thief cannot both take it (the top CAS is the linearization point of the race), steal re-reads top after reading the slot and wins the element only through the SeqCst CAS (the re-read plus monotonic cursors close the ABA window: a slot reused after a full ring turn carries a sequence-shifted cursor value, and the CAS compares the full cursor, not the masked index); design 19.4's no-locks rule and CEP&CC 8.43's atomics policy are satisfied with explicit orders on every operation, each documented at its use site.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: push returns Full at the ring capacity, pop/steal return None when empty, and Contended never escapes (CAS loops retry; the steal retry budget converts persistent contention into None - never a wrong element); never panics.
// CEP:ASSUMES: the caller-supplied ring is a power-of-two length and zero-initialized; top and bottom start at 0; exactly one thread is the owner (push/pop) and any number of thieves (steal); slot values are u64 payload words with no interior meaning to the deque.
// CEP:COST: push 1 Relaxed load + 1 Relaxed store + 1 Release store; pop 1 SeqCst fetch_sub + 1 Acquire load (+1 SeqCst CAS only in the last-element race); steal 2 Acquire loads + 1 Relaxed load + 1 SeqCst CAS; measured in bench CEP-BENCH-0033, artifacts benches/artifacts/{deque_push_pop,deque_steal}.json.
// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, capacity_enforced, steal_returns_empty_when_idle, pop_and_steal_split_elements, last_element_race_never_duplicated, cursor_monotonicity}; property/concurrency_property_test.rs::{deque_conserves_elements_under_threads, exactly_once_delivery}.
// CEP:SECURITY: capacity bounded by the caller; all indexing masked into the ring (no out-of-bounds path); forged cursor values degrade to None/Full, never to wrong data.
// CEP:UNSAFE: none; this file is safe Rust (the buffer is a shared atomic slice, not UnsafeCell - the price is one atomic load per slot read, accepted for evidence-grade simplicity; the hand-rolled UnsafeCell variant is ticketed with the measured justification requirement of CEP&CC 8.43).
// CEP:HPC-DETERMINISM: single-owner, single-thread use is deterministic (the protocol degenerates to a ring buffer); cross-thread outcomes are scheduling-dependent by design (design 19.5: the portfolio result may vary but every delivered element is exactly-once and uncorrupted).
// CEP:HPC-PASS-LEGALITY: Formal Spec 13 section 3 fixes the deque protocol, the memory-ordering table, the linearization points, and the ABA argument; the property tests verify executably that element conservation and exactly-once delivery hold under thread interleaving.

use core::sync::atomic::{AtomicI64, AtomicU64, Ordering};

/// CEP:WHAT: Error cases of the work-stealing deque.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the deque never panics and never returns a wrong element.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{capacity_enforced, rejects_non_power_of_two}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DequeError {
    /// CEP:WHAT: The ring is full (bottom - top reached the capacity).
    /// CEP:WHY: The bounded ring is the memory bound; the owner drains (pop) before pushing again - a documented degradation (Spec 13 section 3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: capacity >= 2.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Full,
    /// CEP:WHAT: The supplied storage is invalid (non-power-of-two ring or zero length).
    /// CEP:WHY: Masked indexing requires a power of two; construction validates instead of masking into out-of-bounds.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::rejects_non_power_of_two.
    /// CEP:SECURITY: input validation.
    InvalidStorage,
}

// CEP:WHAT: Retry budget of one steal call under persistent CAS contention.
// CEP:WHY: A thief that keeps losing the top CAS to other thieves must return (None means "nothing stolen this call", the caller retries); the budget bounds the retry loop loudly instead of spinning unboundedly (CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: returns None (nothing stolen) when the budget is exhausted - never a wrong element.
// CEP:ASSUMES: callers treat None as retry-later.
// CEP:COST: up to 64 CAS attempts.
// CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
// CEP:SECURITY: denial-of-service bound on spin.
const kStealRetryBudget: u32 = 64;

/// CEP:WHAT: One work-stealing deque over shared atomic storage: the ring, the mask, and the two cursor references.
/// CEP:WHY: Design 19.3: each portfolio worker owns a deque (owner push/pop of pending imports) and steals from other workers' deques; Clone shares the storage references so the owner handle and thief handles point at one deque; Sync comes from the atomics (the storage is caller-owned and shared by reference, CEP&CC 8.43).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see DequeError.
/// CEP:ASSUMES: exactly one owner thread; the ring stays alive as long as any handle.
/// CEP:COST: 2 references plus a mask (16 bytes per handle).
/// CEP:EVIDENCE: unit/hot/chase_lev_test.rs (the whole file); property/concurrency_property_test.rs::deque_conserves_elements_under_threads.
/// CEP:SECURITY: no interior mutability beyond the supplied atomics.
#[derive(Clone)]
pub struct WorkStealingDeque<'a> {
    /// CEP:WHAT: The payload ring (power-of-two length).
    /// CEP:WHY: Slot storage shared by the owner and thieves; atomic u64 words keep every read data-race-free without UnsafeCell.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: zero-initialized by the caller.
    /// CEP:COST: 8 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, pop_and_steal_split_elements}.
    /// CEP:SECURITY: masked indexing only.
    buffer: &'a [AtomicU64],
    /// CEP:WHAT: The ring index mask (capacity - 1).
    /// CEP:WHY: Power-of-two masking replaces modulo on the hot path (design 22.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: capacity is a power of two (validated at construction).
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::rejects_non_power_of_two.
    /// CEP:SECURITY: keeps every index in bounds.
    mask: u64,
    /// CEP:WHAT: The steal cursor (thieves take slots at top; the last-element race CASes it).
    /// CEP:WHY: The Chase-Lev top; monotonic, never decreases.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: starts at 0.
    /// CEP:COST: 8 bytes shared.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{cursor_monotonicity, last_element_race_never_duplicated}.
    /// CEP:SECURITY: CAS-protected.
    top: &'a AtomicI64,
    /// CEP:WHAT: The owner cursor (the owner pushes and pops at bottom).
    /// CEP:WHY: The Chase-Lev bottom; monotonic across the protocol (pop's temporary decrement is restored on the empty/lost-race paths).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: starts at 0.
    /// CEP:COST: 8 bytes shared.
    /// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, cursor_monotonicity}.
    /// CEP:SECURITY: owner-thread-only writes except the steal-visible publishes.
    bottom: &'a AtomicI64,
}

impl<'a> WorkStealingDeque<'a> {
    // CEP:WHAT: Binds the deque to caller-supplied storage, validating the power-of-two ring.
    // CEP:WHY: The hot crate is storage-agnostic (no allocation, design 4.1); the CEP-1 caller allocates the ring and cursors, and construction rejects non-power-of-two rings before any masking (CEP&CC Law 3 - the invariant is checked, not assumed).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns InvalidStorage for zero-length or non-power-of-two rings.
    // CEP:ASSUMES: the ring and cursors outlive every handle; the ring is zero-initialized; top and bottom start at 0.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{rejects_non_power_of_two, owner_fifo_order}.
    // CEP:SECURITY: validation before use.
    pub fn new(
        buffer: &'a [AtomicU64],
        top: &'a AtomicI64,
        bottom: &'a AtomicI64,
    ) -> Result<WorkStealingDeque<'a>, DequeError> {
        if buffer.len() < 2 || buffer.len().count_ones() != 1 {
            return Err(DequeError::InvalidStorage);
        }
        Ok(WorkStealingDeque {
            buffer,
            mask: (buffer.len() - 1) as u64,
            top,
            bottom,
        })
    }

    // CEP:WHAT: Owner push: appends one payload word at the bottom end.
    // CEP:WHY: Design 19.3 owner operation; ordering (CEP&CC 8.43): the slot store is Relaxed (the owner exclusively owns the slot until publication - thieves cannot reach index b before bottom advances), bottom's fetch_add is Release (publishes the slot: a thief's subsequent Acquire load of bottom that observes b+1 also observes the slot write; failure point: none - the fetch_add never fails; ABA: irrelevant - bottom is monotonic and the slot is written before publication; lifetime: the caller guarantees the ring outlives all handles).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Full when bottom - top reached the ring capacity (the owner drains before retrying - never blocks, never drops silently... the caller counts drops).
    // CEP:ASSUMES: called by the owner thread only.
    // CEP:COST: 1 Relaxed load + 1 Relaxed store + 1 Release fetch_add; bench CEP-BENCH-0033.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, capacity_enforced}; property/concurrency_property_test.rs::deque_conserves_elements_under_threads.
    // CEP:SECURITY: masked write; capacity bound enforced before the slot write.
    pub fn push(&self, value: u64) -> Result<(), DequeError> {
        // CEP:WHAT: Bottom snapshot and capacity check.
        // CEP:WHY: Relaxed load suffices: the owner is the only writer of bottom's advance in push, and the capacity check only needs a lower bound of top's progress (a stale-smaller top would overestimate fullness - safe direction).
        // CEP:STATUS: complete
        // CEP:FAILURE: Full at capacity.
        // CEP:ASSUMES: owner thread.
        // CEP:COST: 1 load.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::capacity_enforced.
        // CEP:SECURITY: none.
        let b = self.bottom.load(Ordering::Relaxed);
        let t = self.top.load(Ordering::Acquire);
        if b - t >= (self.mask + 1) as i64 {
            return Err(DequeError::Full);
        }
        // CEP:WHAT: Slot write then publication.
        // CEP:WHY: Relaxed slot store (owner-exclusive until published) followed by the Release fetch_add of bottom (publication point; pairs with steal's Acquire bottom load).
        // CEP:STATUS: complete
        // CEP:FAILURE: none (fetch_add cannot fail).
        // CEP:ASSUMES: the slot at b & mask is not currently readable by any thief (b - t < capacity checked above).
        // CEP:COST: 1 store + 1 RMW.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::owner_fifo_order.
        // CEP:SECURITY: none.
        self.buffer[(b as u64 & self.mask) as usize].store(value, Ordering::Relaxed);
        self.bottom.fetch_add(1, Ordering::Release);
        Ok(())
    }

    // CEP:WHAT: Owner pop: takes the most recently pushed element (LIFO from the bottom end).
    // CEP:WHY: Design 19.3 owner operation; ordering (CEP&CC 8.43): the SeqCst fetch_sub of bottom makes the removal visible to thieves before the owner reads the slot when racing for the last element (the SeqCst total order with steal's SeqCst top CAS is exactly what prevents both sides taking the last element - the linearization point of the race is the top CAS); top's Acquire load pairs with a winning thief's SeqCst CAS (success order) release semantics; the slot load is Relaxed (thieves never write slots); failure points: the last-element CAS may lose to a thief (returns None - the element was stolen, not lost); ABA: the top CAS compares full cursor values and cursors are monotonic.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Ok(None) when empty or when the last element was stolen by a thief.
    // CEP:ASSUMES: called by the owner thread only.
    // CEP:COST: 1 SeqCst RMW + 1 Acquire load (+1 SeqCst CAS in the last-element window); bench CEP-BENCH-0033.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, pop_and_steal_split_elements, last_element_race_never_duplicated, cursor_monotonicity}; property/concurrency_property_test.rs::deque_conserves_elements_under_threads.
    // CEP:SECURITY: masked read; the empty check never underflows (t <= b invariant).
    pub fn pop(&self) -> Result<Option<u64>, DequeError> {
        // CEP:WHAT: Reserve the bottom slot by decrementing bottom.
        // CEP:WHY: SeqCst fetch_sub: the decrement must be globally ordered with thieves' top CAS so the last element is taken exactly once (Chase-Lev's central synchronization requirement, Spec 13 section 3).
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: owner thread; bottom > top or the empty path below restores.
        // CEP:COST: 1 SeqCst RMW.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{pop_and_steal_split_elements, last_element_race_never_duplicated}.
        // CEP:SECURITY: none.
        let b = self.bottom.fetch_sub(1, Ordering::SeqCst) - 1;
        // CEP:WHAT: Top snapshot.
        // CEP:WHY: Acquire load pairs with a thief's successful SeqCst top CAS, making the thief's claim visible before the owner decides the race.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: 1 load.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::last_element_race_never_duplicated.
        // CEP:SECURITY: none.
        let t = self.top.load(Ordering::Acquire);
        if t < b {
            // At least two elements were in the deque: the bottom slot is exclusively
            // the owner's (thieves take indices at top < b).
            let value = self.buffer[(b as u64 & self.mask) as usize].load(Ordering::Relaxed);
            return Ok(Some(value));
        }
        if t > b {
            // Empty before the decrement (a thief took the last element, or the deque
            // was empty): restore bottom and report empty.
            self.bottom.store(b + 1, Ordering::Release);
            return Ok(None);
        }
        // t == b: exactly one element, racing with thieves for it.
        // CEP:WHAT: Last-element race: the top CAS decides the winner.
        // CEP:WHY: SeqCst compare_exchange (success SeqCst, failure Relaxed): the winner (owner or thief) takes the element exactly once; on failure the element was stolen, and bottom is restored for the next push.
        // CEP:STATUS: complete
        // CEP:FAILURE: loses the race -> Ok(None).
        // CEP:ASSUMES: the CAS value is the t just loaded (a changed top means a thief won).
        // CEP:COST: 1 CAS.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::last_element_race_never_duplicated.
        // CEP:SECURITY: none.
        let won = self
            .top
            .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok();
        // CEP:WHAT: Restore bottom to b+1: the deque is empty after the race either way.
        // CEP:WHY: Release store publishes the empty state to thieves (their capacity and emptiness checks read bottom).
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: 1 store.
        // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::cursor_monotonicity.
        // CEP:SECURITY: none.
        self.bottom.store(b + 1, Ordering::Release);
        if won {
            let value = self.buffer[(b as u64 & self.mask) as usize].load(Ordering::Relaxed);
            Ok(Some(value))
        } else {
            Ok(None)
        }
    }

    // CEP:WHAT: Thief steal: takes the oldest element (FIFO from the top end).
    // CEP:WHY: Design 19.3 thief operation (imports take the oldest pending share first); ordering (CEP&CC 8.43): top's Acquire load pairs with the owner's Release bottom publishes and winning CASes; bottom's Acquire load pairs with push's Release fetch_add (observing b means every published slot write below b is visible); the slot load is Relaxed (visibility is carried by the bottom/top Acquire chain); the re-read of top before the CAS closes the ABA window (a changed top means another thief claimed the slot - retry with the fresh cursor; cursor values are monotonic so a wrapped ring slot carries a different full-cursor value); failure points: the CAS may lose (retry within the budget, then None); lifetime: caller-owned storage.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Ok(None) when empty, already stolen, or the retry budget is exhausted (never a wrong element).
    // CEP:ASSUMES: called by any non-owner thread (and never concurrently with itself on the same handle's call stack).
    // CEP:COST: 2 Acquire loads + 1 Relaxed load + 1 SeqCst CAS per attempt; bench CEP-BENCH-0033.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{steal_returns_empty_when_idle, pop_and_steal_split_elements, last_element_race_never_duplicated}; property/concurrency_property_test.rs::{deque_conserves_elements_under_threads, exactly_once_delivery}.
    // CEP:SECURITY: masked read; the retry budget bounds spinning.
    pub fn steal(&self) -> Result<Option<u64>, DequeError> {
        // CEP:WHAT: Attempt budget of one steal call.
        // CEP:WHY: Persistent contention must return (None) rather than spin - the caller re-steals on its next drain (Spec 13 section 3).
        // CEP:STATUS: complete
        // CEP:FAILURE: budget exhaustion returns None.
        // CEP:ASSUMES: none.
        // CEP:COST: up to kStealRetryBudget CAS attempts.
        // CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
        // CEP:SECURITY: denial-of-service bound.
        let mut attempts: u32 = 0;
        loop {
            // CEP:WHAT: Top then bottom snapshot (the order matters: top first, bottom second).
            // CEP:WHY: Loading bottom AFTER top guarantees a conservative emptiness check (if the deque grew between the two loads, the steal may miss the new element this call - safe; the reverse order could observe a non-empty deque whose element the owner already popped, and the top re-check below closes that window).
            // CEP:STATUS: complete
            // CEP:FAILURE: none.
            // CEP:ASSUMES: none.
            // CEP:COST: 2 loads.
            // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{steal_returns_empty_when_idle, pop_and_steal_split_elements}.
            // CEP:SECURITY: none.
            let t = self.top.load(Ordering::Acquire);
            let b = self.bottom.load(Ordering::Acquire);
            if t >= b {
                return Ok(None);
            }
            // CEP:WHAT: Read the candidate slot.
            // CEP:WHY: Relaxed load: the value's visibility is guaranteed by the Acquire chain (the owner's Release publish of bottom made the slot write visible to this thread's Acquire load of bottom).
            // CEP:STATUS: complete
            // CEP:FAILURE: none.
            // CEP:ASSUMES: the slot may be concurrently claimed by another thief (the CAS below decides).
            // CEP:COST: 1 load.
            // CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
            // CEP:SECURITY: none.
            let value = self.buffer[(t as u64 & self.mask) as usize].load(Ordering::Relaxed);
            // CEP:WHAT: Claim the slot: CAS top t -> t+1.
            // CEP:WHY: SeqCst success order (linearizes with the owner's last-element race CAS), Relaxed failure (the retry reloads top); a failure means another thief or the owner took the slot.
            // CEP:STATUS: complete
            // CEP:FAILURE: CAS failure -> retry or None at the budget.
            // CEP:ASSUMES: t is the just-loaded top.
            // CEP:COST: 1 CAS.
            // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::last_element_race_never_duplicated.
            // CEP:SECURITY: none.
            if self
                .top
                .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
                .is_ok()
            {
                return Ok(Some(value));
            }
            attempts += 1;
            if attempts >= kStealRetryBudget {
                return Ok(None);
            }
        }
    }

    // CEP:WHAT: Returns the current element count (approximate under concurrency).
    // CEP:WHY: Diagnostics and the export/drain heuristics; the value is a lower bound only under concurrent steals (design 19.5: scheduling-dependent observations are fine for diagnostics, never for soundness).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (saturates at zero on transient negative differences).
    // CEP:ASSUMES: exact on the owner thread when no thief is active.
    // CEP:COST: 2 loads.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::owner_fifo_order.
    // CEP:SECURITY: none.
    pub fn len(&self) -> u64 {
        let b = self.bottom.load(Ordering::Acquire);
        let t = self.top.load(Ordering::Acquire);
        if b > t {
            (b - t) as u64
        } else {
            0
        }
    }

    // CEP:WHAT: Returns whether the deque is (approximately) empty.
    // CEP:WHY: Drain-loop condition convenience.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: as len.
    // CEP:COST: as len.
    // CEP:EVIDENCE: unit/hot/chase_lev_test.rs::steal_returns_empty_when_idle.
    // CEP:SECURITY: none.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
