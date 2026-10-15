// CEP:FILE: hot/concurrency/mpmc_pool.rs
// CEP:WHAT: The bounded lock-free MPMC clause-sharing pool (design 19.2): a Vyukov-style array queue of fixed-size u64-word records over caller-supplied atomic storage - per-cell sequence numbers, a produce cursor, and a consume cursor - multi-producer, multi-consumer, exactly-once delivery.
// CEP:WHY: Design 26 Phase 4 and Vyukov's bounded MPMC queue algorithm: each cell carries a sequence number (initialized to its index); a producer claims a cell by CASing the produce cursor (Relaxed - the claim is exclusive but unordered), writes the record words (Relaxed - the cell is exclusively the producer's until the sequence publish), and publishes by storing seq = pos+1 (Release - pairs with every consumer's Acquire seq load, making the record words visible); a consumer claims by CASing the consume cursor and re-publishes seq = pos + capacity (Release) to recycle the cell exactly one full ring turn later (the next produce position mapping to the cell); the full/empty checks compare the cell's sequence against the cursor positions (seq == pos: empty-and-reachable; seq < pos: the cell still holds an unconsumed older turn - full; seq == pos+1: a published record); ABA is impossible because claims advance monotonic cursors and recycling requires a full turn plus the sequence publish; CEP&CC 8.43 is satisfied with explicit orders at every operation, documented at each use site.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: enqueue returns Full at capacity (the exporter counts the drop - never silent) and InvalidStorage for malformed storage; dequeue returns None when empty or contention-exhausted (never a wrong or duplicated record); never panics.
// CEP:ASSUMES: the caller-supplied storage is a power-of-two cell count with kSharedClauseMaxWords word slots per cell, sequence numbers initialized to the cell index, and both cursors at 0; any number of producers and consumers; records are plain u64 words.
// CEP:COST: enqueue 1 Acquire load + 1 Relaxed CAS + N Relaxed stores + 1 Release store; dequeue 1 Acquire load + N Relaxed loads + 1 Relaxed CAS + 1 Release store; measured in bench CEP-BENCH-0034, artifact benches/artifacts/mpmc_enqueue_dequeue.json.
// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, capacity_enforced, rejects_invalid_storage, sequence_recycling}; property/concurrency_property_test.rs::{exactly_once_delivery, mpmc_conserves_records_under_threads}.
// CEP:SECURITY: capacity bounded by the caller; every access masked into the storage; forged sequence numbers degrade to Full/None, never to wrong data.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: single-threaded use is deterministic FIFO; cross-thread delivery order is scheduling-dependent by design (design 19.5) but every record is delivered exactly once and uncorrupted.
// CEP:HPC-PASS-LEGALITY: Formal Spec 13 section 2 fixes the cell protocol, the memory-ordering table, the linearization points (the cursor CASes), and the ABA argument; the property tests verify executably that exactly-once delivery and record conservation hold under thread interleaving.

use core::sync::atomic::{AtomicI64, AtomicU64, Ordering};

use mapt_config::limits::kSharedClauseMaxWords;

/// CEP:WHAT: Error cases of the sharing pool.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the pool never panics, never duplicates, never corrupts.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{capacity_enforced, rejects_invalid_storage}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PoolError {
    /// CEP:WHAT: The ring is full (every cell holds an unconsumed record).
    /// CEP:WHY: The bounded pool is the shared-memory bound (design 19.2 "bounded MPMC"); the exporter counts and skips.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: capacity >= 2.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Full,
    /// CEP:WHAT: The supplied storage is malformed (zero or non-power-of-two cells, or the word array does not match cells x words).
    /// CEP:WHY: Construction validates the layout before any masking (CEP&CC Law 3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::rejects_invalid_storage.
    /// CEP:SECURITY: input validation.
    InvalidStorage,
}

// CEP:WHAT: Retry budget of one enqueue/dequeue call under persistent cursor contention.
// CEP:WHY: Losing the cursor CAS must return (Full/None - retry later) instead of spinning; the budget bounds the loop (CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: budget exhaustion maps to the caller-visible retry outcome.
// CEP:ASSUMES: callers treat the outcome as retry-later.
// CEP:COST: up to 64 CAS attempts.
// CEP:EVIDENCE: property/concurrency_property_test.rs::{exactly_once_delivery, mpmc_conserves_records_under_threads}.
// CEP:SECURITY: denial-of-service bound on spin.
const kPoolRetryBudget: u32 = 64;

/// CEP:WHAT: The clause-sharing pool: per-cell sequences, the record-word array, the produce cursor, and the consume cursor.
/// CEP:WHY: Design 19.2: one global bounded pool carries the weight/LBD/rule-filtered derived clauses between portfolio workers; the storage is caller-supplied (the hot crate stays allocation-free, design 4.1) and Sync comes from the atomics (CEP&CC 8.43); records are fixed-size word arrays so no allocation or serialization lock is ever needed on the sharing path.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see PoolError.
/// CEP:ASSUMES: storage outlives every user; exactly-once delivery per record.
/// CEP:COST: 2 references plus a mask and the words-per-cell constant.
/// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs (the whole file); property/concurrency_property_test.rs::mpmc_conserves_records_under_threads.
/// CEP:SECURITY: no interior mutability beyond the supplied atomics; every index masked.
pub struct SharingPool<'a> {
    /// CEP:WHAT: Per-cell sequence numbers (cell i initialized to i by the caller).
    /// CEP:WHY: The Vyukov protocol's state machine: seq == pos means reachable-for-produce, seq == pos+1 means published-for-consume, anything behind means a full turn is pending recycle.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: caller-initialized.
    /// CEP:COST: 8 bytes per cell.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, sequence_recycling}.
    /// CEP:SECURITY: none.
    sequences: &'a [AtomicI64],
    /// CEP:WHAT: Record-word storage (cells x kSharedClauseMaxWords words, cell-major).
    /// CEP:WHY: Fixed-size records keep the claim-then-write-then-publish protocol allocation-free.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: cell i's words are [i * words, (i+1) * words).
    /// CEP:COST: 8 bytes per word.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, capacity_enforced}.
    /// CEP:SECURITY: masked access.
    words: &'a [AtomicU64],
    /// CEP:WHAT: The cell-index mask (cells - 1).
    /// CEP:WHY: Power-of-two masking (design 22.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: cells is a power of two (validated).
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::rejects_invalid_storage.
    /// CEP:SECURITY: keeps every index in bounds.
    mask: u64,
    /// CEP:WHAT: The produce cursor (monotonic).
    /// CEP:WHY: The enqueue claim point; CAS-advanced.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: starts at 0.
    /// CEP:COST: 8 bytes shared.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
    /// CEP:SECURITY: CAS-protected.
    produce_pos: &'a AtomicI64,
    /// CEP:WHAT: The consume cursor (monotonic).
    /// CEP:WHY: The dequeue claim point; CAS-advanced.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: starts at 0.
    /// CEP:COST: 8 bytes shared.
    /// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
    /// CEP:SECURITY: CAS-protected.
    consume_pos: &'a AtomicI64,
}

impl<'a> SharingPool<'a> {
    // CEP:WHAT: Binds the pool to caller-supplied storage, validating the layout.
    // CEP:WHY: The hot crate is storage-agnostic; construction checks the power-of-two cell count and the words-array extent so every later masked access is provably in bounds (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns InvalidStorage for malformed storage.
    // CEP:ASSUMES: sequences initialized to cell indices; cursors at 0; storage outlives all users.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{rejects_invalid_storage, fifo_order_single_thread}.
    // CEP:SECURITY: validation before use.
    pub fn new(
        sequences: &'a [AtomicI64],
        words: &'a [AtomicU64],
        produce_pos: &'a AtomicI64,
        consume_pos: &'a AtomicI64,
    ) -> Result<SharingPool<'a>, PoolError> {
        if sequences.len() < 2 || sequences.len().count_ones() != 1 {
            return Err(PoolError::InvalidStorage);
        }
        if words.len() != sequences.len() * kSharedClauseMaxWords {
            return Err(PoolError::InvalidStorage);
        }
        Ok(SharingPool {
            sequences,
            words,
            mask: (sequences.len() - 1) as u64,
            produce_pos,
            consume_pos,
        })
    }

    // CEP:WHAT: Enqueues one fixed-size record (the caller's word slice, zero-padded to the record width).
    // CEP:WHY: Design 19.2 producer side; ordering (CEP&CC 8.43): the sequence Acquire load pairs with a consumer's Release sequence publish (recycle) so a recycled cell's previous read is complete before the producer overwrites; the produce-cursor CAS is Relaxed on both orders (the claim is exclusive - only the CAS winner writes the cell - and no data visibility rides on the claim itself); the record stores are Relaxed (the cell is exclusively the claiming producer's until the sequence publish); the sequence Release store publishes the record (pairs with every consumer's Acquire sequence load); failure point: the cursor CAS may lose (retry within the budget, then Full); ABA: cursors are monotonic and a cell recycles only after seq advanced a full turn - a stale claimant CASes a cursor value that no longer exists.
    // CEP:STATUS: complete
    // CEP:FAILURE: Full when the ring is full or the retry budget is exhausted.
    // CEP:ASSUMES: record.len() <= kSharedClauseMaxWords; any producer count.
    // CEP:COST: see the file header; bench CEP-BENCH-0034.
    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, capacity_enforced, sequence_recycling}; property/concurrency_property_test.rs::{exactly_once_delivery, mpmc_conserves_records_under_threads}.
    // CEP:SECURITY: masked writes; the words beyond record.len() are zero-filled (no stale data leaks).
    pub fn enqueue(&self, record: &[u64]) -> Result<(), PoolError> {
        if record.len() > kSharedClauseMaxWords {
            return Err(PoolError::InvalidStorage);
        }
        // CEP:WHAT: Enqueue attempt budget.
        // CEP:WHY: Persistent cursor contention must return Full (retry-later), never spin.
        // CEP:STATUS: complete
        // CEP:FAILURE: budget exhaustion returns Full.
        // CEP:ASSUMES: none.
        // CEP:COST: bounded CAS attempts.
        // CEP:EVIDENCE: property/concurrency_property_test.rs::mpmc_conserves_records_under_threads.
        // CEP:SECURITY: denial-of-service bound.
        let mut attempts: u32 = 0;
        // CEP:WHAT: Produce-cursor snapshot.
        // CEP:WHY: Relaxed load: the loop re-validates through the cell sequence, so a stale cursor only costs a retry.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: 1 load.
        // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
        // CEP:SECURITY: none.
        let mut pos = self.produce_pos.load(Ordering::Relaxed);
        loop {
            let cell = (pos as u64 & self.mask) as usize;
            // CEP:WHAT: Cell sequence check (Acquire: pairs with the consumer's recycle publish).
            // CEP:WHY: seq == pos: the cell is free this turn; seq < pos: the cell still holds an unconsumed record (full); seq > pos: another producer claimed ahead - refresh the cursor.
            // CEP:STATUS: complete
            // CEP:FAILURE: Full when behind.
            // CEP:ASSUMES: caller-initialized sequences.
            // CEP:COST: 1 load.
            // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, capacity_enforced}.
            // CEP:SECURITY: none.
            let seq = self.sequences[cell].load(Ordering::Acquire);
            if seq == pos {
                // CEP:WHAT: Claim the cell by advancing the produce cursor.
                // CEP:WHY: Relaxed CAS: the claim is exclusive (only the winner writes); ordering is irrelevant because the sequence publish carries the visibility.
                // CEP:STATUS: complete
                // CEP:FAILURE: CAS loss -> retry.
                // CEP:ASSUMES: pos is the loaded cursor value.
                // CEP:COST: 1 CAS.
                // CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
                // CEP:SECURITY: none.
                if self
                    .produce_pos
                    .compare_exchange(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    // CEP:WHAT: Write the record words (Relaxed: exclusive cell ownership until the sequence publish) and zero-pad the tail.
                    // CEP:WHY: Zero-padding prevents stale-word leakage from the previous turn (the decoder validates the record's own header, but hygiene is defense in depth).
                    // CEP:STATUS: complete
                    // CEP:FAILURE: none.
                    // CEP:ASSUMES: the claiming producer exclusively owns the cell.
                    // CEP:COST: words stores.
                    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
                    // CEP:SECURITY: no stale-data leak.
                    let base = cell * kSharedClauseMaxWords;
                    for (slot, word) in self.words[base..base + kSharedClauseMaxWords]
                        .iter()
                        .zip(record.iter().chain(core::iter::repeat(&0u64)))
                    {
                        slot.store(*word, Ordering::Relaxed);
                    }
                    // CEP:WHAT: Publish: seq = pos + 1 (Release).
                    // CEP:WHY: Pairs with every consumer's Acquire sequence load: observing pos+1 makes the whole record visible.
                    // CEP:STATUS: complete
                    // CEP:FAILURE: none.
                    // CEP:ASSUMES: none.
                    // CEP:COST: 1 store.
                    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
                    // CEP:SECURITY: none.
                    self.sequences[cell].store(pos + 1, Ordering::Release);
                    return Ok(());
                }
            } else if seq < pos {
                // The cell holds an unconsumed record from the previous turn: full.
                return Err(PoolError::Full);
            }
            attempts += 1;
            if attempts >= kPoolRetryBudget {
                return Err(PoolError::Full);
            }
            pos = self.produce_pos.load(Ordering::Relaxed);
        }
    }

    // CEP:WHAT: Dequeues one record into the caller's word slice; returns the record length or None when empty.
    // CEP:WHY: Design 19.2 consumer side; ordering (CEP&CC 8.43): the sequence Acquire load pairs with the producer's Release publish (observing pos+1 makes the record words visible); the consume-cursor CAS is Relaxed (exclusive claim); the word loads are Relaxed (visibility carried by the sequence Acquire); the recycle Release store (seq = pos + cells + 1) tells producers the cell is free a full turn ahead and orders the consumer's reads before the next overwrite; failure point: the cursor CAS may lose (retry within the budget, then None); ABA: monotonic cursors plus the full-turn recycle discipline.
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) when empty or contention-exhausted (never a wrong or duplicated record); the record length comes from the record's own header word (the caller validates).
    // CEP:ASSUMES: out.len() >= kSharedClauseMaxWords; any consumer count.
    // CEP:COST: see the file header; bench CEP-BENCH-0034.
    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, sequence_recycling}; property/concurrency_property_test.rs::{exactly_once_delivery, mpmc_conserves_records_under_threads}.
    // CEP:SECURITY: masked reads; the caller bounds-checks the decoded record.
    pub fn dequeue(&self, out: &mut [u64]) -> Result<Option<usize>, PoolError> {
        if out.len() < kSharedClauseMaxWords {
            return Err(PoolError::InvalidStorage);
        }
        // CEP:WHAT: Dequeue attempt budget.
        // CEP:WHY: As enqueue's budget.
        // CEP:STATUS: complete
        // CEP:FAILURE: budget exhaustion returns None.
        // CEP:ASSUMES: none.
        // CEP:COST: bounded CAS attempts.
        // CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
        // CEP:SECURITY: denial-of-service bound.
        let mut attempts: u32 = 0;
        // CEP:WHAT: Consume-cursor snapshot.
        // CEP:WHY: Relaxed load: the cell sequence validates; a stale cursor costs a retry.
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: 1 load.
        // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
        // CEP:SECURITY: none.
        let mut pos = self.consume_pos.load(Ordering::Relaxed);
        loop {
            let cell = (pos as u64 & self.mask) as usize;
            // CEP:WHAT: Cell sequence check (Acquire: pairs with the producer's publish).
            // CEP:WHY: seq == pos + 1: a published record; seq < pos + 1: empty (no published record at this turn); seq > pos + 1: another consumer claimed ahead - refresh.
            // CEP:STATUS: complete
            // CEP:FAILURE: empty returns None.
            // CEP:ASSUMES: caller-initialized sequences.
            // CEP:COST: 1 load.
            // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, capacity_enforced}.
            // CEP:SECURITY: none.
            let seq = self.sequences[cell].load(Ordering::Acquire);
            let difference = seq - pos;
            if difference == 1 {
                // CEP:WHAT: Claim the record by advancing the consume cursor.
                // CEP:WHY: Relaxed CAS: exclusive claim; the recycle publish carries ordering.
                // CEP:STATUS: complete
                // CEP:FAILURE: CAS loss -> retry.
                // CEP:ASSUMES: pos is the loaded cursor value.
                // CEP:COST: 1 CAS.
                // CEP:EVIDENCE: property/concurrency_property_test.rs::exactly_once_delivery.
                // CEP:SECURITY: none.
                if self
                    .consume_pos
                    .compare_exchange(pos, pos + 1, Ordering::Relaxed, Ordering::Relaxed)
                    .is_ok()
                {
                    // CEP:WHAT: Read the record words (Relaxed: visibility carried by the sequence Acquire).
                    // CEP:WHY: The claiming consumer exclusively owns the cell until the recycle publish.
                    // CEP:STATUS: complete
                    // CEP:FAILURE: none.
                    // CEP:ASSUMES: the producer's publish was observed.
                    // CEP:COST: words loads.
                    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
                    // CEP:SECURITY: none.
                    let base = cell * kSharedClauseMaxWords;
                    for (slot, cell_word) in out
                        .iter_mut()
                        .zip(self.words[base..base + kSharedClauseMaxWords].iter())
                    {
                        *slot = cell_word.load(Ordering::Relaxed);
                    }
                    // CEP:WHAT: Recycle: seq = pos + cells (Release).
                    // CEP:WHY: Frees the cell exactly for the produce position one full turn ahead (the next pos mapping to this cell is pos + cells) and orders this consumer's reads before that producer's overwrite; the value is the Vyukov recycle rule.
                    // CEP:STATUS: complete
                    // CEP:FAILURE: none.
                    // CEP:ASSUMES: none.
                    // CEP:COST: 1 store.
                    // CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::sequence_recycling.
                    // CEP:SECURITY: none.
                    self.sequences[cell].store(pos + (self.mask + 1) as i64, Ordering::Release);
                    // The record's first word carries its length (the codec's header).
                    let length = (out[0] & kRecordLengthMask as u64) as usize;
                    let length = length.min(kSharedClauseMaxWords);
                    return Ok(Some(length));
                }
            } else if difference < 1 {
                // No published record at this turn: empty.
                return Ok(None);
            }
            attempts += 1;
            if attempts >= kPoolRetryBudget {
                return Ok(None);
            }
            pos = self.consume_pos.load(Ordering::Relaxed);
        }
    }
}

// CEP:WHAT: Header mask extracting the record length from a record's first word.
// CEP:WHY: The codec's header packs [length:16][reserved:16][literal_count:16][...]; the pool only needs the total word length; the named mask keeps the extraction auditable against the codec's layout (Spec 13 section 4).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the codec's header layout (clause_codec.rs pins it with a constant assertion).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, header_layout_pinned}.
// CEP:SECURITY: none.
const kRecordLengthMask: u32 = 0xFFFF;
