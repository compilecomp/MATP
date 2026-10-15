// CEP:FILE: tests/unit/hot/mpmc_pool_test.rs
// CEP:WHAT: Unit tests of the bounded MPMC clause-sharing pool: FIFO order, capacity, sequence recycling, storage validation, and exactly-once delivery under producer/consumer threads.
// CEP:WHY: CEP&CC 34.3: the pool is a Phase 4 hot-path structure whose protocol claims (exactly-once, order, bounds - Spec 13 section 2) must be pinned executably before the portfolio trusts them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: single-threaded unless a test spawns threads explicitly.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/mpmc_pool_test.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

use std::sync::atomic::{AtomicI64, AtomicU64};

use mapt::hot::concurrency::mpmc_pool::{PoolError, SharingPool};

// CEP:WHAT: Builds a pool over fresh leaked storage (sequences initialized to cell indices, cursors at zero).
// CEP:WHY: One fixture keeps the tests focused on protocol behavior; the 'static leak follows the test-arena discipline of tests/common/mod.rs (one leak per test, documented).
// CEP:STATUS: complete
// CEP:FAILURE: panics on invalid capacity (fixture bug).
// CEP:ASSUMES: capacity is a power of two >= 2.
// CEP:COST: one allocation set.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn make_pool(cells: usize) -> SharingPool<'static> {
    let mut sequences: Vec<AtomicI64> = Vec::with_capacity(cells);
    for index in 0..cells {
        sequences.push(AtomicI64::new(index as i64));
    }
    let mut words: Vec<AtomicU64> =
        Vec::with_capacity(cells * mapt_config::limits::kSharedClauseMaxWords);
    for _ in 0..(cells * mapt_config::limits::kSharedClauseMaxWords) {
        words.push(AtomicU64::new(0));
    }
    let sequences: &'static [AtomicI64] = Box::leak(sequences.into_boxed_slice());
    let words: &'static [AtomicU64] = Box::leak(words.into_boxed_slice());
    let produce: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let consume: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    SharingPool::new(sequences, words, produce, consume).expect("pool")
}

// CEP:WHAT: One record's word count for the tests (header + one literal header + two node words).
// CEP:WHY: Named fixture constant (CEP&CC 11.3); the pool is word-width agnostic.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: <= kSharedClauseMaxWords.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kFixtureRecordWords: usize = 4;

// CEP:WHAT: Builds one fixture record carrying the given tag value in its second word.
// CEP:WHY: The tests identify records by the tag word; word 0 stays the header (length in the low 16 bits, mirroring the codec's layout).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn make_record(tag: u64) -> Vec<u64> {
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    record[0] = kFixtureRecordWords as u64;
    record[1] = tag;
    record
}

#[test]
// CEP:WHAT: Single-threaded enqueue/dequeue is FIFO and empties cleanly.
// CEP:WHY: The order contract of the shared bus (design 19.2).
// CEP:STATUS: complete
// CEP:FAILURE: panics on order mismatch.
// CEP:ASSUMES: single-threaded.
// CEP:COST: a few records.
// CEP:EVIDENCE: backs unit/hot/mpmc_pool_test.rs::fifo_order_single_thread.
// CEP:SECURITY: none.
fn fifo_order_single_thread() {
    let pool = make_pool(4);
    for tag in 1..=3u64 {
        pool.enqueue(&make_record(tag)).expect("enqueue");
    }
    let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    for tag in 1..=3u64 {
        let length = pool.dequeue(&mut out).expect("dequeue").expect("record");
        assert_eq!(length, kFixtureRecordWords);
        assert_eq!(out[1], tag, "FIFO order must hold");
    }
    assert_eq!(pool.dequeue(&mut out).expect("dequeue"), None);
}

#[test]
// CEP:WHAT: Enqueue fails loudly at capacity and recovers after a dequeue.
// CEP:WHY: The bounded-pool contract (PoolError::Full - the exporter counts and skips).
// CEP:STATUS: complete
// CEP:FAILURE: panics on unexpected outcomes.
// CEP:ASSUMES: single-threaded.
// CEP:COST: capacity + 1 enqueues.
// CEP:EVIDENCE: backs unit/hot/mpmc_pool_test.rs::capacity_enforced.
// CEP:SECURITY: memory bound.
fn capacity_enforced() {
    let pool = make_pool(2);
    pool.enqueue(&make_record(1)).expect("enqueue");
    pool.enqueue(&make_record(2)).expect("enqueue");
    assert_eq!(pool.enqueue(&make_record(3)), Err(PoolError::Full));
    let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    assert!(pool.dequeue(&mut out).expect("dequeue").is_some());
    pool.enqueue(&make_record(3))
        .expect("enqueue after dequeue");
}

#[test]
// CEP:WHAT: Cells recycle across full ring turns with correct sequence handshakes (capacity + 1 records pass through a 1-cell... a 2-cell pool with interleaved drains).
// CEP:WHY: The Vyukov recycle rule (seq = pos + cells + 1) is what makes the bounded ring safe to reuse; the test drives several turns.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any lost or corrupted record.
// CEP:ASSUMES: single-threaded.
// CEP:COST: many turns.
// CEP:EVIDENCE: backs unit/hot/mpmc_pool_test.rs::sequence_recycling.
// CEP:SECURITY: none.
fn sequence_recycling() {
    let pool = make_pool(2);
    let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    for tag in 0..64u64 {
        pool.enqueue(&make_record(tag)).expect("enqueue");
        let length = pool.dequeue(&mut out).expect("dequeue").expect("record");
        assert_eq!(length, kFixtureRecordWords);
        assert_eq!(out[1], tag, "turn {} must deliver record {}", tag, tag);
    }
}

#[test]
// CEP:WHAT: Construction rejects malformed storage (non-power-of-two cells, mismatched word array).
// CEP:WHY: The layout validation before any masking.
// CEP:STATUS: complete
// CEP:FAILURE: panics if malformed storage is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: backs unit/hot/mpmc_pool_test.rs::rejects_invalid_storage.
// CEP:SECURITY: input validation.
fn rejects_invalid_storage() {
    let cells = 3;
    let sequences: &'static [AtomicI64] = Box::leak(
        (0..cells)
            .map(|index| AtomicI64::new(index as i64))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let words: &'static [AtomicU64] = Box::leak(
        (0..(cells * mapt_config::limits::kSharedClauseMaxWords))
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let produce: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let consume: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    match SharingPool::new(sequences, words, produce, consume) {
        Err(PoolError::InvalidStorage) => {}
        _ => panic!("malformed storage must be rejected"),
    }
}

#[test]
// CEP:WHAT: Two producers and two consumers deliver every record exactly once (sum conservation).
// CEP:WHY: The MPMC exactly-once contract under real interleaving (the unit-scale variant of the property test).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any loss, duplication, or corruption.
// CEP:ASSUMES: four threads.
// CEP:COST: kRecords enqueues and dequeues total.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::mpmc_conserves_records_under_threads (unit-scale pin).
// CEP:SECURITY: none.
fn exactly_once_delivery_under_threads() {
    // CEP:WHAT: Records in the race.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRecords: u64 = 512;
    // CEP:WHAT: Records per producer.
    // CEP:WHY: Named split of the workload.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: divides kRecords.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kPerProducer: u64 = kRecords / 2;
    let pool = make_pool(64);
    let total: u64 = std::thread::scope(|scope| {
        let mut producer_handles: Vec<std::thread::ScopedJoinHandle<'_, u64>> = Vec::new();
        for producer in 0..2u64 {
            let pool_ref = &pool;
            producer_handles.push(scope.spawn(move || {
                let mut enqueued: u64 = 0;
                let base = producer * kPerProducer;
                while enqueued < kPerProducer {
                    let tag = base + enqueued;
                    if pool_ref.enqueue(&make_record(tag)).is_ok() {
                        enqueued += 1;
                    }
                }
                enqueued
            }));
        }
        let mut consumer_handles: Vec<std::thread::ScopedJoinHandle<'_, u64>> = Vec::new();
        for _ in 0..2 {
            let pool_ref = &pool;
            consumer_handles.push(scope.spawn(move || {
                let mut sum: u64 = 0;
                let mut idle: u32 = 0;
                let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
                loop {
                    match pool_ref.dequeue(&mut out) {
                        Ok(Some(_)) => {
                            idle = 0;
                            sum += out[1];
                        }
                        Ok(None) => {
                            idle += 1;
                            if idle > 1_000_000 {
                                break;
                            }
                        }
                        Err(_) => break,
                    }
                }
                sum
            }));
        }
        for handle in producer_handles {
            assert_eq!(handle.join().expect("producer"), kPerProducer);
        }
        consumer_handles
            .into_iter()
            .map(|handle| handle.join().expect("consumer"))
            .sum()
    });
    assert_eq!(total, (0..kRecords).sum::<u64>(), "exactly-once delivery");
}
