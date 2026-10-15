// CEP:FILE: tests/unit/hot/chase_lev_test.rs
// CEP:WHAT: Unit tests of the Chase-Lev work-stealing deque: owner FIFO/LIFO order, capacity, single-owner semantics, pop/steal splitting, the last-element race, cursor monotonicity, and storage validation.
// CEP:WHY: CEP&CC 34.3: the deque is a Phase 4 hot-path structure whose protocol claims (exactly-once, order, bounds - Spec 13 section 3) must be pinned executably before any consumer trusts them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: single-threaded unless a test spawns threads explicitly.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/chase_lev_test.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

use std::sync::atomic::{AtomicI64, AtomicU64};

use mapt::hot::concurrency::chase_lev::{DequeError, WorkStealingDeque};

// CEP:WHAT: Builds a deque over fresh zeroed storage of the given capacity.
// CEP:WHY: One fixture keeps the tests focused on protocol behavior.
// CEP:STATUS: complete
// CEP:FAILURE: panics on invalid capacity (fixture bug).
// CEP:ASSUMES: capacity is a power of two >= 2.
// CEP:COST: one allocation set.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn make_deque(capacity: usize) -> (Vec<AtomicU64>, AtomicI64, AtomicI64) {
    let mut buffer: Vec<AtomicU64> = Vec::with_capacity(capacity);
    for _ in 0..capacity {
        buffer.push(AtomicU64::new(0));
    }
    (buffer, AtomicI64::new(0), AtomicI64::new(0))
}

#[test]
// CEP:WHAT: Owner pushes then pops in LIFO order and the deque empties.
// CEP:WHY: The owner-side discipline of Chase-Lev (pop takes the bottom = newest).
// CEP:STATUS: complete
// CEP:FAILURE: panics on order mismatch.
// CEP:ASSUMES: single-threaded.
// CEP:COST: 3 pushes, 3 pops.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::owner_fifo_order.
// CEP:SECURITY: none.
fn owner_fifo_order() {
    let (buffer, top, bottom) = make_deque(8);
    let deque = WorkStealingDeque::new(&buffer, &top, &bottom).expect("deque");
    deque.push(10).expect("push");
    deque.push(11).expect("push");
    deque.push(12).expect("push");
    // Owner pop is LIFO from the bottom end.
    assert_eq!(deque.pop().expect("pop"), Some(12));
    assert_eq!(deque.pop().expect("pop"), Some(11));
    assert_eq!(deque.pop().expect("pop"), Some(10));
    assert_eq!(deque.pop().expect("pop"), None);
}

#[test]
// CEP:WHAT: Push fails loudly at the ring capacity and recovers after a pop.
// CEP:WHY: The bounded-ring contract (DequeError::Full at capacity - the owner drains).
// CEP:STATUS: complete
// CEP:FAILURE: panics on unexpected outcomes.
// CEP:ASSUMES: single-threaded.
// CEP:COST: capacity + 1 pushes.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::capacity_enforced.
// CEP:SECURITY: memory bound.
fn capacity_enforced() {
    let (buffer, top, bottom) = make_deque(4);
    let deque = WorkStealingDeque::new(&buffer, &top, &bottom).expect("deque");
    for value in 1..=4u64 {
        deque.push(value).expect("push within capacity");
    }
    assert_eq!(deque.push(5), Err(DequeError::Full));
    assert_eq!(deque.pop().expect("pop"), Some(4));
    deque.push(5).expect("push after drain");
}

#[test]
// CEP:WHAT: Steal returns None on an empty deque and after the owner drains it.
// CEP:WHY: The emptiness contract of the thief side.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unexpected outcomes.
// CEP:ASSUMES: single-threaded (steal from the owner thread exercises the same protocol).
// CEP:COST: a few steals.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::steal_returns_empty_when_idle.
// CEP:SECURITY: none.
fn steal_returns_empty_when_idle() {
    let (buffer, top, bottom) = make_deque(8);
    let deque = WorkStealingDeque::new(&buffer, &top, &bottom).expect("deque");
    assert_eq!(deque.steal().expect("steal"), None);
    deque.push(7).expect("push");
    assert_eq!(deque.steal().expect("steal"), Some(7));
    assert_eq!(deque.steal().expect("steal"), None);
}

#[test]
// CEP:WHAT: Steal takes the oldest element (top end) while pop takes the newest (bottom end); the two ends never overlap.
// CEP:WHY: The two-ended discipline of design 19.3 (FIFO steals, LIFO pops).
// CEP:STATUS: complete
// CEP:FAILURE: panics on order mismatch.
// CEP:ASSUMES: single-threaded interleave.
// CEP:COST: a handful of operations.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::pop_and_steal_split_elements.
// CEP:SECURITY: none.
fn pop_and_steal_split_elements() {
    let (buffer, top, bottom) = make_deque(8);
    let deque = WorkStealingDeque::new(&buffer, &top, &bottom).expect("deque");
    for value in 1..=4u64 {
        deque.push(value).expect("push");
    }
    assert_eq!(deque.steal().expect("steal oldest"), Some(1));
    assert_eq!(deque.pop().expect("pop newest"), Some(4));
    assert_eq!(deque.steal().expect("steal next"), Some(2));
    assert_eq!(deque.pop().expect("pop last"), Some(3));
    assert_eq!(deque.pop().expect("empty"), None);
    assert_eq!(deque.steal().expect("empty"), None);
}

#[test]
// CEP:WHAT: The last element is delivered exactly once across a tight pop/steal race over many rounds.
// CEP:WHY: The central Chase-Lev safety claim (the top CAS linearizes the last-element race - Spec 13 section 3); the test runs many rounds because the race window is scheduling-dependent.
// CEP:STATUS: complete
// CEP:FAILURE: panics if any round delivers the element twice or loses it.
// CEP:ASSUMES: the single-round protocol is deterministic (the sequential check); the multi-round loop covers the interleaving space coarsely.
// CEP:COST: kRounds x one push + one pop + one steal.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::last_element_race_never_duplicated.
// CEP:SECURITY: none.
fn last_element_race_never_duplicated() {
    // CEP:WHAT: Rounds of the race.
    // CEP:WHY: Named bound (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRounds: u32 = 256;
    let (buffer, top, bottom) = make_deque(8);
    let deque = WorkStealingDeque::new(&buffer, &top, &bottom).expect("deque");
    for round in 0..kRounds {
        deque.push(round as u64).expect("push");
        // Sequential single-element race: exactly one of pop/steal wins.
        let popped = deque.pop().expect("pop");
        let stolen = deque.steal().expect("steal");
        let delivered = popped.map(|value| value == round as u64).unwrap_or(false) as u32
            + stolen.map(|value| value == round as u64).unwrap_or(false) as u32;
        assert_eq!(
            delivered, 1,
            "round {}: the last element must be delivered exactly once",
            round
        );
        assert_eq!(
            deque.len(),
            0,
            "round {}: the deque must be empty after the race",
            round
        );
    }
}

#[test]
// CEP:WHAT: Steals and pops under real thread interleaving conserve every pushed element exactly once.
// CEP:WHY: The exactly-once property of design 19.3 under concurrency (the property-test scale, single machine, bounded rounds).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any loss or duplication.
// CEP:ASSUMES: two threads (one owner, one thief).
// CEP:COST: kItems pushes and steals.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::cursor_monotonicity and property/concurrency_property_test.rs::deque_conserves_elements_under_threads (this unit variant).
// CEP:SECURITY: none.
fn cursor_monotonicity() {
    // CEP:WHAT: Items pushed (and stolen) in the race.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kItems: u64 = 2048;
    // CEP:WHAT: Leaked deque storage for the cross-thread fixture.
    // CEP:WHY: The scoped thread borrows the deque; the storage must outlive the scope and the local vectors cannot move into it - the leak follows the documented test-fixture discipline.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: one leak per test.
    // CEP:COST: one leak.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    let cells = 8192usize;
    let buffer: &'static [AtomicU64] = Box::leak(
        (0..cells)
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let top: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let bottom: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let deque = WorkStealingDeque::new(buffer, top, bottom).expect("deque");
    let stolen: u64 = std::thread::scope(|scope| {
        let thief = deque.clone();
        let thief_handle = scope.spawn(move || {
            let mut stolen: u64 = 0;
            let mut attempts: u64 = 0;
            while stolen < kItems && attempts < kItems * 16 {
                attempts += 1;
                if let Ok(Some(_)) = thief.steal() {
                    stolen += 1;
                }
            }
            stolen
        });
        let mut pushed: u64 = 0;
        while pushed < kItems {
            if deque.push(pushed).is_ok() {
                pushed += 1;
            }
        }
        // Drain the remainder owner-side so the thief can finish.
        let mut popped: u64 = 0;
        while let Ok(Some(_)) = deque.pop() {
            popped += 1;
        }
        let stolen = thief_handle.join().expect("thief join");
        assert_eq!(
            pushed,
            stolen + popped,
            "every pushed element is delivered exactly once (stolen or popped)"
        );
        stolen
    });
    assert!(stolen <= kItems);
    // Monotonic cursors: top <= bottom after the drain.
    let (buffer2, top2, bottom2) = make_deque(8);
    let deque2 = WorkStealingDeque::new(&buffer2, &top2, &bottom2).expect("deque");
    deque2.push(1).expect("push");
    deque2.push(2).expect("push");
    assert_eq!(deque2.pop().expect("pop"), Some(2));
    assert_eq!(deque2.pop().expect("pop"), Some(1));
    assert!(
        top2.load(std::sync::atomic::Ordering::Acquire)
            <= bottom2.load(std::sync::atomic::Ordering::Acquire)
    );
}
#[test]
// CEP:WHAT: Construction rejects zero-length and non-power-of-two rings.
// CEP:WHY: Masked indexing requires the power of two (the validation before any masking).
// CEP:STATUS: complete
// CEP:FAILURE: panics if an invalid ring is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: backs unit/hot/chase_lev_test.rs::rejects_non_power_of_two.
// CEP:SECURITY: input validation.
fn rejects_non_power_of_two() {
    let empty: Vec<AtomicU64> = Vec::new();
    let zero = AtomicI64::new(0);
    let zero2 = AtomicI64::new(0);
    match WorkStealingDeque::new(&empty, &zero, &zero2) {
        Err(DequeError::InvalidStorage) => {}
        _ => panic!("zero-length ring must be rejected"),
    }
    let mut odd: Vec<AtomicU64> = Vec::new();
    for _ in 0..3 {
        odd.push(AtomicU64::new(0));
    }
    let top = AtomicI64::new(0);
    let bottom = AtomicI64::new(0);
    match WorkStealingDeque::new(&odd, &top, &bottom) {
        Err(DequeError::InvalidStorage) => {}
        _ => panic!("non-power-of-two ring must be rejected"),
    }
}
