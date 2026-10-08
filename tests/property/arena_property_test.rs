// CEP:FILE: tests/property/arena_property_test.rs
// CEP:WHAT: Property tests for the arena: random allocation sequences keep the cursor in bounds, ranges never overlap, and reset reuses the region.
// CEP:WHY: CEP&CC 32.8 and 38.43: property testing complements unit tests with randomized sequences; the fixed-seed generator makes every run reproducible.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/memory/arena.rs property claims.
// CEP:SECURITY: adversarial allocation patterns are randomized.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::memory::arena::ArenaRange;

// CEP:WHAT: Number of random allocation rounds per property test.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3) balancing coverage and runtime.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyRounds: u32 = 2_048;

// CEP:WHAT: Verifies the cursor stays in bounds under random allocations.
// CEP:WHY: The front <= capacity invariant is the memory-safety core.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cursor leaves the capacity.
// CEP:ASSUMES: none.
// CEP:COST: kPropertyRounds allocations.
// CEP:EVIDENCE: cited by hot/memory/arena.rs front invariant.
// CEP:SECURITY: none.
#[test]
fn cursor_stays_in_bounds() {
    let arena = make_arena(65_536);
    let mut rng = DeterministicRng::new(0x41524541);
    for _ in 0..kPropertyRounds {
        let size = rng.below(512) as u32 + 1;
        let align = 1u32 << rng.below(7);
        let _ = arena.alloc_bytes(size, align);
        assert!(arena.used_bytes() <= arena.capacity_bytes());
    }
}

// CEP:WHAT: Verifies live ranges never overlap before a reset.
// CEP:WHY: The bump discipline guarantees disjoint ranges within a generation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any overlap.
// CEP:ASSUMES: none.
// CEP:COST: kPropertyRounds allocations plus O(n^2) overlap scan.
// CEP:EVIDENCE: cited by hot/memory/arena.rs uniqueness contract.
// CEP:SECURITY: none.
#[test]
fn ranges_disjoint() {
    let arena = make_arena(262_144);
    let mut rng = DeterministicRng::new(0x4F495352);
    let mut ranges: Vec<ArenaRange> = Vec::new();
    for _ in 0..512 {
        let size = rng.below(256) as u32 + 1;
        let align = 1u32 << rng.below(7);
        if let Ok(range) = arena.alloc_bytes(size, align) {
            for previous in ranges.iter() {
                let disjoint = range.end <= previous.start || previous.end <= range.start;
                assert!(disjoint, "ranges must never overlap");
            }
            ranges.push(range);
        }
    }
}

// CEP:WHAT: Verifies reset reuses the region for new allocations.
// CEP:WHY: O(1) reclamation semantics (design 8.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cursor does not rewind.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs reset_to.
// CEP:SECURITY: none.
#[test]
fn reset_then_allocate_reuses_region() {
    let arena = make_arena(4_096);
    let checkpoint = arena.checkpoint();
    let first = arena.alloc_bytes(1_024, 4).expect("alloc");
    let after_first = arena.used_bytes();
    arena.reset_to(checkpoint).expect("reset");
    assert!(arena.used_bytes() < after_first);
    let second = arena.alloc_bytes(1_024, 4).expect("realloc");
    assert_eq!(
        second.start, first.start,
        "the region must be reused from the checkpoint"
    );
}
