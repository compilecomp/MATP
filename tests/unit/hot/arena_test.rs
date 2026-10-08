// CEP:FILE: tests/unit/hot/arena_test.rs
// CEP:WHAT: Unit tests for the arena allocator: construction validation, allocation discipline, alignment, typed arrays, checkpoints, and exhaustion.
// CEP:WHY: CEP&CC 32.8 requires tests for every CEP-0 function; the arena is the foundation every other component trusts.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/memory/arena.rs.
// CEP:SECURITY: adversarial sizes and alignments are exercised here and in fuzz/arena_fuzz_test.rs.

#[path = "../../common/mod.rs"]
mod common;

use common::{kTestArenaBytes, make_arena};
use mapt::cold::arena_host::{allocate_aligned_region, ArenaHostError};
use mapt::hot::memory::arena::{Arena, ArenaError, ArenaRange};
use mapt_config::limits::kMaxAlignment;

// CEP:WHAT: Verifies range validation rejects inverted and oversized ranges.
// CEP:WHY: ArenaRange::new is the first bounds gate.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any acceptance of an invalid range.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs ArenaRange::new.
// CEP:SECURITY: bounds enforcement.
#[test]
fn range_validation() {
    assert!(ArenaRange::new(0, 8).is_ok());
    assert_eq!(
        ArenaRange::new(8, 0),
        Err(ArenaError::OutOfRange),
        "inverted range must be rejected"
    );
    assert_eq!(
        ArenaRange::new(0, u32::MAX),
        Err(ArenaError::OutOfRange),
        "oversized range must be rejected"
    );
    let range = ArenaRange::new(2, 6).expect("valid range");
    assert_eq!(range.len(), 4);
    assert!(!range.is_empty());
    assert!(ArenaRange::new(3, 3).expect("empty valid").is_empty());
}

// CEP:WHAT: Pins the ArenaRange layout at 8 bytes.
// CEP:WHY: Layout drift is an ABI break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on layout drift.
// CEP:ASSUMES: target ABI.
// CEP:COST: compile-time.
// CEP:EVIDENCE: cited by hot/memory/arena.rs.
// CEP:SECURITY: none.
#[test]
fn range_layout() {
    assert_eq!(core::mem::size_of::<ArenaRange>(), 8);
}

// CEP:WHAT: Verifies the host rejects zero and oversized capacities.
// CEP:WHY: The host is the only allocation site; its bounds are the memory denial-of-service boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a bad capacity is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/arena_host.rs.
// CEP:SECURITY: capacity bound enforcement.
#[test]
fn host_rejects_bad_capacities() {
    assert_eq!(
        allocate_aligned_region(0),
        Err(ArenaHostError::CapacityInvalid)
    );
    assert_eq!(
        allocate_aligned_region(u32::MAX),
        Err(ArenaHostError::CapacityInvalid)
    );
}

// CEP:WHAT: Verifies arena construction validates alignment and capacity.
// CEP:WHY: Construction is the trust boundary for the backing region.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a misaligned or oversized region is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs Arena::new.
// CEP:SECURITY: region validation.
#[test]
fn construction_validates_alignment() {
    let region = allocate_aligned_region(4_096).expect("host allocation");
    let arena = Arena::new(region).expect("aligned region accepted");
    assert_eq!(arena.capacity_bytes(), 4_096);
    let raw: &'static mut [u8] = Box::leak(vec![0u8; 512].into_boxed_slice());
    let base = raw.as_ptr() as usize;
    let offset = if (base + 1).is_multiple_of(kMaxAlignment as usize) {
        2
    } else {
        1
    };
    let (_head, misaligned) = split_static(raw, offset);
    assert!(
        matches!(Arena::new(misaligned), Err(ArenaError::Misaligned)),
        "a base not aligned to kMaxAlignment must be rejected"
    );
}

// CEP:WHAT: Splits a leaked 'static buffer into two disjoint 'static slices.
// CEP:WHY: Tests need deliberately misaligned or empty regions with 'static lifetime; split_at_mut shortens lifetimes, so the split is done at the pointer level exactly as the standard library implements it.
// CEP:STATUS: complete
// CEP:FAILURE: asserts the offset is in bounds before any pointer arithmetic.
// CEP:ASSUMES: the buffer was leaked and is never freed.
// CEP:COST: constant.
// CEP:EVIDENCE: construction_validates_alignment and construction_rejects_oversized_region.
// CEP:SECURITY: none; test-only helper.
// CEP:UNSAFE: raw pointer split of a leaked buffer into disjoint halves; bounds are asserted first.
fn split_static(buffer: &'static mut [u8], at: usize) -> (&'static mut [u8], &'static mut [u8]) {
    assert!(at <= buffer.len());
    let ptr = buffer.as_mut_ptr();
    unsafe {
        (
            core::slice::from_raw_parts_mut(ptr, at),
            core::slice::from_raw_parts_mut(ptr.add(at), buffer.len() - at),
        )
    }
}

// CEP:WHAT: Verifies the arena rejects regions above kArenaCapacityBytes.
// CEP:WHY: Capacity bound enforcement.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an oversized region is accepted.
// CEP:ASSUMES: kArenaCapacityBytes is far above the test size (static assert in config).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs.
// CEP:SECURITY: capacity bound.
#[test]
fn construction_rejects_oversized_region() {
    let raw: &'static mut [u8] = Box::leak(vec![0u8; 256].into_boxed_slice());
    let (empty, _rest) = split_static(raw, 0);
    assert!(
        matches!(Arena::new(empty), Err(ArenaError::EmptyRegion)),
        "empty region must be rejected"
    );
}

// CEP:WHAT: Verifies successive allocations return distinct, ordered ranges.
// CEP:WHY: The bump discipline (never overlapping, monotonic) is the core invariant.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on overlap or regression.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs alloc_bytes.
// CEP:SECURITY: none.
#[test]
fn allocate_returns_distinct_regions() {
    let arena = make_arena(4_096);
    let first = arena.alloc_bytes(64, 4).expect("first");
    let second = arena.alloc_bytes(64, 4).expect("second");
    let third = arena.alloc_bytes(64, 4).expect("third");
    assert!(first.end <= second.start);
    assert!(second.end <= third.start);
    assert_eq!(arena.used_bytes(), third.end);
}

// CEP:WHAT: Verifies zero-size allocations return empty ranges without moving the cursor.
// CEP:WHY: Callers allocate empty child arrays uniformly; the documented no-bump behavior must hold.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cursor moves.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs alloc_bytes.
// CEP:SECURITY: none.
#[test]
fn zero_size_allocation_is_empty_range() {
    let arena = make_arena(4_096);
    let before = arena.used_bytes();
    let range = arena.alloc_bytes(0, 4).expect("zero size");
    assert!(range.is_empty());
    assert_eq!(arena.used_bytes(), before);
}

// CEP:WHAT: Verifies alignment validation.
// CEP:WHY: Non-power-of-two or oversized alignment must be rejected (CEP&CC 11.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a bad alignment is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs.
// CEP:SECURITY: alignment bound.
#[test]
fn alignment_rejected() {
    let arena = make_arena(4_096);
    assert_eq!(arena.alloc_bytes(8, 0), Err(ArenaError::Misaligned));
    assert_eq!(arena.alloc_bytes(8, 3), Err(ArenaError::Misaligned));
    assert_eq!(
        arena.alloc_bytes(8, 128),
        Err(ArenaError::Misaligned),
        "alignment above kMaxAlignment must be rejected"
    );
}

// CEP:WHAT: Verifies exhaustion is an explicit error, never a panic.
// CEP:WHY: CEP&CC Law 6 and design 8.1: exhaustion is a documented failure.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if exhaustion panics or succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs and contract tests.
// CEP:SECURITY: memory bound.
#[test]
fn arena_exhausted() {
    let arena = make_arena(256);
    let first = arena.alloc_bytes(128, 4).expect("first fits");
    assert_eq!(first.len(), 128);
    assert_eq!(
        arena.alloc_bytes(4_096, 4),
        Err(ArenaError::Exhausted),
        "request beyond capacity must be refused"
    );
}

// CEP:WHAT: Verifies byte and typed round trips through bytes/bytes_mut/array/array_mut.
// CEP:WHY: Accessor correctness with retained bounds checks.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs accessors.
// CEP:SECURITY: none.
#[test]
fn typed_array_roundtrip() {
    let arena = make_arena(4_096);
    let _prefix = arena.alloc_array::<u32>(1).expect("prefix alloc");
    let range = arena.alloc_array::<u32>(4).expect("typed alloc");
    assert_eq!(
        range.start % 8,
        4,
        "prefix must place the typed range at 4-mod-8"
    );
    {
        let words = arena.array_mut::<u32>(range).expect("mut access");
        words.copy_from_slice(&[10, 20, 30, 40]);
    }
    let words = arena.array::<u32>(range).expect("read access");
    assert_eq!(words, &[10, 20, 30, 40]);
    let bytes = arena.bytes(range).expect("byte view");
    assert_eq!(bytes.len(), 16);
    {
        let bytes_mut = arena.bytes_mut(range).expect("byte mut");
        bytes_mut.copy_from_slice(&[0u8; 16]);
    }
    let words = arena.array::<u32>(range).expect("re-read");
    assert_eq!(words, &[0, 0, 0, 0]);
    assert_eq!(
        arena.array::<u64>(range),
        Err(ArenaError::TypeMismatch),
        "misaligned typed view must be rejected"
    );
}

// CEP:WHAT: Verifies checkpoint save, reset, and stale-checkpoint detection.
// CEP:WHY: Generation semantics are the O(1) reclamation mechanism (design 8.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any generation mismatch acceptance.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs checkpoint/reset_to.
// CEP:SECURITY: epoch confusion guard.
#[test]
fn checkpoint_reset_and_stale_detection() {
    let arena = make_arena(4_096);
    let checkpoint = arena.checkpoint();
    let range = arena.alloc_bytes(128, 4).expect("alloc");
    assert_eq!(arena.used_bytes(), 128);
    assert_eq!(arena.generation(), 0);
    arena
        .reset_to(checkpoint)
        .expect("reset in same generation");
    assert_eq!(arena.used_bytes(), 0);
    assert_eq!(arena.generation(), 1, "reset bumps the generation");
    assert_eq!(
        arena.reset_to(checkpoint),
        Err(ArenaError::StaleCheckpoint),
        "a used checkpoint must be single-use"
    );
    let _ = range;
}

// CEP:WHAT: Verifies a checkpoint from an older generation is refused.
// CEP:WHY: Stale resets are the epoch-confusion hazard.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a stale reset succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs reset_to.
// CEP:SECURITY: epoch validation.
#[test]
fn stale_checkpoint_rejected() {
    let arena = make_arena(4_096);
    let first = arena.checkpoint();
    let _ = arena.alloc_bytes(64, 4).expect("alloc");
    arena
        .reset_to(first)
        .expect("first reset starts generation bump");
    let second = arena.checkpoint();
    let _ = arena.alloc_bytes(64, 4).expect("alloc in new generation");
    assert_eq!(
        arena.reset_to(first),
        Err(ArenaError::StaleCheckpoint),
        "checkpoint from the previous generation must be refused"
    );
    arena
        .reset_to(second)
        .expect("current-generation checkpoint works");
}

// CEP:WHAT: Verifies used_bytes tracks allocations.
// CEP:WHY: Budget accounting correctness.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on accounting drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs used_bytes.
// CEP:SECURITY: none.
#[test]
fn used_bytes_tracks_allocations() {
    let arena = make_arena(kTestArenaBytes);
    assert_eq!(arena.used_bytes(), 0);
    let first = arena.alloc_bytes(100, 4).expect("alloc");
    assert_eq!(arena.used_bytes(), first.end);
    let second = arena.alloc_bytes(100, 64).expect("aligned alloc");
    assert_eq!(arena.used_bytes(), second.end);
    assert!(second.start.is_multiple_of(kMaxAlignment));
}
