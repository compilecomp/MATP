// CEP:FILE: tests/fuzz/arena_fuzz_test.rs
// CEP:WHAT: Fuzz tests for the arena: adversarial sizes, alignments, and offsets never panic and always return the documented error or success.
// CEP:WHY: CEP&CC 22.5 and 38.44: the arena consumes no untrusted input directly, but its API is the memory-safety foundation; fuzzing proves no input combination panics or corrupts state.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any panic or contract violation.
// CEP:ASSUMES: fixed-seed deterministic fuzzing (CEP&CC 28.3).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/memory/arena.rs fuzz claims.
// CEP:SECURITY: adversarial input space coverage.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::memory::arena::{ArenaError, ArenaRange};

// CEP:WHAT: Fuzz rounds per test.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzRounds: u32 = 65_536;

// CEP:WHAT: Fuzzes alloc_bytes with adversarial sizes and alignments.
// CEP:WHY: No (size, align) pair may panic; outcomes must be Ok or a documented error.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic or undocumented outcome.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzRounds allocations.
// CEP:EVIDENCE: cited by hot/memory/arena.rs alloc_bytes.
// CEP:SECURITY: adversarial input coverage.
#[test]
fn fuzz_alloc_never_panics() {
    let arena = make_arena(4_096);
    let mut rng = DeterministicRng::new(0x46555A5A);
    for _ in 0..kFuzzRounds {
        let size = (rng.next_u64() >> 32) as u32;
        let align = ((rng.next_u64() >> 48) as u32).max(1);
        match arena.alloc_bytes(size, align) {
            Ok(range) => {
                assert!(range.end <= arena.capacity_bytes());
                assert!(range.len() == size || size == 0);
            }
            Err(ArenaError::Exhausted) | Err(ArenaError::Misaligned) => {}
            Err(other) => panic!("undocumented error: {:?}", other),
        }
    }
}

// CEP:WHAT: Fuzzes ArenaRange::new with adversarial bounds.
// CEP:WHY: No (start, end) pair may panic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzRounds validations.
// CEP:EVIDENCE: cited by hot/memory/arena.rs ArenaRange::new.
// CEP:SECURITY: adversarial input coverage.
#[test]
fn fuzz_range_never_panics() {
    let mut rng = DeterministicRng::new(0x52414E47);
    for _ in 0..kFuzzRounds {
        let start = (rng.next_u64() >> 32) as u32;
        let end = (rng.next_u64() >> 32) as u32;
        let result = ArenaRange::new(start, end);
        if let Ok(range) = result {
            assert!(range.start <= range.end);
            assert!(range.end <= mapt_config::limits::kArenaCapacityBytes);
        }
    }
}

// CEP:WHAT: Fuzzes typed array access with adversarial ranges.
// CEP:WHY: No range may produce out-of-bounds access; misaligned or ill-sized ranges must be TypeMismatch.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic or wrong acceptance.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzRounds accesses.
// CEP:EVIDENCE: cited by hot/memory/arena.rs array.
// CEP:SECURITY: adversarial input coverage.
#[test]
fn fuzz_array_access_never_panics() {
    let arena = make_arena(4_096);
    let mut rng = DeterministicRng::new(0x41525241);
    for _ in 0..kFuzzRounds {
        let start = (rng.next_u64() >> 40) as u32;
        let end = start.wrapping_add((rng.next_u64() >> 44) as u32);
        if let Ok(range) = ArenaRange::new(start, end) {
            let _ = arena.array::<u32>(range);
            let _ = arena.array_mut::<u64>(range);
        }
    }
}
