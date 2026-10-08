// CEP:FILE: tests/contract/arena_contract_test.rs
// CEP:WHAT: Contract tests for the arena: exhaustion is an explicit error never a panic, misalignment is refused, and checkpoint contracts hold.
// CEP:WHY: CEP&CC Law 6 (no unbounded failure) and 32.8: API contracts must be executable; these tests pin the failure behavior callers depend on.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on contract violations.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/memory/arena.rs contract claims.
// CEP:SECURITY: adversarial sizes are part of the contract.

#[path = "../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::memory::arena::ArenaError;

// CEP:WHAT: Verifies exhaustion under repeated maximal allocations is always an error.
// CEP:WHY: Callers rely on exhaust-then-error, never panic (design 8.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any allocation panics or succeeds past capacity.
// CEP:ASSUMES: none.
// CEP:COST: fills a small arena completely.
// CEP:EVIDENCE: cited by hot/memory/arena.rs alloc_bytes.
// CEP:SECURITY: memory bound contract.
#[test]
fn exhaustion_is_explicit_error_never_panic() {
    let arena = make_arena(1_024);
    let mut allocated = 0;
    loop {
        match arena.alloc_bytes(256, 4) {
            Ok(range) => {
                allocated += range.len();
                assert!(allocated <= arena.capacity_bytes());
            }
            Err(ArenaError::Exhausted) => break,
            Err(other) => panic!("unexpected error: {:?}", other),
        }
    }
    assert!(
        arena.used_bytes() + 256 > arena.capacity_bytes(),
        "exhaustion must be real"
    );
    assert_eq!(
        arena.alloc_bytes(1, 4),
        Err(ArenaError::Exhausted),
        "post-exhaustion allocation must keep failing"
    );
}

// CEP:WHAT: Verifies the misalignment contract for every illegal alignment form.
// CEP:WHY: Zero, non-power-of-two, and oversized alignments are all refused.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any illegal alignment is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs alloc_bytes.
// CEP:SECURITY: alignment contract.
#[test]
fn misalignment_contract() {
    let arena = make_arena(1_024);
    let illegal = [0u32, 3, 5, 6, 7, 12, 100, 65, 128];
    for align in illegal.iter() {
        assert_eq!(
            arena.alloc_bytes(8, *align),
            Err(ArenaError::Misaligned),
            "alignment {} must be rejected",
            align
        );
    }
    let legal = [1u32, 2, 4, 8, 16, 32, 64];
    for align in legal.iter() {
        assert!(
            arena.alloc_bytes(8, *align).is_ok(),
            "alignment {} must be accepted",
            align
        );
    }
}

// CEP:WHAT: Verifies checkpoints are single-use within a generation.
// CEP:WHY: Callers depend on the documented single-use semantics.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a checkpoint is reusable.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/memory/arena.rs reset_to.
// CEP:SECURITY: none.
#[test]
fn checkpoint_single_use_contract() {
    let arena = make_arena(1_024);
    let checkpoint = arena.checkpoint();
    let _ = arena.alloc_bytes(64, 4).expect("alloc");
    arena.reset_to(checkpoint).expect("first use");
    assert_eq!(
        arena.reset_to(checkpoint),
        Err(ArenaError::StaleCheckpoint),
        "second use in a new generation must fail"
    );
    let fresh = arena.checkpoint();
    arena.reset_to(fresh).expect("fresh checkpoint works");
}
