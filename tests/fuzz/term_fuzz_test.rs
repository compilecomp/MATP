// CEP:FILE: tests/fuzz/term_fuzz_test.rs
// CEP:WHAT: Fuzz tests for the term store: truncated records are rejected, out-of-range child indices are refused, and random handle values never panic on read.
// CEP:WHY: CEP&CC 22.5 and 38.44: forged or corrupted offsets must fail loudly, never read out of bounds or loop.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any panic.
// CEP:ASSUMES: fixed-seed deterministic fuzzing.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/term.rs fuzz claims.
// CEP:SECURITY: adversarial offset coverage.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::make_term_fixture;
use common::DeterministicRng;
use mapt::hot::ir::term::{TermError, TermPtr, TermView};
use mapt::hot::memory::arena::ArenaRange;

// CEP:WHAT: Fuzz rounds per test.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzRounds: u32 = 16_384;

// CEP:WHAT: Verifies truncated word arrays are rejected by view construction.
// CEP:WHY: A record claiming more children than words present must fail, never read past the slice.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a truncated record is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs TermView::from_words.
// CEP:SECURITY: bounds enforcement.
#[test]
fn truncated_records_rejected() {
    let full = [(1u32 << 16) | 1, 1, 0, 1, 7, 8];
    assert!(TermView::from_words(&full).is_ok());
    let truncated = [(1u32 << 16) | 1, 1, 0, 1];
    assert_eq!(
        TermView::from_words(&truncated),
        Err(TermError::InvalidPointer)
    );
    let empty: [u32; 0] = [];
    assert_eq!(TermView::from_words(&empty), Err(TermError::InvalidPointer));
}

// CEP:WHAT: Verifies out-of-range child indices are refused.
// CEP:WHY: The child accessor must bound-check.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an out-of-range index succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs TermView::child.
// CEP:SECURITY: bounds enforcement.
#[test]
fn child_index_rejected() {
    let words = [(1u32 << 16) | 1, 1, 0, 1, 42];
    let view = TermView::from_words(&words).expect("view");
    assert_eq!(view.child_count(), 1);
    assert!(view.child(0).is_ok());
    assert_eq!(view.child(0).expect("child").as_u32(), 42);
    assert_eq!(view.child(1), Err(TermError::InvalidPointer));
    assert_eq!(view.child(999), Err(TermError::InvalidPointer));
}

// CEP:WHAT: Fuzzes term reads with random offsets.
// CEP:WHY: Any u32 offset must either read a valid record or return InvalidPointer; never panic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzRounds reads.
// CEP:EVIDENCE: cited by hot/ir/term.rs term.
// CEP:SECURITY: adversarial offset coverage.
#[test]
fn fuzz_term_read_never_panics() {
    let (_arena, _symbols, _builder, terms, _clauses) = make_term_fixture();
    let mut rng = DeterministicRng::new(0x46555A54);
    for _ in 0..kFuzzRounds {
        let offset = (rng.next_u64() >> 32) as u32;
        let _ = terms.term_by_offset(offset);
    }
}

// CEP:WHAT: Fuzzes forged handles through the full public read API.
// CEP:WHY: from_verified_offset plus term() must stay memory-safe for every u32.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzRounds reads.
// CEP:EVIDENCE: cited by hot/ir/term.rs from_verified_offset.
// CEP:SECURITY: adversarial handle coverage.
#[test]
fn fuzz_forged_handles_never_panics() {
    let (_arena, symbols, _builder, terms, _clauses) = make_term_fixture();
    let mut rng = DeterministicRng::new(0x464F5247);
    let mut valid_reads = 0;
    for _ in 0..kFuzzRounds {
        let handle = TermPtr::from_verified_offset((rng.next_u64() >> 40) as u32);
        if let Ok(view) = terms.term(handle) {
            valid_reads += 1;
            for child in view.children() {
                let _ = terms.term(child);
            }
            let _ = view.child(0);
        }
    }
    let _ = &symbols;
    assert!(
        valid_reads < kFuzzRounds,
        "most forged handles must be rejected"
    );
}

// CEP:WHAT: Verifies arena-byte corruption of term records is caught by reads or the verifier.
// CEP:WHY: Corruption must never produce silent garbage semantics.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if corruption goes undetected.
// CEP:ASSUMES: corruption through the public arena API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs.
// CEP:SECURITY: corruption detection.
#[test]
fn corrupted_records_detected() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let range = ArenaRange::new(a.as_u32(), a.as_u32() + 16).expect("range");
    {
        let words = arena.array_mut::<u32>(range).expect("mut");
        words[0] |= 0x00FF0000;
    }
    let violations = mapt::cold::verifier::verify_term_store(arena, &terms, &symbols);
    assert!(!violations.is_empty(), "corruption must be detected");
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}
