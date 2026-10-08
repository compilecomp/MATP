// CEP:FILE: tests/fuzz/sat_fuzz_test.rs
// CEP:WHAT: Fuzz tests for the SAT core: random clause sets with occasional invalid input never panic, and structural invariants hold after propagation.
// CEP:WHY: CEP&CC 22.5 and 38.44: DIMACS input is untrusted (design 25.1); the core must refuse bad input loudly and stay sound on valid input.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any panic or invariant break.
// CEP:ASSUMES: fixed-seed deterministic fuzzing.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/clause.rs and hot/sat/bcp.rs fuzz claims.
// CEP:SECURITY: adversarial input coverage.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::{make_sat_fixture, DeterministicRng};
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::database::AttachOutcome;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt_config::limits::kInvalidClauseOffset;

// CEP:WHAT: Fuzz rounds per test.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzFormulas: u32 = 1_024;

// CEP:WHAT: Fuzzes clause creation and propagation with occasional invalid literals.
// CEP:WHY: Invalid input must be refused loudly; valid input must propagate without panic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any panic.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzFormulas formulas.
// CEP:EVIDENCE: cited by hot/sat/clause.rs new_clause.
// CEP:SECURITY: adversarial input coverage.
#[test]
fn fuzz_clause_creation_never_panics() {
    let mut rng = DeterministicRng::new(0x46555A53);
    for _ in 0..kFuzzFormulas {
        let (_arena, core) = make_sat_fixture(8);
        for _ in 0..16 {
            let length = rng.below(5) as usize;
            let mut literals = Vec::with_capacity(length);
            for _ in 0..length {
                // Deliberately include out-of-range variables in the adversarial stream.
                let variable = rng.below(12) as u32;
                let positive = rng.below(2) == 0;
                if let Ok(literal) = SatLiteral::new(SatVar(variable), positive) {
                    literals.push(literal);
                }
            }
            let _ = core.add_clause(&literals);
        }
        let _ = core.propagate();
    }
}

// CEP:WHAT: Fuzzes propagation followed by full invariant verification.
// CEP:WHY: After any propagation run, watch lists must be consistent and assignments must satisfy the no-violated-clause property when no conflict was reported.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any invariant break.
// CEP:ASSUMES: only valid clauses are added.
// CEP:COST: kFuzzFormulas formulas with invariant scans.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs propagate.
// CEP:SECURITY: none.
#[test]
fn fuzz_propagation_invariants_hold() {
    let mut rng = DeterministicRng::new(0x494E5641);
    for _ in 0..kFuzzFormulas {
        let (_arena, core) = make_sat_fixture(8);
        let mut offsets = Vec::new();
        for _ in 0..12 {
            let length = rng.below(3) as usize + 1;
            let mut literals = Vec::with_capacity(length);
            for _ in 0..length {
                let variable = rng.below(8) as u32;
                let positive = rng.below(2) == 0;
                literals.push(SatLiteral::new(SatVar(variable), positive).expect("literal"));
            }
            if let Ok(AttachOutcome::Attached(offset)) = core.add_clause(&literals) {
                offsets.push(offset);
            }
        }
        let outcome = core.propagate().expect("propagate");
        if let PropagationOutcome::Conflict(_) = outcome {
            continue;
        }
        for offset in offsets.iter() {
            let header = core.clauses().header(*offset).expect("header");
            let mut has_nonfalse = false;
            for index in 0..header.length {
                let literal = core.clauses().literal(*offset, index).expect("literal");
                if core.value_of_literal(literal) != mapt::hot::sat::assignment::SatValue::False {
                    has_nonfalse = true;
                }
            }
            assert!(has_nonfalse, "a clean run must leave no violated clause");
        }
        // Watch membership: every clause is reachable from both watched literals.
        for offset in offsets.iter() {
            for slot in 0..2u32 {
                let watched = core.clauses().literal(*offset, slot).expect("watched");
                let mut cursor = core.watches().head(watched);
                let mut found = false;
                let mut hops = 0;
                while cursor != kInvalidClauseOffset {
                    hops += 1;
                    assert!(hops <= offsets.len() * 2 + 2, "lists must terminate");
                    if cursor == *offset {
                        found = true;
                        break;
                    }
                    let lit0 = core.clauses().literal(cursor, 0).expect("lit0");
                    let link_slot = if lit0 == watched { 0 } else { 1 };
                    cursor = core
                        .clauses()
                        .next_in_watch(cursor, link_slot)
                        .expect("link");
                }
                assert!(found, "clause must remain reachable from its watches");
            }
        }
    }
}

// CEP:WHAT: Fuzzes adversarial header and literal reads.
// CEP:WHY: Random offsets must never panic on read.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on panic.
// CEP:ASSUMES: none.
// CEP:COST: kFuzzFormulas reads.
// CEP:EVIDENCE: cited by hot/sat/clause.rs header/literal.
// CEP:SECURITY: adversarial offset coverage.
#[test]
fn fuzz_header_reads_never_panics() {
    let (_arena, core) = make_sat_fixture(8);
    core.add_clause(&[
        SatLiteral::new(SatVar(0), true).expect("literal"),
        SatLiteral::new(SatVar(1), false).expect("literal"),
    ])
    .expect("clause");
    let mut rng = DeterministicRng::new(0x48454144);
    for _ in 0..kFuzzFormulas {
        let offset = (rng.next_u64() >> 40) as u32;
        let _ = core.clauses().header(offset);
        let index = (rng.next_u64() >> 48) as u32;
        if let Ok(header) = core.clauses().header(offset) {
            if index < header.length {
                let _ = core.clauses().literal(offset, index);
            }
        }
        let _ = core.clauses().literal(offset, index);
    }
}
