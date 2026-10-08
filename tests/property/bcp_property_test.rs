// CEP:FILE: tests/property/bcp_property_test.rs
// CEP:WHAT: Property tests for BCP: soundness against a brute-force oracle on random formulas, fixpoint completeness, and watch-list integrity.
// CEP:WHY: CEP&CC 38.43 and design 11.4: every learnt assignment must be a logical consequence; the fixpoint property (no clause unit-and-unassigned remains) defines propagation completeness; watch-list integrity is the data-structure invariant the whole scheme rests on.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the oracle enumerates all 2^n assignments of the random formula.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/bcp.rs soundness and integrity claims.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::{make_sat_fixture, DeterministicRng};
use mapt::hot::sat::assignment::SatValue;
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::database::AttachOutcome;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt_config::limits::kInvalidClauseOffset;

// CEP:WHAT: Number of random formulas per property test.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyFormulas: u32 = 256;

// CEP:WHAT: Variables per random formula.
// CEP:WHY: Small enough for the 2^n oracle, large enough for nontrivial propagation.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kOracleVariables: u32 = 10;

// CEP:WHAT: Builds one random literal.
// CEP:WHY: Shared fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: variable below kOracleVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_literal(rng: &mut DeterministicRng, variables: u32) -> SatLiteral {
    let variable = rng.below(variables as u64) as u32;
    let positive = rng.below(2) == 0;
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Verifies BCP soundness: every propagated assignment is entailed by the formula.
// CEP:WHY: An unsound propagation would corrupt every later proof step; the oracle checks that each propagated literal is true in every model of the clauses (design 11.4 correctness).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any propagated literal is not entailed.
// CEP:ASSUMES: units enqueue at level 0 and conflicts abort the formula.
// CEP:COST: 2^kOracleVariables model enumeration per formula.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs soundness.
// CEP:SECURITY: none.
#[test]
fn propagation_is_sound() {
    let mut rng = DeterministicRng::new(0x534F554E);
    for _ in 0..kPropertyFormulas {
        let (_arena, core) = make_sat_fixture(kOracleVariables);
        let mut clauses: Vec<Vec<SatLiteral>> = Vec::new();
        for _ in 0..rng.below(12) + 2 {
            let length = rng.below(3) + 1;
            let mut clause = Vec::new();
            for _ in 0..length {
                clause.push(random_literal(&mut rng, kOracleVariables));
            }
            clauses.push(clause);
        }
        let mut conflict = false;
        for clause in clauses.iter() {
            match core.add_clause(clause) {
                Ok(AttachOutcome::Conflict) => {
                    conflict = true;
                    break;
                }
                Ok(_) => {}
                Err(_) => {
                    conflict = true;
                    break;
                }
            }
        }
        if conflict {
            continue;
        }
        let outcome = core.propagate().expect("propagate");
        if let PropagationOutcome::Conflict(_) = outcome {
            continue;
        }
        // Oracle: collect models of the formula.
        let mut models: Vec<Vec<bool>> = Vec::new();
        for assignment in 0..(1u64 << kOracleVariables) {
            let values: Vec<bool> = (0..kOracleVariables)
                .map(|variable| assignment & (1 << variable) != 0)
                .collect();
            let satisfied = clauses.iter().all(|clause| {
                clause
                    .iter()
                    .any(|literal| values[literal.variable().0 as usize] == literal.is_positive())
            });
            if satisfied {
                models.push(values);
            }
        }
        if models.is_empty() {
            continue;
        }
        for variable in 0..kOracleVariables {
            let literal = SatLiteral::new(SatVar(variable), true).expect("literal");
            if core.value_of_literal(literal) == SatValue::True {
                assert!(
                    models.iter().all(|model| model[variable as usize]),
                    "propagated variable {} must be true in every model",
                    variable
                );
            }
            if core.value_of_literal(literal) == SatValue::False {
                assert!(
                    models.iter().all(|model| !model[variable as usize]),
                    "propagated variable {} must be false in every model",
                    variable
                );
            }
        }
    }
}

// CEP:WHAT: Verifies the propagation fixpoint: no clause is unit with an unassigned literal after a clean run.
// CEP:WHY: Completeness of unit propagation (design 11.1 S9).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a unit clause remains unpropagated.
// CEP:ASSUMES: none.
// CEP:COST: linear in clauses times literals.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs propagate.
// CEP:SECURITY: none.
#[test]
fn propagation_reaches_fixpoint() {
    let mut rng = DeterministicRng::new(0x46495850);
    for _ in 0..kPropertyFormulas {
        let (_arena, core) = make_sat_fixture(kOracleVariables);
        let mut offsets = Vec::new();
        for _ in 0..rng.below(12) + 2 {
            let length = rng.below(3) + 2;
            let mut clause = Vec::new();
            for _ in 0..length {
                clause.push(random_literal(&mut rng, kOracleVariables));
            }
            if let Ok(AttachOutcome::Attached(offset)) = core.add_clause(&clause) {
                offsets.push(offset);
            }
        }
        if core.propagate().expect("propagate") == PropagationOutcome::NoConflict {
            for offset in offsets.iter() {
                let header = core.clauses().header(*offset).expect("header");
                let mut unassigned = 0;
                for index in 0..header.length {
                    let literal = core.clauses().literal(*offset, index).expect("literal");
                    if core.value_of_literal(literal) == SatValue::Unassigned {
                        unassigned += 1;
                    }
                }
                assert!(
                    unassigned != 1,
                    "a unit clause must not remain unpropagated after a clean run"
                );
            }
        }
    }
}

// CEP:WHAT: Verifies watch-list integrity: every attached clause appears exactly in the lists of its first two literals.
// CEP:WHY: The watched-literal invariant is the correctness core of the amortized O(1) scheme.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missing or duplicated membership.
// CEP:ASSUMES: none.
// CEP:COST: linear in total list length.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs scan_watch_list.
// CEP:SECURITY: none.
#[test]
fn watch_lists_consistent() {
    let mut rng = DeterministicRng::new(0x5741544348);
    for _ in 0..kPropertyFormulas {
        let (_arena, core) = make_sat_fixture(kOracleVariables);
        let mut offsets = Vec::new();
        for _ in 0..rng.below(12) + 2 {
            let length = rng.below(3) + 2;
            let mut clause = Vec::new();
            for _ in 0..length {
                clause.push(random_literal(&mut rng, kOracleVariables));
            }
            if let Ok(AttachOutcome::Attached(offset)) = core.add_clause(&clause) {
                offsets.push(offset);
            }
        }
        let _ = core.propagate();
        for offset in offsets.iter() {
            for slot in 0..2u32 {
                let watched = core
                    .clauses()
                    .literal(*offset, slot)
                    .expect("watched literal");
                let mut cursor = core.watches().head(watched);
                let mut found = false;
                let mut hops = 0;
                while cursor != kInvalidClauseOffset {
                    assert!(hops <= offsets.len() * 2 + 2, "watch list must terminate");
                    hops += 1;
                    if cursor == *offset {
                        found = true;
                        break;
                    }
                    let lit0 = core.clauses().literal(cursor, 0).expect("literal 0");
                    let slot = if lit0 == watched { 0 } else { 1 };
                    cursor = core.clauses().next_in_watch(cursor, slot).expect("link");
                }
                assert!(
                    found,
                    "clause {} must be reachable from its watched literal at slot {}",
                    offset, slot
                );
            }
        }
    }
}
