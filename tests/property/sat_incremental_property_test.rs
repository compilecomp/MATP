// CEP:FILE: tests/property/sat_incremental_property_test.rs
// CEP:WHAT: Property tests for assumption-based incremental solving: agreement with a brute-force oracle over random formulas and assumption sets, and validity of extracted failed cores.
// CEP:WHY: Spec 10 sections 3-5: the assumption solve's three-way outcome must agree with the oracle on formula-plus-assumptions satisfiability, and every reported core's conjunction must be refutable with the formula.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any disagreement.
// CEP:ASSUMES: the deterministic LCG; small variable counts keep brute force exact.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/solver.rs::solve_with_assumptions and hot/sat/cdcl.rs::analyze_final.
// CEP:SECURITY: no untrusted input; fixed seeds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{AssumptionOutcome, CdclSolver};

// CEP:WHAT: Variables per formula.
// CEP:WHY: Brute force is 2^n; 8 keeps the oracle exact.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 8;

// CEP:WHAT: Formulas per run.
// CEP:WHY: Named property-test size (CEP&CC 28.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFormulas: u64 = 60;

// CEP:WHAT: Brute-force satisfiability of a formula under unit assumptions.
// CEP:WHY: The oracle: assignments fixed by the assumption literals.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: variables below kVariables.
// CEP:COST: O(2^n x clauses).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn brute_force_under(formula: &[Vec<SatLiteral>], assumptions: &[SatLiteral]) -> bool {
    for assignment in 0..(1u64 << kVariables) {
        let assumptions_ok = assumptions.iter().all(|literal| {
            ((assignment >> literal.variable().0) & 1 == 1) == literal.is_positive()
        });
        if !assumptions_ok {
            continue;
        }
        let satisfied = formula.iter().all(|clause| {
            clause.iter().any(|literal| {
                ((assignment >> literal.variable().0) & 1 == 1) == literal.is_positive()
            })
        });
        if satisfied {
            return true;
        }
    }
    false
}

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Verifies assumption solves agree with brute force.
// CEP:WHY: Spec 10's three-way outcome contract, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any outcome disagreement.
// CEP:ASSUMES: none.
// CEP:COST: 60 formulas x oracles.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::solve_with_assumptions.
// CEP:SECURITY: none.
#[test]
fn assumption_solves_agree_with_brute_force() {
    let mut rng = DeterministicRng::new(0xFACE_0005);
    for _ in 0..kFormulas {
        let clause_count = 3 + rng.below(8u64);
        let mut formula: Vec<Vec<SatLiteral>> = Vec::new();
        for _ in 0..clause_count {
            let length = 1 + rng.below(3u64);
            let mut clause: Vec<SatLiteral> = Vec::new();
            for _ in 0..length {
                clause.push(lit(
                    rng.below(kVariables as u64) as u32,
                    rng.below(2u64) == 0,
                ));
            }
            formula.push(clause);
        }
        let mut assumptions: Vec<SatLiteral> = Vec::new();
        for _ in 0..(1 + rng.below(3u64)) {
            assumptions.push(lit(
                rng.below(kVariables as u64) as u32,
                rng.below(2u64) == 0,
            ));
        }
        let oracle = brute_force_under(&formula, &assumptions);
        let arena = make_arena(12_582_912);
        let solver =
            CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            solver.add_clause(clause).expect("add");
        }
        let outcome = solver.solve_with_assumptions(&assumptions);
        match outcome {
            AssumptionOutcome::Satisfiable => assert!(
                oracle,
                "solver says SAT under assumptions, oracle says UNSAT"
            ),
            AssumptionOutcome::UnsatUnderAssumptions => assert!(
                !oracle,
                "solver says UNSAT under assumptions, oracle says SAT"
            ),
            AssumptionOutcome::Unsatisfiable => {
                // The formula alone is refuted: the oracle must agree on the
                // formula-only satisfiability too.
                let formula_only = brute_force_under(&formula, &[]);
                assert!(!formula_only, "formula-only refutation must be sound");
            }
            AssumptionOutcome::Indeterminate(error) => {
                panic!("unexpected indeterminate: {:?}", error)
            }
        }
    }
}

// CEP:WHAT: Verifies extracted failed cores are valid: the formula plus the core is unsatisfiable.
// CEP:WHY: Spec 10 section 4's soundness statement, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a core's conjunction is satisfiable with the formula.
// CEP:ASSUMES: cores only from UnsatUnderAssumptions outcomes.
// CEP:COST: 60 formulas x oracles.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{failed_assumptions_into, record_core} and hot/sat/cdcl.rs::analyze_final.
// CEP:SECURITY: none.
#[test]
fn cores_are_valid() {
    let mut rng = DeterministicRng::new(0xFACE_0006);
    for _ in 0..kFormulas {
        let clause_count = 3 + rng.below(8u64);
        let mut formula: Vec<Vec<SatLiteral>> = Vec::new();
        for _ in 0..clause_count {
            let length = 1 + rng.below(3u64);
            let mut clause: Vec<SatLiteral> = Vec::new();
            for _ in 0..length {
                clause.push(lit(
                    rng.below(kVariables as u64) as u32,
                    rng.below(2u64) == 0,
                ));
            }
            formula.push(clause);
        }
        let mut assumptions: Vec<SatLiteral> = Vec::new();
        for _ in 0..(1 + rng.below(3u64)) {
            assumptions.push(lit(
                rng.below(kVariables as u64) as u32,
                rng.below(2u64) == 0,
            ));
        }
        let arena = make_arena(12_582_912);
        let solver =
            CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            solver.add_clause(clause).expect("add");
        }
        let outcome = solver.solve_with_assumptions(&assumptions);
        if let AssumptionOutcome::UnsatUnderAssumptions = outcome {
            let mut core = [lit(0, true); 8];
            let count = solver.failed_assumptions_into(&mut core);
            assert!(count >= 1, "an unsat-under-assumptions core is nonempty");
            let core_valid = !brute_force_under(&formula, &core[..count]);
            assert!(
                core_valid,
                "the formula plus the core must be unsatisfiable (core len {})",
                count
            );
        }
    }
}
