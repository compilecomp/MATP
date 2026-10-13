// CEP:FILE: tests/property/sat_preprocess_property_test.rs
// CEP:WHAT: Property tests for SAT preprocessing: satisfiability preservation against a brute-force oracle over random formulas, and size monotonicity (the live database never grows across a completed pass).
// CEP:WHY: Spec 09 theorems 1-4: tautology deletion, subsumption deletion, duplicate removal, strengthening, and vivification each preserve satisfiability; the brute-force oracle verifies the composed pass on every generated formula.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any preserved-satisfiability violation.
// CEP:ASSUMES: the deterministic LCG from tests/common/mod.rs; small variable counts keep brute force exact.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/preprocess.rs.
// CEP:SECURITY: no untrusted input; fixed seeds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::preprocess::{simplify, SimplifyOptions, SimplifyStatus};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::CdclSolver;

// CEP:WHAT: Variables per formula.
// CEP:WHY: Brute force is 2^n; 8 keeps the oracle exact and fast.
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

// CEP:WHAT: Brute-force satisfiability oracle.
// CEP:WHY: The independent ground truth for the preservation check.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: clauses use variables below kVariables.
// CEP:COST: O(2^n x clauses).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn brute_force_satisfiable(formula: &[Vec<SatLiteral>]) -> bool {
    for assignment in 0..(1u64 << kVariables) {
        let mut satisfied = true;
        for clause in formula.iter() {
            let clause_ok = clause.iter().any(|literal| {
                let bit = (assignment >> literal.variable().0) & 1 == 1;
                bit == literal.is_positive()
            });
            if !clause_ok {
                satisfied = false;
                break;
            }
        }
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

// CEP:WHAT: Verifies preprocessing preserves satisfiability on random formulas.
// CEP:WHY: Spec 09's combined-preservation theorem, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a satisfiable formula becomes unsatisfiable or vice versa.
// CEP:ASSUMES: the preprocessing result is either Complete or a budget stop; both preserve satisfiability by theorem.
// CEP:COST: 60 formulas x brute force.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs (file header) and config/limits.rs kSatSubsumptionPairBudget.
// CEP:SECURITY: none.
#[test]
fn preprocessing_preserves_satisfiability() {
    let mut rng = DeterministicRng::new(0xBEEF_0003);
    for _ in 0..kFormulas {
        let clause_count = 3 + rng.below(9u64);
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
        let before = brute_force_satisfiable(&formula);
        let arena = make_arena(12_582_912);
        let solver =
            CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            // The solver rejects the empty clause literal list; empty clauses in the
            // random formula mean immediate UNSAT, which the oracle also reports.
            if clause.is_empty() {
                continue;
            }
            solver.add_clause(clause).expect("add");
        }
        let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
        match outcome.status {
            SimplifyStatus::Unsatisfiable => assert!(
                !before,
                "a satisfiable formula was refuted by preprocessing"
            ),
            _ => {
                let after = solver.solve();
                let after_sat = matches!(after, mapt::hot::sat::solver::SolveResult::Satisfiable);
                assert_eq!(
                    before, after_sat,
                    "satisfiability must be preserved (before {})",
                    before
                );
            }
        }
    }
}

// CEP:WHAT: Verifies a completed pass never grows the live database.
// CEP:WHY: Every rewrite replaces one clause with a smaller-or-equal one or deletes outright.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the live count grows.
// CEP:ASSUMES: the pass completed (budget stops may leave the set mid-rewrite).
// CEP:COST: 40 formulas.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, SimplifyStats}.
// CEP:SECURITY: none.
#[test]
fn preprocessing_shrinks_or_preserves() {
    let mut rng = DeterministicRng::new(0xBEEF_0004);
    for _ in 0..40 {
        let clause_count = 3 + rng.below(8u64);
        let arena = make_arena(12_582_912);
        let solver =
            CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
        let mut input_count = 0usize;
        for _ in 0..clause_count {
            let length = 1 + rng.below(3u64);
            let mut clause: Vec<SatLiteral> = Vec::new();
            for _ in 0..length {
                clause.push(lit(
                    rng.below(kVariables as u64) as u32,
                    rng.below(2u64) == 0,
                ));
            }
            solver.add_clause(&clause).expect("add");
            input_count += 1;
        }
        let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
        if !matches!(outcome.status, SimplifyStatus::Complete) {
            continue;
        }
        let live = (0..solver.registry().entry_count())
            .filter(|index| {
                !solver
                    .registry()
                    .entry(*index)
                    .expect("entry")
                    .tombstone
                    .get()
            })
            .count();
        assert!(
            live <= input_count,
            "the live database must not grow: {} > {}",
            live,
            input_count
        );
    }
}
