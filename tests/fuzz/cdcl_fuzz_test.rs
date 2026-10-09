// CEP:FILE: tests/fuzz/cdcl_fuzz_test.rs
// CEP:WHAT: Fuzz tests for the CDCL solver: larger random CNFs solved without panics, with model verification on SAT and oracle agreement on a sampled subset, across mixed clause lengths and densities.
// CEP:WHY: CEP&CC 32.10 and design 26: the Phase 2 SAT engine must survive arbitrary clause sets loudly (explicit results, never panics); fuzzing with deterministic seeds makes crashes reproducible.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any panic or invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the deterministic LCG makes every run identical.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/solver.rs fuzz pointers.
// CEP:SECURITY: malformed clause floods are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolveResult};

// CEP:WHAT: Variables in the fuzz formulas.
// CEP:WHY: Named constant; 14 variables keep the oracle (16k assignments) affordable for the sampled subset (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzVariables: u32 = 14;

// CEP:WHAT: Formulas per fuzz run.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzFormulas: u32 = 48;

// CEP:WHAT: Arena bytes for one solver.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzArenaBytes: u32 = 8_388_608;

// CEP:WHAT: Generates one fuzz clause with a random length between 1 and 4 and dense variables.
// CEP:WHY: Fuzzing must mix units, binaries, and longer clauses with repeated variables to hit the watch machinery's edge cases.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure (impossible below the variable count).
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fuzz_clause(rng: &mut DeterministicRng) -> Vec<SatLiteral> {
    let length = 1 + fair_below(rng, 4);
    let mut literals: Vec<SatLiteral> = Vec::new();
    for _ in 0..length {
        let variable = fair_below(rng, kFuzzVariables as u64) as u32;
        literals.push(SatLiteral::new(SatVar(variable), fair_below(rng, 2) == 0).expect("literal"));
    }
    literals
}

// CEP:WHAT: High-bit bounded random draw.
// CEP:WHY: The fixture LCG has alternating low bits (an LCG property), which starves literal polarities; drawing from bits 32..63 restores balanced distributions without changing the committed Phase 1 fixture.
// CEP:STATUS: complete
// CEP:FAILURE: returns 0 when bound is 0 (documented, as below).
// CEP:ASSUMES: bound > 0 for meaningful draws.
// CEP:COST: one shift and one modulo.
// CEP:EVIDENCE: used by fuzz_clause.
// CEP:SECURITY: none.
fn fair_below(rng: &mut DeterministicRng, bound: u64) -> u64 {
    if bound == 0 {
        return 0;
    }
    (rng.next_u64() >> 32) % bound
}

// CEP:WHAT: Fuzz: every random formula solves without panicking, SAT models verify, and a sampled subset agrees with the brute-force oracle.
// CEP:WHY: CEP&CC 22.4 and Law 6: no unreachable states, no panics, explicit outcomes; the oracle sample keeps the run time bounded.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any panic, bad model, or oracle disagreement.
// CEP:ASSUMES: deterministic seeds.
// CEP:COST: one solve per formula plus 2^14 x clauses for every eighth formula.
// CEP:EVIDENCE: cited by hot/sat/solver.rs solve.
// CEP:SECURITY: arbitrary clause sets.
#[test]
fn fuzz_solver_survives_arbitrary_formulas() {
    let mut rng = DeterministicRng::new(0xF00D_0001);
    let mut sat_count = 0;
    let mut unsat_count = 0;
    let mut oracle_checks = 0;
    for index in 0..kFuzzFormulas {
        let clause_count = 20u64 + fair_below(&mut rng, 60);
        let mut formula: Vec<Vec<SatLiteral>> = Vec::new();
        for _ in 0..clause_count {
            formula.push(fuzz_clause(&mut rng));
        }
        let arena = make_arena(kFuzzArenaBytes);
        let solver =
            CdclSolver::new(arena, kFuzzVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            solver.add_clause(clause).expect("add clause");
        }
        let outcome = solver.solve();
        match outcome {
            SolveResult::Satisfiable => {
                sat_count += 1;
                for clause in formula.iter() {
                    let satisfied = clause.iter().any(|literal| {
                        solver.model_value(literal.variable().0) == Some(literal.is_positive())
                    });
                    assert!(satisfied, "fuzz model must satisfy every clause");
                }
            }
            SolveResult::Unsatisfiable => {
                unsat_count += 1;
            }
            SolveResult::Indeterminate(error) => {
                panic!("fuzz solve returned Indeterminate: {:?}", error)
            }
        }
        // Oracle agreement on every eighth formula.
        if index % 8 == 0 {
            oracle_checks += 1;
            let expected = brute_force_satisfiable(&formula);
            let actual = matches!(outcome, SolveResult::Satisfiable);
            assert_eq!(
                expected, actual,
                "fuzz outcome must agree with the brute-force oracle"
            );
        }
    }
    assert!(
        sat_count > 0 && unsat_count > 0,
        "the fuzzer must see both outcomes"
    );
    assert!(oracle_checks > 0);
}

// CEP:WHAT: Fuzz: duplicate-literal and tautology-heavy clauses solve without panicking (sanitization is Phase 3).
// CEP:WHY: Design 11.1 S30-S37 arrive in Phase 3; until then the solver must still terminate loudly on unsanitized input.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any panic or non-terminal outcome.
// CEP:ASSUMES: none.
// CEP:COST: one solve.
// CEP:EVIDENCE: cited by hot/sat/solver.rs solve.
// CEP:SECURITY: unsanitized clause floods.
#[test]
fn fuzz_duplicates_and_tautologies_terminate() {
    let arena = make_arena(kFuzzArenaBytes);
    let solver =
        CdclSolver::new(arena, kFuzzVariables, RestartPolicy::Geometric, false).expect("solver");
    let literal = SatLiteral::new(SatVar(3), true).expect("literal");
    let negated = SatLiteral::new(SatVar(3), false).expect("literal");
    // A clause of many duplicates of one literal.
    let mut duplicated: Vec<SatLiteral> = Vec::new();
    for _ in 0..8 {
        duplicated.push(literal);
    }
    solver.add_clause(&duplicated).expect("duplicates");
    // A tautology (x or -x or ...).
    solver.add_clause(&[literal, negated]).expect("tautology");
    // A contradictory pair of duplicate-heavy clauses.
    solver
        .add_clause(&[SatLiteral::new(SatVar(7), true).expect("literal"); 4])
        .expect("positive duplicates");
    solver
        .add_clause(&[SatLiteral::new(SatVar(7), false).expect("literal"); 4])
        .expect("negative duplicates");
    let outcome = solver.solve();
    assert_eq!(outcome, SolveResult::Unsatisfiable);
}

// CEP:WHAT: Brute-force satisfiability oracle over 14 variables.
// CEP:WHY: The independent reference for the sampled subset.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: dense variables below kFuzzVariables.
// CEP:COST: 2^14 x clauses.
// CEP:EVIDENCE: used by fuzz_solver_survives_arbitrary_formulas.
// CEP:SECURITY: none.
fn brute_force_satisfiable(formula: &[Vec<SatLiteral>]) -> bool {
    for model in 0..(1u64 << kFuzzVariables) {
        let mut satisfied = true;
        for clause in formula.iter() {
            let mut clause_satisfied = false;
            for literal in clause.iter() {
                if ((model >> literal.variable().0) & 1 == 1) == literal.is_positive() {
                    clause_satisfied = true;
                    break;
                }
            }
            if !clause_satisfied {
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
