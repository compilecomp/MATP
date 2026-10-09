// CEP:FILE: tests/property/cdcl_property_test.rs
// CEP:WHAT: Property tests for the CDCL solver: solve outcomes agree with a brute-force oracle on random 3-CNFs, satisfying models satisfy every clause, and learnt clauses are false only under the current assignment and entailed by the original formula.
// CEP:WHY: CEP&CC 32.9 and Formal Spec 06 section 8: SAT/UNSAT correctness is the strongest property of the engine; the brute-force oracle is the independent reference; the learnt-clause checks verify the analysis directly on a manual search loop.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any violated property.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the deterministic LCG makes every run identical.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/cdcl.rs and hot/sat/solver.rs property pointers.
// CEP:SECURITY: none; no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::cdcl::{CdclError, ConflictAnalyzer};
use mapt::hot::sat::database::SatCore;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolveResult};
use mapt::hot::sat::vsids::VsidsHeap;

// CEP:WHAT: Variables in the random formulas.
// CEP:WHY: Named constant; 10 variables keep the brute-force oracle at 1024 models per formula (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kOracleVariables: u32 = 10;

// CEP:WHAT: Clauses per random formula.
// CEP:WHY: Named constant; 24 clauses over 10 variables at ratio 2.4 sits near the SAT/UNSAT phase transition, exercising both outcomes.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kOracleClauses: u32 = 24;

// CEP:WHAT: Formulas per test.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kOracleFormulas: u32 = 32;

// CEP:WHAT: Arena bytes for one solver.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kSolverArenaBytes: u32 = 8_388_608;

// CEP:WHAT: One random 3-CNF clause.
// CEP:WHY: The oracle formulas are 3-CNFs with distinct variables per clause.
// CEP:STATUS: complete
// CEP:FAILURE: panics on literal construction failure (impossible below the variable count).
// CEP:ASSUMES: rng with enough entropy.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_clause(rng: &mut DeterministicRng) -> Vec<SatLiteral> {
    let mut variables: Vec<u32> = Vec::new();
    while variables.len() < 3 {
        let candidate = fair_below(rng, kOracleVariables as u64) as u32;
        if !variables.contains(&candidate) {
            variables.push(candidate);
        }
    }
    variables
        .iter()
        .map(|variable| {
            SatLiteral::new(SatVar(*variable), fair_below(rng, 2) == 0).expect("literal")
        })
        .collect()
}

// CEP:WHAT: High-bit bounded random draw.
// CEP:WHY: The fixture LCG has alternating low bits (an LCG property), which starves literal polarities; drawing from bits 32..63 restores balanced polarity and variable distributions without changing the committed Phase 1 fixture.
// CEP:STATUS: complete
// CEP:FAILURE: returns 0 when bound is 0 (documented, as below).
// CEP:ASSUMES: bound > 0 for meaningful draws.
// CEP:COST: one shift and one modulo.
// CEP:EVIDENCE: used by random_clause and random_formula.
// CEP:SECURITY: none.
fn fair_below(rng: &mut DeterministicRng, bound: u64) -> u64 {
    if bound == 0 {
        return 0;
    }
    (rng.next_u64() >> 32) % bound
}

// CEP:WHAT: Generates a full random formula.
// CEP:WHY: Shared generator for both the solver and the oracle.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_formula(rng: &mut DeterministicRng) -> Vec<Vec<SatLiteral>> {
    let mut formula: Vec<Vec<SatLiteral>> = Vec::new();
    for _ in 0..kOracleClauses {
        formula.push(random_clause(rng));
    }
    formula
}

// CEP:WHAT: Brute-force satisfiability oracle.
// CEP:WHY: The independent reference: enumerate all 2^n assignments.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: variables densely below kOracleVariables.
// CEP:COST: 2^n x clauses.
// CEP:EVIDENCE: used by solve_agrees_with_brute_force.
// CEP:SECURITY: none.
fn brute_force_satisfiable(formula: &[Vec<SatLiteral>]) -> bool {
    for model in 0..(1u64 << kOracleVariables) {
        let mut satisfied = true;
        for clause in formula.iter() {
            let mut clause_satisfied = false;
            for literal in clause.iter() {
                let bit = (model >> literal.variable().0) & 1 == 1;
                if bit == literal.is_positive() {
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

// CEP:WHAT: Checks an assignment satisfies a clause set under a value reader.
// CEP:WHY: Shared model verification.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the reader answers for every clause variable.
// CEP:COST: linear in the formula.
// CEP:EVIDENCE: used by models_satisfy_formulas.
// CEP:SECURITY: none.
fn formula_satisfied(formula: &[Vec<SatLiteral>], value_of: impl Fn(u32) -> Option<bool>) -> bool {
    for clause in formula.iter() {
        let mut clause_satisfied = false;
        for literal in clause.iter() {
            if value_of(literal.variable().0) == Some(literal.is_positive()) {
                clause_satisfied = true;
                break;
            }
        }
        if !clause_satisfied {
            return false;
        }
    }
    true
}

// CEP:WHAT: Property: the solver agrees with the brute-force oracle on every random formula.
// CEP:WHY: Spec 06 section 8: Satisfiable iff a model exists; the oracle enumerates all models.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: random formulas.
// CEP:COST: 2^n per formula for the oracle.
// CEP:EVIDENCE: cited by hot/sat/solver.rs solve.
// CEP:SECURITY: none.
#[test]
fn solve_agrees_with_brute_force() {
    let mut rng = DeterministicRng::new(0xC0FFEE01);
    let mut sat_count = 0;
    let mut unsat_count = 0;
    for index in 0..kOracleFormulas {
        let formula = if index % 2 == 0 {
            random_formula(&mut rng)
        } else {
            // Double density near and above the phase transition to produce UNSAT halves.
            let mut dense = random_formula(&mut rng);
            dense.extend(random_formula(&mut rng));
            dense
        };
        let expected = brute_force_satisfiable(&formula);
        let arena = make_arena(kSolverArenaBytes);
        let solver =
            CdclSolver::new(arena, kOracleVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            solver.add_clause(clause).expect("add clause");
        }
        let outcome = solver.solve();
        match outcome {
            SolveResult::Satisfiable => {
                assert!(expected, "solver claimed SAT on an UNSAT formula");
                sat_count += 1;
            }
            SolveResult::Unsatisfiable => {
                assert!(!expected, "solver claimed UNSAT on a SAT formula");
                unsat_count += 1;
            }
            SolveResult::Indeterminate(error) => {
                panic!(
                    "solver returned Indeterminate on a small formula: {:?}",
                    error
                )
            }
        }
    }
    assert!(
        sat_count > 0 && unsat_count > 0,
        "the generator must produce both outcomes"
    );
}

// CEP:WHAT: Property: every satisfying model actually satisfies every clause.
// CEP:WHY: Spec 06 section 8: Satisfiable certifies a model; the model must check out.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any unsatisfied clause.
// CEP:ASSUMES: random formulas.
// CEP:COST: linear per formula.
// CEP:EVIDENCE: cited by hot/sat/solver.rs model_value.
// CEP:SECURITY: none.
#[test]
fn models_satisfy_formulas() {
    let mut rng = DeterministicRng::new(0xC0FFEE02);
    for _ in 0..kOracleFormulas {
        let formula = random_formula(&mut rng);
        let arena = make_arena(kSolverArenaBytes);
        let solver =
            CdclSolver::new(arena, kOracleVariables, RestartPolicy::Luby, false).expect("solver");
        for clause in formula.iter() {
            solver.add_clause(clause).expect("add clause");
        }
        if solver.solve() == SolveResult::Satisfiable {
            assert!(
                formula_satisfied(&formula, |variable| solver.model_value(variable)),
                "the reported model must satisfy the formula"
            );
        }
    }
}

// CEP:WHAT: Property: every learnt clause is false under the assignment it was analyzed at and entailed by the original formula.
// CEP:WHY: Spec 06 sections 5-6: the learnt clause is a resolvent of the formula's clauses (entailment) and is falsified by the current assignment (that is why the analysis happened); the manual loop drives core, VSIDS, and analyzer exactly like the solver but pauses at each conflict for the checks.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any non-false or non-entailed learnt clause.
// CEP:ASSUMES: small formulas so the oracle can enumerate the formula's models.
// CEP:COST: 2^n per learnt clause for the entailment oracle.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: none.
#[test]
fn learnt_clauses_are_entailed() {
    let mut rng = DeterministicRng::new(0xC0FFEE03);
    let mut checked_learnts = 0;
    for _ in 0..kOracleFormulas / 2 {
        let formula = random_formula(&mut rng);
        let arena = make_arena(kSolverArenaBytes);
        let core = SatCore::new(arena, kOracleVariables).expect("core");
        let analyzer = ConflictAnalyzer::new(arena, kOracleVariables).expect("analyzer");
        let vsids = VsidsHeap::new(arena, kOracleVariables).expect("vsids");
        for clause in formula.iter() {
            core.add_clause(clause).expect("add clause");
        }
        // Manual CDCL loop with per-conflict checks.
        let mut conflicts_seen = 0;
        let conflict_budget = 2_000u64;
        loop {
            match core.propagate().expect("propagate") {
                PropagationOutcome::Conflict(conflict) => {
                    if core.trail().level() == 0 {
                        break;
                    }
                    conflicts_seen += 1;
                    if conflicts_seen as u64 > conflict_budget {
                        break;
                    }
                    vsids.decay();
                    let mut buffer = [SatLiteral::new(SatVar(0), true).expect("literal"); 512];
                    let outcome = analyzer
                        .analyze(&core, &vsids, conflict, &mut buffer)
                        .expect("analyze");
                    // Check 1: every learnt literal is false under the current assignment.
                    for literal in buffer.iter().take(outcome.literal_count as usize) {
                        assert_eq!(
                            core.value_of_literal(*literal),
                            mapt::hot::sat::assignment::SatValue::False,
                            "every learnt literal must be false at analysis time"
                        );
                    }
                    // Check 2: the learnt clause is entailed: every model of the formula
                    // satisfies it.
                    let learnt: Vec<SatLiteral> = buffer[..outcome.literal_count as usize].to_vec();
                    for model in 0..(1u64 << kOracleVariables) {
                        let satisfies_formula = formula.iter().all(|clause| {
                            clause.iter().any(|literal| {
                                ((model >> literal.variable().0) & 1 == 1) == literal.is_positive()
                            })
                        });
                        if !satisfies_formula {
                            continue;
                        }
                        let learnt_satisfied = learnt.iter().any(|literal| {
                            ((model >> literal.variable().0) & 1 == 1) == literal.is_positive()
                        });
                        assert!(
                            learnt_satisfied,
                            "the learnt clause must be entailed by the formula"
                        );
                    }
                    checked_learnts += 1;
                    // Learn, backjump, assert (mirroring the solver).
                    let literals: Vec<SatLiteral> =
                        buffer[..outcome.literal_count as usize].to_vec();
                    let attached = core
                        .add_learnt_clause(&literals, outcome.lbd as u8)
                        .expect("learn");
                    let offset = match attached {
                        mapt::hot::sat::database::AttachOutcome::Attached(offset) => offset,
                        mapt::hot::sat::database::AttachOutcome::UnitEnqueued(offset) => offset,
                        _ => 0,
                    };
                    // Backjump with phase saving and heap reinsertion.
                    let keep = core.trail().cancel_keep_index(outcome.backjump_level);
                    let mut index = core.trail().len();
                    while index > keep {
                        index -= 1;
                        if let Some(literal) = core.trail().literal_at(index) {
                            vsids.insert(literal.variable().0);
                        }
                    }
                    core.cancel_until(outcome.backjump_level);
                    if outcome.literal_count > 1 {
                        core.assign_with_reason(literals[0], offset)
                            .expect("assert");
                    }
                }
                PropagationOutcome::NoConflict => {
                    let decision = vsids.pick_unassigned(|variable| {
                        match SatLiteral::new(SatVar(variable), true) {
                            Ok(literal) => {
                                core.value_of_literal(literal)
                                    != mapt::hot::sat::assignment::SatValue::Unassigned
                            }
                            Err(_) => true,
                        }
                    });
                    match decision {
                        None => break,
                        Some(variable) => {
                            let literal =
                                SatLiteral::new(SatVar(variable), false).expect("literal");
                            core.decide(literal).expect("decide");
                        }
                    }
                }
            }
        }
        let _ = CdclError::LevelZeroConflict; // vocabulary reference for the loop above
    }
    assert!(
        checked_learnts > 0,
        "the generator must produce conflicts worth checking"
    );
}
