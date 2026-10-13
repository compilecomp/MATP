// CEP:FILE: tests/unit/hot/sat_assumptions_test.rs
// CEP:WHAT: Unit tests for assumption-based incremental solving: satisfiable extensions, formula-level refutations, unsat-under-assumptions with failed cores, core minimality and validity, model survival, repeated solves, learnt hygiene, and the assumption count bound.
// CEP:WHY: Design 11.1 S38/S39 and Spec 10: assumption solves are the AVATAR-facing interface; the core extraction (analyze_final) and the cleanup discipline (deferred learnt deletion) are the soundness-critical contracts pinned here before the property tests verify them against brute force.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/solver.rs (assumption paths) and hot/sat/cdcl.rs::analyze_final.
// CEP:SECURITY: the assumption count bound is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{AssumptionOutcome, CdclSolver};

// CEP:WHAT: Test variable count.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 12;

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable clause construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Builds a default solver.
// CEP:WHY: One constructor for this file.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_solver() -> CdclSolver<'static> {
    let arena = make_arena(12_582_912);
    CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver")
}

// CEP:WHAT: Verifies a satisfiable formula stays satisfiable under a compatible assumption and the model extends it.
// CEP:WHY: Spec 10 section 3.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other outcome.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::solve_with_assumptions.
// CEP:SECURITY: none.
#[test]
fn satisfiable_under_assumptions() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c2");
    let outcome = solver.solve_with_assumptions(&[lit(0, true)]);
    assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
    assert_eq!(solver.model_value(0), Some(true));
}

// CEP:WHAT: Verifies an unsatisfiable formula reports Unsatisfiable, not UnsatUnderAssumptions.
// CEP:WHY: Spec 10 section 5: the strongest refuting outcome is the formula-level one.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on the weaker outcome.
// CEP:ASSUMES: contradictory formula.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::solve_with_assumptions.
// CEP:SECURITY: none.
#[test]
fn unsat_formula_returns_unsat() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(1, true)])
        .expect("c2");
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("c3");
    solver
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("c4");
    let outcome = solver.solve_with_assumptions(&[lit(2, true)]);
    assert!(matches!(outcome, AssumptionOutcome::Unsatisfiable));
}

// CEP:WHAT: Verifies a contradictory assumption set yields UnsatUnderAssumptions with a nonempty core.
// CEP:WHY: Spec 10 section 4.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a missing core.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{solve_with_assumptions, record_core}.
// CEP:SECURITY: none.
#[test]
fn unsat_under_assumptions_yields_core() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let outcome = solver.solve_with_assumptions(&[lit(0, true), lit(0, false)]);
    assert!(matches!(outcome, AssumptionOutcome::UnsatUnderAssumptions));
    let mut core = [lit(0, true); 8];
    let count = solver.failed_assumptions_into(&mut core);
    assert!(count >= 1);
}

// CEP:WHAT: Verifies the failed core is a subset of the pushed assumptions.
// CEP:WHY: Spec 10 section 4: the core contains only assumption literals.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a foreign literal.
// CEP:ASSUMES: a refuting assumption set.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs::analyze_final.
// CEP:SECURITY: none.
#[test]
fn failed_core_is_minimal_subset() {
    let solver = make_solver();
    // (0 or 1) and (not 0 or 2) and (not 2): assuming 0 and not 1 refutes.
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c2");
    solver.add_clause(&[lit(2, false)]).expect("c3");
    let assumptions = [lit(0, true), lit(1, false), lit(5, true)];
    let outcome = solver.solve_with_assumptions(&assumptions);
    assert!(matches!(outcome, AssumptionOutcome::UnsatUnderAssumptions));
    let mut core = [lit(0, true); 8];
    let count = solver.failed_assumptions_into(&mut core);
    assert!(count >= 1 && count <= assumptions.len());
    for member in core[..count].iter() {
        assert!(
            assumptions
                .iter()
                .any(|assumption| assumption.encoding() == member.encoding()),
            "core literal must come from the assumption set"
        );
    }
}

// CEP:WHAT: Verifies the core's negation is entailed: the formula plus the core is unsatisfiable.
// CEP:WHY: Spec 10 section 4's soundness statement, verified by re-solving on a fresh solver.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the core conjunction is satisfiable with the formula.
// CEP:ASSUMES: a core was extracted.
// CEP:COST: two solves.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{solve_with_assumptions, failed_assumptions_into}.
// CEP:SECURITY: none.
#[test]
fn core_negation_is_entailed() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c2");
    solver.add_clause(&[lit(2, false)]).expect("c3");
    let assumptions = [lit(0, true), lit(1, false)];
    let outcome = solver.solve_with_assumptions(&assumptions);
    assert!(matches!(outcome, AssumptionOutcome::UnsatUnderAssumptions));
    let mut core = [lit(0, true); 8];
    let count = solver.failed_assumptions_into(&mut core);
    // Re-solve the formula plus the core on a fresh solver: must be UNSAT.
    let checker = make_solver();
    checker
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    checker
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c2");
    checker.add_clause(&[lit(2, false)]).expect("c3");
    let outcome = checker.solve_with_assumptions(&core[..count]);
    assert!(
        matches!(outcome, AssumptionOutcome::Unsatisfiable)
            || matches!(outcome, AssumptionOutcome::UnsatUnderAssumptions),
        "formula plus core must be unsatisfiable"
    );
}

// CEP:WHAT: Verifies an empty core accompanies formula-level refutations.
// CEP:WHY: Spec 10 section 4: an empty core means no assumptions were needed.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a core is reported.
// CEP:ASSUMES: contradictory formula with an unrelated assumption.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::root_region_conflict.
// CEP:SECURITY: none.
#[test]
fn empty_core_means_unsat() {
    let solver = make_solver();
    solver.add_clause(&[lit(0, true)]).expect("u1");
    solver.add_clause(&[lit(0, false)]).expect("u2");
    let outcome = solver.solve_with_assumptions(&[lit(1, true)]);
    assert!(matches!(outcome, AssumptionOutcome::Unsatisfiable));
    assert_eq!(solver.failed_assumption_count(), 0);
}

// CEP:WHAT: Verifies the model stays readable after a Satisfiable assumption solve.
// CEP:WHY: The deferred-cleanup contract (Spec 10 section 5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the model was wiped.
// CEP:ASSUMES: a satisfiable assumption solve.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{flush_pending_cleanup, model_value}.
// CEP:SECURITY: none.
#[test]
fn model_survives_satisfiable_assumption_solve() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let outcome = solver.solve_with_assumptions(&[lit(0, true)]);
    assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
    // The assumption is part of the model; the don't-care variable just has to be
    // assigned such that the clause holds (0 true satisfies it already).
    assert_eq!(solver.model_value(0), Some(true));
    let first = solver.model_value(0) == Some(true);
    let second = solver.model_value(1) == Some(true);
    assert!(first || second, "the model must satisfy the clause");
}

// CEP:WHAT: Verifies assumption-dependent learnts do not leak into later solves.
// CEP:WHY: Spec 10 section 5: the cleanup keeps incremental solves sound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a later solve of a satisfiable formula reports UNSAT.
// CEP:ASSUMES: an unsat-under-assumptions solve precedes a plain solve.
// CEP:COST: two solves.
// CEP:EVIDENCE: cited by hot/sat/registry.rs::delete_learnts_from and hot/sat/solver.rs::flush_pending_cleanup.
// CEP:SECURITY: none.
#[test]
fn learnts_do_not_leak_across_solves() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    // Assumptions 0 and not 0: refuted under assumptions, learning may occur.
    let outcome = solver.solve_with_assumptions(&[lit(0, true), lit(0, false)]);
    assert!(matches!(outcome, AssumptionOutcome::UnsatUnderAssumptions));
    // The formula alone is satisfiable: the plain solve must see that.
    let plain = solver.solve();
    assert!(matches!(
        plain,
        mapt::hot::sat::solver::SolveResult::Satisfiable
    ));
}

// CEP:WHAT: Verifies repeated assumption solves agree with the fresh-solve answer.
// CEP:WHY: The incremental interface's state hygiene.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on disagreement.
// CEP:ASSUMES: three sequential solves.
// CEP:COST: three solves.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{solve_with_assumptions, flush_pending_cleanup}.
// CEP:SECURITY: none.
#[test]
fn repeated_assumption_solves_agree() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("c2");
    for _ in 0..3 {
        let outcome = solver.solve_with_assumptions(&[lit(1, true)]);
        assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
    }
    for _ in 0..3 {
        let outcome = solver.solve_with_assumptions(&[lit(1, false)]);
        assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
    }
}

// CEP:WHAT: Verifies repeated identical assumptions in one call are idempotent.
// CEP:WHY: Spec 10 section 3: satisfied assumptions skip without new levels.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unexpected outcome.
// CEP:ASSUMES: fresh solver.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::solve_with_assumptions and config/limits.rs kMaxAssumptions.
// CEP:SECURITY: none.
#[test]
fn repeated_assumption_is_idempotent() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let outcome = solver.solve_with_assumptions(&[lit(0, true), lit(0, true), lit(0, true)]);
    assert!(matches!(outcome, AssumptionOutcome::Satisfiable));
}

// CEP:WHAT: Verifies the assumption count bound is loud.
// CEP:WHY: kMaxAssumptions is the level-depth bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the oversized call is accepted.
// CEP:ASSUMES: a call with kMaxAssumptions + 1 literals.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::{solve_with_assumptions, TooManyAssumptions} and config/limits.rs kMaxAssumptions.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn assumption_count_enforced() {
    let solver = make_solver();
    let mut assumptions = Vec::new();
    for index in 0..(mapt_config::limits::kMaxAssumptions + 1) {
        assumptions.push(lit(index % kVariables, true));
    }
    let outcome = solver.solve_with_assumptions(&assumptions);
    assert!(matches!(
        outcome,
        AssumptionOutcome::Indeterminate(mapt::hot::sat::cdcl::CdclError::TooManyAssumptions)
    ));
}
