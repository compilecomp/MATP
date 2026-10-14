// CEP:FILE: tests/unit/hot/sat_preprocess_test.rs
// CEP:WHAT: Unit tests for SAT preprocessing: tautology deletion, duplicate-literal removal, subsumption deletion, self-subsuming strengthening, vivification (shortening, restoration, budget stops, vivify-refuted formulas with the empty-clause proof step), contradictory-unit refutation, and the round bound.
// CEP:WHY: Design 11.1 S30/S33/S34/S36 and Spec 09: preprocessing rewrites must preserve satisfiability with exact proof-trace ordering; the four rewrite kinds and their budget stops are pinned here before the property test verifies satisfiability preservation against brute force.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; injected budgets for the stop tests.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/preprocess.rs.
// CEP:SECURITY: the pair and vivification budgets are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::preprocess::{simplify, SimplifyOptions, SimplifyStatus};
use mapt::hot::sat::proof::ProofStepKind;
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};

// CEP:WHAT: Test variable count.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 10;

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

// CEP:WHAT: Counts live registry entries.
// CEP:WHY: Several tests assert on the shrunken database size.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(entries).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn live_count(solver: &CdclSolver<'_>) -> usize {
    (0..solver.registry().entry_count())
        .filter(|index| {
            !solver
                .registry()
                .entry(*index)
                .expect("entry")
                .tombstone
                .get()
        })
        .count()
}

// CEP:WHAT: Verifies tautological clauses are deleted.
// CEP:WHY: S33.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the tautology survives.
// CEP:ASSUMES: one tautology plus one normal clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, read_clause}.
// CEP:SECURITY: none.
#[test]
fn tautologies_removed() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(0, false), lit(1, true)])
        .expect("t");
    solver.add_clause(&[lit(2, true), lit(3, true)]).expect("n");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.tautologies >= 1);
    assert_eq!(live_count(&solver), 1);
}

// CEP:WHAT: Verifies duplicate literals are removed by replacement clauses.
// CEP:WHY: S34.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no rewrite happens.
// CEP:ASSUMES: a clause with a duplicated literal.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, dedupe}.
// CEP:SECURITY: none.
#[test]
fn duplicates_removed() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, false), lit(0, true), lit(1, false)])
        .expect("dup");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.duplicates >= 1);
    // The replacement (0 or not 1) is live; the original is tombstoned: net size 1.
    assert_eq!(live_count(&solver), 1);
}

// CEP:WHAT: Verifies subsumed clauses are deleted.
// CEP:WHY: S30.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the subsumed clause survives.
// CEP:ASSUMES: a unit subsuming a longer clause.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, subset_of}.
// CEP:SECURITY: none.
#[test]
fn subsumption_deletes() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true)]).expect("unit");
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("subsumed");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.subsumed >= 1);
    assert_eq!(live_count(&solver), 1);
}

// CEP:WHAT: Verifies self-subsuming resolution strengthens clauses.
// CEP:WHY: S30's strengthening half.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no rewrite happens.
// CEP:ASSUMES: (A or x) and (B or not x) with A a subset of B.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, self_subsumption_pivot}.
// CEP:SECURITY: none.
#[test]
fn strengthening_rewrites() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    // (1 or 0) and (2 or 1 or not 0): the second strengthens to (2 or 1).
    solver
        .add_clause(&[lit(1, true), lit(0, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(2, true), lit(1, true), lit(0, false)])
        .expect("c2");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.strengthened >= 1);
}

// CEP:WHAT: Verifies vivification shortens a clause that the database refutes a prefix of.
// CEP:WHY: S36.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no shortening happens.
// CEP:ASSUMES: target (0 or 1 or 2) with database {Q = (0 or 1 or 3), R = (not 3 or 1)}:
// assuming not-0 leaves Q non-unit, and then assuming not-1 makes R propagate not-3,
// which falsifies Q - a two-step propagation conflict on a strict prefix, so the
// target shortens to (0 or 1); no subsumption or self-subsumption pair exists among
// the three clauses (checked by hand), so the shortening is vivification's alone.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, vivify}.
// CEP:SECURITY: none.
#[test]
fn vivification_shortens_clause() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(3, true)])
        .expect("Q");
    solver
        .add_clause(&[lit(3, false), lit(1, true)])
        .expect("R");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true)])
        .expect("target");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(
        outcome.stats.vivified >= 1,
        "expected at least one vivification, stats: {:?}",
        outcome.stats
    );
}

// CEP:WHAT: Verifies clauses that cannot be shortened are restored (no raw mark leaks).
// CEP:WHY: The isolation discipline: every raw mark resolves.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the clause stays marked deleted.
// CEP:ASSUMES: a clause whose every prefix negation is satisfiable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{vivify, unmark_deleted}.
// CEP:SECURITY: none.
#[test]
fn vivification_restores_unchanged_clause() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true)])
        .expect("target");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert_eq!(outcome.stats.vivified, 0);
    // The clause is live and unmarked.
    assert_eq!(live_count(&solver), 1);
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    assert!(!solver.core().clauses().is_deleted(offset).expect("flag"));
}

// CEP:WHAT: Verifies contradictory units refute during preprocessing.
// CEP:WHY: Spec 09 section 6.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status.
// CEP:ASSUMES: units x and not x.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, refuted}.
// CEP:SECURITY: none.
#[test]
fn contradictory_units_refute() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true)]).expect("u1");
    solver.add_clause(&[lit(0, false)]).expect("u2");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Unsatisfiable);
}

// CEP:WHAT: Verifies a vivification-produced clause that refutes the formula ends the round
// as Unsatisfiable and emits the empty-clause proof step (the level-0 propagation-conflict
// sub-case of add_clause_checked).
// CEP:WHY: Spec 09 section 6 and Spec 11 section 4: every refutation trace must end with the
// empty clause regardless of which scan triggered it; the vivify None arm previously reported
// Complete and the propagation-conflict sub-case emitted no refutation step at all.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status or a non-empty last step.
// CEP:ASSUMES: fixture with database (0 or 1), (not 1), (not 0 or 2), (not 2), candidate
// (0 or 3): vivifying the candidate negates 0, which makes (0 or 1) unit on 0 (1 is false at
// level 0) and conflicts immediately, shortening the candidate to the unit (0); adding (0)
// enqueues 0=true, and (not 0 or 2) is unit on not-0 (2 is false at level 0), so propagation
// conflicts at level 0 - the added unit was NOT falsified at attach, so this is exactly the
// propagation-conflict sub-case; the earlier two candidates cannot shorten (checked by hand:
// negating their first literals satisfies every other clause).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{add_clause_checked, vivify}.
// CEP:SECURITY: none.
#[test]
fn vivified_clause_refutes_formula() {
    let arena = make_arena(12_582_912);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.record_proof = true;
    // Injected small proof capacities: the default buffers (1M steps) are sized
    // for production arenas, not this 12 MiB fixture arena.
    options.proof_step_capacity = 64;
    options.proof_map_capacity = 64;
    options.proof_literal_capacity = 256;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver.add_clause(&[lit(1, false)]).expect("u1");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c2");
    solver.add_clause(&[lit(2, false)]).expect("u2");
    solver
        .add_clause(&[lit(0, true), lit(3, true)])
        .expect("candidate");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Unsatisfiable);
    // The refutation step is the last recorded proof step: an Add with zero
    // literals (the empty clause), emitted by the propagation-conflict arm.
    let recorder = solver.proof().expect("recorder");
    let last = recorder.step(recorder.step_count() - 1).expect("last step");
    assert_eq!(last.kind, ProofStepKind::Add);
    assert_eq!(last.literal_count, 0, "last step must be the empty clause");
}

// CEP:WHAT: Verifies the pair budget stops the pass honestly.
// CEP:WHY: Law 6: partial work is reported.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pass claims completion.
// CEP:ASSUMES: pair budget 1 with two pairs to examine.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify_round, kSatSubsumptionPairBudget} and config/limits.rs.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn pair_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    for variable in 0..4u32 {
        solver
            .add_clause(&[lit(variable, true), lit(variable + 4, true)])
            .expect("c");
    }
    let mut options = SimplifyOptions::new();
    options.pair_budget = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::PairBudgetExhausted);
    assert_eq!(outcome.stats.pairs_examined, 1);
}

// CEP:WHAT: Verifies the vivification candidate budget stops the pass honestly.
// CEP:WHY: Law 6.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pass claims completion.
// CEP:ASSUMES: candidate budget 1 with two candidates.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify_round, kSatVivifyCandidateLimit}.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn candidate_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(2, true), lit(3, true)])
        .expect("c2");
    let mut options = SimplifyOptions::new();
    options.vivify_candidates = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::VivifyBudgetExhausted);
    assert_eq!(outcome.stats.vivify_attempts, 1);
}

// CEP:WHAT: Verifies the vivification propagation budget stops mid-candidate without corrupting state.
// CEP:WHY: Law 6 and the conservative mid-candidate abort.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pass claims completion or leaves marks.
// CEP:ASSUMES: propagation budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{vivify, kSatVivifyPropagationBudget}.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn vivification_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true)])
        .expect("c");
    let mut options = SimplifyOptions::new();
    options.vivify_budget = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::VivifyBudgetExhausted);
    // The candidate is restored (no mark leak) despite the abort.
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    assert!(!solver.core().clauses().is_deleted(offset).expect("flag"));
}

// CEP:WHAT: Verifies the propagation budget alias cited by the propagation-budget-stops evidence.
// CEP:WHY: The propagation budget stop shares the candidate-budget test shape; this alias keeps the cited name live.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the budget is not respected.
// CEP:ASSUMES: propagation budget 2 with a three-literal candidate.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::vivify and config/limits.rs kSatVivifyPropagationBudget.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn propagation_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true), lit(3, true)])
        .expect("c");
    let mut options = SimplifyOptions::new();
    options.vivify_budget = 2;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::VivifyBudgetExhausted);
}

// CEP:WHAT: Verifies the round bound is respected.
// CEP:WHY: kMaxSimplifyRounds bounds the pass.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when more rounds run.
// CEP:ASSUMES: rounds 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::{simplify, SimplifyOptions} and config/limits.rs kMaxSimplifyRounds.
// CEP:SECURITY: none.
#[test]
fn rounds_bounded() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    solver
        .add_clause(&[lit(2, true), lit(3, true)])
        .expect("c2");
    let mut options = SimplifyOptions::new();
    options.rounds = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert!(outcome.stats.rounds_done <= 1);
}
