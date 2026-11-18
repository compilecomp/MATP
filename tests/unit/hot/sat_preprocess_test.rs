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
use mapt::hot::sat::assignment::SatValue;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::preprocess::{simplify, SimplifyOptions, SimplifyStatus};
use mapt::hot::sat::proof::ProofStepKind;
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolveResult, SolverOptions};
use mapt_config::limits::kSatBceStackDepth;

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
// CEP:ASSUMES: one tautology plus one normal clause; the surviving clause (2 or 3) is not blocked: every blocking candidate's negation occurrence set is empty (vacuous blockedness is skipped, Spec 09 section 11), so the clause survives the full pass.
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
    // (Its blocking candidates all have empty negation-occurrence sets, so the
    // blocked-clause elimination skips it - Spec 09 section 11.)
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
// CEP:ASSUMES: a clause whose every prefix negation is satisfiable; every blocking candidate of the single clause has an empty negation-occurrence set, so the blocked-clause elimination skips it and the clause stays live and unmarked.
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

// CEP:WHAT: Verifies failed-literal probing derives the negated literal as a unit.
// CEP:WHY: S35: the failed literal 9 (its negation occurs through the chain (not 9 or 6), (not 9 or 7), (not 6 or not 7)) conflicts when decided, so the database entails not-9 and the unit is added; vivification cannot derive it (the conflict fires at the last prefix position of every clause containing 9, which leaves each clause unchanged), so the unit is probing's alone.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no unit is derived or the trail lacks it.
// CEP:ASSUMES: the fixture above; the trail keeps the derived unit at level 0.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::probe_literal.
// CEP:SECURITY: none.
#[test]
fn probe_derives_unit() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(3, true), lit(9, false)])
        .expect("a");
    solver.add_clause(&[lit(5, true), lit(9, true)]).expect("b");
    solver
        .add_clause(&[lit(6, true), lit(9, false)])
        .expect("c");
    solver
        .add_clause(&[lit(7, true), lit(9, false)])
        .expect("d");
    solver
        .add_clause(&[lit(6, false), lit(7, false)])
        .expect("e");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.probe_units >= 1, "stats: {:?}", outcome.stats);
    assert_eq!(
        solver.core().value_of_literal(lit(9, false)),
        SatValue::True,
        "the derived unit must sit on the trail"
    );
}

// CEP:WHAT: Verifies the probe budget stops the pass honestly.
// CEP:WHY: S35 budget discipline (Law 4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status.
// CEP:ASSUMES: one probe excursion per budget unit; injected budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::probe_literal and config/limits.rs kSatProbeBudget.
// CEP:SECURITY: denial-of-service bound exercised.
#[test]
fn probe_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver.add_clause(&[lit(0, true), lit(2, true)]).expect("b");
    solver
        .add_clause(&[lit(1, false), lit(2, false)])
        .expect("c");
    let mut options = SimplifyOptions::new();
    options.probe_budget = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::ProbeBudgetExhausted);
}

// CEP:WHAT: Verifies hyper-binary resolution derives the resolvent of a complementary binary pair and the fixpoint turns it into the classic unit.
// CEP:WHY: S37: (0 or 1) and (not 0 or 2) resolve to (1 or 2), whose self-subsumption with (not 1 or 2) yields the unit 2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no resolvent is added or the unit is missing.
// CEP:ASSUMES: the fixture above; the strengthening pair survives BCE because every candidate's negation occurs (non-vacuous).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::hyper_binary_pair.
// CEP:SECURITY: none.
#[test]
fn hyper_binary_derives_unit() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("b");
    solver
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("c");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(
        outcome.stats.hyper_binaries >= 1,
        "stats: {:?}",
        outcome.stats
    );
    assert_eq!(
        solver.core().value_of_literal(lit(2, true)),
        SatValue::True,
        "the hyper-binary chain must derive the unit"
    );
}

// CEP:WHAT: Verifies the hyper-binary pair budget stops the pass honestly.
// CEP:WHY: S37 budget discipline (Law 4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status.
// CEP:ASSUMES: three binaries make three pairs; injected budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::hyper_binary_pair and config/limits.rs kSatHyperBinaryPairBudget.
// CEP:SECURITY: denial-of-service bound exercised.
#[test]
fn hyper_binary_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver.add_clause(&[lit(0, true), lit(2, true)]).expect("b");
    solver.add_clause(&[lit(3, true), lit(4, true)]).expect("c");
    let mut options = SimplifyOptions::new();
    options.hyper_binary_budget = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::HyperBinaryBudgetExhausted);
}

// CEP:WHAT: Verifies bounded variable elimination replaces a variable's clauses by its resolvent.
// CEP:WHY: S32: the resolvent of (0 or 1) and (not 0 or 2) is (1 or 2); the parents are deleted and the reconstruction record is appended.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the variable's clauses survive or no resolvent is added.
// CEP:ASSUMES: the fixture above; the fixpoint dedups the doubled resolvent (hyper-binary derives it too).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bve_eliminate.
// CEP:SECURITY: none.
#[test]
fn bve_eliminates_variable() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("b");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(
        outcome.stats.bve_resolvents >= 1,
        "stats: {:?}",
        outcome.stats
    );
    assert_eq!(solver.ext_entry_count(), 1);
    // The fixpoint dedups the doubled resolvent down to one live clause.
    assert_eq!(live_count(&solver), 1);
}

// CEP:WHAT: Verifies the BVE model reconstruction: the solved model satisfies the original formula.
// CEP:WHY: Spec 09 section 12: BVE deletion is equisatisfiable only; model_value flips the eliminated variable to the side its deleted clauses demand, and the extended model must satisfy every original clause.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the extended model falsifies an original clause.
// CEP:ASSUMES: the fixture above; solve assigns every variable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::model_value (ext_eliminated_variable_flip).
// CEP:SECURITY: none.
#[test]
fn bve_model_extension_satisfies_original() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("b");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert_eq!(solver.solve(), SolveResult::Satisfiable);
    let model = |variable: u32| solver.model_value(variable).expect("model");
    let (m0, m1, m2) = (model(0), model(1), model(2));
    assert!(
        (m0 || m1) && (!m0 || m2),
        "the extended model must satisfy the original formula"
    );
}

// CEP:WHAT: Verifies BVE skips a candidate whose positive occurrences exceed the fixed buffer.
// CEP:WHY: S32 honesty: occurrence-bound skips are sound (no mutation) and must be visible.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the clauses are mutated or the skip is unreported.
// CEP:ASSUMES: 65 clauses contain variable 0 positively (kSatBveOccurrenceLimit + 1).
// CEP:COST: linear in the fixture.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bve_eliminate and config/limits.rs kSatBveOccurrenceLimit.
// CEP:SECURITY: buffer bound exercised.
#[test]
fn bve_occurrence_bound_skips() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, 66, RestartPolicy::Luby, false).expect("solver");
    for variable in 1..=65u32 {
        solver
            .add_clause(&[lit(0, true), lit(variable, true)])
            .expect("c");
    }
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert!(outcome.stats.bve_skipped >= 1, "stats: {:?}", outcome.stats);
    assert_eq!(live_count(&solver), 65);
}

// CEP:WHAT: Verifies BVE skips a candidate whose resolvent count exceeds the budget.
// CEP:WHY: S32 honesty: the resolvent bound keeps elimination from growing the database; skips are sound and visible.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the clauses are mutated or the skip is unreported.
// CEP:ASSUMES: variable 0 has a 2x2 occurrence structure (four resolvents); injected budget 1. Hyper-binary first derives the four cross-resolvents, all counted.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bve_eliminate and config/limits.rs kSatBveResolventBudget.
// CEP:SECURITY: budget bound exercised.
#[test]
fn bve_resolvent_bound_skips() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver.add_clause(&[lit(0, true), lit(2, true)]).expect("b");
    solver
        .add_clause(&[lit(0, false), lit(3, true)])
        .expect("c");
    solver
        .add_clause(&[lit(0, false), lit(4, true)])
        .expect("d");
    let mut options = SimplifyOptions::new();
    options.bve_resolvents = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert_eq!(outcome.stats.bve_resolvents, 0);
    assert!(outcome.stats.bve_skipped >= 1, "stats: {:?}", outcome.stats);
}

// CEP:WHAT: Verifies the BVE variable budget stops the pass honestly.
// CEP:WHY: S32 budget discipline (Law 4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status.
// CEP:ASSUMES: at least one eliminable variable plus further unassigned variables; injected budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bve_eliminate and config/limits.rs kSatBveVariableLimit.
// CEP:SECURITY: denial-of-service bound exercised.
#[test]
fn bve_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver.add_clause(&[lit(0, true), lit(1, true)]).expect("a");
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("b");
    solver.add_clause(&[lit(3, true), lit(4, true)]).expect("c");
    solver
        .add_clause(&[lit(3, false), lit(5, true)])
        .expect("d");
    let mut options = SimplifyOptions::new();
    options.bve_variables = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::BveBudgetExhausted);
}

// CEP:WHAT: Verifies blocked-clause elimination deletes a clause that resolves tautologically against every clause containing the blocking literal's negation, and records it for the model reconstruction.
// CEP:WHY: S31: (u or w or c...) against (not u or not w or d...) resolves to a tautology on u, so the clause is blocked and deleted; the reconstruction record feeds model_value.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the clause survives or no record is appended.
// CEP:ASSUMES: the long-clause fixture also defeats BVE (its reconstruction payload exceeds the stack stride), so the elimination is BCE's alone.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bce_eliminate.
// CEP:SECURITY: none.
#[test]
fn bce_eliminates_blocked_clause() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, 30, RestartPolicy::Luby, false).expect("solver");
    let mut positive = Vec::new();
    positive.push(lit(0, true));
    positive.push(lit(1, true));
    for variable in 2..16u32 {
        positive.push(lit(variable, true));
    }
    let mut negative = Vec::new();
    negative.push(lit(0, false));
    negative.push(lit(1, false));
    for variable in 16..30u32 {
        negative.push(lit(variable, true));
    }
    solver.add_clause(&positive).expect("blocked");
    solver.add_clause(&negative).expect("partner");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert_eq!(outcome.stats.bce_clauses, 1, "stats: {:?}", outcome.stats);
    assert_eq!(solver.ext_entry_count(), 1);
    assert_eq!(live_count(&solver), 1);
}

// CEP:WHAT: Verifies the BCE model reconstruction: the solved model satisfies the original formula.
// CEP:WHY: Spec 09 section 11: BCE deletion is equisatisfiable only; model_value overrides the blocking literal when the blocked clause is unsatisfied, and the extended model must satisfy every original clause.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the extended model falsifies an original clause.
// CEP:ASSUMES: the fixture above; solve assigns every variable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/solver.rs::model_value (ext_blocked_clause_satisfied).
// CEP:SECURITY: none.
#[test]
fn bce_model_extension_satisfies_original() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, 30, RestartPolicy::Luby, false).expect("solver");
    let mut positive = Vec::new();
    positive.push(lit(0, true));
    positive.push(lit(1, true));
    for variable in 2..16u32 {
        positive.push(lit(variable, true));
    }
    let mut negative = Vec::new();
    negative.push(lit(0, false));
    negative.push(lit(1, false));
    for variable in 16..30u32 {
        negative.push(lit(variable, true));
    }
    solver.add_clause(&positive).expect("blocked");
    solver.add_clause(&negative).expect("partner");
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::Complete);
    assert_eq!(solver.solve(), SolveResult::Satisfiable);
    let model = |variable: u32| solver.model_value(variable).expect("model");
    let mut blocked_satisfied = false;
    for variable in 0..16u32 {
        if model(variable) {
            blocked_satisfied = true;
        }
    }
    let mut partner_satisfied = false;
    for slot in 0..2u32 {
        if !model(slot) {
            partner_satisfied = true;
        }
    }
    for variable in 16..30u32 {
        if model(variable) {
            partner_satisfied = true;
        }
    }
    assert!(
        blocked_satisfied && partner_satisfied,
        "the extended model must satisfy the original formula"
    );
}

// CEP:WHAT: Verifies the BCE check budget stops the pass honestly.
// CEP:WHY: S31 budget discipline (Law 4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any other status.
// CEP:ASSUMES: the candidate's negation occurs in ten clauses (defeating BVE through the payload bound); injected check budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bce_eliminate and config/limits.rs kSatBceCheckBudget.
// CEP:SECURITY: denial-of-service bound exercised.
#[test]
fn bce_budget_stops_early() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, 13, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true)])
        .expect("candidate");
    for variable in 3..13u32 {
        solver
            .add_clause(&[lit(0, false), lit(variable, true)])
            .expect("neg");
    }
    let mut options = SimplifyOptions::new();
    options.bce_checks = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(outcome.status, SimplifyStatus::BceBudgetExhausted);
}

// CEP:WHAT: Verifies the model-extension stack bound skips BVE candidates honestly instead of overflowing.
// CEP:WHY: S31/S32 honesty: the stack is bounded; candidates beyond the depth are skipped (sound, no mutation) and visible in the stats.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the stack overflows its bound or the skip is unreported.
// CEP:ASSUMES: 65 eliminable variable pairs (kSatBceStackDepth + 1 eliminations attempted); the last candidate is skipped at the pre-check.
// CEP:COST: linear in the fixture.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs::bve_eliminate and config/limits.rs kSatBceStackDepth.
// CEP:SECURITY: memory bound exercised.
#[test]
fn bve_stack_overflow_skips() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, 130, RestartPolicy::Luby, false).expect("solver");
    for pair in 0..65u32 {
        let positive = pair * 2;
        let negative = pair * 2 + 1;
        solver
            .add_clause(&[lit(positive, true), lit(negative, true)])
            .expect("a");
        solver
            .add_clause(&[lit(positive, false), lit(negative, false)])
            .expect("b");
    }
    let outcome = simplify(&solver, &SimplifyOptions::new()).expect("simplify");
    assert!(outcome.stats.bve_skipped >= 1, "stats: {:?}", outcome.stats);
    assert_eq!(
        solver.ext_entry_count() as usize,
        kSatBceStackDepth as usize
    );
}
