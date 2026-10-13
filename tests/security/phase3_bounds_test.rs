// CEP:FILE: tests/security/phase3_bounds_test.rs
// CEP:WHAT: Security tests for the Phase 3 bounds: the registry capacity, the proof step budget, the passive and active capacities, the feature pool capacity, and the SAT preprocessing pair and vivification budgets - every bound exercised at small injected scales on the production code path.
// CEP:WHY: CEP&CC 34.3: test the mechanism, not a copy; every denial-of-service bound named in Phase 3 must demonstrably fire.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly when a bound does not fire.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; injected small bounds.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by config/limits.rs and the bounded components.
// CEP:SECURITY: this file IS the security evidence for the Phase 3 bounds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::preprocess::{simplify, SimplifyOptions};
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
const kVariables: u32 = 8;

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

// CEP:WHAT: Verifies the registry capacity bound fires.
// CEP:WHY: The memory-exhaustion boundary of the enumerable database.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when registration succeeds past the bound.
// CEP:ASSUMES: injected capacity 3.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatRegistryCapacity and hot/sat/registry.rs::{register, Full}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn registry_capacity_enforced() {
    let arena = make_arena(12_582_912);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.registry_capacity = 3;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    for variable in 0..3u32 {
        solver.add_clause(&[lit(variable, true)]).expect("add");
    }
    assert!(
        solver.add_clause(&[lit(4, true)]).is_err(),
        "the fourth registration must fail at capacity 3"
    );
}

// CEP:WHAT: Verifies the proof step budget fires loudly.
// CEP:WHY: Never a silent truncation (Law 6).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when recording succeeds past the bound.
// CEP:ASSUMES: step capacity 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatProofStepCapacity and hot/sat/proof.rs::{record_add, StepBufferFull}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn proof_step_budget_enforced() {
    let arena = make_arena(16_777_216);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.record_proof = true;
    options.proof_step_capacity = 2;
    options.proof_map_capacity = 8;
    options.proof_literal_capacity = 64;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    solver.add_clause(&[lit(0, true)]).expect("c1");
    solver.add_clause(&[lit(1, true)]).expect("c2");
    assert!(
        solver.add_clause(&[lit(2, true)]).is_err(),
        "the third axiom add must fail at step capacity 2"
    );
}

// CEP:WHAT: Verifies the passive-set capacity bound fires.
// CEP:WHY: The search-state memory boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a push past the bound succeeds.
// CEP:ASSUMES: capacity 2 via the search space constructor.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kPassiveHeapCapacity and hot/search/passive.rs::{push, PassiveError::Full}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn passive_capacity_enforced() {
    let arena = make_arena(1_048_576);
    let heap = mapt::hot::search::passive::PassiveHeap::new_with(
        arena,
        2,
        mapt::hot::search::passive::SelectionStrategy::AgeOnly,
    )
    .expect("heap");
    assert!(heap.push(1, 10, 0, 1).is_ok());
    assert!(heap.push(2, 20, 0, 1).is_ok());
    assert!(heap.push(3, 30, 0, 1).is_err());
}

// CEP:WHAT: Verifies the active-set capacity bound fires.
// CEP:WHY: The search-state memory boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an insert past the bound succeeds.
// CEP:ASSUMES: slot capacity 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kActiveSetCapacity and hot/search/active.rs::{insert, ActiveError::SlotsFull}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn active_capacity_enforced() {
    use mapt::hot::ir::literal::Literal;
    let (fixture_arena, _s, _b, terms, _p, _sub) = {
        let (arena, symbols, builder, terms, precedence, substitution) =
            common::make_inference_fixture();
        (arena, symbols, builder, terms, precedence, substitution)
    };
    let _active = mapt::hot::search::active::ActiveSet::new_with(fixture_arena, 2, 256, 256, 1024)
        .expect("active");
    let store = mapt::hot::ir::clause::ClauseStore::new(fixture_arena);
    let a = terms.intern_var(0).expect("var");
    let _ = a;
    // Three single-literal clauses over predicate atoms require symbol lookups the
    // fixture does not expose here; use variables as atoms directly through a
    // simpler route: literal count is what the bound checks, so reuse one literal.
    let literal = Literal::new(mapt::hot::ir::term::TermPtr::invalid(), true);
    let _ = store;
    let _ = literal;
    // The bound is exercised at the structural level by the search_db test with
    // readable atoms; this test pins the slot counter behavior through the same
    // constructor the search uses (the capacity check happens before any term
    // read, so the invalid filler is safe for the bound probe).
    // ... covered below with real atoms via the inference fixture.
    let (arena2, symbols2, builder2, terms2, _prec, _sub2) = common::make_inference_fixture();
    let active2 =
        mapt::hot::search::active::ActiveSet::new_with(arena2, 2, 256, 256, 1024).expect("active");
    let store2 = mapt::hot::ir::clause::ClauseStore::new(arena2);
    let x = terms2.intern_var(0).expect("x");
    let atom = terms2
        .intern_pred(&symbols2, common::symbol_id(&builder2, "p"), &[x])
        .expect("atom");
    let clause = [Literal::new(atom, true)];
    let derivation = mapt::hot::ir::clause::DerivationStep {
        rule: mapt::hot::ir::clause::InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [0; 4],
        substitution: mapt_config::limits::kInvalidSubstitutionOffset,
    };
    let ptr_a = store2
        .new_clause(&terms2, &clause, 0, derivation)
        .expect("c");
    let ptr_b = store2
        .new_clause(&terms2, &clause, 1, derivation)
        .expect("c");
    let ptr_c = store2
        .new_clause(&terms2, &clause, 2, derivation)
        .expect("c");
    assert!(active2.insert(&terms2, ptr_a.as_u32(), &clause).is_ok());
    assert!(active2.insert(&terms2, ptr_b.as_u32(), &clause).is_ok());
    assert!(
        active2.insert(&terms2, ptr_c.as_u32(), &clause).is_err(),
        "the third insertion must fail at slot capacity 2"
    );
}

// CEP:WHAT: Verifies the feature-pool capacity bound fires.
// CEP:WHY: The index memory boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a build past the bound succeeds.
// CEP:ASSUMES: pool capacity 2 words.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kFeatureVectorPoolWords and hot/index/feature_vector.rs::{new_with, build}.
// CEP:SECURITY: the memory bound under test.
#[test]
fn feature_pool_capacity_enforced() {
    let (arena, symbols, builder, terms, _prec, _sub) = common::make_inference_fixture();
    let index =
        mapt::hot::index::feature_vector::FeatureVectorIndex::new_with(arena, 2).expect("index");
    let a = terms
        .intern_fun(&symbols, common::symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, common::symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let atom = terms
        .intern_pred(&symbols, common::symbol_id(&builder, "p"), &[f_a])
        .expect("atom");
    let clause = [mapt::hot::ir::literal::Literal::new(atom, true)];
    assert!(
        index.build(&terms, &clause).is_err(),
        "a two-pair vector must fail at pool capacity 2 words"
    );
}

// CEP:WHAT: Verifies the preprocessing subsumption pair budget fires.
// CEP:WHY: The preprocessing denial-of-service boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pass claims completion past the bound.
// CEP:ASSUMES: pair budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatSubsumptionPairBudget and hot/sat/preprocess.rs::{simplify_round, SimplifyStatus::PairBudgetExhausted}.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn subsumption_budget_enforced() {
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
    assert_eq!(
        outcome.status,
        mapt::hot::sat::preprocess::SimplifyStatus::PairBudgetExhausted
    );
}

// CEP:WHAT: Verifies the preprocessing vivification budget fires.
// CEP:WHY: The preprocessing denial-of-service boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pass claims completion past the bound.
// CEP:ASSUMES: propagation budget 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatVivifyPropagationBudget and hot/sat/preprocess.rs::{vivify, SimplifyStatus::VivifyBudgetExhausted}.
// CEP:SECURITY: the denial-of-service bound under test.
#[test]
fn vivify_budget_enforced() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(arena, kVariables, RestartPolicy::Luby, false).expect("solver");
    solver
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true)])
        .expect("c");
    let mut options = SimplifyOptions::new();
    options.vivify_budget = 1;
    let outcome = simplify(&solver, &options).expect("simplify");
    assert_eq!(
        outcome.status,
        mapt::hot::sat::preprocess::SimplifyStatus::VivifyBudgetExhausted
    );
}
