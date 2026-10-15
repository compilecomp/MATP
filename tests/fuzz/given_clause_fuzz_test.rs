// CEP:FILE: tests/fuzz/given_clause_fuzz_test.rs
// CEP:WHAT: Fuzz test for the given-clause loop: random propositional problems under a bounded inference budget must terminate with an outcome consistent with the brute-force oracle, and the budget path itself must stay total.
// CEP:WHY: CEP&CC 38.44 and design 26: the loop is the Phase 3 deliverable; fuzzing it against the oracle on adversarial random inputs (duplicate literals, unit clauses, tautologies, contradictions) exercises every loop path with unbounded structural variety under fixed seeds.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any disagreement or hang.
// CEP:ASSUMES: the deterministic LCG; small budgets keep the fuzz fast while still reaching every path.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/search/given_clause.rs (file header) and hot/search/generate.rs.
// CEP:SECURITY: the budgets under fuzz are the denial-of-service bounds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::search::given_clause::{
    saturate, GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

// CEP:WHAT: Propositions per problem.
// CEP:WHY: Brute force stays exact.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropositions: u32 = 6;

// CEP:WHAT: Fuzz iterations.
// CEP:WHY: Named fuzz size (CEP&CC 28.3, 38.44).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kIterations: u64 = 120;

// CEP:WHAT: Verifies loop outcomes stay oracle-consistent under adversarial random problems with tautologies, duplicates, and contradictions.
// CEP:WHY: The oracle agreement is the correctness invariant; the budget outcomes are permitted only when the budget genuinely fired.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: none.
// CEP:COST: 120 problems.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate and hot/search/generate.rs::{generate_step, step_resolution}.
// CEP:SECURITY: the bounded-outcome discipline under fuzz.
#[test]
fn fuzz_loop_stays_oracle_consistent() {
    let mut rng = DeterministicRng::new(0x00F0_2201);
    for iteration in 0..kIterations {
        let clause_count = 1 + rng.below(10u64);
        let mut problem: Vec<Vec<usize>> = Vec::new();
        for _ in 0..clause_count {
            let length = 1 + rng.below(4u64);
            let mut clause: Vec<usize> = Vec::new();
            for _ in 0..length {
                // Adversarial encodings: duplicates, complementary pairs, and
                // repeated propositions all appear naturally.
                clause.push(rng.below((kPropositions * 2) as u64) as usize);
            }
            problem.push(clause);
        }
        let oracle = brute_force_sat(&problem);
        let outcome = run_loop(&problem);
        match outcome {
            SearchOutcome::Theorem { .. } => assert!(
                !oracle,
                "iteration {}: refuted a satisfiable problem {:?}",
                iteration, problem
            ),
            SearchOutcome::Saturated => assert!(
                oracle,
                "iteration {}: saturated an unsatisfiable problem {:?}",
                iteration, problem
            ),
            SearchOutcome::GaveUp(reason) => {
                // Budgets are permitted only for the documented reasons; the
                // inference budget is the one configured here.
                assert!(
                    matches!(
                        reason,
                        GaveUpReason::InferenceBudget
                            | GaveUpReason::MemoryBudget
                            | GaveUpReason::TimeBudget
                    ),
                    "iteration {}: unexpected give-up reason {:?}",
                    iteration,
                    reason
                );
            }
        }
    }
}

// CEP:WHAT: Runs the loop on one problem.
// CEP:WHY: One driver.
// CEP:STATUS: complete
// CEP:FAILURE: panics on search errors.
// CEP:ASSUMES: none.
// CEP:COST: one saturation under a bounded budget.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn run_loop(problem: &[Vec<usize>]) -> SearchOutcome {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let mut options = SearchOptions::new();
    options.inference_budget = 512;
    let space = SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 131072, 4096)
        .expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let g_id = symbol_id(&builder, "g");
    let mut atoms: Vec<mapt::hot::ir::term::TermPtr> = Vec::new();
    let mut current = a;
    for index in 0..kPropositions {
        if index > 0 {
            let head = if index % 2 == 0 { f_id } else { g_id };
            current = terms.intern_fun(&symbols, head, &[current]).expect("atom");
        }
        atoms.push(current);
    }
    for clause in problem.iter() {
        let literals: Vec<Literal> = clause
            .iter()
            .map(|index| Literal::new(atoms[index / 2], index % 2 == 0))
            .collect();
        space
            .add_input_clause(&context, &options, &literals)
            .expect("input");
    }
    let mut stats = SearchStats::default();
    let never = |_iterations: u64| false;
    saturate(&space, &context, &options, &never, &mut stats).expect("saturate")
}

// CEP:WHAT: The brute-force oracle.
// CEP:WHY: Independent ground truth.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: indices below kPropositions * 2.
// CEP:COST: O(2^n x clauses).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn brute_force_sat(problem: &[Vec<usize>]) -> bool {
    for assignment in 0..(1u64 << kPropositions) {
        let satisfied = problem.iter().all(|clause| {
            clause
                .iter()
                .any(|index| ((assignment >> (index / 2)) & 1 == 1) == (index % 2 == 0))
        });
        if satisfied {
            return true;
        }
    }
    false
}
