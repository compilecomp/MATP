// CEP:FILE: tests/property/given_clause_property_test.rs
// CEP:WHAT: Property tests for the given-clause loop: three-way agreement with the CDCL SAT solver and a brute-force oracle on propositional clause sets, pigeonhole refutation, and selection determinism.
// CEP:WHY: Spec 08 section 7: the loop's Theorem outcomes must be genuine refutations and its Saturated outcomes must agree with satisfiability - propositional clause sets (ground 0-ary-shaped atoms) give an exact oracle while exercising the full resolution path end to end.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any disagreement.
// CEP:ASSUMES: the deterministic LCG; the CDCL solver itself is oracle-verified by property/cdcl_property_test.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/search/given_clause.rs::saturate and hot/search/generate.rs.
// CEP:SECURITY: no untrusted input; fixed seeds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

// CEP:WHAT: Propositions per problem (distinct ground atoms).
// CEP:WHY: Brute force is 2^n; 7 keeps the oracle fast while the loop sees a real search.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropositions: u32 = 7;

// CEP:WHAT: Problems per run.
// CEP:WHY: Named property-test size (CEP&CC 28.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kProblems: u64 = 25;

// CEP:WHAT: One propositional problem fixture: the space, context, and the ground atoms.
// CEP:WHY: Propositions are ground p(f^k(a)) atoms; the fixture holds the search space and the atom list.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one space plus kPropositions interns.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
struct ProblemFixture {
    space: &'static SearchSpace<'static>,
    context: InferenceContext<'static>,
    #[allow(dead_code)]
    terms: &'static mapt::hot::ir::term::TermStore<'static>,
    #[allow(dead_code)]
    symbols: &'static mapt::hot::ir::symbol_table::SymbolTable<'static>,
    #[allow(dead_code)]
    builder: mapt::cold::symbol_table_builder::SymbolTableBuilder,
    atoms: Vec<mapt::hot::ir::term::TermPtr>,
}

// CEP:WHAT: Builds a problem fixture with kPropositions distinct ground atoms.
// CEP:WHY: One constructor.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_problem(passive_capacity: u32) -> ProblemFixture {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions::new();
    let space = Box::leak(Box::new(
        SearchSpace::new_with(
            arena,
            &options,
            passive_capacity,
            512,
            2048,
            4096,
            65536,
            4096,
        )
        .expect("space"),
    ));
    let symbols: &'static _ = Box::leak(Box::new(symbols));
    let terms: &'static _ = Box::leak(Box::new(terms));
    let precedence: &'static _ = Box::leak(Box::new(precedence));
    let a = terms
        .intern_fun(symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let g_id = symbol_id(&builder, "g");
    let mut atoms: Vec<mapt::hot::ir::term::TermPtr> = Vec::new();
    let mut current = a;
    for index in 0..kPropositions {
        if index > 0 {
            let head = if index % 2 == 0 { f_id } else { g_id };
            current = terms.intern_fun(symbols, head, &[current]).expect("atom");
        }
        atoms.push(current);
    }
    let context = InferenceContext {
        terms,
        symbols,
        substitution: &space.substitution,
        precedence,
        ordering: OrderingKind::Kbo,
    };
    ProblemFixture {
        space,
        context,
        terms,
        symbols,
        builder,
        atoms,
    }
}

// CEP:WHAT: Verifies the loop agrees with the CDCL solver on random propositional clause sets.
// CEP:WHY: The SAT solver is the independent engine (itself oracle-verified); Theorem must imply UNSAT and Saturated must imply SAT.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: the loop's budgets never fire on these small problems.
// CEP:COST: 25 problems x two engines.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate and hot/search/generate.rs::generate_step.
// CEP:SECURITY: none.
#[test]
fn loop_agrees_with_sat_solver() {
    let mut rng = DeterministicRng::new(0x0100_C001);
    for _ in 0..kProblems {
        let clause_count = 3 + rng.below(6u64);
        let mut problem: Vec<Vec<usize>> = Vec::new();
        for _ in 0..clause_count {
            let length = 1 + rng.below(3u64);
            let mut clause: Vec<usize> = Vec::new();
            for _ in 0..length {
                // Encode (proposition, polarity) as index*2 + (polarity?0:1).
                clause.push(rng.below((kPropositions * 2) as u64) as usize);
            }
            problem.push(clause);
        }
        let outcome = run_loop(&problem, 1024);
        let sat = sat_answer(&problem);
        match outcome {
            SearchOutcome::Theorem { .. } => assert!(
                !sat,
                "the loop refuted a satisfiable problem: {:?}",
                problem
            ),
            SearchOutcome::Saturated => assert!(
                sat,
                "the loop saturated an unsatisfiable problem: {:?}",
                problem
            ),
            other => panic!("unexpected outcome on a small problem: {:?}", other),
        }
    }
}

// CEP:WHAT: Verifies the loop agrees with a brute-force oracle on random propositional clause sets.
// CEP:WHY: The fully independent ground truth (2^n enumeration).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: none.
// CEP:COST: 25 problems x 2^n.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate.
// CEP:SECURITY: none.
#[test]
fn loop_agrees_with_brute_force() {
    let mut rng = DeterministicRng::new(0x0100_C002);
    for _ in 0..kProblems {
        let clause_count = 3 + rng.below(6u64);
        let mut problem: Vec<Vec<usize>> = Vec::new();
        for _ in 0..clause_count {
            let length = 1 + rng.below(3u64);
            let mut clause: Vec<usize> = Vec::new();
            for _ in 0..length {
                clause.push(rng.below((kPropositions * 2) as u64) as usize);
            }
            problem.push(clause);
        }
        let outcome = run_loop(&problem, 1024);
        let sat = brute_force_sat(&problem);
        match outcome {
            SearchOutcome::Theorem { .. } => assert!(!sat, "refuted a SAT problem"),
            SearchOutcome::Saturated => assert!(sat, "saturated an UNSAT problem"),
            other => panic!("unexpected outcome: {:?}", other),
        }
    }
}

// CEP:WHAT: Verifies the loop refutes the pigeonhole principle PHP(3,2).
// CEP:WHY: The classic propositional refutation exercising resolution chains.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any non-Theorem outcome.
// CEP:ASSUMES: propositions 0..5 encode pigeon-hole occupancy.
// CEP:COST: one run.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate and hot/search/passive.rs.
// CEP:SECURITY: none.
#[test]
fn loop_refutes_pigeonhole() {
    // Propositions: pigeon i in hole j -> proposition i * 2 + j; the encoded
    // problem index is proposition * 2 + (0 for positive, 1 for negative).
    let mut problem: Vec<Vec<usize>> = Vec::new();
    for pigeon in 0..3usize {
        problem.push(vec![(pigeon * 2) * 2, (pigeon * 2 + 1) * 2]);
    }
    for hole in 0..2usize {
        for first in 0..3usize {
            for second in (first + 1)..3usize {
                // not (first in hole) or not (second in hole): negated index + 1
                // offset by the encoding (see run_loop's decode).
                problem.push(vec![
                    (first * 2 + hole) * 2 + 1,
                    (second * 2 + hole) * 2 + 1,
                ]);
            }
        }
    }
    let outcome = run_loop(&problem, 4096);
    assert!(
        matches!(outcome, SearchOutcome::Theorem { .. }),
        "PHP(3,2) must refute: {:?}",
        outcome
    );
}

// CEP:WHAT: Verifies the loop's selection and generation are deterministic for a fixed problem.
// CEP:WHY: CEP&CC 38.10 end to end.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when two identical runs disagree.
// CEP:ASSUMES: none.
// CEP:COST: two runs.
// CEP:EVIDENCE: cited by hot/search/passive.rs (file header) and hot/search/given_clause.rs::saturate.
// CEP:SECURITY: none.
#[test]
fn selection_is_deterministic() {
    let problem: Vec<Vec<usize>> = vec![
        vec![0, 2, 4],
        vec![1, 3, 5],
        vec![0, 3],
        vec![2, 5, 1],
        vec![4],
    ];
    let run = || {
        let fixture = make_problem(1024);
        let mut stats = SearchStats::default();
        add_problem(&fixture, &problem);
        let options = SearchOptions::new();
        let never = |_iterations: u64| false;
        let outcome = saturate(
            fixture.space,
            &fixture.context,
            &options,
            &never,
            &mut stats,
        )
        .expect("saturate");
        (outcome, stats)
    };
    let first = run();
    let second = run();
    assert_eq!(
        format!("{:?}", first.0),
        format!("{:?}", second.0),
        "outcomes must agree"
    );
    assert_eq!(first.1.given_processed, second.1.given_processed);
    assert_eq!(first.1.inferences, second.1.inferences);
}

// CEP:WHAT: Adds a propositional problem to a fixture.
// CEP:WHY: The encoding: index i means proposition i/2 with polarity i%2 == 0 (positive).
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: indices below kPropositions * 2.
// CEP:COST: one input clause per problem clause.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn add_problem(fixture: &ProblemFixture, problem: &[Vec<usize>]) {
    let options = SearchOptions::new();
    for clause in problem.iter() {
        let literals: Vec<Literal> = clause
            .iter()
            .map(|index| {
                let proposition = index / 2;
                let positive = index % 2 == 0;
                Literal::new(fixture.atoms[proposition], positive)
            })
            .collect();
        fixture
            .space
            .add_input_clause(&fixture.context, &options, &literals)
            .expect("input");
    }
}

// CEP:WHAT: Runs the loop on a problem and returns the outcome.
// CEP:WHY: One driver.
// CEP:STATUS: complete
// CEP:FAILURE: panics on search errors.
// CEP:ASSUMES: none.
// CEP:COST: one saturation.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn run_loop(problem: &[Vec<usize>], passive_capacity: u32) -> SearchOutcome {
    let fixture = make_problem(passive_capacity);
    add_problem(&fixture, problem);
    let options = SearchOptions::new();
    let mut stats = SearchStats::default();
    let never = |_iterations: u64| false;
    saturate(
        fixture.space,
        &fixture.context,
        &options,
        &never,
        &mut stats,
    )
    .expect("saturate")
}

// CEP:WHAT: The brute-force satisfiability oracle.
// CEP:WHY: Fully independent ground truth.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: indices below kPropositions * 2.
// CEP:COST: O(2^n x clauses).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn brute_force_sat(problem: &[Vec<usize>]) -> bool {
    for assignment in 0..(1u64 << kPropositions) {
        let satisfied = problem.iter().all(|clause| {
            clause.iter().any(|index| {
                let proposition = (index / 2) as u32;
                let positive = index % 2 == 0;
                ((assignment >> proposition) & 1 == 1) == positive
            })
        });
        if satisfied {
            return true;
        }
    }
    false
}

// CEP:WHAT: The CDCL solver answer for the same problem.
// CEP:WHY: The independent engine oracle.
// CEP:STATUS: complete
// CEP:FAILURE: panics on solver errors.
// CEP:ASSUMES: none.
// CEP:COST: one solve.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn sat_answer(problem: &[Vec<usize>]) -> bool {
    use mapt::hot::sat::literal::{SatLiteral, SatVar};
    use mapt::hot::sat::restart::RestartPolicy;
    use mapt::hot::sat::solver::{CdclSolver, SolveResult};
    let arena = common::make_arena(common::kSatFixtureArenaBytes * 8);
    let solver = CdclSolver::new(arena, kPropositions, RestartPolicy::Luby, false).expect("s");
    for clause in problem.iter() {
        let literals: Vec<SatLiteral> = clause
            .iter()
            .map(|index| SatLiteral::new(SatVar((index / 2) as u32), index % 2 == 0).expect("lit"))
            .collect();
        solver.add_clause(&literals).expect("add");
    }
    matches!(solver.solve(), SolveResult::Satisfiable)
}
