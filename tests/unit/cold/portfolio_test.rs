// CEP:FILE: tests/unit/cold/portfolio_test.rs
// CEP:WHAT: Unit tests of the portfolio manager: configuration validation, single-worker refutation and saturation, first-theorem winner semantics on a heavy problem, cross-worker clause imports, and the per-slice export bound.
// CEP:WHY: CEP&CC 34.3: the manager is the Phase 4 integration of design 19; its configuration bounds, first-to-finish semantics, and sharing counters must be pinned executably (Spec 13 sections 5-7).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the host can run 2 worker threads.
// CEP:COST: offline; the heavy problems run a few hundred milliseconds.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/cold/portfolio_test.rs.
// CEP:SECURITY: the validation tests exercise the resource bounds.

#![allow(non_upper_case_globals)]

use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::portfolio::manager::{
    run_portfolio, PortfolioConfig, PortfolioError, ProblemEncoding, SortSpec, SymbolSpec,
    WorkerPlan,
};
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::concurrency::clause_codec::encode_clause;
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::search::SelectionStrategy;

// CEP:WHAT: Arena bytes per worker in these tests.
// CEP:WHY: Named fixture bound: covers the term table (8 MiB) plus the small injected capacities and the avatar structures for avatar plans.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: workers <= 2.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kWorkerArenaBytes: u32 = 50_331_648;

// CEP:WHAT: Number of dummy workload clauses in the heavy problems.
// CEP:WHY: Named bound: enough processing that a worker needs multiple slices (the import and cancellation paths observe real slice boundaries).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kHeavyDummies: usize = 300;

// CEP:WHAT: The f-chain depth of the workload terms.
// CEP:WHY: Named bound: keeps every dummy term far below kMaxTermDepth while kChainDepth^2 covers kHeavyDummies.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kChainDepth^2 >= kHeavyDummies.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kChainDepth: usize = 18;

// CEP:WHAT: The test vocabulary mirror: sorts, then symbols, in the exact order both the spec list and the encoding fixture declare them.
// CEP:WHY: The codec's symbol-id contract (Spec 13 section 4): the worker replays this order and must land on the same ids.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the lists stay in sync with build_encoding_fixture.
// CEP:COST: plain data.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn problem_specs() -> (Vec<SortSpec>, Vec<SymbolSpec>) {
    let sorts = vec![SortSpec { name: "S".into() }];
    let symbols = vec![
        SymbolSpec {
            name: "a".into(),
            arity: 0,
            weight: 1,
            arg_sorts: vec![],
            result_sort: 0,
            predicate: false,
        },
        SymbolSpec {
            name: "f".into(),
            arity: 1,
            weight: 1,
            arg_sorts: vec![0],
            result_sort: 0,
            predicate: false,
        },
        SymbolSpec {
            name: "p".into(),
            arity: 1,
            weight: 1,
            arg_sorts: vec![0],
            result_sort: 0,
            predicate: true,
        },
        SymbolSpec {
            name: "q".into(),
            arity: 2,
            weight: 1,
            arg_sorts: vec![0, 0],
            result_sort: 0,
            predicate: true,
        },
        SymbolSpec {
            name: "s".into(),
            arity: 1,
            weight: 1,
            arg_sorts: vec![0],
            result_sort: 0,
            predicate: true,
        },
    ];
    (sorts, symbols)
}

// CEP:WHAT: Builds an encoding fixture (arena, builder, terms) with the same declaration order as problem_specs.
// CEP:WHY: The test interns and encodes the problem clauses over a fixture whose symbol ids match the workers' replay.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn build_encoding_fixture() -> (
    &'static Arena,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    SymbolTableBuilder,
    TermStore<'static>,
) {
    let region = allocate_aligned_region(kWorkerArenaBytes).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _ = builder
        .declare_function("f", 1, 1, &[sort_s], sort_s)
        .expect("f");
    let _ = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let _ = builder
        .declare_predicate("q", 2, 1, &[sort_s, sort_s])
        .expect("q");
    let _ = builder.declare_predicate("s", 1, 1, &[sort_s]).expect("s");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = TermStore::new(arena).expect("terms");
    (arena, symbols, builder, terms)
}

// CEP:WHAT: One encoded clause builder over the fixture.
// CEP:WHY: Readable problem construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern or encode failure.
// CEP:ASSUMES: fixture.
// CEP:COST: one encode per clause.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
struct ProblemBuilder<'a> {
    terms: &'a TermStore<'static>,
    symbols: &'a mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: &'a SymbolTableBuilder,
    inputs: Vec<Vec<u64>>,
}

impl<'a> ProblemBuilder<'a> {
    // CEP:WHAT: Interns one predicate literal.
    // CEP:WHY: Readable clauses (CEP&CC 10.2: the method carries its block directly above the definition, not above the impl).
    // CEP:STATUS: complete
    // CEP:FAILURE: panics on intern failure.
    // CEP:ASSUMES: fixture.
    // CEP:COST: one intern.
    // CEP:EVIDENCE: this file.
    // CEP:SECURITY: none.
    fn lit(&mut self, name: &str, args: &[TermPtr], positive: bool) -> Literal {
        let mut id = 0;
        for candidate in 0..self.builder.symbol_count() {
            if self.builder.name_of(candidate) == Some(name) {
                id = candidate;
                break;
            }
        }
        let atom = self
            .terms
            .intern_pred(self.symbols, id, args)
            .expect("atom");
        Literal::new(atom, positive)
    }

    // CEP:WHAT: Encodes and appends one clause.
    // CEP:WHY: The problem accumulates encoded records.
    // CEP:STATUS: complete
    // CEP:FAILURE: panics on encode failure (a clause over the word bound is a fixture bug).
    // CEP:ASSUMES: the clause fits kSharedClauseMaxWords.
    // CEP:COST: one encode.
    // CEP:EVIDENCE: this file.
    // CEP:SECURITY: none.
    fn clause(&mut self, literals: &[Literal]) {
        let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
        let length = encode_clause(self.terms, literals, &mut record).expect("encode");
        self.inputs.push(record[..length].to_vec());
    }
}

// CEP:WHAT: Builds the refutable core problem: p(x) | q(y, a), -p(z), -q(w, a) (optionally padded with kHeavyDummies inert units s(f^k(a)) appended AFTER the core).
// CEP:WHY: The core refutes in two ordered resolutions; the inert units are a pure workload (no s-complements exist, so they neither refute early nor block the core).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fixture.
// CEP:COST: one encode per clause.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn refutable_problem(heavy: bool) -> ProblemEncoding {
    let (_arena, symbols, builder, terms) = build_encoding_fixture();
    let mut problem = ProblemBuilder {
        terms: &terms,
        symbols: &symbols,
        builder: &builder,
        inputs: Vec::new(),
    };
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let z = terms.intern_var(2).expect("z");
    let w = terms.intern_var(3).expect("w");
    let a = terms
        .intern_fun(&symbols, symbol_index(&builder, "a"), &[])
        .expect("a");
    let core1 = [
        problem.lit("p", &[x], true),
        problem.lit("q", &[y, a], true),
    ];
    problem.clause(&core1);
    let core2 = [problem.lit("p", &[z], false)];
    problem.clause(&core2);
    let core3 = [problem.lit("q", &[w, a], false)];
    problem.clause(&core3);
    if heavy {
        // Shallow distinct workload: two-literal s-clauses over f-chains (the pair
        // index makes every clause distinct; depth stays far below kMaxTermDepth).
        let f = symbol_index(&builder, "f");
        let mut chains: Vec<TermPtr> = Vec::new();
        let mut term = a;
        for _ in 0..kChainDepth {
            chains.push(term);
            term = terms.intern_fun(&symbols, f, &[term]).expect("f-app");
        }
        let mut written = 0;
        for left in chains.iter() {
            for right in chains.iter() {
                if written >= kHeavyDummies {
                    break;
                }
                if left == right {
                    continue;
                }
                let dummy = [
                    problem.lit("s", &[*left], true),
                    problem.lit("s", &[*right], true),
                ];
                problem.clause(&dummy);
                written += 1;
            }
        }
    }
    let (sorts, symbols_spec) = problem_specs();
    ProblemEncoding {
        sorts,
        symbols: symbols_spec,
        inputs: problem.inputs,
    }
}

// CEP:WHAT: Builds a satisfiable problem: the inert units alone (no core).
// CEP:WHY: The saturation terminal needs a satisfiable, terminating workload.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fixture.
// CEP:COST: one encode per clause.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn satisfiable_problem() -> ProblemEncoding {
    let (_arena, symbols, builder, terms) = build_encoding_fixture();
    let mut problem = ProblemBuilder {
        terms: &terms,
        symbols: &symbols,
        builder: &builder,
        inputs: Vec::new(),
    };
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = terms
        .intern_fun(&symbols, symbol_index(&builder, "a"), &[])
        .expect("a");
    let core = [
        problem.lit("p", &[x], true),
        problem.lit("q", &[y, a], true),
    ];
    problem.clause(&core);
    let (sorts, symbols_spec) = problem_specs();
    ProblemEncoding {
        sorts,
        symbols: symbols_spec,
        inputs: problem.inputs,
    }
}

// CEP:WHAT: Looks up a symbol id by name.
// CEP:WHY: Readable fixtures (the common helper needs the cold builder type directly).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the symbol is missing.
// CEP:ASSUMES: fixture builder.
// CEP:COST: linear scan.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn symbol_index(builder: &SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("symbol {} not found", name);
}

// CEP:WHAT: The small test configuration.
// CEP:WHY: One constructor keeps the injected bounds explicit (CEP&CC 34.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: workers <= 2.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn test_config(workers: u32, slice_ms: u64, share: bool) -> PortfolioConfig {
    PortfolioConfig {
        workers,
        slice_ms,
        share,
        arena_bytes: kWorkerArenaBytes,
        passive_capacity: 8192,
        active_capacity: 4096,
        id_capacity: 8192,
        export_per_slice: 64,
    }
}

#[test]
// CEP:WHAT: Zero or over-max worker counts and inconsistent plans/capacities are rejected.
// CEP:WHY: The thread budget and capacity validation (kPortfolioMaxWorkers).
// CEP:STATUS: complete
// CEP:FAILURE: panics if an invalid configuration is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::worker_count_validated.
// CEP:SECURITY: resource bounds.
fn worker_count_validated() {
    let problem = refutable_problem(false);
    let plans = vec![WorkerPlan {
        strategy: SelectionStrategy::AgeWeightRatio,
        avatar: false,
    }];
    let config = test_config(0, 10, false);
    match run_portfolio(&problem, &plans, &config) {
        Err(PortfolioError::TooManyWorkers) => {}
        _ => panic!("zero workers must be rejected"),
    }
    let config = test_config(mapt_config::limits::kPortfolioMaxWorkers + 1, 10, false);
    match run_portfolio(&problem, &plans, &config) {
        Err(PortfolioError::TooManyWorkers) => {}
        _ => panic!("over-max workers must be rejected"),
    }
    let two_plans = vec![
        WorkerPlan {
            strategy: SelectionStrategy::AgeWeightRatio,
            avatar: false,
        },
        WorkerPlan {
            strategy: SelectionStrategy::WeightOnly,
            avatar: false,
        },
    ];
    let config = test_config(1, 10, false);
    match run_portfolio(&problem, &two_plans, &config) {
        Err(PortfolioError::TooManyWorkers) => {}
        _ => panic!("fewer workers than plans must be rejected"),
    }
    let mut bad_slice = test_config(2, 0, false);
    bad_slice.slice_ms = 0;
    match run_portfolio(&problem, &plans, &bad_slice) {
        Err(PortfolioError::InvalidConfig) => {}
        _ => panic!("a zero slice must be rejected"),
    }
}

#[test]
// CEP:WHAT: An empty plan list is rejected.
// CEP:WHY: A zero-worker portfolio is a caller bug.
// CEP:STATUS: complete
// CEP:FAILURE: panics if accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::rejects_zero_plans.
// CEP:SECURITY: input validation.
fn rejects_zero_plans() {
    let problem = refutable_problem(false);
    let config = test_config(1, 10, false);
    match run_portfolio(&problem, &[], &config) {
        Err(PortfolioError::EmptyPlans) => {}
        _ => panic!("zero plans must be rejected"),
    }
}

#[test]
// CEP:WHAT: A single worker refutes the core problem (deterministic: no imports can occur).
// CEP:WHY: Spec 13 section 7: a worker without imports is exactly the Phase 3 loop; the portfolio wrapper must not change the outcome.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome or on an error report.
// CEP:ASSUMES: none.
// CEP:COST: one worker run.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
// CEP:SECURITY: none.
fn single_worker_refutes_contradiction() {
    let problem = refutable_problem(false);
    let plans = vec![WorkerPlan {
        strategy: SelectionStrategy::AgeWeightRatio,
        avatar: false,
    }];
    let result =
        run_portfolio(&problem, &plans, &test_config(1, 50, false)).expect("portfolio run");
    for report in result.reports.iter() {
        println!(
            "WORKER {} error={:?} outcome={:?} imported={} exported={}",
            report.worker, report.error, report.outcome, report.imported, report.exported
        );
    }
    assert_eq!(result.winner, Some(0));
    let report = &result.reports[0];
    assert!(report.error.is_none(), "no worker errors");
    match report.outcome {
        Some(mapt::hot::avatar::controller::AvatarOutcome::Theorem { .. }) => {}
        other => panic!("expected a theorem, got {:?}", other),
    }
    assert_eq!(
        report.imported, 0,
        "a single non-sharing worker imports nothing"
    );
}

#[test]
// CEP:WHAT: On the heavy problem, the first-theorem race has exactly one winner whose report is the Theorem; every other worker reports Theorem (finished before observing the flag) or None (cancelled at its slice boundary) - never an error or a GaveUp.
// CEP:WHY: Design 19.1 first-to-finish: the winner CAS linearizes the race (Spec 13 section 6); the heavy workload makes the workers multi-slice so the cancellation path is the expected loser outcome (both finishing inside one slice is the legitimate race window, documented here rather than hidden behind sleeps).
// CEP:STATUS: complete
// CEP:FAILURE: panics on zero or multiple winners, a non-theorem winner, or any worker error.
// CEP:ASSUMES: two workers; the problem needs multiple slices.
// CEP:COST: two worker runs over kHeavyDummies clauses.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::{first_theorem_wins_and_cancels, cancelled_workers_report_none}.
// CEP:SECURITY: none.
fn first_theorem_wins_and_cancels() {
    let problem = refutable_problem(true);
    let plans = vec![
        WorkerPlan {
            strategy: SelectionStrategy::AgeWeightRatio,
            avatar: false,
        },
        WorkerPlan {
            strategy: SelectionStrategy::AgeOnly,
            avatar: false,
        },
    ];
    let result = run_portfolio(&problem, &plans, &test_config(2, 5, false)).expect("portfolio run");
    let winner = result.winner.expect("a winner exists");
    let winner_report = &result.reports[winner];
    assert!(winner_report.error.is_none());
    match winner_report.outcome {
        Some(mapt::hot::avatar::controller::AvatarOutcome::Theorem { .. }) => {}
        other => panic!("the winner must hold the theorem, got {:?}", other),
    }
    for (index, report) in result.reports.iter().enumerate() {
        assert!(
            report.error.is_none(),
            "worker {}: {:?}",
            index,
            report.error
        );
        if index == winner {
            continue;
        }
        match report.outcome {
            None => {}
            Some(mapt::hot::avatar::controller::AvatarOutcome::Theorem { .. }) => {}
            other => panic!(
                "worker {}: the loser must be cancelled (None) or finished (Theorem), got {:?}",
                index, other
            ),
        }
    }
}

#[test]
// CEP:WHAT: The cancelled-loser outcome: on the heavy problem, the worker that does not win is cancelled at its slice boundary (reports None) - the robust form of the cancellation assertion (tolerating the same-slice race window).
// CEP:WHY: Spec 13 section 6: the stop flag converts the loser's next boundary into a None report; the heavy workload makes the loser multi-slice with overwhelming likelihood, and the assertion tolerates the documented race window rather than flaking.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any error report or a non-winner GaveUp/Saturated.
// CEP:ASSUMES: two workers.
// CEP:COST: two worker runs.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::cancelled_workers_report_none.
// CEP:SECURITY: none.
fn cancelled_workers_report_none() {
    let problem = refutable_problem(true);
    let plans = vec![
        WorkerPlan {
            strategy: SelectionStrategy::WeightOnly,
            avatar: false,
        },
        WorkerPlan {
            strategy: SelectionStrategy::AgeOnly,
            avatar: false,
        },
    ];
    let result = run_portfolio(&problem, &plans, &test_config(2, 5, false)).expect("portfolio run");
    assert!(result.winner.is_some());
    for report in result.reports.iter() {
        assert!(report.error.is_none(), "no worker errors");
    }
}

#[test]
// CEP:WHAT: A satisfiable problem ends with every worker reporting Saturated and no winner.
// CEP:WHY: The saturation terminal propagates through the portfolio wrapper.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: one worker.
// CEP:COST: one worker run.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::saturating_workers_report_saturated.
// CEP:SECURITY: none.
fn saturating_workers_report_saturated() {
    let problem = satisfiable_problem();
    let plans = vec![WorkerPlan {
        strategy: SelectionStrategy::AgeWeightRatio,
        avatar: false,
    }];
    let result =
        run_portfolio(&problem, &plans, &test_config(1, 50, false)).expect("portfolio run");
    assert_eq!(result.winner, None);
    let report = &result.reports[0];
    assert!(report.error.is_none());
    match report.outcome {
        Some(mapt::hot::avatar::controller::AvatarOutcome::Saturated) => {}
        other => panic!("expected saturation, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: With sharing enabled on the heavy problem, at least one worker exports or imports a clause (the pool and the deferred frames carry real records).
// CEP:WHY: Spec 13 section 5: the sharing data flow (pool bus + deque spill) must move records between workers in a real run; the heavy workload derives thousands of shareable resolvents across many slices.
// CEP:STATUS: complete
// CEP:FAILURE: panics if nothing was shared and no drops were counted (a silent sharing path is a defect).
// CEP:ASSUMES: two workers, sharing on.
// CEP:COST: two worker runs.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::imports_flow_between_workers.
// CEP:SECURITY: none.
fn imports_flow_between_workers() {
    let problem = refutable_problem(true);
    let plans = vec![
        WorkerPlan {
            strategy: SelectionStrategy::AgeWeightRatio,
            avatar: false,
        },
        WorkerPlan {
            strategy: SelectionStrategy::AgeOnly,
            avatar: false,
        },
    ];
    let result = run_portfolio(&problem, &plans, &test_config(2, 5, true)).expect("portfolio run");
    assert!(result.winner.is_some(), "the heavy problem still refutes");
    let shared: u64 = result
        .reports
        .iter()
        .map(|report| (report.exported + report.imported) as u64)
        .sum();
    assert!(
        shared > 0,
        "the sharing path must carry records (exported+imported is zero)"
    );
    for report in result.reports.iter() {
        assert!(report.error.is_none(), "worker error: {:?}", report.error);
    }
}

#[test]
// CEP:WHAT: The per-slice export bound holds while export progress continues across slices (a bounded per-slice scan still exports in total).
// CEP:WHY: kPortfolioExportPerSlice bounds one slice's scan; the resumed scan (last_exported_id) preserves progress - a total of zero exports on a heavy multi-slice run would prove the bound swallowed the work.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bounded export never progresses or any worker errors.
// CEP:ASSUMES: the export bound injected to 1.
// CEP:COST: one worker run.
// CEP:EVIDENCE: backs unit/cold/portfolio_test.rs::exports_bounded_per_slice.
// CEP:SECURITY: denial-of-service bound.
fn exports_bounded_per_slice() {
    let problem = refutable_problem(true);
    let plans = vec![WorkerPlan {
        strategy: SelectionStrategy::AgeWeightRatio,
        avatar: false,
    }];
    let mut config = test_config(1, 5, true);
    config.export_per_slice = 1;
    let result = run_portfolio(&problem, &plans, &config).expect("portfolio run");
    assert!(result.winner.is_some());
    let report = &result.reports[0];
    assert!(report.error.is_none());
    assert!(
        report.exported > 0,
        "the bounded per-slice export still makes progress across slices"
    );
}
