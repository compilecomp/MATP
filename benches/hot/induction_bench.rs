// CEP:FILE: benches/hot/induction_bench.rs
// CEP:WHAT: Automated-induction benchmarks (bench CEP-BENCH-0036): cycles per scheme-clause installation (scan amortized: validation, signature scan, builder interning, staging, store insert, passive push) on a fixture with eight occurring unary predicates, and cycles per input-signature scan node.
// CEP:WHY: Design 26 (revised build order Phase 4) and CEP&CC 23: the induction feature adds clauses to the search - its installation cost must carry OPT-0 cycle evidence; the per-scheme measurement amortizes the one-time scan over the sixteen scheme clauses (eight predicates x two), which is the production shape (the installer runs once per problem), and the per-node measurement isolates the scan's dominant loop for future optimization tickets.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly; it is not production code).
// CEP:ASSUMES: The cycle counter is accurate (harness asserts it); measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs (CEP:COST), hot/induction/scheme.rs, and scripts/bench_gate.py baselines induction_scheme_install and induction_scan_node.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::induction::{add_induction_schemes, InductionDeclaration};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::SearchOptions;
use mapt::hot::search::SearchSpace;
use mapt_config::limits::{kInductionScanNodeBudget, kMaxInductionAttempts};

// CEP:WHAT: Arena bytes for the induction bench.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 100_663_296;

// CEP:WHAT: The number of unary predicates in the bench fixture.
// CEP:WHY: Named fixture size: sixteen scheme clauses amortize the one-time scan (the production shape).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_PREDICATES: usize = 8;

// CEP:WHAT: Builds the bench fixture: eight unary predicates over one sort with two inputs each, plus the Nat declaration symbols.
// CEP:WHY: One constructor keeps the measured scenario identical across runs.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_fixture() -> (
    &'static Arena,
    SymbolTable<'static>,
    SymbolTableBuilder,
    TermStore<'static>,
    PrecedenceTable<'static>,
    Vec<u32>,
    u32,
    u32,
    u32,
) {
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_n = SortId(builder.declare_sort("N").expect("sort"));
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_n)
        .expect("zero");
    let _sk = builder
        .declare_function("sk", 0, 1, &[], sort_n)
        .expect("sk");
    let a = builder.declare_function("a", 0, 1, &[], sort_n).expect("a");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_n], sort_n)
        .expect("succ");
    let mut predicates: Vec<u32> = Vec::new();
    for index in 0..KBENCH_PREDICATES {
        predicates.push(
            builder
                .declare_predicate(&format!("q{}", index), 1, 1, &[sort_n])
                .expect("predicate"),
        );
    }
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    (
        arena, symbols, builder, terms, precedence, predicates, zero, succ, a,
    )
}

// CEP:WHAT: Adds the fixture's input clauses (two per predicate) and returns the fixture bundle with the space and context.
// CEP:WHY: The installation measurement needs the inputs present (the scan reads them).
// CEP:STATUS: complete
// CEP:FAILURE: panics on add failure.
// CEP:ASSUMES: none.
// CEP:COST: O(inputs).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn add_inputs(
    arena: &'static Arena,
    symbols: &SymbolTable<'static>,
    terms: &TermStore<'static>,
    precedence: &PrecedenceTable<'static>,
    predicates: &[u32],
    a: u32,
) -> (SearchSpace<'static>, SearchOptions) {
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    let context = InferenceContext {
        terms,
        symbols,
        substitution: &space.substitution,
        precedence,
        ordering: OrderingKind::Kbo,
    };
    let t_a = terms.intern_fun(symbols, a, &[]).expect("a");
    let t_x = terms.intern_var(0).expect("x");
    for predicate in predicates.iter() {
        let p_a = terms
            .intern_pred(symbols, *predicate, &[t_a])
            .expect("p(a)");
        let p_x = terms
            .intern_pred(symbols, *predicate, &[t_x])
            .expect("p(x)");
        space
            .add_input_clause(&context, &options, &[Literal::new(p_a, true)])
            .expect("input");
        space
            .add_input_clause(&context, &options, &[Literal::new(p_x, false)])
            .expect("input");
    }
    (space, options)
}

// CEP:WHAT: The bench entry point: builds the fixture and records the three measurements (installation per clause, per scanned node, and the pure builder).
// CEP:WHY: CEP&CC 10.2: every function carries a preceding CEP comment block, bench mains included.
// CEP:STATUS: complete
// CEP:FAILURE: panics on measurement failure (bench tooling may fail loudly).
// CEP:ASSUMES: the harness's cycle counter assertions hold.
// CEP:COST: the measured operations' costs are the artifact.
// CEP:EVIDENCE: this file's artifacts under benches/artifacts/.
// CEP:SECURITY: no untrusted input.
fn main() {
    let (arena, symbols, builder, terms, precedence, predicates, zero, succ, a) = make_fixture();
    let skolem = (0..builder.symbol_count())
        .find(|id| builder.name_of(*id) == Some("sk"))
        .expect("sk");

    // Measurement 1: cycles per scheme clause for the full installation
    // (validation + scan + build + staging + insert + passive push). The
    // installation is single-shot by nature (a second run on the same space
    // would re-scan the first run's schemes), so each repeat prepares a fresh
    // space and input set OUTSIDE the timed region and times one installation
    // with direct counter reads; the median over the repeats is the artifact.
    let mut per_clause: Vec<f64> = Vec::new();
    let mut per_node: Vec<f64> = Vec::new();
    for _ in 0..17 {
        let (space, options) = add_inputs(arena, &symbols, &terms, &precedence, &predicates, a);
        let context = InferenceContext {
            terms: &terms,
            symbols: &symbols,
            substitution: &space.substitution,
            precedence: &precedence,
            ordering: OrderingKind::Kbo,
        };
        let declaration = InductionDeclaration {
            zero,
            succ,
            skolem,
            well_founded: None,
        };
        let begin = harness::cycle_counter();
        let stats = add_induction_schemes(
            &space,
            &context,
            &options,
            &declaration,
            kMaxInductionAttempts,
            kInductionScanNodeBudget,
        )
        .expect("schemes");
        let end = harness::cycle_counter();
        assert_eq!(stats.structural_schemes, 16);
        per_clause.push((end - begin) as f64 / 16.0);
        per_node.push((end - begin) as f64 / stats.nodes_visited as f64);
    }
    per_clause.sort_by(|x, y| x.partial_cmp(y).expect("nan"));
    per_node.sort_by(|x, y| x.partial_cmp(y).expect("nan"));
    let clause_median = per_clause[per_clause.len() / 2];
    let clause_min = per_clause[0];
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0036",
        name: "induction_scheme_install",
        iterations: 1,
        cycles_median: clause_median,
        cycles_min: clause_min,
    });
    println!(
        "induction_scheme_install: {:.2} cycles median per scheme clause (min {:.2})",
        clause_median, clause_min
    );
    let node_median = per_node[per_node.len() / 2];
    let node_min = per_node[0];
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0036",
        name: "induction_scan_node",
        iterations: 1,
        cycles_median: node_median,
        cycles_min: node_min,
    });
    println!(
        "induction_scan_node: {:.2} cycles median per node (min {:.2})",
        node_median, node_min
    );

    // Measurement 3: cycles per pure scheme-clause build (the builder functions
    // alone, hash-consed warm; the interning and staging costs above are the
    // installation's, this isolates the literal assembly).
    let build_predicate = predicates[0];
    let declaration = InductionDeclaration {
        zero,
        succ,
        skolem,
        well_founded: None,
    };
    let (build_median, build_min) = measure_cycles(200_000, |_| {
        let (_literals, count) = mapt::hot::induction::scheme::structural_scheme_literals(
            &terms,
            &symbols,
            build_predicate,
            &declaration,
            0,
        )
        .expect("build");
        count as u64
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0036",
        name: "induction_scheme_build",
        iterations: 200_000,
        cycles_median: build_median,
        cycles_min: build_min,
    });
    println!(
        "induction_scheme_build: {:.2} cycles median (min {:.2})",
        build_median, build_min
    );
}
