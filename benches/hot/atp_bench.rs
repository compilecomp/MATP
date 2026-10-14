// CEP:FILE: benches/hot/atp_bench.rs
// CEP:WHAT: ATP inference benchmarks (bench CEP-BENCH-0010): cycles per resolution rule step (unify, apply, conclude on a fixed, fixture-renamed premise pair) and cycles per registry bookkeeping step (register plus activity bump).
// CEP:WHY: Design 26 Phase 3 ("Superposition + resolution + factoring") and design 10.3: resolution is the workhorse inference of the given-clause loop and must carry OPT-0 cost evidence; the registry step (S4/S24 bookkeeping on every learnt clause) is the amortized cost the Phase 3 CDCL loop adds per conflict; the same bench file carries both measurements so the ATP and SAT bookkeeping costs are comparable on one host.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly; it is not production code).
// CEP:ASSUMES: The cycle counter is accurate (harness asserts it); measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs (CEP:COST), hot/inference/builder.rs, hot/sat/registry.rs (CEP:COST), and scripts/bench_gate.py baselines atp_resolution_step and sat_registry_step.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::inference::selection::compute_selection_flags;
use mapt::hot::inference::{InferenceContext, OrderingKind, SelectionFunction};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SymbolTable;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};
use mapt::hot::unification::substitution::Substitution;

// CEP:WHAT: Arena bytes for the inference bench (term table plus small search caps).
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 12_582_912;

// CEP:WHAT: Builds the fixture: leaked arena, symbol table, term store, precedence, substitution.
// CEP:WHY: One setup for both measurements.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_fixture() -> (
    &'static Arena,
    SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    TermStore<'static>,
    PrecedenceTable<'static>,
    Substitution<'static>,
) {
    // The same standard vocabulary as the test fixtures (constants a, b; unary f,
    // g; binary h; predicates p/1, q/2, r/0), built inline so the bench is
    // self-contained.
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    let sort_s = mapt::hot::ir::symbol_table::SortId(builder.declare_sort("S").expect("S"));
    let sort_t = mapt::hot::ir::symbol_table::SortId(builder.declare_sort("T").expect("T"));
    for name in ["a", "b"] {
        builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("c");
    }
    builder
        .declare_function("f", 1, 1, &[sort_s], sort_s)
        .expect("f");
    builder
        .declare_function("g", 1, 1, &[sort_s], sort_s)
        .expect("g");
    builder
        .declare_function("h", 2, 1, &[sort_s, sort_s], sort_s)
        .expect("h");
    builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    builder.declare_predicate("s", 1, 1, &[sort_s]).expect("s");
    builder
        .declare_predicate("q", 2, 1, &[sort_s, sort_t])
        .expect("q");
    builder.declare_predicate("r", 0, 1, &[]).expect("r");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let substitution = Substitution::new(arena);
    (arena, symbols, builder, terms, precedence, substitution)
}

// CEP:WHAT: Looks up a fixture symbol id by name.
// CEP:WHY: Readable term construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics when absent.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: O(symbols).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("symbol {} not found", name);
}

// CEP:WHAT: Bench entry: measures the resolution step and the registry step.
// CEP:WHY: The two measurements share the fixture; see the file header.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fresh fixtures.
// CEP:COST: see the measurements.
// CEP:EVIDENCE: the artifacts cited in the file header.
// CEP:SECURITY: none.
fn main() {
    let (_arena, symbols, builder, terms, precedence, substitution) = make_fixture();

    // Resolution step: premises p(x) or r and not p(f(a)) or s(f(a)); the right
    // premise is pre-renamed into the shared namespace by the fixture (the
    // generator's rename is not part of the measured rule call); each iteration
    // runs the rule step (unify, apply, conclude; flags already cached) with
    // the substitution trail rewound by the rule itself.
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let p_x = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let r = terms
        .intern_pred(&symbols, symbol_id(&builder, "r"), &[])
        .expect("r");
    let not_p_fa = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[f_a])
        .expect("p(f(a))");
    // The second right-premise literal is the non-complementary filler s(f(a))
    // (previously interned with symbol "p" under the label "q(f(a))" - hash
    // consing silently made the premise a tautology; the measured resolved
    // pair was unaffected, but the fixture now matches its comment).
    let second_p_fa = terms
        .intern_pred(&symbols, symbol_id(&builder, "s"), &[f_a])
        .expect("s(f(a))");
    let mut left = [Literal::new(p_x, true), Literal::new(r, true)];
    let mut right = [
        Literal::new(not_p_fa, false),
        Literal::new(second_p_fa, true),
    ];
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    compute_selection_flags(&context, SelectionFunction::None, &mut left).expect("flags");
    compute_selection_flags(&context, SelectionFunction::None, &mut right).expect("flags");
    let mut output = [Literal::new(mapt::hot::ir::term::TermPtr::invalid(), true); 64];
    let (resolution_median, resolution_min) =
        measure_cycles(
            100_000,
            |_| match mapt::hot::inference::resolution::resolve(
                &context,
                &left,
                0,
                &right,
                0,
                &mut output,
            ) {
                Ok(mapt::hot::inference::resolution::ResolutionOutcome::Concluded(count)) => {
                    count as u64
                }
                _ => 0,
            },
        );
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0010",
        name: "atp_resolution_step",
        iterations: 100_000,
        cycles_median: resolution_median,
        cycles_min: resolution_min,
    });
    println!(
        "atp_resolution_step: median {:.2} cycles/op, min {:.2} cycles/op",
        resolution_median, resolution_min
    );

    // Registry step: bump_activity (the per-conflict S24 bookkeeping) over a
    // CDCL solver's registry - the amortized cost the Phase 3 loop adds on top
    // of every conflict; the clause is registered once up front because the
    // ascending-offset invariant forbids re-registering one offset.
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region 2");
    let arena2 = Box::leak(Box::new(Arena::new(region).expect("arena 2")));
    let options = SolverOptions::new(16, RestartPolicy::Luby, false);
    let solver = CdclSolver::new_advanced(arena2, options).expect("solver 2");
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("clause");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    let (registry_median, registry_min) =
        measure_cycles(100_000, |_| match solver.registry().bump_activity(offset) {
            Ok(_) => 1,
            Err(_) => 0,
        });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0010",
        name: "sat_registry_step",
        iterations: 100_000,
        cycles_median: registry_median,
        cycles_min: registry_min,
    });
    println!(
        "sat_registry_step: median {:.2} cycles/op, min {:.2} cycles/op",
        registry_median, registry_min
    );
}

// CEP:WHAT: Builds a SAT literal for the registry workload.
// CEP:WHY: Readable construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below 16.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> mapt::hot::sat::literal::SatLiteral {
    mapt::hot::sat::literal::SatLiteral::new(mapt::hot::sat::literal::SatVar(variable), positive)
        .expect("literal")
}
