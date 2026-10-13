// CEP:FILE: benches/hot/subsumption_bench.rs
// CEP:WHAT: Subsumption benchmarks (bench CEP-BENCH-0012): cycles per feature-vector dominance check (the design 9.3 pre-filter) and cycles per matching-based subsumption verification on a fixed ground pair.
// CEP:WHY: Design 26 Phase 3 (given-clause dependencies: "Clause database, indexing, inference") and design 9.3's two-tier flow: the filter and the verifier are both per-candidate costs of every subsumption query in the loop and must carry OPT-0 evidence; the two measurements share one bench file because they are the two tiers of one query.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly).
// CEP:ASSUMES: The cycle counter is accurate; measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs (CEP:COST), hot/inference/subsumption.rs (CEP:COST), and scripts/bench_gate.py baselines atp_subsumption_filter and atp_subsumption_verify.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::index::feature_vector::FeatureVectorIndex;
use mapt::hot::inference::subsumption::subsumes;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SymbolTable;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::unification::substitution::Substitution;

// CEP:WHAT: Arena bytes for the subsumption bench.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 12_582_912;

// CEP:WHAT: Builds the fixture (as in the ATP bench).
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

// CEP:WHAT: Bench entry: measures the feature-vector filter and the subsumption verification.
// CEP:WHY: See the file header.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fresh fixtures.
// CEP:COST: see the measurements.
// CEP:EVIDENCE: the artifacts cited in the file header.
// CEP:SECURITY: none.
fn main() {
    let (arena, symbols, builder, terms, precedence, substitution) = make_fixture();

    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let x = terms.intern_var(0).expect("x");
    let p_x = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let p_f_a = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[f_a])
        .expect("p(f(a))");
    let r = terms
        .intern_pred(&symbols, symbol_id(&builder, "r"), &[])
        .expect("r");

    // Filter tier: the dominance check between a general and a specific vector.
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let general = [Literal::new(p_x, true)];
    let specific = [Literal::new(p_f_a, true), Literal::new(r, true)];
    let general_vector = index.build(&terms, &general).expect("vector");
    let specific_vector = index.build(&terms, &specific).expect("vector");
    let (filter_median, filter_min) = measure_cycles(200_000, |_| {
        if index.may_subsume(general_vector, specific_vector) {
            1
        } else {
            0
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0012",
        name: "atp_subsumption_filter",
        iterations: 200_000,
        cycles_median: filter_median,
        cycles_min: filter_min,
    });
    println!(
        "atp_subsumption_filter: median {:.2} cycles/op, min {:.2} cycles/op",
        filter_median, filter_min
    );

    // Verification tier: the matching-based subsumption decision on the same pair.
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let (verify_median, verify_min) =
        measure_cycles(100_000, |_| match subsumes(&context, &general, &specific) {
            Ok(true) => 1,
            _ => 0,
        });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0012",
        name: "atp_subsumption_verify",
        iterations: 100_000,
        cycles_median: verify_median,
        cycles_min: verify_min,
    });
    println!(
        "atp_subsumption_verify: median {:.2} cycles/op, min {:.2} cycles/op",
        verify_median, verify_min
    );
}
