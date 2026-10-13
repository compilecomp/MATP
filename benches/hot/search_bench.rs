// CEP:FILE: benches/hot/search_bench.rs
// CEP:WHAT: Search benchmarks (bench CEP-BENCH-0011): cycles per passive-set push/pop pair (the selection tick of the given-clause loop) and cycles per selection-flag computation over a three-literal clause.
// CEP:WHY: Design 26 Phase 3 ("Given-clause loop (bounded)") and design 8.4/15.2/15.3: the passive heap's O(log n) push/pop pair and the per-clause flag computation (maximality over KBO) are the loop's fixed per-clause costs and must carry OPT-0 evidence; the two measurements share one bench file because both are per-given-clause constants of the same loop.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly).
// CEP:ASSUMES: The cycle counter is accurate; measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/search/passive.rs (CEP:COST), hot/search/given_clause.rs (SelectionWeight, compute path), and scripts/bench_gate.py baselines atp_passive_step and atp_selection_flags.
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
use mapt::hot::search::passive::{PassiveHeap, SelectionStrategy};
use mapt::hot::unification::substitution::Substitution;

// CEP:WHAT: Arena bytes for the search bench.
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

// CEP:WHAT: Bench entry: measures the passive push/pop pair and the selection-flag computation.
// CEP:WHY: See the file header.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fresh fixtures.
// CEP:COST: see the measurements.
// CEP:EVIDENCE: the artifacts cited in the file header.
// CEP:SECURITY: none.
fn main() {
    let (arena, symbols, builder, terms, precedence, substitution) = make_fixture();

    // Passive step: a push/pop pair over a 4096-entry heap (the loop's selection
    // tick; the heap returns to the same state each iteration).
    let heap = PassiveHeap::new_with(arena, 4096, SelectionStrategy::AgeWeightRatio).expect("heap");
    let (passive_median, passive_min) = measure_cycles(200_000, |iteration| {
        let id = (iteration % 4096) as u64;
        if heap
            .push(id, (id % 1024) as u32, id as u32, (id % 8 + 1) as u32)
            .is_err()
        {
            return 0;
        }
        match heap.pop() {
            Some(_) => 1,
            None => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0011",
        name: "atp_passive_step",
        iterations: 200_000,
        cycles_median: passive_median,
        cycles_min: passive_min,
    });
    println!(
        "atp_passive_step: median {:.2} cycles/op, min {:.2} cycles/op",
        passive_median, passive_min
    );

    // Selection flags: compute_selection_flags over a fixed three-literal clause
    // (two comparable predicate atoms plus a proposition) - the per-clause
    // maximality cost paid once per stored clause.
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let x = terms.intern_var(0).expect("x");
    let p_f_a = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[f_a])
        .expect("p(f(a))");
    let p_x = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[x])
        .expect("p(x)");
    let r = terms
        .intern_pred(&symbols, symbol_id(&builder, "r"), &[])
        .expect("r");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let mut literals = [
        Literal::new(p_x, true),
        Literal::new(p_f_a, true),
        Literal::new(r, false),
    ];
    let (flags_median, flags_min) = measure_cycles(100_000, |_| {
        match compute_selection_flags(&context, SelectionFunction::None, &mut literals) {
            Ok(_) => 1,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0011",
        name: "atp_selection_flags",
        iterations: 100_000,
        cycles_median: flags_median,
        cycles_min: flags_min,
    });
    println!(
        "atp_selection_flags: median {:.2} cycles/op, min {:.2} cycles/op",
        flags_median, flags_min
    );
}
