// CEP:FILE: benches/hot/ordering_bench.rs
// CEP:WHAT: Ordering benchmark (bench CEP-BENCH-0007): cycles per KBO comparison on weight-differing ground pairs, on weight-equal lexicographic pairs, and per LPO comparison on nested ground pairs.
// CEP:WHY: CEP&CC Law 4 and design 8.3: ordering comparison is on the hot path of every superposition and resolution side condition and must be OPT-0; its CEP:COST and CEP:OPTIMAL fields cite this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/ordering_*.json.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::ordering::{compare_kbo, compare_lpo};

// CEP:WHAT: Fixture arena bytes (term hash table plus data).
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kOrderingBenchArenaBytes: u32 = 16_777_216;

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable bench setup.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/ordering_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(kOrderingBenchArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort).expect("a");
    let _ = builder.declare_function("b", 0, 1, &[], sort).expect("b");
    let _ = builder
        .declare_function("f", 1, 1, &[sort], sort)
        .expect("f");
    let _ = builder
        .declare_function("h", 2, 1, &[sort, sort], sort)
        .expect("h");
    let symbols: SymbolTable = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");

    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f = symbol_id(&builder, "f");
    let h = symbol_id(&builder, "h");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let ffa = terms.intern_fun(&symbols, f, &[fa]).expect("f(f(a))");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let hba = terms.intern_fun(&symbols, h, &[b, a]).expect("h(b, a)");

    // KBO weight-dominance fast path: f(f(a)) vs f(a) decides on cached header weights.
    let (weight_median, weight_min) = measure_cycles(1_000_000, |_| {
        match compare_kbo(&terms, &precedence, ffa, fa) {
            Ok(mapt::hot::ordering::OrderingComparison::Greater) => 1,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0007",
        name: "ordering_kbo_weight",
        iterations: 1_000_000,
        cycles_median: weight_median,
        cycles_min: weight_min,
    });
    println!(
        "ordering_kbo_weight: median {:.2} cycles/op, min {:.2} cycles/op",
        weight_median, weight_min
    );

    // KBO equal-weight lexicographic path: h(a, b) vs h(b, a) recurses into children.
    let (lex_median, lex_min) = measure_cycles(1_000_000, |_| {
        match compare_kbo(&terms, &precedence, hab, hba) {
            Ok(_) => 1,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0007",
        name: "ordering_kbo_lex",
        iterations: 1_000_000,
        cycles_median: lex_median,
        cycles_min: lex_min,
    });
    println!(
        "ordering_kbo_lex: median {:.2} cycles/op, min {:.2} cycles/op",
        lex_median, lex_min
    );

    // LPO nested ground comparison: f(f(a)) vs f(a) through the subterm case.
    let (lpo_median, lpo_min) = measure_cycles(500_000, |_| {
        match compare_lpo(&terms, &precedence, ffa, fa) {
            Ok(mapt::hot::ordering::OrderingComparison::Greater) => 1,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0007",
        name: "ordering_lpo",
        iterations: 500_000,
        cycles_median: lpo_median,
        cycles_min: lpo_min,
    });
    println!(
        "ordering_lpo: median {:.2} cycles/op, min {:.2} cycles/op",
        lpo_median, lpo_min
    );
}
