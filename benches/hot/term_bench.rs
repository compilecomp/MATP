// CEP:FILE: benches/hot/term_bench.rs
// CEP:WHAT: Term store benchmark (bench CEP-BENCH-0002): cycles per symbol-table lookup and per intern of a binary term.
// CEP:WHY: CEP&CC Law 4: interning and symbol lookup are CEP-0 hot paths cited in CEP:COST fields; measurement is median-of-repeats.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/term_*.json.
// CEP:SECURITY: none.

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/term_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(67_108_864).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let a_id = builder.declare_function("a", 0, 1, &[], sort).expect("a");
    let h_id = builder
        .declare_function("h", 2, 1, &[sort, sort], sort)
        .expect("h");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("store");
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let (lookup_median, lookup_min) = measure_cycles(1_000_000, |iteration| {
        let id = if iteration % 2 == 0 { a_id } else { h_id };
        match symbols.info(id) {
            Ok(info) => info.weight as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0002",
        name: "term_symbol_lookup",
        iterations: 1_000_000,
        cycles_median: lookup_median,
        cycles_min: lookup_min,
    });
    println!(
        "term_symbol_lookup: median {:.2} cycles/op, min {:.2} cycles/op",
        lookup_median, lookup_min
    );
    // Interning h(a, a) repeatedly: the term is already canonical after the first call, so the
    // steady-state measurement is the probe-hit path (the common case in search).
    let (intern_median, intern_min) = measure_cycles(1_000_000, |_| {
        match terms.intern_fun(&symbols, h_id, &[a, a]) {
            Ok(handle) => handle.as_u32() as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0002",
        name: "term_intern_binary_hit",
        iterations: 1_000_000,
        cycles_median: intern_median,
        cycles_min: intern_min,
    });
    println!(
        "term_intern_binary_hit: median {:.2} cycles/op, min {:.2} cycles/op",
        intern_median, intern_min
    );
}
