// CEP:FILE: benches/hot/substitution_bench.rs
// CEP:WHAT: Substitution engine benchmark (bench CEP-BENCH-0004): cycles per lookup and per application on a small term.
// CEP:WHY: CEP&CC Law 4: lookup is the OPT-0 path cited in CEP:COST; application covers the rebuild-and-reintern path.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/substitution_*.json.
// CEP:SECURITY: none.

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::unification::substitution::Substitution;

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/substitution_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(67_108_864).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let a_id = builder.declare_function("a", 0, 1, &[], sort).expect("a");
    let f_id = builder
        .declare_function("f", 1, 1, &[sort], sort)
        .expect("f");
    let h_id = builder
        .declare_function("h", 2, 1, &[sort, sort], sort)
        .expect("h");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("store");
    let substitution = Substitution::new(arena);
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let var = terms.intern_var(0).expect("V0");
    let f_var = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V0)");
    let h_term = terms
        .intern_fun(&symbols, h_id, &[f_var, var])
        .expect("h(f(V0),V0)");
    substitution.bind(0, a).expect("bind V0 -> a");
    let (lookup_median, lookup_min) = measure_cycles(1_000_000, |iteration| {
        let variable = iteration % 64;
        match substitution.lookup(variable) {
            Ok(Some(handle)) => handle.as_u32() as u64,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0004",
        name: "substitution_lookup",
        iterations: 1_000_000,
        cycles_median: lookup_median,
        cycles_min: lookup_min,
    });
    println!(
        "substitution_lookup: median {:.2} cycles/op, min {:.2} cycles/op",
        lookup_median, lookup_min
    );
    let (apply_median, apply_min) = measure_cycles(1_000_000, |_| {
        match substitution.apply(&terms, h_term, &symbols) {
            Ok(handle) => handle.as_u32() as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0004",
        name: "substitution_apply_small",
        iterations: 1_000_000,
        cycles_median: apply_median,
        cycles_min: apply_min,
    });
    println!(
        "substitution_apply_small: median {:.2} cycles/op, min {:.2} cycles/op",
        apply_median, apply_min
    );
}
