// CEP:FILE: benches/hot/unify_bench.rs
// CEP:WHAT: Unification benchmark (bench CEP-BENCH-0006): cycles per ground-identical unification, per one-binding unification, per failed occurs check, and per successful match.
// CEP:WHY: CEP&CC Law 4 and design 8.2: unification is OPT-0 and called millions of times per second by every inference rule; its CEP:COST and CEP:OPTIMAL fields cite this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/unify_*.json.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::SymbolTable;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::unification::substitution::Substitution;
use mapt::hot::unification::unify::{match_terms, unify};

// CEP:WHAT: Fixture arena bytes (term hash table plus data).
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kUnifyBenchArenaBytes: u32 = 16_777_216;

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
// CEP:EVIDENCE: benches/artifacts/unify_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(kUnifyBenchArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    let sort = mapt::hot::ir::symbol_table::SortId(builder.declare_sort("S").expect("sort"));
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
    let substitution = Substitution::new(arena);

    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let h = symbol_id(&builder, "h");
    let f = symbol_id(&builder, "f");
    let ground_pair_left = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let ground_pair_right = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let bind_left = terms.intern_fun(&symbols, h, &[x, b]).expect("h(x, b)");
    let bind_right = terms.intern_fun(&symbols, h, &[a, y]).expect("h(a, y)");
    let fx = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");

    // Ground-identical unification (hash-consing fast path).
    let (ground_median, ground_min) = measure_cycles(1_000_000, |_| {
        let outcome = unify(&terms, &substitution, ground_pair_left, ground_pair_right);
        match outcome {
            Ok(true) => 1,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0006",
        name: "unify_ground_identical",
        iterations: 1_000_000,
        cycles_median: ground_median,
        cycles_min: ground_min,
    });
    println!(
        "unify_ground_identical: median {:.2} cycles/op, min {:.2} cycles/op",
        ground_median, ground_min
    );

    // One-binding-per-side unification (h(x, b) vs h(a, y)) with undo per iteration.
    let (bind_median, bind_min) = measure_cycles(200_000, |_| {
        let entry = substitution.trail_depth();
        let outcome = unify(&terms, &substitution, bind_left, bind_right);
        substitution.undo_to(entry);
        match outcome {
            Ok(true) => 1,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0006",
        name: "unify_bind_pair",
        iterations: 200_000,
        cycles_median: bind_median,
        cycles_min: bind_min,
    });
    println!(
        "unify_bind_pair: median {:.2} cycles/op, min {:.2} cycles/op",
        bind_median, bind_min
    );

    // Failed occurs check (x vs f(x)) with the trail unwind included.
    let (occurs_median, occurs_min) =
        measure_cycles(200_000, |_| match unify(&terms, &substitution, x, fx) {
            Ok(false) => 1,
            _ => 0,
        });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0006",
        name: "unify_occurs_reject",
        iterations: 200_000,
        cycles_median: occurs_median,
        cycles_min: occurs_min,
    });
    println!(
        "unify_occurs_reject: median {:.2} cycles/op, min {:.2} cycles/op",
        occurs_median, occurs_min
    );

    // Successful match (f(x) onto f(a)) with witness and undo.
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let (match_median, match_min) = measure_cycles(200_000, |_| {
        let entry = substitution.trail_depth();
        let outcome = match_terms(&terms, &symbols, &substitution, fx, fa);
        substitution.undo_to(entry);
        match outcome {
            Ok(true) => 1,
            _ => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0006",
        name: "match_witness_success",
        iterations: 200_000,
        cycles_median: match_median,
        cycles_min: match_min,
    });
    println!(
        "match_witness_success: median {:.2} cycles/op, min {:.2} cycles/op",
        match_median, match_min
    );
}
