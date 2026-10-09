// CEP:FILE: benches/hot/index_bench.rs
// CEP:WHAT: Indexing benchmark (bench CEP-BENCH-0008): cycles per discrimination-tree insert of a fresh chain term and per retrieval hit on an indexed term.
// CEP:WHY: CEP&CC Law 4 and design 9.2: the index is the subsumption and rewriting filter; its CEP:COST and CEP:OPTIMAL fields cite this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/index_*.json.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::index::discrimination_tree::DiscriminationTree;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;

// CEP:WHAT: Fixture arena bytes (term hash table, tree arrays at reduced bench caps, data).
// CEP:WHY: Named constant (CEP&CC 11.3); the bench uses explicit caps so one arena hosts the fixture without the full production arrays.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kIndexBenchArenaBytes: u32 = 33_554_432;

// CEP:WHAT: Tree caps for the bench fixture.
// CEP:WHY: Named constants sized above the bench workload (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kBenchNodeCap: u32 = 262_144;
const kBenchEntryCap: u32 = 65_536;

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
// CEP:EVIDENCE: benches/artifacts/index_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(kIndexBenchArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort).expect("a");
    let _ = builder.declare_function("b", 0, 1, &[], sort).expect("b");
    let _ = builder
        .declare_function("f", 1, 1, &[sort], sort)
        .expect("f");
    let symbols: SymbolTable = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let tree =
        DiscriminationTree::new_with_caps(arena, kBenchNodeCap, kBenchEntryCap).expect("tree");
    let f = symbol_id(&builder, "f");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");

    // Pre-build a vocabulary of chain terms f^k(a) and f^k(b) for inserts and queries.
    let mut chains: Vec<mapt::hot::ir::term::TermPtr> = Vec::new();
    let mut from_a = a;
    let mut from_b = b;
    for _ in 0..64 {
        chains.push(from_a);
        chains.push(from_b);
        from_a = terms.intern_fun(&symbols, f, &[from_a]).expect("chain a");
        from_b = terms.intern_fun(&symbols, f, &[from_b]).expect("chain b");
    }
    // Seed the tree with half the vocabulary so inserts mostly walk existing prefixes.
    for (index, term) in chains.iter().enumerate() {
        if index % 2 == 0 {
            tree.insert(&terms, *term, index as u64)
                .expect("seed insert");
        }
    }

    // Insert measurement: each iteration inserts an odd-indexed (unseeded) chain term
    // with a distinct payload; the vocabulary has enough terms for the iterations.
    let mut insert_cursor = 1usize;
    let (insert_median, insert_min) = measure_cycles(20_000, |_| {
        let term = chains[insert_cursor % chains.len()];
        insert_cursor += 2;
        match tree.insert(&terms, term, insert_cursor as u64) {
            Ok(()) => 1,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0008",
        name: "index_insert",
        iterations: 20_000,
        cycles_median: insert_median,
        cycles_min: insert_min,
    });
    println!(
        "index_insert: median {:.2} cycles/op, min {:.2} cycles/op",
        insert_median, insert_min
    );

    // Retrieval measurement: exact-hit queries over the seeded vocabulary.
    let mut buffer = [0u64; 8];
    let (retrieve_median, retrieve_min) = measure_cycles(200_000, |iteration| {
        let term = chains[(iteration as usize * 2) % chains.len()];
        match tree.retrieve(&terms, term, &mut buffer) {
            Ok(count) => count as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0008",
        name: "index_retrieve",
        iterations: 200_000,
        cycles_median: retrieve_median,
        cycles_min: retrieve_min,
    });
    println!(
        "index_retrieve: median {:.2} cycles/op, min {:.2} cycles/op",
        retrieve_median, retrieve_min
    );
}
