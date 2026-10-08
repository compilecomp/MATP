// CEP:FILE: benches/hot/clause_bench.rs
// CEP:WHAT: Clause construction benchmark (bench CEP-BENCH-0003): cycles per new_clause call for a three-literal clause.
// CEP:WHY: CEP&CC Law 4: clause construction is CEP-0 and its CEP:COST field cites this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/clause_new_3lit.json.
// CEP:SECURITY: none.

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::clause::{ClauseStore, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt_config::limits::{kInvalidClauseId, kInvalidSubstitutionOffset};

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/clause_new_3lit.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(67_108_864).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let a_id = builder.declare_function("a", 0, 1, &[], sort).expect("a");
    let b_id = builder.declare_function("b", 0, 1, &[], sort).expect("b");
    let p_id = builder.declare_predicate("p", 1, 1, &[sort]).expect("p");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("store");
    let clauses = ClauseStore::new(arena);
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let b = terms.intern_fun(&symbols, b_id, &[]).expect("b");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(&symbols, p_id, &[b]).expect("p(b)");
    let literals = [
        Literal::new(pa, true),
        Literal::new(pb, false),
        Literal::new(pa, false),
    ];
    let derivation = DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; 4],
        substitution: kInvalidSubstitutionOffset,
    };
    let (median, minimum) = measure_cycles(200_000, |_| {
        match clauses.new_clause(&terms, &literals, 0, derivation) {
            Ok(ptr) => ptr.as_u32() as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0003",
        name: "clause_new_3lit",
        iterations: 200_000,
        cycles_median: median,
        cycles_min: minimum,
    });
    println!(
        "clause_new_3lit: median {:.2} cycles/op, min {:.2} cycles/op",
        median, minimum
    );
}
