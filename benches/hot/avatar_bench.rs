// CEP:FILE: benches/hot/avatar_bench.rs
// CEP:WHAT: AVATAR benchmark (bench CEP-BENCH-0031/0032): cycles per split decision on the two-component clause shape and per component interning (canonicalize + hash + compare).
// CEP:WHY: CEP&CC Law 4 and 13: the splitter and the component table are Phase 4 hot-path structures; their per-operation cycle cost must be measured with stored artifacts (compiler, flags, target, input, cycles, date).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on counter unavailability or fixture failure (bench tooling may fail loudly).
// CEP:ASSUMES: single-threaded, otherwise idle machine (measurement evidence, not a synchronization contract).
// CEP:COST: offline; measurement loops dominate.
// CEP:EVIDENCE: produces benches/artifacts/{avatar_split_step,avatar_intern_step}.json consumed by CEP:COST fields in hot/avatar and by scripts/bench_gate.py.
// CEP:SECURITY: no untrusted input; writes only into the repository artifacts directory.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::avatar::component::{canonical_component_words, ComponentTable};
use mapt::hot::avatar::splitter::{try_split, SplitDecision};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::unification::substitution::Substitution;

// CEP:WHAT: Arena bytes for the bench fixture.
// CEP:WHY: Named fixture bound: the component table's small injected capacities plus the term table.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: covers the fixture.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 12_582_912;

// CEP:WHAT: Builds the bench fixture: arena, symbols, terms, precedence.
// CEP:WHY: One constructor; the clause shape matches the splitter's core case (two variable-disjoint 2-literal components).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn make_fixture() -> (
    &'static Arena,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    SymbolTableBuilder,
    TermStore<'static>,
    PrecedenceTable<'static>,
    Substitution<'static>,
) {
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b"].iter() {
        let _ = builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("constant");
    }
    for name in ["p", "q"].iter() {
        let _ = builder
            .declare_predicate(name, 2, 1, &[sort_s, sort_s])
            .expect("predicate");
    }
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = TermStore::new(arena).expect("terms");
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let substitution = Substitution::new(arena);
    (arena, symbols, builder, terms, precedence, substitution)
}

// CEP:WHAT: Bench entry point.
// CEP:WHY: The harness=false bench runs main directly (CEP&CC 10.2: the entry point carries its block like any nontrivial function).
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture or counter failure (bench tooling may fail loudly).
// CEP:ASSUMES: idle machine.
// CEP:COST: the measurement loops.
// CEP:EVIDENCE: the artifacts written below.
// CEP:SECURITY: none.
fn main() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &_substitution,
        precedence: &_precedence,
        ordering: OrderingKind::Kbo,
    };
    let _ = context;
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = terms
        .intern_fun(&symbols, symbol_id_of(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id_of(&builder, "b"), &[])
        .expect("b");
    let p_id = symbol_id_of(&builder, "p");
    let q_id = symbol_id_of(&builder, "q");
    let lit = |symbol: u32, left, right, positive| -> Literal {
        Literal::new(
            terms
                .intern_pred(&symbols, symbol, &[left, right])
                .expect("atom"),
            positive,
        )
    };
    let clause = [
        lit(p_id, x, a, true),
        lit(p_id, x, b, true),
        lit(q_id, y, a, true),
        lit(q_id, y, b, true),
    ];
    // The fixture must split (the bench's precondition).
    assert!(matches!(
        try_split(&terms, &clause),
        SplitDecision::Splittable(_)
    ));

    // CEP-BENCH-0031: cycles per split decision.
    let (median, minimum) = measure_cycles(1024, |_| match try_split(&terms, &clause) {
        SplitDecision::Splittable(_) => 1,
        SplitDecision::Unsplittable => 0,
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0031",
        name: "avatar_split_step",
        iterations: 1024,
        cycles_median: median,
        cycles_min: minimum,
    });

    // CEP-BENCH-0032: cycles per component interning (canonicalize + hash + probe).
    let table = ComponentTable::new_with(arena, 64, 512).expect("table");
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let (median, minimum) = measure_cycles(1024, |iteration| {
        let component = [
            lit(p_id, x, if iteration % 2 == 0 { a } else { b }, true),
            lit(p_id, x, if iteration % 2 == 0 { b } else { a }, true),
        ];
        let count = canonical_component_words(&component, &mut words);
        match table.intern(&words[..count], 1) {
            Ok(_) => 1,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0032",
        name: "avatar_intern_step",
        iterations: 1024,
        cycles_median: median,
        cycles_min: minimum,
    });
    println!("avatar bench complete");
}

// CEP:WHAT: Looks up a fixture symbol id by name.
// CEP:WHY: Readable fixtures (the bench cannot import the test common module).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the symbol is missing.
// CEP:ASSUMES: fixture builder.
// CEP:COST: linear scan.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn symbol_id_of(builder: &SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("bench symbol {} not found", name);
}
