// CEP:FILE: benches/hot/concurrency_bench.rs
// CEP:WHAT: Concurrency benchmark (bench CEP-BENCH-0033/0034/0035): cycles per Chase-Lev owner push+pop pair and per steal, per MPMC enqueue+dequeue pair, and per portable clause codec roundtrip.
// CEP:WHY: CEP&CC Law 4 and 13: the lock-free structures and the codec are Phase 4 hot-path components; their per-operation cycle cost must be measured with stored artifacts.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on counter unavailability or fixture failure (bench tooling may fail loudly).
// CEP:ASSUMES: single-threaded, otherwise idle machine (the steal/pop measurements exercise the uncontended protocol; contention costs are scheduling-dependent and out of scope for cycle evidence).
// CEP:COST: offline; measurement loops dominate.
// CEP:EVIDENCE: produces benches/artifacts/{deque_push_pop,deque_steal,mpmc_enqueue_dequeue,codec_roundtrip}.json consumed by CEP:COST fields in hot/concurrency and by scripts/bench_gate.py.
// CEP:SECURITY: no untrusted input; writes only into the repository artifacts directory.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use std::sync::atomic::{AtomicI64, AtomicU64};

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::concurrency::chase_lev::WorkStealingDeque;
use mapt::hot::concurrency::clause_codec::{decode_clause, encode_clause};
use mapt::hot::concurrency::mpmc_pool::SharingPool;
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;

// CEP:WHAT: Arena bytes for the codec bench fixture.
// CEP:WHY: Named fixture bound (the term table).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: covers the fixture.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 12_582_912;

// CEP:WHAT: Bench entry point.
// CEP:WHY: The harness=false bench runs main directly (CEP&CC 10.2: the entry point carries its block like any nontrivial function).
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture or counter failure (bench tooling may fail loudly).
// CEP:ASSUMES: idle machine.
// CEP:COST: the measurement loops.
// CEP:EVIDENCE: the artifacts written below.
// CEP:SECURITY: none.
fn main() {
    // ---- Chase-Lev deque (CEP-BENCH-0033) ----
    let cells = 8192usize;
    let buffer: &'static [AtomicU64] = Box::leak(
        (0..cells)
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let top: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let bottom: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let deque = WorkStealingDeque::new(buffer, top, bottom).expect("deque");
    let (median, minimum) = measure_cycles(1024, |iteration| {
        let mut sink: u64 = 0;
        for _ in 0..64 {
            if deque.push(iteration as u64).is_ok() {
                if let Ok(Some(value)) = deque.pop() {
                    sink = sink.wrapping_add(value);
                }
            }
        }
        sink
    });
    let (per_op_median, per_op_min) = (median / 128.0, minimum / 128.0);
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0033",
        name: "deque_push_pop",
        iterations: 1024,
        cycles_median: per_op_median,
        cycles_min: per_op_min,
    });
    // Steal side: fill, then steal everything (uncontended - the protocol cost).
    let (median, minimum) = measure_cycles(256, |iteration| {
        let mut sink: u64 = 0;
        for index in 0..64u64 {
            let _ = deque.push(index);
        }
        while let Ok(Some(value)) = deque.steal() {
            sink = sink.wrapping_add(value);
        }
        let _ = deque.pop();
        sink.wrapping_add(iteration as u64)
    });
    let (steal_median, steal_min) = (median / 64.0, minimum / 64.0);
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0033",
        name: "deque_steal",
        iterations: 256,
        cycles_median: steal_median,
        cycles_min: steal_min,
    });

    // ---- MPMC pool (CEP-BENCH-0034) ----
    let pool_cells = 1024usize;
    let sequences: &'static [AtomicI64] = Box::leak(
        (0..pool_cells)
            .map(|index| AtomicI64::new(index as i64))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let words: &'static [AtomicU64] = Box::leak(
        (0..(pool_cells * mapt_config::limits::kSharedClauseMaxWords))
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let produce: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let consume: &'static AtomicI64 = Box::leak(Box::new(AtomicI64::new(0)));
    let pool = SharingPool::new(sequences, words, produce, consume).expect("pool");
    let record: Vec<u64> = {
        let mut record = vec![0u64; mapt_config::limits::kSharedClauseMaxWords];
        record[0] = 8;
        record[1] = 1;
        record
    };
    let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let (median, minimum) = measure_cycles(1024, |iteration| {
        let mut sink: u64 = 0;
        for _ in 0..16 {
            if pool.enqueue(&record).is_ok() {
                if let Ok(Some(length)) = pool.dequeue(&mut out) {
                    sink = sink.wrapping_add(length as u64 + out[1]);
                }
            }
        }
        sink.wrapping_add(iteration as u64)
    });
    let (enq_median, enq_min) = (median / 32.0, minimum / 32.0);
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0034",
        name: "mpmc_enqueue_dequeue",
        iterations: 1024,
        cycles_median: enq_median,
        cycles_min: enq_min,
    });

    // ---- Portable clause codec (CEP-BENCH-0035) ----
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _ = builder.declare_function("b", 0, 1, &[], sort_s).expect("b");
    let _ = builder
        .declare_predicate("p", 2, 1, &[sort_s, sort_s])
        .expect("p");
    let _ = builder
        .declare_predicate("q", 2, 1, &[sort_s, sort_s])
        .expect("q");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = TermStore::new(arena).expect("terms");
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
    let literals = [
        Literal::new(
            terms.intern_pred(&symbols, p_id, &[x, a]).expect("atom"),
            true,
        ),
        Literal::new(
            terms.intern_pred(&symbols, p_id, &[x, b]).expect("atom"),
            true,
        ),
        Literal::new(
            terms.intern_pred(&symbols, q_id, &[y, a]).expect("atom"),
            false,
        ),
        Literal::new(
            terms.intern_pred(&symbols, q_id, &[y, b]).expect("atom"),
            false,
        ),
    ];
    let mut encoded: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    let (median, minimum) = measure_cycles(1024, |iteration| {
        let mut sink: u64 = 0;
        for _ in 0..16 {
            if let Ok(length) = encode_clause(&terms, &literals, &mut encoded) {
                if let Ok(count) = decode_clause(&encoded[..length], &terms, &symbols, &mut decoded)
                {
                    sink = sink.wrapping_add(length as u64 + count as u64);
                }
            }
        }
        sink.wrapping_add(iteration as u64)
    });
    let (codec_median, codec_min) = (median / 32.0, minimum / 32.0);
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0035",
        name: "codec_roundtrip",
        iterations: 1024,
        cycles_median: codec_median,
        cycles_min: codec_min,
    });
    println!("concurrency bench complete");
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
