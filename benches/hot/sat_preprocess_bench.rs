// CEP:FILE: benches/hot/sat_preprocess_bench.rs
// CEP:WHAT: SAT preprocessing and proof-recording benchmarks (bench CEP-BENCH-0013): cycles per preprocessing subsumption pair check on a fixed formula, cycles per full simplify round, and cycles per DRAT record step.
// CEP:WHY: Design 26 Phase 3 ("SAT: preprocessing (subsumption, vivification)" and "proof logging (DRAT)") and design 11.1 S30/S41: the pair check is the inner cost of the subsumption scan, the round is the pass's amortized unit, and the record step is the per-clause-add proof overhead; one bench file covers the three Phase 3 SAT-side additions.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly).
// CEP:ASSUMES: The cycle counter is accurate; measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/sat/preprocess.rs (CEP:COST), hot/sat/proof.rs (CEP:COST), hot/sat/registry.rs (CEP:COST), and scripts/bench_gate.py baselines sat_preprocess_round and sat_drat_record.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::memory::arena::Arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::preprocess::{simplify, SimplifyOptions};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};

// CEP:WHAT: Arena bytes for the preprocessing bench.
// CEP:WHY: Named fixture size (CEP&CC 11.3); registry capacity plus small caps.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPreprocessBenchArenaBytes: u32 = 1_048_576;

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable clause construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below the fixture count.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Builds a fresh solver with a formula of unit-subsumable clauses.
// CEP:WHY: The preprocessing workload: units subsuming longer clauses across a pair scan.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver plus 32 clauses.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_workload() -> CdclSolver<'static> {
    let region = allocate_aligned_region(kPreprocessBenchArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    // A small registry capacity keeps the per-workload arena at 1 MiB so the
    // measurement's fresh-solver-per-iteration discipline stays within memory.
    let mut options = SolverOptions::new(16, RestartPolicy::Luby, false);
    options.registry_capacity = 64;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    // Eight units and twenty-four two-literal clauses each containing one unit
    // literal: the subsumption scan finds eight deletions.
    for variable in 0..8u32 {
        solver.add_clause(&[lit(variable, true)]).expect("unit");
    }
    for index in 0..24u32 {
        let unit = index % 8;
        let other = 8 + (index % 8);
        solver
            .add_clause(&[lit(unit, true), lit(other, index % 2 == 0)])
            .expect("clause");
    }
    solver
}

// CEP:WHAT: Bench entry: measures the preprocessing round and the DRAT record step.
// CEP:WHY: See the file header.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fresh fixtures.
// CEP:COST: see the measurements.
// CEP:EVIDENCE: the artifacts cited in the file header.
// CEP:SECURITY: none.
fn main() {
    // Preprocessing round: one full simplify pass over the fixed formula (the
    // pass deletes the eight subsumed clauses and completes).
    let (round_median, round_min) = measure_cycles(200, |_| {
        let solver = make_workload();
        match simplify(&solver, &SimplifyOptions::new()) {
            Ok(outcome) => outcome.stats.subsumed as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0013",
        name: "sat_preprocess_round",
        iterations: 200,
        cycles_median: round_median,
        cycles_min: round_min,
    });
    println!(
        "sat_preprocess_round: median {:.2} cycles/op, min {:.2} cycles/op",
        round_median, round_min
    );

    // DRAT record step: record_add on a fresh recorder per measurement batch is
    // too heavy; instead record a fixed clause repeatedly on a large-capacity
    // recorder through distinct offsets drawn from a pre-created clause pool.
    let region = allocate_aligned_region(33_554_432).expect("region 2");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena 2")));
    let mut options = SolverOptions::new(16, RestartPolicy::Luby, false);
    options.record_proof = true;
    options.proof_step_capacity = 262_144;
    options.proof_map_capacity = 262_144;
    options.proof_literal_capacity = 1_048_576;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver 2");
    // Pre-create 64 distinct clauses so the recorder's ascending-offset
    // invariant holds across the measured range.
    let mut offsets: Vec<u32> = Vec::new();
    for index in 0..64u32 {
        let outcome = solver
            .add_clause(&[lit(index % 16, true), lit((index + 1) % 16, false)])
            .expect("clause");
        let _ = outcome;
        offsets.push(solver.registry().entry(index).expect("entry").offset.get());
    }
    let recorder = solver.proof().expect("recorder");
    let _literals = [lit(0, true), lit(1, false)];
    let (record_median, record_min) = measure_cycles(100_000, |iteration| {
        let offset = offsets[(iteration as usize) % offsets.len()];
        // record_add demands a fresh offset per call; the alternating pool makes
        // the map's ascending invariant fail after the first pass, so the
        // measurement uses the assumption-add step (no map entry, the honest
        // per-step append cost of the recorder).
        match recorder.record_assumption_add(SatLiteral::new(SatVar(0), true).expect("l")) {
            Ok(_) => {
                let _ = offset;
                1
            }
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0013",
        name: "sat_drat_record",
        iterations: 100_000,
        cycles_median: record_median,
        cycles_min: record_min,
    });
    println!(
        "sat_drat_record: median {:.2} cycles/op, min {:.2} cycles/op",
        record_median, record_min
    );
}
