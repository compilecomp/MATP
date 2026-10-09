// CEP:FILE: benches/hot/cdcl_bench.rs
// CEP:WHAT: CDCL benchmark (bench CEP-BENCH-0009): cycles per conflict analysis on a fixed implication graph, cycles per VSIDS decision, and cycles per conflict of an end-to-end pigeonhole refutation.
// CEP:WHY: CEP&CC Law 4 and design 11.2: conflict analysis and decision selection are two of the three hottest paths and must be OPT-0; their CEP:COST and CEP:OPTIMAL fields cite this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/cdcl_*.json.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::memory::arena::Arena;
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::cdcl::ConflictAnalyzer;
use mapt::hot::sat::database::SatCore;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolveResult};
use mapt::hot::sat::vsids::VsidsHeap;

// CEP:WHAT: Fixture arena bytes for one core plus analyzer plus VSIDS heap.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kCdclBenchArenaBytes: u32 = 8_388_608;

// CEP:WHAT: Variables in the analysis fixture graph.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kGraphVariables: u32 = 12;

// CEP:WHAT: Builds a literal or fails the bench.
// CEP:WHY: Readable graph construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below the fixture count.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Rebuilds the fixed level-2 conflict graph and returns the conflict offset.
// CEP:WHY: The analysis measurement must run against the identical implication graph every iteration; the graph matches the unit-test fixture (clauses at level 0, decisions at levels 1 and 2).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the graph does not conflict.
// CEP:ASSUMES: fresh arena.
// CEP:COST: constant.
// CEP:EVIDENCE: used by main.
// CEP:SECURITY: none.
fn build_graph() -> (
    SatCore<'static>,
    ConflictAnalyzer<'static>,
    VsidsHeap<'static>,
    u32,
) {
    let region = allocate_aligned_region(kCdclBenchArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    let _ = core.add_clause(&[lit(0, true)]).expect("unit 0");
    let _ = core
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("clause 2");
    let _ = core
        .add_clause(&[lit(1, false), lit(3, true)])
        .expect("clause 3");
    let _ = core
        .add_clause(&[lit(2, false), lit(3, false), lit(5, false), lit(6, false)])
        .expect("conflict clause");
    let _ = core
        .add_clause(&[lit(4, false), lit(5, true)])
        .expect("clause 5");
    let _ = core
        .add_clause(&[lit(4, false), lit(6, true)])
        .expect("clause 6");
    let _ = core.propagate().expect("propagate level 0");
    core.decide(lit(1, true)).expect("decide 1");
    let _ = core.propagate().expect("propagate level 1");
    core.decide(lit(4, true)).expect("decide 4");
    match core.propagate().expect("propagate level 2") {
        PropagationOutcome::Conflict(offset) => (core, analyzer, vsids, offset),
        PropagationOutcome::NoConflict => panic!("expected the graph to conflict"),
    }
}

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/cdcl_*.json.
// CEP:SECURITY: none.
fn main() {
    // Conflict analysis: measure analyze() on the fixed graph; each iteration re-runs the
    // analysis against the same (unchanged) trail state because the measurement must not
    // mutate the graph (learning is exercised by the end-to-end measurement below).
    let (core, analyzer, vsids, conflict) = build_graph();
    let mut buffer = [lit(0, true); 64];
    let (analyze_median, analyze_min) = measure_cycles(200_000, |_| {
        match analyzer.analyze(&core, &vsids, conflict, &mut buffer) {
            Ok(_) => 1,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0009",
        name: "cdcl_analyze",
        iterations: 200_000,
        cycles_median: analyze_median,
        cycles_min: analyze_min,
    });
    println!(
        "cdcl_analyze: median {:.2} cycles/op, min {:.2} cycles/op",
        analyze_median, analyze_min
    );

    // VSIDS decision: bump-and-pick cycles over a fresh heap (pick assigns nothing here;
    // the caller-side assignment is simulated by reinserting the picked variable).
    let region = allocate_aligned_region(kCdclBenchArenaBytes).expect("region 2");
    let arena2 = Box::leak(Box::new(Arena::new(region).expect("arena 2")));
    let heap = VsidsHeap::new(arena2, 256).expect("heap");
    let (decide_median, decide_min) = measure_cycles(100_000, |iteration| {
        // Round-robin bump to keep activities non-trivial, then pick and reinsert.
        heap.bump(iteration % 256);
        match heap.pick_unassigned(|_| false) {
            Some(variable) => {
                heap.insert(variable);
                1
            }
            None => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0009",
        name: "cdcl_decide",
        iterations: 100_000,
        cycles_median: decide_median,
        cycles_min: decide_min,
    });
    println!(
        "cdcl_decide: median {:.2} cycles/op, min {:.2} cycles/op",
        decide_median, decide_min
    );

    // End-to-end: PHP(3,4) refutation, cycles per conflict.
    let region = allocate_aligned_region(kCdclBenchArenaBytes).expect("region 3");
    let arena3 = Box::leak(Box::new(Arena::new(region).expect("arena 3")));
    let solver = CdclSolver::new(arena3, 12, RestartPolicy::Luby, false).expect("solver");
    let holes: u32 = 3;
    let pigeons: u32 = 4;
    for pigeon in 0..pigeons {
        let mut clause: Vec<SatLiteral> = Vec::new();
        for hole in 0..holes {
            clause.push(lit(pigeon * holes + hole, true));
        }
        solver.add_clause(&clause).expect("pigeon clause");
    }
    for hole in 0..holes {
        for first in 0..pigeons {
            for second in (first + 1)..pigeons {
                solver
                    .add_clause(&[
                        lit(first * holes + hole, false),
                        lit(second * holes + hole, false),
                    ])
                    .expect("hole clause");
            }
        }
    }
    let start = harness::cycle_counter();
    let outcome = solver.solve();
    let elapsed = harness::cycle_counter().saturating_sub(start);
    assert_eq!(outcome, SolveResult::Unsatisfiable, "PHP(3,4) must refute");
    let conflicts = solver.conflicts().max(1);
    let per_conflict = elapsed as f64 / conflicts as f64;
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0009",
        name: "cdcl_solve_per_conflict",
        iterations: conflicts as u32,
        cycles_median: per_conflict,
        cycles_min: per_conflict,
    });
    println!(
        "cdcl_solve_per_conflict: {:.2} cycles/conflict over {} conflicts",
        per_conflict, conflicts
    );
}
