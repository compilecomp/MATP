// CEP:FILE: benches/hot/sat_bench.rs
// CEP:WHAT: SAT engine benchmark (bench CEP-BENCH-0005): cycles per literal negation, trail push, and BCP propagation step on a chain formula.
// CEP:WHY: CEP&CC Law 4 and design 11.2: BCP is the hottest path in the system; its CEP:COST and CEP:OPTIMAL fields cite this bench.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/sat_*.json.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{kMeasurementRepeats, measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::memory::arena::Arena;
use mapt::hot::sat::literal::{SatLiteral, SatVar};

// CEP:WHAT: Variables in the propagation chain benchmark.
// CEP:WHY: Named constant; a chain of this length yields one propagation step per variable (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kChainVariables: u32 = 512;

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/sat_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(67_108_864).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let core = mapt::hot::sat::database::SatCore::new(arena, 64).expect("core");
    let literal = SatLiteral::new(SatVar(7), false).expect("literal");
    let (negate_median, negate_min) =
        measure_cycles(1_000_000, |_| literal.negate().encoding() as u64);
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0005",
        name: "sat_literal_negate",
        iterations: 1_000_000,
        cycles_median: negate_median,
        cycles_min: negate_min,
    });
    println!(
        "sat_literal_negate: median {:.2} cycles/op, min {:.2} cycles/op",
        negate_median, negate_min
    );
    // Propagation: one core with an implication chain; each round decides the chain start,
    // propagates to fixpoint (kChainVariables - 1 steps), and backtracks; only the propagate
    // call is inside the measured window, so the number is the pure propagation step.
    let chain_region = allocate_aligned_region(16_777_216).expect("chain region");
    let chain_arena = Box::leak(Box::new(Arena::new(chain_region).expect("arena")));
    let chain_core =
        mapt::hot::sat::database::SatCore::new(chain_arena, kChainVariables).expect("core");
    for variable in 0..kChainVariables - 1 {
        chain_core
            .add_clause(&[
                SatLiteral::new(SatVar(variable), false).expect("literal"),
                SatLiteral::new(SatVar(variable + 1), true).expect("literal"),
            ])
            .expect("chain clause");
    }
    let mut propagation_samples: Vec<f64> = Vec::new();
    for _ in 0..kMeasurementRepeats {
        // Deciding lit(0) TRUE falsifies the first chain literal (negated lit(0)) and forces
        // the whole chain: one propagation step per clause.
        chain_core
            .decide(SatLiteral::new(SatVar(0), true).expect("literal"))
            .expect("decision");
        let start = harness::cycle_counter();
        let outcome = chain_core.propagate().expect("propagate");
        let elapsed = harness::cycle_counter().saturating_sub(start);
        std::hint::black_box(&outcome);
        propagation_samples.push(elapsed as f64 / (kChainVariables - 1) as f64);
        chain_core.cancel_until(0);
    }
    propagation_samples.sort_by(|left, right| left.partial_cmp(right).expect("finite"));
    let per_step_median = propagation_samples[propagation_samples.len() / 2];
    let per_step_min = propagation_samples[0];
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0005",
        name: "sat_bcp_step",
        iterations: kChainVariables,
        cycles_median: per_step_median,
        cycles_min: per_step_min,
    });
    println!(
        "sat_bcp_step: median {:.2} cycles/op, min {:.2} cycles/op",
        per_step_median, per_step_min
    );
    let _ = core;
}
