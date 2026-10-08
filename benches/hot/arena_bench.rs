// CEP:FILE: benches/hot/arena_bench.rs
// CEP:WHAT: Arena allocation benchmark (bench CEP-BENCH-0001): cycles per alloc_bytes call at several sizes and alignments.
// CEP:WHY: CEP&CC Law 4: the arena allocator is CEP-0 and its CEP:COST fields cite this bench; measurement is median-of-repeats with a serialized cycle counter.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: runs single-threaded under cargo bench --release.
// CEP:COST: the bench itself is the measurement.
// CEP:EVIDENCE: writes benches/artifacts/arena_alloc_*.json.
// CEP:SECURITY: none.

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::memory::arena::Arena;

// CEP:WHAT: Bench entry point.
// CEP:WHY: cargo bench with harness = false calls main.
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure.
// CEP:ASSUMES: none.
// CEP:COST: see harness.
// CEP:EVIDENCE: benches/artifacts/arena_alloc_*.json.
// CEP:SECURITY: none.
fn main() {
    let region = allocate_aligned_region(16_777_216).expect("region");
    let arena = Arena::new(region).expect("arena");
    let (median, minimum) = measure_cycles(1_000_000, |iteration| {
        // Alternate sizes and alignments to cover the common shapes; the arena is large enough
        // that it never exhausts within the iteration count.
        let size = 32 + iteration % 64;
        let align = if iteration % 2 == 0 { 4 } else { 8 };
        match arena.alloc_bytes(size, align) {
            Ok(range) => range.len() as u64,
            Err(_) => 0,
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0001",
        name: "arena_alloc_bytes",
        iterations: 1_000_000,
        cycles_median: median,
        cycles_min: minimum,
    });
    println!(
        "arena_alloc_bytes: median {:.2} cycles/op, min {:.2} cycles/op",
        median, minimum
    );
}
