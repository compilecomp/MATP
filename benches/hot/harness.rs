// CEP:FILE: benches/hot/harness.rs
// CEP:WHAT: Shared benchmark harness: cycle-counter accuracy assertion, median-of-repeats measurement, and JSON artifact emission for CEP-0 cost evidence.
// CEP:WHY: CEP&CC Law 4 and 13: hot code must be measured with stored artifacts (compiler, flags, target, input, cycles, date); the harness centralizes measurement so every bench reports identically structured evidence (CEP&CC 38.47 benchmark requirements).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on counter unavailability or IO failure (bench tooling may fail loudly; it is not production code).
// CEP:ASSUMES: The cycle counter is accurate (checked at start); measurements run single-threaded on an otherwise idle machine; results are evidence records, so timestamps are required content (CEP&CC 13.1), not nondeterminism.
// CEP:COST: offline tool; measurement loop cost dominates.
// CEP:EVIDENCE: produces benches/artifacts/*.json consumed by CEP:COST and CEP:EVIDENCE fields across the hot crate and by scripts/bench_gate.py.
// CEP:SECURITY: no untrusted input; writes only into the repository artifacts directory.

#![allow(non_upper_case_globals)]

use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

// CEP:WHAT: Repeats per measurement (median reported).
// CEP:WHY: Named constant; the median of repeats filters scheduler noise deterministically for fixed inputs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by measure_cycles.
// CEP:SECURITY: none.
pub const kMeasurementRepeats: u32 = 15;

// CEP:WHAT: Result of one measurement.
// CEP:WHY: Structured evidence for artifact emission and gate checks.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: plain data.
// CEP:EVIDENCE: consumed by write_artifact.
// CEP:SECURITY: none.
pub struct Measurement {
    /// CEP:WHAT: Bench identifier (for example CEP-BENCH-0001).
    pub bench_id: &'static str,
    /// CEP:WHAT: Measurement name (for example alloc_bytes_64).
    pub name: &'static str,
    /// CEP:WHAT: Iterations inside the measured closure per repeat.
    pub iterations: u32,
    /// CEP:WHAT: Median cycles per operation.
    pub cycles_median: f64,
    /// CEP:WHAT: Minimum cycles per operation observed.
    pub cycles_min: f64,
}

// CEP:WHAT: Reads the cycle counter, asserting accuracy.
// CEP:WHY: Fabricated cycle numbers violate CEP&CC Law 4; the harness refuses to record them without a real counter.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the target has no accurate counter.
// CEP:ASSUMES: none.
// CEP:COST: one counter read.
// CEP:EVIDENCE: called by every bench.
// CEP:SECURITY: none.
pub fn cycle_counter() -> u64 {
    assert!(
        mapt_target::cycle_counter_is_accurate(),
        "this target has no accurate cycle counter; refusing to record cycle evidence"
    );
    mapt_target::read_cycle_counter()
}

// CEP:WHAT: Measures cycles per operation for a closure, reporting the median of repeats.
// CEP:WHY: CEP&CC 13.3: expected-case cost from repeated measurement; the closure receives a sink value to prevent dead-code elimination of the measured work.
// CEP:STATUS: complete
// CEP:FAILURE: panics on counter unavailability.
// CEP:ASSUMES: the closure is deterministic and side-effect-light apart from its measurement purpose.
// CEP:COST: iterations x repeats operations.
// CEP:EVIDENCE: used by all benches.
// CEP:SECURITY: none.
pub fn measure_cycles<F>(iterations: u32, mut operation: F) -> (f64, f64)
where
    F: FnMut(u32) -> u64,
{
    let mut samples: Vec<f64> = Vec::with_capacity(kMeasurementRepeats as usize);
    for _ in 0..kMeasurementRepeats {
        let start = cycle_counter();
        let mut sink: u64 = 0;
        for iteration in 0..iterations {
            // black_box on input and result prevents dead-code elimination of measured work.
            sink = sink.wrapping_add(std::hint::black_box(operation(std::hint::black_box(
                iteration,
            ))));
        }
        let elapsed = cycle_counter().saturating_sub(start);
        std::hint::black_box(sink);
        samples.push(elapsed as f64 / iterations as f64);
    }
    samples.sort_by(|left, right| left.partial_cmp(right).expect("samples are finite"));
    let median = samples[samples.len() / 2];
    let minimum = samples[0];
    (median, minimum)
}

// CEP:WHAT: Writes one measurement as a JSON artifact into benches/artifacts.
// CEP:WHY: CEP&CC 13.1: measurement artifacts must store compiler, flags, target, input, cycles, and date; JSON keeps the gate script parseable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on filesystem failure.
// CEP:ASSUMES: run from the workspace root (cargo bench cwd).
// CEP:COST: one file write.
// CEP:EVIDENCE: consumed by scripts/bench_gate.py and cited by CEP:EVIDENCE fields.
// CEP:SECURITY: writes only inside the repository.
pub fn write_artifact(measurement: &Measurement) {
    let mut path = PathBuf::from("benches/artifacts");
    fs::create_dir_all(&path).expect("artifact directory");
    path.push(format!("{}.json", measurement.name));
    let date = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("wall clock after epoch")
        .as_secs();
    let json = format!(
        "{{\n  \"bench\": \"{}\",\n  \"name\": \"{}\",\n  \"iterations\": {},\n  \"cycles_median\": {},\n  \"cycles_min\": {},\n  \"rustc\": \"{}\",\n  \"profile\": \"release\",\n  \"target\": \"{}\",\n  \"cycle_counter\": \"serialized-rdtsc\",\n  \"date_unix\": {}\n}}\n",
        measurement.bench_id,
        measurement.name,
        measurement.iterations,
        measurement.cycles_median,
        measurement.cycles_min,
        rustc_version(),
        mapt_config::target::selected::kTargetName,
        date
    );
    fs::write(&path, json).expect("write artifact");
}

// CEP:WHAT: Returns the pinned rustc version string.
// CEP:WHY: CEP&CC 13.1 requires the compiler version in artifacts; the workspace pins it in Cargo.toml.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the manifest rust-version equals the toolchain (rust-toolchain.toml pins it).
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: rust-toolchain.toml.
// CEP:SECURITY: none.
pub fn rustc_version() -> String {
    env!("CARGO_PKG_RUST_VERSION").to_string()
}
