// CEP:FILE: target/x86_64.rs
// CEP:WHAT: x86-64 cycle counter: serialized rdtsc (lfence; rdtsc) through the core arch intrinsic.
// CEP:WHY: CEP&CC 13.1 requires measured cycles for CEP-0 claims; rdtsc is the x86-64 cycle counter and lfence serializes it so measurements bracket a well-defined instruction window (Intel SDM Vol. 3, RDTSC instruction).
// CEP:CLASS: CEP-1
// CEP:TARGET: x86-64
// CEP:STATUS: complete
// CEP:FAILURE: none; the counter always reads.
// CEP:ASSUMES: The TSC is invariant (constant rate) on the supported x86-64 baseline (RDTSCP/constant-TSC, Intel SDM Vol. 3 chapter 17); on variant-TSC legacy parts the measurement degrades but never fails.
// CEP:COST: lfence + rdtsc, roughly 20-30 cycles of overhead per read on mainstream cores; the benches bracket each measurement window with counter reads, so the per-operation medians absorb the overhead amortized over the iteration count.
// CEP:EVIDENCE: benches/artifacts/*.json record measurements taken with this counter; bracketing in benches/hot/harness.rs.
// CEP:SECURITY: none; counter reads reveal no secrets and accept no input.
// CEP:UNSAFE: the intrinsic call itself is unsafe because reading a model-specific register is outside safe Rust's model; the wrapper restores safety by construction (no inputs, pure read).

/// CEP:WHAT: Reads the serialized timestamp counter.
/// CEP:WHY: Benchmark timing; lfence prevents reordering of the counter read relative to the measured region.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: invariant TSC (see file header).
/// CEP:COST: see file header.
/// CEP:EVIDENCE: benches/hot/harness.rs.
/// CEP:SECURITY: none.
/// CEP:TARGET: x86-64
pub fn read_cycle_counter() -> u64 {
    // CEP:UNSAFE: lfence serializes the instruction stream and rdtsc reads the timestamp counter; pure reads, no memory accessed, no preconditions.
    // CEP:ASSUMES: x86-64 target (cfg-gated).
    // CEP:SECURITY: no untrusted input involved.
    unsafe {
        core::arch::asm!("lfence", options(nomem, nostack, preserves_flags));
        core::arch::x86_64::_rdtsc() as u64
    }
}

// CEP:WHAT: Reports that the x86-64 counter is a real hardware counter.
// CEP:WHY: Benches gate cycle claims on this flag.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: benches/hot/harness.rs.
// CEP:SECURITY: none.
pub fn cycle_counter_is_accurate() -> bool {
    true
}
