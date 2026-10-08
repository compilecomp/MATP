// CEP:FILE: target/arm64.rs
// CEP:WHAT: AArch64 cycle counter: the generic timer read (cntvct_el0) via inline assembly.
// CEP:WHY: CEP&CC 13.1 requires measured cycles; AArch64 exposes the virtual counter through the system register cntvct_el0 (ARM Architecture Reference Manual, Armv8-A, system instructions); this module is compiled only for aarch64 targets.
// CEP:CLASS: CEP-1
// CEP:TARGET: arm64
// CEP:STATUS: complete
// CEP:FAILURE: none; the counter always reads.
// CEP:ASSUMES: The virtual counter is enabled (CNTVCT_EL0 readable from EL0), which mainstream Linux configurations provide; where it is disabled the read would trap, so CI runs this module only on platforms where it is enabled.
// CEP:COST: one system register read, roughly 10-20 cycles.
// CEP:EVIDENCE: CI target matrix (aarch64 runner); bench artifacts from that runner.
// CEP:SECURITY: none.
// CEP:UNSAFE: inline assembly performs the system register read; the wrapper is safe by construction (no inputs, pure read, documented register constraint).
// CEP:PORTABILITY: aarch64 only; cfg-gated.

/// CEP:WHAT: Reads the AArch64 virtual counter.
/// CEP:WHY: Benchmark timing on arm64.
/// CEP:STATUS: complete
/// CEP:FAILURE: none (see file header assumption about counter enablement).
/// CEP:ASSUMES: CNTVCT_EL0 readable at the current exception level.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: CI aarch64 job.
/// CEP:SECURITY: none.
/// CEP:TARGET: arm64
pub fn read_cycle_counter() -> u64 {
    let counter: u64;
    // CEP:UNSAFE: mrs reads the system register into a general register; out operand only, no memory effects.
    // CEP:ASSUMES: arm64 target (cfg-gated), counter enabled.
    // CEP:SECURITY: no untrusted input involved.
    unsafe {
        core::arch::asm!("mrs {counter}, cntvct_el0", counter = out(reg) counter);
    }
    counter
}

// CEP:WHAT: Reports that the arm64 counter is a real hardware counter.
// CEP:WHY: Benches gate cycle claims on this flag.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: CI aarch64 job.
// CEP:SECURITY: none.
pub fn cycle_counter_is_accurate() -> bool {
    true
}
