// CEP:FILE: target/riscv64.rs
// CEP:WHAT: RV64 cycle counter: the rdcycle pseudo-instruction via inline assembly.
// CEP:WHY: CEP&CC 13.1 requires measured cycles; RISC-V exposes the cycle counter through the rdcycle CSR read (RISC-V Unprivileged ISA Vol. 2, Zicsr); this module is compiled only for riscv64 targets.
// CEP:CLASS: CEP-1
// CEP:TARGET: riscv64
// CEP:STATUS: complete
// CEP:FAILURE: none; the counter always reads on configurations where the cycle CSR is readable.
// CEP:ASSUMES: The cycle CSR is readable from user mode (mcounteren/scounteren bits set by the kernel); mainstream Linux configurations provide it.
// CEP:COST: one CSR read, roughly 5-15 cycles.
// CEP:EVIDENCE: CI target matrix (riscv64 runner); bench artifacts from that runner.
// CEP:SECURITY: none.
// CEP:UNSAFE: inline assembly performs the CSR read; the wrapper is safe by construction (no inputs, pure read, documented register constraint).
// CEP:PORTABILITY: riscv64 only; cfg-gated.

/// CEP:WHAT: Reads the RV64 cycle counter.
/// CEP:WHY: Benchmark timing on riscv64.
/// CEP:STATUS: complete
/// CEP:FAILURE: none (see file header assumption about CSR readability).
/// CEP:ASSUMES: cycle CSR readable at the current privilege level.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: CI riscv64 job.
/// CEP:SECURITY: none.
/// CEP:TARGET: riscv64
pub fn read_cycle_counter() -> u64 {
    let counter: u64;
    // CEP:UNSAFE: rdcycle reads the cycle CSR into a general register; out operand only, no memory effects.
    // CEP:ASSUMES: riscv64 target (cfg-gated), CSR readable.
    // CEP:SECURITY: no untrusted input involved.
    unsafe {
        core::arch::asm!("rdcycle {counter}", counter = out(reg) counter);
    }
    counter
}

// CEP:WHAT: Reports that the riscv64 counter is a real hardware counter.
// CEP:WHY: Benches gate cycle claims on this flag.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: CI riscv64 job.
// CEP:SECURITY: none.
pub fn cycle_counter_is_accurate() -> bool {
    true
}
