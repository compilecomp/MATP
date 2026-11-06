// CEP:FILE: target/lib.rs
// CEP:WHAT: Root module of the mapt-target crate: architecture-isolated cycle counters and target hooks.
// CEP:WHY: CEP&CC 32.5 requires all ISA-specific code to live under the target directory; benchmark evidence (CEP&CC 13.1) needs a cycle counter, and each architecture provides its own, cfg-gated so exactly one implementation compiles per build.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: one architecture module compiles per build (cfg attributes).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: benches/hot uses read_cycle_counter on x86-64; CI target matrix compiles the arm64 and riscv64 modules.
// CEP:SECURITY: inline assembly is confined to this crate and documented per block (CEP&CC 25.7).

//! Architecture-isolated cycle counters and target hooks for MAPT.
//!
//! CEP&CC 32.5 requires all ISA-specific code to live under the target directory. Exactly one module compiles per build (cfg-gated on `target_arch`); benches reach the selected implementation through `read_cycle_counter` and verify it with `cycle_counter_is_accurate` before recording cycle claims. Targets without a hardware counter report 0 and false, so benchmark evidence degrades to wall-clock instead of fabricating numbers.

#![no_std]
// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: See the same allowance in config/lib.rs; CEP&CC 50.5 exempts constant names from mechanical checking while the standard resolves the kPascalCase conflict.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CEP&CC 50.5.
// CEP:SECURITY: none.
#![allow(non_upper_case_globals)]
// CEP:WHAT: Denies the missing_docs lint crate-wide.
// CEP:WHY: Documentation Style Guide (doc standard.md) section 5.2 requires every public item to carry a doc comment; the gap was closed under CEP-1057.
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails when a public item lacks a doc comment; no runtime effect.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CI docs job (cargo doc with RUSTDOCFLAGS -D warnings; Documentation Style Guide 5).
// CEP:SECURITY: none.
#![deny(missing_docs)]

/// AArch64 cycle counter: the generic timer read (`cntvct_el0`) via inline assembly.
#[cfg(target_arch = "aarch64")]
pub mod arm64;
/// Generic fallback target: no hardware cycle counter; benches must use wall-clock and mark measurements accordingly.
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
)))]
pub mod generic;
/// RV64 cycle counter: the `rdcycle` pseudo-instruction via inline assembly.
#[cfg(target_arch = "riscv64")]
pub mod riscv64;
/// x86-64 cycle counter: serialized `rdtsc` (`lfence` then `rdtsc`) through the core arch intrinsic.
#[cfg(target_arch = "x86_64")]
pub mod x86_64;

#[cfg(target_arch = "aarch64")]
pub use arm64 as selected;
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
)))]
pub use generic as selected;
#[cfg(target_arch = "riscv64")]
pub use riscv64 as selected;
#[cfg(target_arch = "x86_64")]
pub use x86_64 as selected;

/// Reads the architecture cycle counter.
///
/// One call site for benches; the selected module provides the ISA-specific implementation (CEP&CC 38.30 target hooks). Never fails; targets without a counter report 0 and `cycle_counter_is_accurate` returns false so benches refuse to record cycle claims. Cost: one counter read (target-specific latency). Assumed to be called from CEP-2 benchmark code, never from CEP-0 hot paths.
pub fn read_cycle_counter() -> u64 {
    selected::read_cycle_counter()
}

/// Returns true when the cycle counter is a real hardware counter.
///
/// Bench evidence must not record fabricated cycle numbers (CEP&CC Law 4: no unmeasured hot code); the generic fallback reports false and benches fall back to wall-clock with an explicit marker. Constant cost.
pub fn cycle_counter_is_accurate() -> bool {
    selected::cycle_counter_is_accurate()
}
