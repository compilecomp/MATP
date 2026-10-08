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

#[cfg(target_arch = "aarch64")]
pub mod arm64;
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "riscv64"
)))]
pub mod generic;
#[cfg(target_arch = "riscv64")]
pub mod riscv64;
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

// CEP:WHAT: Reads the architecture cycle counter.
// CEP:WHY: One call site for benches; the selected module provides the ISA-specific implementation (CEP&CC 38.30 target hooks).
// CEP:STATUS: complete
// CEP:FAILURE: never fails; targets without a counter report 0 and cycle_counter_is_accurate() returns false so benches refuse to record cycle claims.
// CEP:ASSUMES: called from CEP-2 benchmark code, never from CEP-0 hot paths.
// CEP:COST: one counter read (target-specific latency).
// CEP:EVIDENCE: benches/hot/*.rs.
// CEP:SECURITY: none.
pub fn read_cycle_counter() -> u64 {
    selected::read_cycle_counter()
}

// CEP:WHAT: Returns true when the cycle counter is a real hardware counter.
// CEP:WHY: Bench evidence must not record fabricated cycle numbers (CEP&CC Law 4: no unmeasured hot code); the generic fallback reports false and benches fall back to wall-clock with an explicit marker.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: benches/hot/*.rs check this before recording.
// CEP:SECURITY: none.
pub fn cycle_counter_is_accurate() -> bool {
    selected::cycle_counter_is_accurate()
}
