// CEP:FILE: config/target_riscv64.rs
// CEP:WHAT: Target configuration constants for RV64 (RISC-V 64-bit, little-endian, 64-byte cache line, 4 KiB pages).
// CEP:WHY: CEP&CC 7.2 and 11.1 require named target facts; this module is the RV64 truth source used when feature target-riscv64 is selected.
// CEP:CLASS: CEP-1
// CEP:HPC-CLASS: HPC-1
// CEP:TARGET: riscv64
// CEP:STATUS: complete
// CEP:FAILURE: none; compile-time constants.
// CEP:ASSUMES: RV64GC ABI (lp64d), little-endian, 64-byte cache line, 4 KiB Sv39/Sv48 base pages.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: RISC-V Unprivileged ISA Spec Vol. 1 (RV64I); RISC-V Privileged Architecture (Sv39/Sv48 paging).
// CEP:SECURITY: none; configuration facts.
// CEP:PORTABILITY: only compiled under feature target-riscv64; CI target matrix compiles it.

/// CEP:WHAT: Target name string.
/// CEP:WHY: Diagnostics and benchmark artifacts must record target identity (CEP&CC 38.30).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: printed by the bench harness.
/// CEP:SECURITY: none.
pub const kTargetName: &str = "riscv64";

/// CEP:WHAT: Cache line size in bytes on this target.
/// CEP:WHY: Alignment and false-sharing avoidance use this named value (CEP&CC 11.1).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 64 bytes on mainstream RV64 cores (SiFive U74, T-Head C910).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: SiFive U74 manual; T-Head C910 manual.
/// CEP:SECURITY: none.
pub const kCacheLineBytes: u32 = 64;

/// CEP:WHAT: Smallest page size in bytes on this target.
/// CEP:WHY: Sizing decisions reference the named page size.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 4 KiB base pages under Sv39/Sv48.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: RISC-V Privileged Architecture, Sv39/Sv48.
/// CEP:SECURITY: none.
pub const kPageBytes: u32 = 4_096;

/// CEP:WHAT: Pointer width in bytes on this target.
/// CEP:WHY: Layout computations reference the named width instead of assuming 8.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 8 bytes; enforced by static assertion when compiled for this target.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: RV64I.
/// CEP:SECURITY: none.
pub const kPointerBytes: u32 = 8;

/// CEP:WHAT: True when the target is little-endian.
/// CEP:WHY: Endianness must be a named, asserted fact (CEP&CC Law 7).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: RISC-V is little-endian in the MAPT-supported profile.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: RISC-V Unprivileged ISA Vol. 1, byte order.
/// CEP:SECURITY: none.
pub const kLittleEndian: bool = true;

// CEP:WHAT: Compile-time cross-checks between declared and actual target facts.
// CEP:WHY: CEP&CC Law 3: assumptions must be enforced.
// CEP:STATUS: complete
// CEP:FAILURE: Compilation fails when compiled for a contradicting target.
// CEP:ASSUMES: compiled only for riscv64 targets under this feature.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CI target matrix.
// CEP:SECURITY: none.
#[cfg(target_arch = "riscv64")]
const _: () = {
    assert!(core::mem::size_of::<usize>() == kPointerBytes as usize);
    assert!(cfg!(target_endian = "little") == kLittleEndian);
};
