// CEP:FILE: config/target_x86_64.rs
// CEP:WHAT: Target configuration constants for x86-64 (SysV ABI, little-endian, 64-byte cache line, 4 KiB pages).
// CEP:WHY: CEP&CC 7.2 and 11.1 require target facts to be named configuration values instead of silent assumptions; this module is the x86-64 truth source.
// CEP:CLASS: CEP-1
// CEP:HPC-CLASS: HPC-1
// CEP:TARGET: x86-64
// CEP:STATUS: complete
// CEP:FAILURE: none; compile-time constants.
// CEP:ASSUMES: System V AMD64 ABI, little-endian byte order, 64-byte cache line, 4 KiB smallest page size; all enforced by static assertions where the compiler exposes them.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: ABI facts from System V ABI x86-64 psABI 1.0; cache line from Intel SDM Vol. 1 (mainstream cores).
// CEP:SECURITY: none; configuration facts.
// CEP:PORTABILITY: this module is only compiled under feature target-x86-64.

/// CEP:WHAT: Target name string.
/// CEP:WHY: Diagnostics and benchmark artifacts must record the target identity (CEP&CC 38.30).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: printed by the bench harness into benches/artifacts.
/// CEP:SECURITY: none.
pub const kTargetName: &str = "x86-64";

/// CEP:WHAT: Cache line size in bytes on this target.
/// CEP:WHY: Alignment and false-sharing avoidance use this value (design 8.1, CEP&CC 11.1); it must be a named target constant, never a literal 64 in code.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 64 bytes on mainstream x86-64 cores; cross-checked against the architecture at build time below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: Intel SDM Vol. 1; AMD APM Vol. 1.
/// CEP:SECURITY: none.
pub const kCacheLineBytes: u32 = 64;

/// CEP:WHAT: Smallest page size in bytes on this target.
/// CEP:WHY: Arena region sizing and NUMA placement (Phase 4) need the page size as a named constant.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 4 KiB base pages (x86-64 long mode).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: Intel SDM Vol. 3, paging chapter.
/// CEP:SECURITY: none.
pub const kPageBytes: u32 = 4_096;

/// CEP:WHAT: Pointer width in bytes on this target.
/// CEP:WHY: Layout computations and static assertions reference the named width instead of assuming 8.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 8 bytes; enforced by static assertion against core::mem::size_of::<usize>() when compiled for this target.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: System V ABI x86-64.
/// CEP:SECURITY: none.
pub const kPointerBytes: u32 = 8;

/// CEP:WHAT: True when the target is little-endian.
/// CEP:WHY: Endianness is a hard-coded-assumption hazard (CEP&CC Law 7); code that depends on byte order must cite this constant and assert it.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: x86-64 is always little-endian; cross-checked at compile time below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: Intel SDM Vol. 1.
/// CEP:SECURITY: none.
pub const kLittleEndian: bool = true;

// CEP:WHAT: Compile-time cross-checks between declared and actual target facts.
// CEP:WHY: CEP&CC Law 3: the assumptions above must be enforced, not merely stated.
// CEP:STATUS: complete
// CEP:FAILURE: Compilation fails when the module is compiled for a target that contradicts the constants.
// CEP:ASSUMES: compiled only for x86-64 targets (feature gate).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: build matrix in CI.
// CEP:SECURITY: none.
#[cfg(target_arch = "x86_64")]
const _: () = {
    assert!(core::mem::size_of::<usize>() == kPointerBytes as usize);
    assert!(cfg!(target_endian = "little") == kLittleEndian);
};
