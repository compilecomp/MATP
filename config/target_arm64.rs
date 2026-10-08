// CEP:FILE: config/target_arm64.rs
// CEP:WHAT: Target configuration constants for AArch64 (AAPCS64 ABI, little-endian, 64-byte cache line, 16 KiB conservative page bound).
// CEP:WHY: CEP&CC 7.2 and 11.1 require named target facts; this module is the AArch64 truth source used when feature target-arm64 is selected.
// CEP:CLASS: CEP-1
// CEP:HPC-CLASS: HPC-1
// CEP:TARGET: arm64
// CEP:STATUS: complete
// CEP:FAILURE: none; compile-time constants.
// CEP:ASSUMES: AAPCS64 ABI, little-endian, 64-byte cache line; page size is the conservative maximum of the 4 KiB and 16 KiB configurations Apple Linux uses.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: ARM Architecture Reference Manual (Armv8-A); AAPCS64 in ARM ELF ABI.
// CEP:SECURITY: none; configuration facts.
// CEP:PORTABILITY: only compiled under feature target-arm64; CI target matrix compiles it.

/// CEP:WHAT: Target name string.
/// CEP:WHY: Diagnostics and benchmark artifacts must record target identity (CEP&CC 38.30).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: printed by the bench harness.
/// CEP:SECURITY: none.
pub const kTargetName: &str = "arm64";

/// CEP:WHAT: Cache line size in bytes on this target.
/// CEP:WHY: Alignment and false-sharing avoidance use this named value (CEP&CC 11.1).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 64 bytes (Cortex-A mainstream); some cores use 128-byte prefetch pairs, documented here as a known variance.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: ARM TRM Cortex-A78, memory system chapter.
/// CEP:SECURITY: none.
pub const kCacheLineBytes: u32 = 64;

/// CEP:WHAT: Smallest portable page size in bytes used for sizing decisions.
/// CEP:WHY: AArch64 Linux ships both 4 KiB and 16 KiB pages; sizing against 16 KiB is safe on both.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: base pages of 4 KiB or 16 KiB.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: Linux kernel arm64 documentation (kernel options for 16 KiB pages).
/// CEP:SECURITY: none.
pub const kPageBytes: u32 = 16_384;

/// CEP:WHAT: Pointer width in bytes on this target.
/// CEP:WHY: Layout computations reference the named width instead of assuming 8.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 8 bytes; enforced by static assertion when compiled for this target.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: AAPCS64.
/// CEP:SECURITY: none.
pub const kPointerBytes: u32 = 8;

/// CEP:WHAT: True when the target is little-endian.
/// CEP:WHY: Endianness must be a named, asserted fact (CEP&CC Law 7).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: little-endian in the MAPT-supported profile (big-endian AArch64 is out of scope and rejected by the assertion below).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: ARM ARMv8-A, single-threaded little-endian data accesses.
/// CEP:SECURITY: none.
pub const kLittleEndian: bool = true;

// CEP:WHAT: Compile-time cross-checks between declared and actual target facts.
// CEP:WHY: CEP&CC Law 3: assumptions must be enforced.
// CEP:STATUS: complete
// CEP:FAILURE: Compilation fails when compiled for a contradicting target.
// CEP:ASSUMES: compiled only for aarch64 targets under this feature.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CI target matrix.
// CEP:SECURITY: none.
#[cfg(target_arch = "aarch64")]
const _: () = {
    assert!(core::mem::size_of::<usize>() == kPointerBytes as usize);
    assert!(cfg!(target_endian = "little") == kLittleEndian);
};
