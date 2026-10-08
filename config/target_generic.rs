// CEP:FILE: config/target_generic.rs
// CEP:WHAT: Conservative fallback target configuration for architectures without a dedicated module.
// CEP:WHY: CEP&CC 32.5 requires a generic fallback in the target directory; the conservative values keep correctness (never performance) on unknown targets.
// CEP:CLASS: CEP-1
// CEP:HPC-CLASS: HPC-1
// CEP:TARGET: generic
// CEP:STATUS: complete
// CEP:FAILURE: none; compile-time constants.
// CEP:ASSUMES: 64-bit pointer width and little-endian are required by MAPT layout assertions; selecting the generic target on another profile fails those assertions.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: layout assertions in hot crate static checks.
// CEP:SECURITY: none; configuration facts.
// CEP:PORTABILITY: usable on any 64-bit little-endian target at reduced performance guarantees.

/// CEP:WHAT: Target name string.
/// CEP:WHY: Diagnostics and benchmark artifacts must record target identity (CEP&CC 38.30).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: printed by the bench harness.
/// CEP:SECURITY: none.
pub const kTargetName: &str = "generic";

/// CEP:WHAT: Conservative cache line size in bytes.
/// CEP:WHY: Alignment decisions on unknown targets use the smallest mainstream line so they never straddle lines on common hardware.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 64 bytes is safe on all supported 64-bit targets.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: common value across x86-64/AArch64/RV64 modules.
/// CEP:SECURITY: none.
pub const kCacheLineBytes: u32 = 64;

/// CEP:WHAT: Conservative page size in bytes.
/// CEP:WHY: Sizing decisions on unknown targets use the smallest mainstream page.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 4 KiB is safe on all supported targets.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: common value across x86-64/RV64 modules.
/// CEP:SECURITY: none.
pub const kPageBytes: u32 = 4_096;

/// CEP:WHAT: Pointer width in bytes.
/// CEP:WHY: Layout computations reference the named width; MAPT requires 64-bit.
/// CEP:STATUS: complete
/// CEP:FAILURE: static assertions in the hot crate fail on non-64-bit builds.
/// CEP:ASSUMES: 8 bytes.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: hot crate layout checks.
/// CEP:SECURITY: none.
pub const kPointerBytes: u32 = 8;

/// CEP:WHAT: True when the target is little-endian.
/// CEP:WHY: Endianness must be a named, asserted fact (CEP&CC Law 7); the generic profile supports little-endian only.
/// CEP:STATUS: complete
/// CEP:FAILURE: static assertions fail on big-endian builds.
/// CEP:ASSUMES: little-endian.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: hot crate layout checks.
/// CEP:SECURITY: none.
pub const kLittleEndian: bool = true;
