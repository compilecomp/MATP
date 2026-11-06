// CEP:FILE: config/lib.rs
// CEP:WHAT: Root module of the mapt-config crate: re-exports limits, target configuration, feature gates, and the security policy.
// CEP:WHY: Single import point (mapt_config::limits::kMaxTermDepth etc.) keeps every constant named, sourced, and auditable from one place (CEP&CC 11.1, 32.11).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: compile_error! is raised by target.rs when no target feature or more than one target feature is selected.
// CEP:ASSUMES: Compiled with exactly one target feature (default target-x86-64); enforced mechanically at compile time.
// CEP:COST: compile-time only; no runtime instructions.
// CEP:EVIDENCE: unit test unit/config/limits_test.rs.
// CEP:SECURITY: no_std, zero dependencies, constants only.

//! Named-constant crate for MAPT: resource limits, target configuration, feature gates, and the security policy.
//!
//! Every value is a compile-time constant with a documented source and rationale; no function, no allocation, no dependency. Consumers import constants from one place (`mapt_config::limits::kMaxTermDepth`) so every bound is named, sourced, and auditable (CEP&CC 11.1, 32.11). Compilation requires exactly one target feature; an ambiguous or absent selection is rejected by `compile_error!` in `config::target`.

#![no_std]
// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: The MAPT design document (section 5.1, 20.1) mandates kPascalCase constants (kTermHashTableCapacity, kMaxTermDepth); CEP&CC 33.15 specifies kPascalCase while CEP&CC 33.20 suggests SCREAMING_SNAKE_CASE for Rust; CEP&CC 50.5 documents this exact conflict as unresolved and deliberately exempts constant names from mechanical checking; MAPT resolves the conflict in favor of the design document, which is the project-level authority.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CEP&CC 50.5 known-limits clause on constant naming.
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

/// Build-feature introspection booleans: one named constant per compiled-in capability.
pub mod feature_gates;
/// Named resource limits and capacity constants for every MAPT engine (ATP, SAT, arena, IR, preprocessing, portfolio).
pub mod limits;
/// Security policy constants and the trust-level vocabulary for MAPT components.
pub mod security_policy;
/// Central target-configuration switch: re-exports exactly one target module selected by Cargo feature and rejects ambiguous selections at compile time.
pub mod target;
/// Target configuration constants for AArch64 (AAPCS64 ABI, little-endian, 64-byte cache line, 16 KiB conservative page bound).
pub mod target_arm64;
/// Conservative fallback target configuration for architectures without a dedicated module.
pub mod target_generic;
/// Target configuration constants for RV64 (RISC-V 64-bit, little-endian, 64-byte cache line, 4 KiB pages).
pub mod target_riscv64;
/// Target configuration constants for x86-64 (SysV ABI, little-endian, 64-byte cache line, 4 KiB pages).
pub mod target_x86_64;
