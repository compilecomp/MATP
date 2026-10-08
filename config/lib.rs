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

pub mod feature_gates;
pub mod limits;
pub mod security_policy;
pub mod target;
pub mod target_arm64;
pub mod target_generic;
pub mod target_riscv64;
pub mod target_x86_64;
