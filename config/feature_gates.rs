// CEP:FILE: config/feature_gates.rs
// CEP:WHAT: Centralized build-feature introspection booleans for MAPT.
// CEP:WHY: CEP&CC 6.2 requires feature checks centralized in one module instead of scattered across the codebase; every cfg!(feature = ...) in MAPT lives here or in target.rs.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; compile-time constants.
// CEP:ASSUMES: Feature flags are declared in config/Cargo.toml; target.rs enforces the exactly-one rule.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: target.rs static guards.
// CEP:SECURITY: prevents silent feature fallback (CEP&CC 6.2).

/// CEP:WHAT: True when the x86-64 target configuration is selected.
/// CEP:WHY: Centralizes the target-x86-64 feature check.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: config/target.rs selection logic.
/// CEP:SECURITY: none.
pub const kTargetX86_64Enabled: bool = cfg!(feature = "target-x86-64");

/// CEP:WHAT: True when the AArch64 target configuration is selected.
/// CEP:WHY: Centralizes the target-arm64 feature check.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: config/target.rs selection logic.
/// CEP:SECURITY: none.
pub const kTargetArm64Enabled: bool = cfg!(feature = "target-arm64");

/// CEP:WHAT: True when the RV64 target configuration is selected.
/// CEP:WHY: Centralizes the target-riscv64 feature check.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: config/target.rs selection logic.
/// CEP:SECURITY: none.
pub const kTargetRiscv64Enabled: bool = cfg!(feature = "target-riscv64");

/// CEP:WHAT: True when the generic fallback target configuration is selected.
/// CEP:WHY: Centralizes the target-generic feature check.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: config/target.rs selection logic.
/// CEP:SECURITY: none.
pub const kTargetGenericEnabled: bool = cfg!(feature = "target-generic");
