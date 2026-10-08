// CEP:FILE: config/target.rs
// CEP:WHAT: Central target-configuration switch: re-exports exactly one target module selected by Cargo feature and rejects ambiguous selections at compile time.
// CEP:WHY: CEP&CC 6.2 forbids scattered feature checks and 38.30 forbids target checks in generic code; this module is the single target hook every other module imports.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: compile_error! fires when no target feature or more than one target feature is enabled.
// CEP:ASSUMES: Exactly one of target-x86-64, target-arm64, target-riscv64, target-generic is enabled; enforced below.
// CEP:COST: compile-time only; no runtime instructions.
// CEP:EVIDENCE: unit/config/limits_test.rs checks the selected target constants are self-consistent.
// CEP:SECURITY: prevents accidental cross-target configuration mixing.

#[cfg(not(any(
    feature = "target-x86-64",
    feature = "target-arm64",
    feature = "target-riscv64",
    feature = "target-generic"
)))]
compile_error!("mapt-config: no target feature selected; enable exactly one of target-x86-64, target-arm64, target-riscv64, target-generic");

#[cfg(all(feature = "target-x86-64", feature = "target-arm64"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(all(feature = "target-x86-64", feature = "target-riscv64"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(all(feature = "target-x86-64", feature = "target-generic"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(all(feature = "target-arm64", feature = "target-riscv64"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(all(feature = "target-arm64", feature = "target-generic"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(all(feature = "target-riscv64", feature = "target-generic"))]
compile_error!("mapt-config: multiple target features selected; enable exactly one");

#[cfg(feature = "target-x86-64")]
pub use crate::target_x86_64 as selected;

#[cfg(feature = "target-arm64")]
pub use crate::target_arm64 as selected;

#[cfg(feature = "target-riscv64")]
pub use crate::target_riscv64 as selected;

#[cfg(feature = "target-generic")]
pub use crate::target_generic as selected;
