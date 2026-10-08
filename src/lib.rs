// CEP:FILE: src/lib.rs
// CEP:WHAT: Root facade crate for MAPT; re-exports the workspace member crates for the test and benchmark packages.
// CEP:WHY: Tests and benches import one stable path (mapt::hot, mapt::cold, mapt::config, mapt::target) instead of reaching into member crates directly, keeping test code independent of crate topology.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; the re-exports are compile-time only.
// CEP:ASSUMES: Workspace members exist at the paths declared in Cargo.toml; enforced by Cargo at build time.
// CEP:COST: compile-time only; no runtime instructions.
// CEP:EVIDENCE: every test target under tests/ compiles against this facade.
// CEP:SECURITY: no untrusted input; no FFI.

pub use mapt_cold as cold;
pub use mapt_config as config;
pub use mapt_hot as hot;
pub use mapt_target as target;
