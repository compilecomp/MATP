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
// CEP:NOTE: CEP-1057 closed 2026-11-07: every public item in hot, cold, config, and target carries a doc comment, and all member crate roots deny the missing_docs lint per doc standard.md section 5.2; the facade itself declares no public items.

//! Root facade crate for MAPT: re-exports the workspace member crates under stable paths (`mapt::hot`, `mapt::cold`, `mapt::config`, `mapt::target`) so tests and benchmarks stay independent of crate topology. Compile-time only; the facade declares no items of its own.

// CEP:WHAT: Denies the missing_docs lint crate-wide.
// CEP:WHY: Documentation Style Guide (doc standard.md) section 5.2 requires every public item to carry a doc comment; the facade re-exports only, so the attribute guards future additions.
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails when a public item lacks a doc comment; no runtime effect.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CI docs job (cargo doc with RUSTDOCFLAGS -D warnings; Documentation Style Guide 5).
// CEP:SECURITY: none.
#![deny(missing_docs)]

pub use mapt_cold as cold;
pub use mapt_config as config;
pub use mapt_hot as hot;
pub use mapt_target as target;
