// CEP:FILE: cold/lib.rs
// CEP:WHAT: Root module of the mapt-cold crate: CEP-1 deterministic runtime code (arena host, symbol table builder, IR verifier, debug printer, proof output: DRAT writer, DRAT checker, and the unified TSTP reconstruction; the certified proof kernel (Spec 19) behind the checker; portfolio manager (Phase 4)).
// CEP:WHY: Design section 4.1: cold code may allocate and use std but must never be called from hot code; a separate std crate makes the direction of the dependency (cold -> hot) mechanical and auditable; Phase 3 adds the proof-output half of design 6.4 (DRAT text emission) and the internal checker of design 11.1 S43; Phase 5 moves the step-by-step verification into the certified kernel (Spec 19) and makes the TSTP writer delegate to it.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: cold code runs before or after the hot path, never inside it.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests under tests/unit/cold.
// CEP:SECURITY: cold code validates all untrusted input before it enters hot structures.

//! Root module of the mapt-cold crate: CEP-1 deterministic runtime code.
//!
//! Contents: the arena host, the symbol table builder, the full IR verifier, the debug printer, the proof-output half (the DRAT writer, the internal DRAT checker, and the unified TSTP reconstruction backed by the certified proof kernel), and the portfolio manager. Cold code may allocate and use `std` but is never called from hot code; the dependency direction (cold -> hot) is mechanical and auditable (design 4.1).

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
// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: The MAPT design document mandates kPascalCase constants; CEP&CC 50.5 documents the kPascalCase-versus-SCREAMING_SNAKE_CASE conflict as unresolved and exempts constant names from mechanical checking; MAPT resolves it in favor of the design document.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CEP&CC 50.5 known-limits clause on constant naming.
// CEP:SECURITY: none.

/// Arena host: allocates the aligned backing region from the system heap and hands it to the CEP-0 arena.
pub mod arena_host;
/// Deterministic debug printer for terms and clauses in s-expression syntax.
pub mod debug_printer;
/// The certified proof kernel: bounded replay and per-rule verification of recorded derivations (Spec 19).
pub mod kernel;
/// The input-parsing module: the shared parse vocabulary and the DIMACS and TPTP front ends (design 6).
pub mod parsing;
/// The portfolio manager: scoped worker threads, wall-clock slices, first-to-finish, and sharing.
pub mod portfolio;
/// Proof output: the DRAT writer, the internal DRAT checker, and the TSTP reconstruction.
pub mod proof_output;
/// CEP-1 construction of the frozen symbol table with validation and arena finalization.
pub mod symbol_table_builder;
/// The full IR verifier: re-validates every structural invariant of the stores and the symbol table.
pub mod verifier;
