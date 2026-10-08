// CEP:FILE: cold/lib.rs
// CEP:WHAT: Root module of the mapt-cold crate: CEP-1 deterministic runtime code (arena host, symbol table builder, IR verifier, debug printer).
// CEP:WHY: Design section 4.1: cold code may allocate and use std but must never be called from hot code; a separate std crate makes the direction of the dependency (cold -> hot) mechanical and auditable.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: cold code runs before or after the hot path, never inside it.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests under tests/unit/cold.
// CEP:SECURITY: cold code validates all untrusted input before it enters hot structures.

#![allow(non_upper_case_globals)]
// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: The MAPT design document mandates kPascalCase constants; CEP&CC 50.5 documents the kPascalCase-versus-SCREAMING_SNAKE_CASE conflict as unresolved and exempts constant names from mechanical checking; MAPT resolves it in favor of the design document.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CEP&CC 50.5 known-limits clause on constant naming.
// CEP:SECURITY: none.

pub mod arena_host;
pub mod debug_printer;
pub mod symbol_table_builder;
pub mod verifier;
