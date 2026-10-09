// CEP:FILE: hot/lib.rs
// CEP:WHAT: Root module of the mapt-hot crate: the CEP-0/HPC-0 hot-path engine layer (arena, IR, substitution engine, unification and matching, term orderings, term indexing, SAT core with CDCL).
// CEP:WHY: Design section 4.1 requires hot/ to contain only CEP-0 code with no logging, no allocation, no I/O, no dyn, and no std runtime; the crate-level no_std attribute enforces the std ban mechanically (CEP&CC 25.3.1).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: All backing memory comes from the caller-provided arena region initialized before the hot path (design 8.1); enforced by the arena API.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: cep_lint CEP-LINT-HOT-BANNED passes on this crate; unit and property tests under tests/unit/hot and tests/property.
// CEP:SECURITY: no_std removes the standard-library attack surface; all input to hot structures is validated by explicit bounds checks.
// CEP:HPC-DETERMINISM: deterministic; no clocks, no randomness, no hash-seed dependence, no thread scheduling dependence.

#![no_std]
// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: The MAPT design document mandates kPascalCase constants; CEP&CC 50.5 documents the kPascalCase-versus-SCREAMING_SNAKE_CASE conflict as unresolved and exempts constant names from mechanical checking; MAPT resolves it in favor of the design document.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CEP&CC 50.5 known-limits clause on constant naming.
// CEP:SECURITY: none.
#![allow(non_upper_case_globals)]

pub mod index;
pub mod ir;
pub mod memory;
pub mod ordering;
pub mod result;
pub mod sat;
pub mod unification;
