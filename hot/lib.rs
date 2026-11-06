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

//! Root module of the mapt-hot crate: the CEP-0/HPC-0 hot-path engine layer.
//!
//! Contents: the arena allocator, the internal representation (frozen symbol table, hash-consed terms, literals, clauses, derivation steps), the substitution engine with unification, matching, and composition, term orderings, term indexing, the inference engines, the given-clause search loop, the integrated CDCL SAT solver, AVATAR clause splitting, automated induction, conjecture generation, and lock-free concurrency primitives. The crate is `no_std`: no logging, no allocation outside the caller-provided arena, no I/O, no `dyn`, no clock reads (CEP&CC 25.3.1, design 4.1). All backing memory comes from the caller-provided arena region initialized before the hot path.

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
// CEP:WHAT: Denies the missing_docs lint crate-wide.
// CEP:WHY: Documentation Style Guide (doc standard.md) section 5.2 requires every public item to carry a doc comment; the gap was closed under CEP-1057.
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails when a public item lacks a doc comment; no runtime effect.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: CI docs job (cargo doc with RUSTDOCFLAGS -D warnings; Documentation Style Guide 5).
// CEP:SECURITY: none.
#![deny(missing_docs)]

/// AVATAR integration: splitter, component table, and the model-guided controller loop.
pub mod avatar;
/// Lock-free concurrency primitives: Chase-Lev deque, bounded MPMC sharing pool, clause codec.
pub mod concurrency;
/// Automated conjecture generation: harvest, bounded template enumeration, mini-refutation filter.
pub mod conjecture;
/// Term and clause indexing: the discrimination tree and the feature-vector filter.
pub mod index;
/// Automated induction: validated datatype declarations and bounded clausal scheme installation.
pub mod induction;
/// Inference engines: selection, resolution, factoring, superposition, demodulation, subsumption.
pub mod inference;
/// Internal representation: symbol table, terms, literals, clauses, derivation steps.
pub mod ir;
/// Memory subsystem: the bump arena allocator shared by all MAPT engines.
pub mod memory;
/// Term orderings: precedence tables, the Knuth-Bendix Ordering, and the Lexicographic Path Ordering.
pub mod ordering;
/// Prover result codes (design 2.2): Theorem, CounterSatisfiable, Saturated, Timeout, MemoryExhausted, InferenceLimit, GaveUp, Error.
pub mod result;
/// SAT engine: literals, assignment, trail, watch lists, database, BCP, CDCL, VSIDS, restarts, registry, preprocessing, incremental solving, proof recording.
pub mod sat;
/// Search loop: passive set, active set, bounded inference generator, given-clause saturation.
pub mod search;
/// Unification subsystem: the substitution engine and the unification, matching, and composition algorithms.
pub mod unification;
