// CEP:FILE: hot/memory/mod.rs
// CEP:WHAT: Memory subsystem module: the arena allocator shared by all MAPT engines.
// CEP:WHY: Design section 4 places memory/ under hot/; the arena is the single allocation domain for terms, clauses, substitutions, and SAT structures.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/arena_test.rs.
// CEP:SECURITY: arena bounds are the primary memory denial-of-service mitigation.

pub mod arena;

pub use arena::{Arena, ArenaError, ArenaRange};
