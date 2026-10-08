// CEP:FILE: hot/ir/mod.rs
// CEP:WHAT: Internal representation module: frozen symbol table, hash-consed terms, literals, clauses, and derivation steps.
// CEP:WHY: Design section 5 fixes one unified IR shared by every engine component; concentrating it under hot/ir/ keeps the IR contract (CEP&CC 38.17) auditable in one place.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: all IR storage lives in the shared arena.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests under tests/unit/hot; cold verifier tests/unit/cold/verifier_test.rs.
// CEP:SECURITY: symbol IDs and term offsets are validated at every access.

pub mod clause;
pub mod literal;
pub mod symbol_table;
pub mod term;

pub use clause::{
    Clause, ClauseError, ClauseId, ClausePtr, ClauseStore, DerivationStep, InferenceRule,
};
pub use literal::{Literal, LiteralFlags};
pub use symbol_table::{SortId, SymbolError, SymbolInfo, SymbolKind, SymbolTable};
pub use term::{TermError, TermPtr, TermStore, TermTag};
