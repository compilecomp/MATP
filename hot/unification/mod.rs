// CEP:FILE: hot/unification/mod.rs
// CEP:WHAT: Unification subsystem module: the substitution engine (Phase 1); unification and matching algorithms arrive in Phase 2.
// CEP:WHY: Design section 4 places unification/ under hot/; Phase 1 delivers the substitution storage and application machinery the algorithms will drive.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/substitution_test.rs.
// CEP:SECURITY: substitution arrays are bounded and bounds-checked.

pub mod substitution;

pub use substitution::{Substitution, SubstitutionError, SubstitutionRecord};
