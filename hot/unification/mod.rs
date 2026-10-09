// CEP:FILE: hot/unification/mod.rs
// CEP:WHAT: Unification subsystem module: the substitution engine (Phase 1) and the unification, matching, and composition algorithms (Phase 2).
// CEP:WHY: Design section 4 places unification/ under hot/; Phase 1 delivered the substitution storage and application machinery, Phase 2 delivers the algorithms that drive it (design 26 build order, ticket CEP-1002).
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/substitution_test.rs; unit/hot/unify_test.rs.
// CEP:SECURITY: substitution arrays are bounded and bounds-checked.

pub mod substitution;
pub mod unify;

pub use substitution::{Substitution, SubstitutionError, SubstitutionRecord};
pub use unify::{compose, match_terms, unify};
