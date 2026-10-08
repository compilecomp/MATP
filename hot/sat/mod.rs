// CEP:FILE: hot/sat/mod.rs
// CEP:WHAT: SAT engine core module: literals, assignment store, trail, intrusive watch lists, clause database, and the Boolean constraint propagation engine.
// CEP:WHY: Design section 11 (components S1-S6, S9-S11): MAPT owns its SAT engine with no FFI boundary to the ATP engine; Phase 1 delivers the data structures and BCP, the hottest path in the whole system.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: all state lives in the shared arena, sized by the variable count at initialization.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests unit/hot/sat_*; property/bcp_property_test.rs; bench CEP-BENCH-0005.
// CEP:SECURITY: variable indices and clause offsets are bounds-checked.

pub mod assignment;
pub mod bcp;
pub mod clause;
pub mod database;
pub mod literal;
pub mod trail;
pub mod watch_lists;

pub use assignment::{AssignmentStore, SatValue};
pub use bcp::PropagationOutcome;
pub use clause::{ClauseStorage, SatClauseError};
pub use database::{AttachOutcome, SatCore, SatCoreError};
pub use literal::{SatLiteral, SatLiteralError, SatVar};
pub use trail::{SatTrail, SatTrailError};
pub use watch_lists::{WatchListError, WatchLists};
