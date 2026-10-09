// CEP:FILE: hot/sat/mod.rs
// CEP:WHAT: SAT engine module: literals, assignment store, trail, intrusive watch lists, clause database, the Boolean constraint propagation engine, CDCL conflict analysis, the VSIDS decision heuristic with phase saving, restart scheduling, and the integrated CDCL solver.
// CEP:WHY: Design section 11 (components S1-S24): MAPT owns its SAT engine with no FFI boundary to the ATP engine; Phase 1 delivered the data structures and BCP, Phase 2 delivers conflict analysis (first UIP, minimization, LBD), learning, backjumping, VSIDS, phase saving, restarts, and the search loop that composes them (design 26 build order).
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: all state lives in the shared arena, sized by the variable count at initialization.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests unit/hot/sat_bcp_test.rs, unit/hot/sat_cdcl_test.rs, unit/hot/sat_vsids_test.rs, unit/hot/sat_restart_test.rs, unit/hot/sat_solver_test.rs; property/bcp_property_test.rs and property/cdcl_property_test.rs; fuzz/cdcl_fuzz_test.rs; bench CEP-BENCH-0005 and CEP-BENCH-0009.
// CEP:SECURITY: variable indices and clause offsets are bounds-checked.

pub mod assignment;
pub mod bcp;
pub mod cdcl;
pub mod clause;
pub mod database;
pub mod literal;
pub mod restart;
pub mod solver;
pub mod trail;
pub mod vsids;
pub mod watch_lists;

pub use assignment::{AssignmentStore, SatValue};
pub use bcp::PropagationOutcome;
pub use cdcl::{AnalysisOutcome, CdclError, ConflictAnalyzer};
pub use clause::{ClauseStorage, SatClauseError};
pub use database::{AttachOutcome, SatCore, SatCoreError};
pub use literal::{SatLiteral, SatLiteralError, SatVar};
pub use restart::{RestartPolicy, RestartScheduler};
pub use solver::{CdclSolver, SolveResult};
pub use trail::{SatTrail, SatTrailError};
pub use vsids::{PhaseTable, VsidsError, VsidsHeap};
pub use watch_lists::{WatchListError, WatchLists};
