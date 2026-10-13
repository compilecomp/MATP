// CEP:FILE: hot/sat/mod.rs
// CEP:WHAT: SAT engine module: literals, assignment store, trail, intrusive watch lists, clause database, the Boolean constraint propagation engine, CDCL conflict analysis, the VSIDS decision heuristic with phase saving, restart scheduling, the integrated CDCL solver, the enumerable clause registry with the learnt-deletion policy, the DRAT proof recorder, and SAT preprocessing (subsumption, self-subsumption, tautology and duplicate removal, vivification).
// CEP:WHY: Design section 11 (components S1-S43): MAPT owns its SAT engine with no FFI boundary to the ATP engine; Phase 1 delivered the data structures and BCP, Phase 2 delivered conflict analysis (first UIP, minimization, LBD), learning, backjumping, VSIDS, phase saving, restarts, and the search loop, and Phase 3 delivers the enumerable database with deletion (S4/S24-S26, CEP-1003), assumption-based incremental solving with failed cores (S38-S40), DRAT proof recording (S41/S42), and preprocessing (S30/S33/S34/S36) per the design 26 Phase 3 build order.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: all state lives in the shared arena, sized by the variable count at initialization.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit tests unit/hot/sat_bcp_test.rs, unit/hot/sat_cdcl_test.rs, unit/hot/sat_vsids_test.rs, unit/hot/sat_restart_test.rs, unit/hot/sat_solver_test.rs, unit/hot/sat_registry_test.rs, unit/hot/sat_proof_test.rs, unit/hot/sat_assumptions_test.rs, unit/hot/sat_preprocess_test.rs; property/bcp_property_test.rs, property/cdcl_property_test.rs, property/sat_incremental_property_test.rs, property/sat_preprocess_property_test.rs; fuzz/cdcl_fuzz_test.rs; bench CEP-BENCH-0005, CEP-BENCH-0009, and CEP-BENCH-0013.
// CEP:SECURITY: variable indices and clause offsets are bounds-checked.

pub mod assignment;
pub mod bcp;
pub mod cdcl;
pub mod clause;
pub mod database;
pub mod literal;
pub mod preprocess;
pub mod proof;
pub mod registry;
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
pub use preprocess::{SimplifyStats, SimplifyStatus};
pub use proof::{ProofError, ProofRecorder, ProofStep, ProofStepKind};
pub use registry::{ClauseRegistry, RegistryEntry, RegistryError};
pub use restart::{RestartPolicy, RestartScheduler};
pub use solver::{AssumptionOutcome, CdclSolver, SolveResult, SolverOptions};
pub use trail::{SatTrail, SatTrailError};
pub use vsids::{PhaseTable, VsidsError, VsidsHeap};
pub use watch_lists::{WatchListError, WatchLists};
