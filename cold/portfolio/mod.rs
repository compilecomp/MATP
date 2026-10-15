// CEP:FILE: cold/portfolio/mod.rs
// CEP:WHAT: The portfolio module (design 19): the manager that runs multiple search strategies in parallel over their own arenas with clause sharing, work stealing, first-to-finish result aggregation, and graceful shutdown.
// CEP:WHY: Design 26 Phase 4 and ticket CEP-1008; the CEP-1 layer owns the threads (CEP&CC 9.29 control-plane concurrency), the lock-free structures' storage (design 19.2/19.3), and the wall-clock slice deadlines (the CEP-1005 clock-free hot callback discipline).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: the problem encoding's declaration lists are the symbol-id contract (Spec 13 section 4).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs; property/concurrency_property_test.rs::portfolio_first_theorem_is_sound.
// CEP:SECURITY: bounded threads and storage; validated imports.
// CEP:HPC-DETERMINISM: single-worker runs are deterministic; multi-worker selection is scheduling-dependent (design 19.5) with independently checkable proofs.

pub mod manager;

pub use manager::{
    run_portfolio, PortfolioConfig, PortfolioError, PortfolioResult, ProblemEncoding, SortSpec,
    SymbolSpec, WorkerPlan, WorkerReport,
};
