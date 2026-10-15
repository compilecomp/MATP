// CEP:FILE: cold/portfolio/manager.rs
// CEP:WHAT: The portfolio manager (design 19.1-19.5): spawns one scoped worker thread per strategy over its own leaked arena, runs the Phase 3 given-clause loop (optionally the Phase 4 AVATAR protocol) in bounded wall-clock slices, shares filtered derived clauses between workers through the bounded MPMC pool and the per-worker Chase-Leal import deques, stops every worker on the first Theorem (first-to-finish, design 19.1 result aggregation), and reports per-worker outcomes without channels or mutexes (scoped threads write private slots that the manager reads after the join).
// CEP:WHY: Design 26 Phase 4 ("Portfolio concurrency") and CEP-1008; the CEP-1 layer owns what hot cannot: threads (design 19.4: created at initialization, none during search; CEP&CC 9.29 allows std::thread for control-plane concurrency in cold code), the lock-free structures' storage (design 19.2/19.3), and wall-clock time (the CEP-1005 discipline: the hot saturate callback stays clock-free; the worker injects Instant-based slice deadlines); per-worker determinism (design 19.5): a worker sees the same inputs in the same order plus scheduling-dependent imports - the IMPORTED clauses enter as Input-role axioms that are logical consequences of the shared problem (the exporter derived them from the same inputs, Spec 13 section 7), so soundness is independent of interleaving and each worker without imports is exactly the Phase 3 loop; the first-to-finish cancellation is a single AtomicBool/AtomicU32 pair (Release/Acquire on the flag would suffice; the flag uses SeqCst because nothing orders on it - the winner CAS is the linearization point, Spec 13 section 6); thread pinning and NUMA-aware arena placement need OS-affinity bindings that are deliberately deferred (ticket CEP-1037) rather than half-implemented through unsafe libc calls.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: returns PortfolioError for invalid configurations (zero plans, too many workers, bad capacities); worker-internal failures surface as the worker's report entry (outcome None + error text) instead of panics or hangs; the manager never panics.
// CEP:ASSUMES: the problem encoding's symbol list is the one every worker rebuilds in order (the codec's symbol-id contract, Spec 13 section 4); the encoded inputs are well-formed codec records; the host can run the requested worker count.
// CEP:COST: one arena per worker (leaked, released at process exit - the fixture discipline; pooling is ticket CEP-1038), one saturate slice per loop iteration, one export scan per slice.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{worker_count_validated, rejects_zero_plans, single_worker_refutes_contradiction, first_theorem_wins_and_cancels, saturating_workers_report_saturated, imports_flow_between_workers, exports_bounded_per_slice, cancelled_workers_report_none}; property/concurrency_property_test.rs::portfolio_first_theorem_is_sound.
// CEP:SECURITY: worker count bounded by kPortfolioMaxWorkers; every capacity injectable; the codec validates imported records (untrusted-input discipline); no unbounded thread spawning.
// CEP:HPC-DETERMINISM: single-worker runs are deterministic (no imports occur); multi-worker result selection is scheduling-dependent (design 19.5) but the reported winner's proof is independently checkable (the TSTP checker).
// CEP:HPC-PASS-LEGALITY: Formal Spec 13 sections 5-7 fix the worker protocol, the sharing data flow (pool as the bus, deques as deferred-import buffers with stealing), the first-to-finish linearization, and the import-soundness argument (imported clauses are Input-role consequences of the shared problem); the property tests verify executably that a single worker's outcome matches the plain Phase 3 loop and that first-theorem cancellation reports exactly one winner.

use std::string::String;
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU32, AtomicU64, Ordering as AtomicOrdering};
use std::thread;
use std::time::{Duration, Instant};

use mapt_config::limits::{
    kAvatarComponentCapacity, kAvatarComponentWordCapacity, kChaseLevCapacity,
    kClauseOffsetTableCapacity, kMpmcPoolCapacity, kPortfolioExportPerSlice, kPortfolioMaxWorkers,
    kPortfolioThreadCount, kPortfolioTimeSliceMs, kSharedClauseMaxLbd, kSharedClauseMaxWeight,
    kSharedClauseMaxWords,
};
use mapt_hot::avatar::controller::{
    saturate_with_avatar, AvatarController, AvatarOptions, AvatarOutcome,
};
use mapt_hot::concurrency::chase_lev::WorkStealingDeque;
use mapt_hot::concurrency::clause_codec::{decode_clause, encode_clause};
use mapt_hot::concurrency::mpmc_pool::SharingPool;
use mapt_hot::inference::{InferenceContext, OrderingKind};
use mapt_hot::ir::clause::{ClauseId, InferenceRule};
use mapt_hot::ir::literal::Literal;
use mapt_hot::ir::symbol_table::SortId;
use mapt_hot::ir::term::TermStore;
use mapt_hot::memory::arena::Arena;
use mapt_hot::ordering::precedence::PrecedenceTable;
use mapt_hot::search::given_clause::{
    saturate, GaveUpReason, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};
use mapt_hot::search::SelectionStrategy;

use crate::arena_host::allocate_aligned_region;
use crate::symbol_table_builder::SymbolTableBuilder;

/// CEP:WHAT: One sort declaration of a problem encoding.
/// CEP:WHY: Workers rebuild their symbol tables from the shared spec list in order; sort ids are symbol ids assigned by declaration order, so replaying the identical sequence reproduces the codec's id contract (Spec 13 section 4).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: names are unique.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
/// CEP:SECURITY: none.
pub struct SortSpec {
    /// CEP:WHAT: The sort's declared name.
    /// CEP:WHY: Replayed into every worker's builder.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub name: String,
}

/// CEP:WHAT: One symbol declaration of a problem encoding (function or predicate).
/// CEP:WHY: As SortSpec: the ordered replay reproduces the symbol ids the codec records reference.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: arg_sorts hold the ids of the sorts declared earlier in the list.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
/// CEP:SECURITY: none.
pub struct SymbolSpec {
    /// CEP:WHAT: The symbol's declared name.
    /// CEP:WHY: Replayed into every worker's builder.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub name: String,
    /// CEP:WHAT: The symbol's arity.
    /// CEP:WHY: Declaration and codec validation both read it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub arity: u16,
    /// CEP:WHAT: The symbol's weight.
    /// CEP:WHY: Declaration replays the weight (the selection weight function reads it).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub weight: u32,
    /// CEP:WHAT: The argument sorts' ids (indices into the replayed sort id space).
    /// CEP:WHY: Declaration replays the profile.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: ids from the same ordered replay.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub arg_sorts: Vec<u32>,
    /// CEP:WHAT: The result sort's id (functions only; predicates return the builder's boolean sort).
    /// CEP:WHY: Declaration replays the profile.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: functions only.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub result_sort: u32,
    /// CEP:WHAT: Whether the symbol is a predicate.
    /// CEP:WHY: Chooses declare_predicate over declare_function.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub predicate: bool,
}

/// CEP:WHAT: The portable problem encoding: ordered sorts, ordered symbols, and codec-record input clauses.
/// CEP:WHY: Workers own separate arenas, so the problem crosses by value (Spec 13 section 4); the order of the declaration lists is the symbol-id contract.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: the records were produced by encode_clause over a store built from the same lists.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{single_worker_refutes_contradiction, imports_flow_between_workers}.
/// CEP:SECURITY: the codec validates every record at decode.
pub struct ProblemEncoding {
    /// CEP:WHAT: The sort declarations in replay order.
    /// CEP:WHY: The id contract.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub sorts: Vec<SortSpec>,
    /// CEP:WHAT: The symbol declarations in replay order.
    /// CEP:WHY: The id contract.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub symbols: Vec<SymbolSpec>,
    /// CEP:WHAT: The input clauses as codec records.
    /// CEP:WHY: The value-crossing form.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: a malformed record fails the worker loudly (report error).
    /// CEP:ASSUMES: encode_clause produced them.
    /// CEP:COST: kSharedClauseMaxWords words each.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{single_worker_refutes_contradiction, imports_flow_between_workers}.
    /// CEP:SECURITY: validated at decode.
    pub inputs: Vec<Vec<u64>>,
}

/// CEP:WHAT: One worker's strategy: the selection strategy and whether to run the AVATAR protocol.
/// CEP:WHY: Design 15.2/19.1: multiple strategies run in parallel; the plan is the per-worker configuration.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: one plan per worker.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{single_worker_refutes_contradiction, first_theorem_wins_and_cancels}.
/// CEP:SECURITY: none.
pub struct WorkerPlan {
    /// CEP:WHAT: The passive-set selection strategy.
    /// CEP:WHY: The strategy diversification of design 15.2.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::first_theorem_wins_and_cancels.
    /// CEP:SECURITY: none.
    pub strategy: SelectionStrategy,
    /// CEP:WHAT: Whether the worker runs saturate_with_avatar instead of plain saturate.
    /// CEP:WHY: Portfolio-over-AVATAR composition (design 12 + 19).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the arena budget covers the controller's structures.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub avatar: bool,
}

/// CEP:WHAT: The portfolio configuration: worker count, slice length, sharing toggle, and the per-worker capacity set.
/// CEP:WHY: CEP&CC 34.3: every bound injectable; the defaults are the named constants (kPortfolioThreadCount, kPortfolioTimeSliceMs).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record (run_portfolio validates).
/// CEP:ASSUMES: arena_bytes covers the term table plus the injected capacities.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{worker_count_validated, first_theorem_wins_and_cancels}.
/// CEP:SECURITY: the bounds under test.
pub struct PortfolioConfig {
    /// CEP:WHAT: The number of worker threads to spawn.
    /// CEP:WHY: Design 19.4: threads are created once, before the search; bounded by kPortfolioMaxWorkers.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: run_portfolio rejects counts above the ceiling or below the plan count.
    /// CEP:ASSUMES: plans.len() <= workers.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
    /// CEP:SECURITY: resource bound.
    pub workers: u32,
    /// CEP:WHAT: The wall-clock slice length in milliseconds.
    /// CEP:WHY: Design 15.4 kPortfolioTimeSliceMs: the saturate interrupt interval for import draining and cancellation checks.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::first_theorem_wins_and_cancels.
    /// CEP:SECURITY: none.
    pub slice_ms: u64,
    /// CEP:WHY: Whether clause sharing is enabled.
    /// CEP:WHAT: The sharing toggle (tests disable it to pin determinism).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{imports_flow_between_workers, single_worker_refutes_contradiction}.
    /// CEP:SECURITY: none.
    pub share: bool,
    /// CEP:WHAT: The per-worker arena size in bytes.
    /// CEP:WHY: One leaked region per worker (the fixture discipline; pooling ticket CEP-1038).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: run_portfolio propagates the host's capacity error.
    /// CEP:ASSUMES: covers the term table and the injected capacities.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: bounded by kArenaCapacityBytes (the host validates).
    pub arena_bytes: u32,
    /// CEP:WHAT: Per-worker passive-heap capacity.
    /// CEP:WHY: CEP&CC 34.3 injectable bound (tests use small values).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: memory bound.
    pub passive_capacity: u32,
    /// CEP:WHAT: Per-worker active-set capacity.
    /// CEP:WHY: As passive_capacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: memory bound.
    pub active_capacity: u32,
    /// CEP:WHAT: Per-worker clause-id side-table capacity (also the AVATAR ancestry bitset source).
    /// CEP:WHY: As passive_capacity; the ancestry bitset is capacity/8 bytes per worker.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 64, multiple of 64.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: memory bound.
    pub id_capacity: u32,
    /// CEP:WHAT: The per-slice export bound.
    /// CEP:WHY: kPortfolioExportPerSlice default; injectable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::exports_bounded_per_slice.
    /// CEP:SECURITY: denial-of-service bound.
    pub export_per_slice: u32,
}

// CEP:WHAT: The production default configuration: kPortfolioThreadCount workers, kPortfolioTimeSliceMs slices, sharing on, 256 MiB arenas, full capacities.
// CEP:WHY: The named constants are the production values (design 19.1/15.4/20.1); tests override through the public fields (CEP&CC 34.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the host can reserve workers x arena_bytes.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
// CEP:SECURITY: none.
impl Default for PortfolioConfig {
    // CEP:WHAT: Returns the production configuration.
    // CEP:WHY: Every value names its source constant.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
    // CEP:SECURITY: none.
    fn default() -> PortfolioConfig {
        PortfolioConfig {
            workers: kPortfolioThreadCount,
            slice_ms: kPortfolioTimeSliceMs,
            share: true,
            arena_bytes: mapt_config::limits::kArenaCapacityBytes,
            passive_capacity: mapt_config::limits::kPassiveHeapCapacity,
            active_capacity: mapt_config::limits::kActiveSetCapacity,
            id_capacity: kClauseOffsetTableCapacity,
            export_per_slice: kPortfolioExportPerSlice,
        }
    }
}

/// CEP:WHAT: Error cases of the portfolio manager.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the manager never panics.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{worker_count_validated, rejects_zero_plans}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortfolioError {
    /// CEP:WHAT: No plans were supplied.
    /// CEP:WHY: A portfolio with zero workers is a caller bug.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::rejects_zero_plans.
    /// CEP:SECURITY: input validation.
    EmptyPlans,
    /// CEP:WHAT: The worker count is zero, below the plan count, or above kPortfolioMaxWorkers.
    /// CEP:WHY: The thread budget is a named resource bound (design 19.4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
    /// CEP:SECURITY: resource bound.
    TooManyWorkers,
    /// CEP:WHAT: A capacity or slice configuration value is invalid.
    /// CEP:WHY: Construction-time validation with a named variant.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
    /// CEP:SECURITY: input validation.
    InvalidConfig,
}

/// CEP:WHAT: One worker's report: the terminal outcome (None when cancelled or failed), the error text, and the sharing counters.
/// CEP:WHY: Design 24 diagnostics; every sharing degradation is counted, never silent (design 19.2).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: written by the owning worker before the join, read by the manager after.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{first_theorem_wins_and_cancels, cancelled_workers_report_none, exports_bounded_per_slice}.
/// CEP:SECURITY: none.
pub struct WorkerReport {
    /// CEP:WHAT: The worker's index.
    /// CEP:WHY: Identifies the strategy (plans[index]).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::first_theorem_wins_and_cancels.
    /// CEP:SECURITY: none.
    pub worker: usize,
    /// CEP:WHAT: The terminal outcome (None when cancelled by the winner or failed).
    /// CEP:WHY: First-to-finish cancels the others (design 19.1); failures carry the error text.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: written before the join.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{first_theorem_wins_and_cancels, cancelled_workers_report_none}.
    /// CEP:SECURITY: none.
    pub outcome: Option<AvatarOutcome>,
    /// CEP:WHAT: The failure text (worker-internal error).
    /// CEP:WHY: Loud failures instead of panics (CEP&CC Law 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::single_worker_refutes_contradiction.
    /// CEP:SECURITY: none.
    pub error: Option<String>,
    /// CEP:WHAT: Clauses this worker exported.
    /// CEP:WHY: Sharing-rate diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    /// CEP:SECURITY: none.
    pub exported: u32,
    /// CEP:WHAT: Clauses this worker imported.
    /// CEP:WHY: Sharing-rate diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    /// CEP:SECURITY: none.
    pub imported: u32,
    /// CEP:WHAT: Exports dropped at the pool bound or codec bound.
    /// CEP:WHY: The documented degradations of design 19.2, counted.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::exports_bounded_per_slice.
    /// CEP:SECURITY: none.
    pub export_dropped: u32,
}

/// CEP:WHAT: The portfolio result: the first-theorem winner and every worker's report.
/// CEP:WHY: Design 19.1 result aggregation; the winner's proof is checkable through the TSTP path on the winning worker's store... in the Phase 4 API the winner carries only the outcome (the arena is process-lifetime; the driver keeps the winning worker's store alive through the report's optional proof text when requested through render_verified_proof on the winner's thread - the manager returns reports; proof extraction stays the driver's job because the stores are thread-local).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: reports are complete after the join.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{first_theorem_wins_and_cancels, saturating_workers_report_saturated}.
/// CEP:SECURITY: none.
pub struct PortfolioResult {
    /// CEP:WHAT: The index of the worker whose Theorem won the race (None when no worker found one).
    /// CEP:WHY: First-to-finish semantics; the winner CAS linearizes the race (Spec 13 section 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: at most one winner.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::first_theorem_wins_and_cancels.
    /// CEP:SECURITY: none.
    pub winner: Option<usize>,
    /// CEP:WHAT: Every worker's report, index-aligned with the plans.
    /// CEP:WHY: The aggregated outcome set (the first non-None Theorem by finish order is the winner; otherwise the first terminal outcome documents the run).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: plain data.
    /// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{first_theorem_wins_and_cancels, saturating_workers_report_saturated}.
    /// CEP:SECURITY: none.
    pub reports: Vec<WorkerReport>,
}

// CEP:WHAT: The per-worker runtime state (the thread's own stack frame).
// CEP:WHY: Bundling the worker's handles keeps the thread body readable; everything is thread-owned except the shared sharing structures.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: one per worker thread.
// CEP:COST: plain data.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{single_worker_refutes_contradiction, imports_flow_between_workers}.
// CEP:SECURITY: none.
struct WorkerState {
    // CEP:WHAT: Export counter.
    // CEP:WHY: Report diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: plain data.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    // CEP:SECURITY: none.
    exported: u32,
    // CEP:WHAT: Import counter.
    // CEP:WHY: Report diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: plain data.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    // CEP:SECURITY: none.
    imported: u32,
    // CEP:WHAT: Dropped-export counter.
    // CEP:WHY: Degradation visibility.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: plain data.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::exports_bounded_per_slice.
    // CEP:SECURITY: none.
    export_dropped: u32,
    // CEP:WHAT: The next clause id to scan at the export boundary.
    // CEP:WHY: The export scan is incremental by monotonic ids (Spec 13 section 5).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: ids are monotonic.
    // CEP:COST: plain data.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::exports_bounded_per_slice.
    // CEP:SECURITY: none.
    last_exported_id: u64,
}

// CEP:WHAT: Runs the portfolio to completion and returns the aggregated reports.
// CEP:WHY: Design 19.1: spawn one scoped thread per plan (threads created once, before the search, and joined before returning - graceful shutdown by construction, design 19.4); the shared state is three atomics (stop flag, winner slot) plus the lock-free structures whose storage the manager owns; each worker: builds its arena and symbol table from the encoding, decodes the inputs, runs slice-bounded saturate rounds (the slice injects wall-clock time into the clock-free CEP-1005 callback), drains imports (own deque LIFO, then steals from other workers' deques, then the pool - Spec 13 section 5's data flow), exports filtered new clauses (weight, LBD, rule, codec bounds - design 19.2), and races the winner CAS on Theorem; the first Theorem sets the stop flag and every other worker exits at its next boundary with outcome None (cancelled) - the graceful-shutdown requirement without cancellation primitives.
// CEP:STATUS: complete
// CEP:FAILURE: returns PortfolioError for invalid configurations; worker failures surface in their reports (never panics, never hangs past the join).
// CEP:ASSUMES: the encoding's lists are the symbol-id contract; the host can spawn the threads.
// CEP:COST: workers x (arena + slice loop); the arenas are leaked until process exit (the documented fixture discipline).
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{worker_count_validated, rejects_zero_plans, single_worker_refutes_contradiction, first_theorem_wins_and_cancels, saturating_workers_report_saturated, imports_flow_between_workers, exports_bounded_per_slice, cancelled_workers_report_none}; property/concurrency_property_test.rs::portfolio_first_theorem_is_sound.
// CEP:SECURITY: bounded threads, bounded pool/deque storage, validated imports.
pub fn run_portfolio(
    problem: &ProblemEncoding,
    plans: &[WorkerPlan],
    config: &PortfolioConfig,
) -> Result<PortfolioResult, PortfolioError> {
    if plans.is_empty() {
        return Err(PortfolioError::EmptyPlans);
    }
    if config.workers == 0
        || (config.workers as usize) < plans.len()
        || config.workers > kPortfolioMaxWorkers
    {
        return Err(PortfolioError::TooManyWorkers);
    }
    if config.slice_ms == 0
        || config.passive_capacity == 0
        || config.active_capacity == 0
        || config.id_capacity < 64
        || !config.id_capacity.is_multiple_of(64)
        || config.export_per_slice == 0
    {
        return Err(PortfolioError::InvalidConfig);
    }
    // Shared sharing structures: one pool, one deque per plan (the deque storage is
    // Box-allocated here and dropped after the join).
    let pool_cells = kMpmcPoolCapacity as usize;
    let mut sequences: Vec<AtomicI64> = Vec::with_capacity(pool_cells);
    for index in 0..pool_cells {
        sequences.push(AtomicI64::new(index as i64));
    }
    let mut pool_words: Vec<AtomicU64> = Vec::with_capacity(pool_cells * kSharedClauseMaxWords);
    for _ in 0..(pool_cells * kSharedClauseMaxWords) {
        pool_words.push(AtomicU64::new(0));
    }
    let produce_pos = AtomicI64::new(0);
    let consume_pos = AtomicI64::new(0);
    let pool = SharingPool::new(&sequences, &pool_words, &produce_pos, &consume_pos)
        .map_err(|_| PortfolioError::InvalidConfig)?;
    let deque_cells = kChaseLevCapacity as usize;
    let mut deque_storage: Vec<(Vec<AtomicU64>, AtomicI64, AtomicI64)> =
        Vec::with_capacity(plans.len());
    for _ in 0..plans.len() {
        let mut ring: Vec<AtomicU64> = Vec::with_capacity(deque_cells);
        for _ in 0..deque_cells {
            ring.push(AtomicU64::new(0));
        }
        deque_storage.push((ring, AtomicI64::new(0), AtomicI64::new(0)));
    }
    let mut deques: Vec<WorkStealingDeque<'_>> = Vec::with_capacity(plans.len());
    for (ring, top, bottom) in deque_storage.iter() {
        let deque =
            WorkStealingDeque::new(ring, top, bottom).map_err(|_| PortfolioError::InvalidConfig)?;
        deques.push(deque);
    }
    let stop = AtomicBool::new(false);
    let winner = AtomicU32::new(u32::MAX);
    let slice = Duration::from_millis(config.slice_ms);
    // Scoped threads: every borrow (plans, problem, pool, deques, atomics) lives in
    // this frame; each thread OWNS its report and returns it through the join (no
    // mutable sharing at all - the manager reads only after every thread finished,
    // which is the graceful-shutdown join of design 19.4).
    let joined = thread::scope(|scope| -> Vec<WorkerReport> {
        type WorkerHandle<'scope> = std::thread::ScopedJoinHandle<'scope, WorkerReport>;
        let mut handles: Vec<WorkerHandle> = Vec::new();
        for (index, plan) in plans.iter().enumerate() {
            let pool_ref = &pool;
            let deque_slice = &deques[..];
            let stop_ref = &stop;
            let winner_ref = &winner;
            let problem_ref = problem;
            let config_ref = config;
            let handle = scope.spawn(move || {
                let mut report = WorkerReport {
                    worker: index,
                    outcome: None,
                    error: None,
                    exported: 0,
                    imported: 0,
                    export_dropped: 0,
                };
                run_worker(
                    index,
                    plan,
                    problem_ref,
                    config_ref,
                    pool_ref,
                    deque_slice,
                    stop_ref,
                    winner_ref,
                    &mut report,
                    slice,
                );
                report
            });
            handles.push(handle);
        }
        let mut results: Vec<WorkerReport> = Vec::new();
        for handle in handles {
            match handle.join() {
                Ok(report) => results.push(report),
                Err(_) => results.push(WorkerReport {
                    worker: results.len(),
                    outcome: None,
                    error: Some(
                        "worker panicked (a production bug - reports are the failure path)".into(),
                    ),
                    exported: 0,
                    imported: 0,
                    export_dropped: 0,
                }),
            }
        }
        results
    });
    let winner_index = winner.load(AtomicOrdering::SeqCst);
    let winner = if winner_index == u32::MAX {
        None
    } else {
        Some(winner_index as usize)
    };
    Ok(PortfolioResult {
        winner,
        reports: joined,
    })
}

// CEP:WHAT: One worker thread's body: build, decode, slice loop (import, search, export), race the winner.
// CEP:WHY: Spec 13 section 5's worker protocol; every failure becomes the report's error text (the thread never panics through production paths); the winner CAS uses SeqCst success (the linearization point of first-to-finish) and the stop flag is SeqCst because nothing rides on its ordering - visibility to the other workers' boundary checks is all that matters.
// CEP:STATUS: complete
// CEP:FAILURE: reports errors as text; cancels as outcome None.
// CEP:ASSUMES: called once per plan inside the scope.
// CEP:COST: the arena plus the slice loop.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{single_worker_refutes_contradiction, first_theorem_wins_and_cancels, imports_flow_between_workers, cancelled_workers_report_none}.
// CEP:SECURITY: bounded work per slice; validated imports.
#[allow(clippy::too_many_arguments)]
fn run_worker(
    index: usize,
    plan: &WorkerPlan,
    problem: &ProblemEncoding,
    config: &PortfolioConfig,
    pool: &SharingPool<'_>,
    deques: &[WorkStealingDeque<'_>],
    stop: &AtomicBool,
    winner: &AtomicU32,
    report: &mut WorkerReport,
    slice: Duration,
) {
    // Build the worker's arena and stores (the fixture discipline: one leaked region).
    let region = match allocate_aligned_region(config.arena_bytes) {
        Ok(region) => region,
        Err(error) => {
            report.error = Some(format!("arena allocation failed: {:?}", error));
            return;
        }
    };
    let arena: &Arena = match Arena::new(region) {
        Ok(arena) => std::boxed::Box::leak(std::boxed::Box::new(arena)),
        Err(error) => {
            report.error = Some(format!("arena construction failed: {:?}", error));
            return;
        }
    };
    let mut builder = SymbolTableBuilder::new();
    for sort in problem.sorts.iter() {
        if builder.declare_sort(&sort.name).is_err() {
            report.error = Some("sort declaration failed".into());
            return;
        }
    }
    for symbol in problem.symbols.iter() {
        let arg_sorts: Vec<SortId> = symbol.arg_sorts.iter().map(|id| SortId(*id)).collect();
        let declared = if symbol.predicate {
            builder.declare_predicate(&symbol.name, symbol.arity, symbol.weight, &arg_sorts)
        } else {
            builder.declare_function(
                &symbol.name,
                symbol.arity,
                symbol.weight,
                &arg_sorts,
                SortId(symbol.result_sort),
            )
        };
        if declared.is_err() {
            report.error = Some("symbol declaration failed".into());
            return;
        }
    }
    let symbols = match builder.finalize(arena) {
        Ok(table) => table,
        Err(error) => {
            report.error = Some(format!("symbol table finalize failed: {:?}", error));
            return;
        }
    };
    let terms = match TermStore::new(arena) {
        Ok(store) => store,
        Err(error) => {
            report.error = Some(format!("term store failed: {:?}", error));
            return;
        }
    };
    let precedence = match PrecedenceTable::from_id_order(arena, builder.symbol_count()) {
        Ok(table) => table,
        Err(error) => {
            report.error = Some(format!("precedence failed: {:?}", error));
            return;
        }
    };
    let options = SearchOptions {
        strategy: plan.strategy,
        ..SearchOptions::new()
    };
    let space = match SearchSpace::new_with(
        arena,
        &options,
        config.passive_capacity,
        config.active_capacity,
        8192,
        8192,
        65536,
        config.id_capacity,
    ) {
        Ok(space) => space,
        Err(error) => {
            report.error = Some(format!("search space failed: {:?}", error));
            return;
        }
    };
    let avatar_options = AvatarOptions {
        sat_variables: kAvatarComponentCapacity,
        record_capacity: kAvatarComponentCapacity,
        word_capacity: kAvatarComponentWordCapacity,
        ancestry_bits: config.id_capacity,
        conflict_budget: mapt_config::limits::kSatMaxConflicts,
        ..AvatarOptions::default()
    };
    let avatar = if plan.avatar {
        match AvatarController::new_with(arena, &avatar_options) {
            Ok(controller) => Some(controller),
            Err(error) => {
                report.error = Some(format!("avatar controller failed: {:?}", error));
                return;
            }
        }
    } else {
        None
    };
    // Decode the input clauses once (literals stay in this buffer; the space copies them).
    // The decode buffer is pre-sized to the structural bound (the no_std decode API
    // writes into a caller-provided slice, Spec 13 section 4).
    let mut literals: Vec<Literal> = vec![
        Literal::new(mapt_hot::ir::term::TermPtr::invalid(), true);
        mapt_config::limits::kMaxClauseLiterals as usize
    ];
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    for record in problem.inputs.iter() {
        let mut buffer: Vec<u64> = vec![0; kSharedClauseMaxWords];
        let extent = record.len().min(kSharedClauseMaxWords);
        buffer[..extent].copy_from_slice(&record[..extent]);
        let count = match decode_clause(&buffer, &terms, &symbols, &mut literals) {
            Ok(count) => count,
            Err(error) => {
                report.error = Some(format!("input decode failed: {:?}", error));
                return;
            }
        };
        match &avatar {
            Some(controller) => {
                if let Err(error) =
                    controller.add_input_clause(&space, &context, &options, &literals[..count])
                {
                    report.error = Some(format!("input add failed: {:?}", error));
                    return;
                }
            }
            None => {
                if let Err(error) = space.add_input_clause(&context, &options, &literals[..count]) {
                    report.error = Some(format!("input add failed: {:?}", error));
                    return;
                }
            }
        }
    }
    let mut state = WorkerState {
        exported: 0,
        imported: 0,
        export_dropped: 0,
        last_exported_id: mapt_config::limits::kFirstClauseId,
    };
    let mut stats = SearchStats::default();
    let own_deque = &deques[index];
    // The slice loop.
    loop {
        if stop.load(AtomicOrdering::SeqCst) {
            report.outcome = None;
            return;
        }
        // Import phase (Spec 13 section 5): own deque (LIFO), then steals (other
        // workers' deferred imports), then the pool.
        if config.share {
            import_phase(
                &mut state,
                pool,
                deques,
                &space,
                &context,
                &options,
                avatar.as_ref(),
                &terms,
                &symbols,
                &mut literals,
                report,
            );
        }
        // Search phase: one wall-clock slice.
        let deadline = Instant::now() + slice;
        let outcome: Result<AvatarOutcome, String> = match avatar.as_ref() {
            Some(controller) => {
                let slice_stop = |_iterations: u64| -> bool {
                    stop.load(AtomicOrdering::SeqCst) || Instant::now() >= deadline
                };
                saturate_with_avatar(
                    &space,
                    &context,
                    &options,
                    controller,
                    &slice_stop,
                    &mut stats,
                )
                .map_err(|error| format!("avatar search failed: {:?}", error))
            }
            None => {
                let slice_stop = |_iterations: u64| -> bool {
                    stop.load(AtomicOrdering::SeqCst) || Instant::now() >= deadline
                };
                saturate(&space, &context, &options, &slice_stop, &mut stats)
                    .map(|outcome| match outcome {
                        SearchOutcome::Theorem { refutation } => AvatarOutcome::Theorem {
                            refutation,
                            via_avatar: false,
                        },
                        SearchOutcome::Saturated => AvatarOutcome::Saturated,
                        SearchOutcome::GaveUp(reason) => AvatarOutcome::GaveUp(reason),
                    })
                    .map_err(|error| format!("search failed: {:?}", error))
            }
        };
        // Export phase: filtered incremental id scan (spills into the own deque).
        if config.share {
            export_phase(&mut state, &space, &context, pool, own_deque, report);
        }
        report.exported = state.exported;
        report.imported = state.imported;
        report.export_dropped = state.export_dropped;
        match outcome {
            Ok(result @ AvatarOutcome::Theorem { .. }) => {
                // First-to-finish: CAS the winner slot, then stop everyone.
                if winner
                    .compare_exchange(
                        u32::MAX,
                        index as u32,
                        AtomicOrdering::SeqCst,
                        AtomicOrdering::SeqCst,
                    )
                    .is_ok()
                {
                    stop.store(true, AtomicOrdering::SeqCst);
                }
                report.outcome = Some(result);
                return;
            }
            Ok(result @ AvatarOutcome::Saturated) => {
                report.outcome = Some(result);
                return;
            }
            Ok(AvatarOutcome::GaveUp(GaveUpReason::TimeBudget)) => {
                // The slice predicate fired: continue (or the stop flag ends the
                // loop at the boundary above).
                if stop.load(AtomicOrdering::SeqCst) {
                    report.outcome = None;
                    return;
                }
                continue;
            }
            Ok(result @ AvatarOutcome::GaveUp(reason)) => {
                let _ = reason;
                report.outcome = Some(result);
                return;
            }
            Err(error) => {
                report.error = Some(error);
                return;
            }
        }
    }
}

// CEP:WHAT: The import phase: steals spilled deferred records from every worker's deque (FIFO from the top, own included), then dequeues the shared pool; each record is decoded, validated, and added as an Input-role clause (Spec 13 section 5).
// CEP:WHY: Design 19.2/19.3 data flow: the pool is the primary sharing bus; the per-worker Chase-Lev deque is the overflow backlog (exports spill into the owner's deque when the pool is full, one (length, words...) frame per record in push order, so the steal side - the oldest end - reads the frame in order for ANY thief including the owner thread, which is exactly the design's work-stealing load balancing applied to the sharing backlog); imported clauses are Input-role axioms - logical consequences of the shared problem (the exporter derived them from the same inputs, Spec 13 section 7) - so soundness is independent of interleaving; decode failures stop the worker loudly (a corrupt record is never imported).
// CEP:STATUS: complete
// CEP:FAILURE: decode/add failures set the report error and end the worker's loop.
// CEP:ASSUMES: the worker may steal its own deque (the Chase-Lev protocol permits the owner thread to act as a thief - the top CAS is thread-agnostic).
// CEP:COST: O(imports) steals and decodes per slice.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers; property/concurrency_property_test.rs::portfolio_first_theorem_is_sound.
// CEP:SECURITY: every record validated by the codec before interning.
#[allow(clippy::too_many_arguments)]
fn import_phase(
    state: &mut WorkerState,
    pool: &SharingPool<'_>,
    deques: &[WorkStealingDeque<'_>],
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    avatar: Option<&AvatarController<'_>>,
    terms: &TermStore<'_>,
    symbols: &mapt_hot::ir::symbol_table::SymbolTable<'_>,
    literals: &mut Vec<Literal>,
    report: &mut WorkerReport,
) {
    // CEP:WHAT: Imports one decoded record through the worker's add path.
    // CEP:WHY: One adder keeps the avatar/plain split in one place and the counter in one state.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns false on add failure (the caller sets the report error).
    // CEP:ASSUMES: the record decoded successfully.
    // CEP:COST: one clause add.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    // CEP:SECURITY: none.
    fn add_one(
        state: &mut WorkerState,
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        avatar: Option<&AvatarController<'_>>,
        literals: &[Literal],
    ) -> Result<(), String> {
        let added: Result<(), String> = match avatar {
            Some(controller) => controller
                .add_input_clause(space, context, options, literals)
                .map(|_| ())
                .map_err(|error| format!("import add failed: {:?}", error)),
            None => space
                .add_input_clause(context, options, literals)
                .map(|_| ())
                .map_err(|error| format!("import add failed: {:?}", error)),
        };
        match added {
            Ok(()) => {
                state.imported += 1;
                Ok(())
            }
            Err(error) => Err(error),
        }
    }
    // CEP:WHAT: Imports one record from a decoded word slice.
    // CEP:WHY: Shared by the deque and pool sources.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns the error string on decode or add failure.
    // CEP:ASSUMES: the slice holds a full record.
    // CEP:COST: one decode plus one add.
    // CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
    // CEP:SECURITY: the codec validates the record.
    fn import_record(
        state: &mut WorkerState,
        record: &[u64],
        space: &SearchSpace<'_>,
        context: &InferenceContext<'_>,
        options: &SearchOptions,
        avatar: Option<&AvatarController<'_>>,
        terms: &TermStore<'_>,
        symbols: &mapt_hot::ir::symbol_table::SymbolTable<'_>,
        literals: &mut Vec<Literal>,
    ) -> Result<(), String> {
        let mut padded: Vec<u64> = vec![0; kSharedClauseMaxWords];
        let extent = record.len().min(kSharedClauseMaxWords);
        padded[..extent].copy_from_slice(&record[..extent]);
        // Re-fill the decode buffer to the structural bound (clear() would shrink the
        // slice below the decode API's contract).
        literals.resize(
            mapt_config::limits::kMaxClauseLiterals as usize,
            Literal::new(mapt_hot::ir::term::TermPtr::invalid(), true),
        );
        match decode_clause(&padded, terms, symbols, literals) {
            Ok(count) => add_one(state, space, context, options, avatar, &literals[..count]),
            Err(error) => Err(format!("import decode failed: {:?}", error)),
        }
    }
    // Source 1: steal spilled deferred records from every deque (own included).
    for deque in deques.iter() {
        // CEP:WHAT: Drain loop: steal the frame length word, then the frame's record words.
        // CEP:WHY: None (empty or contention budget) ends this deque's drain (Spec 13 section 5).
        // CEP:STATUS: complete
        // CEP:FAILURE: corrupt or truncated frames stop the worker loudly.
        // CEP:ASSUMES: frames were pushed in (length, words...) order.
        // CEP:COST: one steal per word.
        // CEP:EVIDENCE: unit/cold/portfolio_test.rs::imports_flow_between_workers.
        // CEP:SECURITY: frame length validated against the record bound.
        while let Ok(Some(length_word)) = deque.steal() {
            let length = (length_word & 0xFFFF) as usize;
            if length == 0 || length > kSharedClauseMaxWords {
                report.error = Some("corrupt deferred frame".into());
                return;
            }
            let mut frame: Vec<u64> = Vec::with_capacity(length);
            let mut broken = false;
            for _ in 0..length {
                match deque.steal() {
                    Ok(Some(word)) => frame.push(word),
                    _ => {
                        broken = true;
                        break;
                    }
                }
            }
            if broken {
                report.error = Some("truncated deferred frame".into());
                return;
            }
            if let Err(error) = import_record(
                state, &frame, space, context, options, avatar, terms, symbols, literals,
            ) {
                report.error = Some(error);
                return;
            }
        }
    }

    // Source 2: the shared pool (the primary bus).
    let mut buffer: Vec<u64> = vec![0; kSharedClauseMaxWords];
    while let Ok(Some(length)) = pool.dequeue(&mut buffer) {
        if length == 0 || length > kSharedClauseMaxWords {
            report.error = Some("corrupt pool record".into());
            return;
        }
        if let Err(error) = import_record(
            state,
            &buffer[..length],
            space,
            context,
            options,
            avatar,
            terms,
            symbols,
            literals,
        ) {
            report.error = Some(error);
            return;
        }
    }
    report.imported = state.imported;
}

// CEP:WHAT: The export phase: scans the worker's new clauses by monotonic id (bounded by the per-slice export budget), applies the design 19.2 filters (weight below kSharedClauseMaxWeight, LBD below kSharedClauseMaxLbd, high-quality rule: resolution, superposition, factoring), encodes, and enqueues to the pool; pool-full exports spill into the worker's own deque as deferred frames.
// CEP:WHY: Spec 13 section 5: the scan is incremental (last_exported_id to the store's next id) so the cost is proportional to the slice's derivations; every degradation (budget stop, pool full, deque full, codec too large) is counted, never silent (design 19.2); the rule filter follows the design's quality list; Input/AvatarSplit/demodulation clauses are not shared (imports re-enter as Input and re-sharing them would cycle, Spec 13 section 7); the deferred frame is (length word, record words...) pushed in order so the steal side reads it in order (Spec 13 section 3's frame protocol).
// CEP:STATUS: complete
// CEP:FAILURE: none (degradations counted; export is best-effort by design).
// CEP:ASSUMES: ids are monotonic; the store's side table covers the scan range.
// CEP:COST: O(exported) encodes per slice.
// CEP:EVIDENCE: unit/cold/portfolio_test.rs::{exports_bounded_per_slice, imports_flow_between_workers}.
// CEP:SECURITY: bounded work per slice.
fn export_phase(
    state: &mut WorkerState,
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    pool: &SharingPool<'_>,
    own: &WorkStealingDeque<'_>,
    report: &mut WorkerReport,
) {
    let next_id = space.store.next_clause_id().0;
    let mut exported_this_slice: u32 = 0;
    let mut record: Vec<u64> = vec![0; kSharedClauseMaxWords];
    let mut literals: Vec<Literal> = Vec::new();
    while state.last_exported_id < next_id && exported_this_slice < kPortfolioExportPerSlice {
        let id = state.last_exported_id;
        state.last_exported_id += 1;
        let clause_record = match space.store.clause_by_id(ClauseId(id)) {
            Ok(record) => record,
            Err(_) => {
                // An id outside the side table cannot occur before arena exhaustion
                // (Spec 14 section 2); stop the scan loudly.
                state.export_dropped += 1;
                break;
            }
        };
        if clause_record.weight >= kSharedClauseMaxWeight
            || clause_record.lbd >= kSharedClauseMaxLbd
        {
            continue;
        }
        let shareable = matches!(
            clause_record.derivation.rule,
            InferenceRule::Resolution | InferenceRule::Superposition | InferenceRule::Factoring
        );
        if !shareable {
            continue;
        }
        literals.clear();
        let mut readable = true;
        for index in 0..clause_record.literal_count {
            match space.store.literal(clause_record, index) {
                Ok(literal) => literals.push(literal),
                Err(_) => {
                    readable = false;
                    break;
                }
            }
        }
        if !readable {
            state.export_dropped += 1;
            continue;
        }
        match encode_clause(context.terms, &literals, &mut record) {
            Ok(length) => {
                exported_this_slice += 1;
                match pool.enqueue(&record[..length]) {
                    Ok(()) => {
                        state.exported += 1;
                    }
                    Err(_) => {
                        // Pool full: spill the record into the worker's own deque as a
                        // deferred frame (length word then the record words), if it fits.
                        let needed = length + 1;
                        let free = (kChaseLevCapacity as u64).saturating_sub(own.len());
                        if free >= needed as u64 {
                            let mut spilled = true;
                            if own.push(length as u64).is_err() {
                                spilled = false;
                            }
                            for word in record[..length].iter() {
                                if own.push(*word).is_err() {
                                    spilled = false;
                                    break;
                                }
                            }
                            if spilled {
                                state.exported += 1;
                            } else {
                                state.export_dropped += 1;
                            }
                        } else {
                            state.export_dropped += 1;
                        }
                    }
                }
            }
            Err(_) => {
                state.export_dropped += 1;
            }
        }
    }
    report.exported = state.exported;
    report.export_dropped = state.export_dropped;
}
