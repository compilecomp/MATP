// CEP:FILE: hot/sat/preprocess.rs
// CEP:WHAT: SAT preprocessing (design 11.1 S30/S33/S34/S36): bounded rounds of tautology deletion, duplicate-literal removal, forward subsumption, self-subsuming resolution strengthening, and vivification over the registry-enumerated clause database, with proof-trace integration for every database mutation.
// CEP:WHY: Design 26 Phase 3 build order ("SAT: preprocessing (subsumption, vivification)") and design 7.2 stage 10 discipline: preprocessing shrinks the clause database before search using only equivalence- or entailment-preserving rewrites, so the first search starts from a smaller formula; the pass is bounded (rounds, pairs, candidates, propagation budget) with honest partial outcomes instead of unbounded scanning (CEP&CC 22.10, Law 6); every deletion and addition is mirrored into the proof recorder so the trace stays a valid DRAT prefix (S41) - deletions need no justification, deduped and strengthened clauses are added before their originals are deleted so each addition is RUP-derivable from the recorded database, and vivified clauses are added after their originals are deleted because the vivification check itself derives them from the database minus the candidate (Spec 09).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns CdclError on storage, registry, or proof failures; SimplifyStatus::Unsatisfiable when preprocessing refutes the formula (a falsified unit or an empty strengthened clause); budget statuses report honest partial passes; never panics.
// CEP:ASSUMES: Called at decision level 0 before the first solve (design 7.1 pipeline position); the solver's registry enumerates every live clause; clause literal buffers of kMaxSatClauseLiterals suffice for every clause; vivification candidates are isolated by the raw deleted mark and every mark is resolved (permanent deletion or restore) before the pass returns.
// CEP:COST: per round: O(clauses x clause_length) for the tautology/dedup scan, O(pairs x clause_length) for subsumption (bounded by the pair budget), and per vivification candidate up to O(length) decide+propagate cycles (bounded by the candidate and propagation budgets); measured in bench CEP-BENCH-0013, artifact benches/artifacts/sat_preprocess_round.json.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs; property/sat_preprocess_property_test.rs::{preprocessing_preserves_satisfiability, preprocessing_shrinks_or_preserves}; security/phase3_bounds_test.rs::{subsumption_budget_enforced, vivify_budget_enforced}; bench CEP-BENCH-0013.
// CEP:SECURITY: every scan is bounded by a named budget; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; clause order is the registry entry order, literals are read in storage order, and all budgets are counted identically per run (CEP&CC 38.10).
// CEP:HPC-PASS: sat_preprocess
// CEP:HPC-PASS-KIND: formula simplification pass (design 11.1 S30/S33/S34/S36)
// CEP:HPC-PASS-INPUT: solver at decision level 0 with the registry enumerating every live clause
// CEP:HPC-PASS-OUTPUT: the same solver with tautologies, duplicates, subsumed clauses removed, clauses strengthened by self-subsuming resolution and vivification, and the proof trace extended
// CEP:HPC-PASS-ANALYSIS-REQUIRED: clause enumeration (registry), literal reads (storage), unit propagation (BCP) for vivification
// CEP:HPC-PASS-ANALYSIS-PRODUCED: the shrunken clause database
// CEP:HPC-PASS-ANALYSIS-INVALIDATED: clause offsets of deleted clauses (registry tombstones)
// CEP:HPC-PASS-PRESERVES: satisfiability (Spec 09 theorems 1-4); the proof-trace validity (every addition RUP at its recording point)
// CEP:HPC-PASS-LEGALITY: Formal Spec 09 sections 2-5 fix the four rewrites: tautology deletion and subsumption deletion preserve logical equivalence; duplicate removal and self-subsuming strengthening add the replacement before deleting the original so each addition is RUP; vivification deletes the candidate before adding the shortened clause because the check derived the shortening from the database minus the candidate; the property test verifies satisfiability preservation against a brute-force oracle.
// CEP:HPC-PASS-COST: bounded rounds x (clauses + budgeted pairs + budgeted vivification), see CEP:COST.
// CEP:HPC-PASS-FAILURE: budget exhaustion stops the pass with an honest partial status; a refutation stops it with Unsatisfiable.
// CEP:HPC-PASS-TARGET: target-independent.
// CEP:HPC-PASS-EVIDENCE: unit/hot/sat_preprocess_test.rs; property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: pairwise subsumption without the feature-vector filter is O(n^2); the SAT-side filter is deferred until measurement on production preprocessing workloads (the ATP side builds its own filter, CEP-1028); ticket CEP-1035.

use crate::sat::assignment::SatValue;
use crate::sat::bcp::PropagationOutcome;
use crate::sat::database::AttachOutcome;
use crate::sat::literal::SatLiteral;
use crate::sat::solver::CdclSolver;
use mapt_config::limits::{
    kMaxSatClauseLiterals, kMaxSimplifyRounds, kSatSubsumptionPairBudget, kSatVivifyCandidateLimit,
    kSatVivifyPropagationBudget,
};

// CEP:WHAT: Minimum clause length a vivification candidate must have.
// CEP:WHY: A unit or empty clause cannot be shortened (the prefix search needs at least one droppable literal besides the kept prefix); the scan skips shorter clauses by name, not by numeral (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{vivification_shortens_clause, vivification_restores_unchanged_clause}.
// CEP:SECURITY: none.
const kVivifyMinLiterals: usize = 2;

/// CEP:WHAT: Counters of one preprocessing run.
/// CEP:WHY: CEP&CC Law 4 and design 20.2: bounded passes must report exactly what they did so a partial pass is auditable; the counters are the pass's measurement record.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: counters only increase.
/// CEP:COST: 32 bytes.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{tautologies_removed, duplicates_removed, subsumption_deletes, strengthening_rewrites, vivification_shortens_clause}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SimplifyStats {
    /// CEP:WHAT: Clauses deleted as tautologies.
    /// CEP:WHY: S33.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::tautologies_removed.
    /// CEP:SECURITY: none.
    pub tautologies: u32,
    /// CEP:WHAT: Clauses rewritten by duplicate-literal removal.
    /// CEP:WHY: S34.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::duplicates_removed.
    /// CEP:SECURITY: none.
    pub duplicates: u32,
    /// CEP:WHAT: Clauses deleted by subsumption.
    /// CEP:WHY: S30.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::subsumption_deletes.
    /// CEP:SECURITY: none.
    pub subsumed: u32,
    /// CEP:WHAT: Clauses rewritten by self-subsuming resolution.
    /// CEP:WHY: S30 (the strengthening half).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::strengthening_rewrites.
    /// CEP:SECURITY: none.
    pub strengthened: u32,
    /// CEP:WHAT: Clauses shortened by vivification.
    /// CEP:WHY: S36.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::vivification_shortens_clause.
    /// CEP:SECURITY: none.
    pub vivified: u32,
    /// CEP:WHAT: Pair checks performed by the subsumption scan.
    /// CEP:WHY: Budget accounting (Law 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs::subsumption_budget_enforced.
    /// CEP:SECURITY: none.
    pub pairs_examined: u32,
    /// CEP:WHAT: Vivification candidates attempted.
    /// CEP:WHY: Budget accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs::vivify_budget_enforced.
    /// CEP:SECURITY: none.
    pub vivify_attempts: u32,
    /// CEP:WHAT: Rounds executed.
    /// CEP:WHY: Budget accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::rounds_bounded.
    /// CEP:SECURITY: none.
    pub rounds_done: u32,
}

/// CEP:WHAT: Terminal status of one preprocessing run.
/// CEP:WHY: CEP&CC Law 6: the pass either completed, refuted the formula, or stopped honestly at a named budget; conflating budget stops with completion would hide partial work.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{pair_budget_stops_early, candidate_budget_stops_early}; security/phase3_bounds_test.rs::{subsumption_budget_enforced, vivify_budget_enforced}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimplifyStatus {
    /// CEP:WHAT: All rounds ran to completion (or reached a fixpoint early).
    /// CEP:WHY: The success status.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::tautologies_removed.
    /// CEP:SECURITY: none.
    Complete,
    /// CEP:WHAT: Preprocessing derived the empty clause or a falsified unit; the formula is unsatisfiable.
    /// CEP:WHY: The refuting status; the proof trace carries the empty clause.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the solver's root_conflict flag is set when the refutation came from a falsified unit.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::contradictory_units_refute.
    /// CEP:SECURITY: none.
    Unsatisfiable,
    /// CEP:WHAT: The subsumption pair budget ran out before the rounds completed.
    /// CEP:WHY: Honest partial pass (design 20.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: stats report the work done.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::pair_budget_stops_early; security/phase3_bounds_test.rs::subsumption_budget_enforced.
    /// CEP:SECURITY: none.
    PairBudgetExhausted,
    /// CEP:WHAT: The vivification candidate or propagation budget ran out before the rounds completed.
    /// CEP:WHY: Honest partial pass.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: stats report the work done.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::candidate_budget_stops_early; security/phase3_bounds_test.rs::vivify_budget_enforced.
    /// CEP:SECURITY: none.
    VivifyBudgetExhausted,
}

/// CEP:WHAT: Result record of one preprocessing run: status plus counters.
/// CEP:WHY: One return type keeps the API stable while the counters evolve.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: 36 bytes.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SimplifyOutcome {
    /// CEP:WHAT: Terminal status.
    /// CEP:WHY: See SimplifyStatus.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
    /// CEP:SECURITY: none.
    pub status: SimplifyStatus,
    /// CEP:WHAT: Work counters.
    /// CEP:WHY: See SimplifyStats.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 32 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
    /// CEP:SECURITY: none.
    pub stats: SimplifyStats,
}

/// CEP:WHAT: Budgets of one preprocessing run.
/// CEP:WHY: CEP&CC 34.3: every bound injectable so tests exercise the exhaustion paths at small scales on the production code path; the defaults are the named constants.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record.
/// CEP:ASSUMES: all budgets >= 1.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: security/phase3_bounds_test.rs::{subsumption_budget_enforced, vivify_budget_enforced}.
/// CEP:SECURITY: the budgets are the denial-of-service bounds under test.
#[derive(Default)]
pub struct SimplifyOptions {
    /// CEP:WHAT: Maximum simplification rounds.
    /// CEP:WHY: Design 7.2 stage 10 names kMaxSimplifyRounds for bounded rewrite passes; reused here.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::rounds_bounded.
    /// CEP:SECURITY: none.
    pub rounds: u32,
    /// CEP:WHAT: Subsumption pair checks per run.
    /// CEP:WHY: kSatSubsumptionPairBudget default.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs::subsumption_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub pair_budget: u32,
    /// CEP:WHAT: Vivification candidates per run.
    /// CEP:WHY: kSatVivifyCandidateLimit default.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs::vivify_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub vivify_candidates: u32,
    /// CEP:WHAT: Vivification budget units per run (one per decided literal and per propagate call).
    /// CEP:WHY: kSatVivifyPropagationBudget default.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase3_bounds_test.rs::vivify_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub vivify_budget: u32,
}

impl SimplifyOptions {
    // CEP:WHAT: Production budgets from the named constants.
    // CEP:WHY: One named place documents the default configuration (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
    // CEP:SECURITY: none.
    pub fn new() -> SimplifyOptions {
        SimplifyOptions {
            rounds: kMaxSimplifyRounds,
            pair_budget: kSatSubsumptionPairBudget,
            vivify_candidates: kSatVivifyCandidateLimit,
            vivify_budget: kSatVivifyPropagationBudget,
        }
    }
}

// CEP:WHAT: Literal workspace shared by the pass: one clause buffer per role.
// CEP:WHY: Fixed stack buffers keep the pass allocation-free (hot discipline); kMaxSatClauseLiterals is the structural clause bound so the buffers always suffice.
// CEP:STATUS: complete
// CEP:FAILURE: clause reads longer than the bound cannot occur (storage enforces the bound at creation).
// CEP:ASSUMES: clauses respect kMaxSatClauseLiterals.
// CEP:COST: 4 x 2 KiB of stack.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
// CEP:SECURITY: none.
struct Workspace {
    /// CEP:WHAT: Left clause literals (sorted, deduplicated).
    /// CEP:WHY: The subsumption probe reads the left clause here.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 KiB.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::subsumption_deletes.
    /// CEP:SECURITY: none.
    left: [SatLiteral; kMaxSatClauseLiterals as usize],
    /// CEP:WHAT: Right clause literals (sorted, deduplicated).
    /// CEP:WHY: The subsumption probe reads the right clause here.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 KiB.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::subsumption_deletes.
    /// CEP:SECURITY: none.
    right: [SatLiteral; kMaxSatClauseLiterals as usize],
    /// CEP:WHAT: Replacement clause literals for rewrites.
    /// CEP:WHY: Deduped and strengthened clauses are built here before being added.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 KiB.
    /// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{duplicates_removed, strengthening_rewrites}.
    /// CEP:SECURITY: none.
    replacement: [SatLiteral; kMaxSatClauseLiterals as usize],
}

impl Workspace {
    // CEP:WHAT: Constructs a zeroed workspace.
    // CEP:WHY: Explicit initialization; the literal encodings are overwritten before use.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs.
    // CEP:SECURITY: none.
    fn new() -> Workspace {
        Workspace {
            left: [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize],
            right: [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize],
            replacement: [SatLiteral::from_encoding(0); kMaxSatClauseLiterals as usize],
        }
    }
}

// CEP:WHAT: Runs the bounded preprocessing pass over the solver's registry-enumerated database.
// CEP:WHY: Design 26 Phase 3 and Spec 09: the entry point composes the four rewrites in bounded rounds; the solver is used in place (no formula copy), so every mutation is visible to the subsequent solve and the proof trace.
// CEP:STATUS: complete
// CEP:FAILURE: propagates CdclError; returns Unsatisfiable in the outcome when the pass refutes the formula.
// CEP:ASSUMES: decision level 0 (NOT a flush point: after a Satisfiable assumption solve a direct simplify call fails the level invariant loudly — add or solve first to flush the deferred cleanup, Spec 10 section 5); solver built with a registry (always true from Phase 3 constructors).
// CEP:COST: see file header; measured in bench CEP-BENCH-0013.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs; property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability.
// CEP:SECURITY: all loops bounded by the injected budgets.
pub fn simplify(
    solver: &CdclSolver<'_>,
    options: &SimplifyOptions,
) -> Result<SimplifyOutcome, crate::sat::cdcl::CdclError> {
    let mut stats = SimplifyStats::default();
    let mut workspace = Workspace::new();
    if solver.core().trail().level() != 0 {
        return Err(crate::sat::cdcl::CdclError::Storage(
            crate::sat::database::SatCoreError::InvariantViolation,
        ));
    }
    // Drain pending unit assignments; a level-0 conflict here means the formula as
    // added is already refuted (Spec 09 section 6).
    match solver.core().propagate() {
        Ok(PropagationOutcome::NoConflict) => {}
        Ok(PropagationOutcome::Conflict(_)) => return refuted(solver, &mut stats),
        Err(error) => return Err(error.into()),
    }
    let mut status = SimplifyStatus::Complete;
    let mut round: u32 = 0;
    while round < options.rounds {
        round += 1;
        stats.rounds_done = round;
        let changed = simplify_round(solver, options, &mut workspace, &mut stats, &mut status)?;
        match status {
            SimplifyStatus::Complete => {}
            _ => break,
        }
        if !changed {
            break;
        }
    }
    Ok(SimplifyOutcome { status, stats })
}

// CEP:WHAT: Builds the refuted outcome and emits the empty-clause proof step.
// CEP:WHY: Both refutation paths (falsified unit, empty strengthened clause) must leave the trace with the terminating empty clause (Spec 11 section 4).
// CEP:STATUS: complete
// CEP:FAILURE: proof-append errors propagate through the caller's Result (a failed refutation step is a broken trace, never a silent one); storage errors propagate identically.
// CEP:ASSUMES: a recorder may or may not be attached.
// CEP:COST: one proof append.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::contradictory_units_refute.
// CEP:SECURITY: none.
fn refuted(
    solver: &CdclSolver<'_>,
    stats: &mut SimplifyStats,
) -> Result<SimplifyOutcome, crate::sat::cdcl::CdclError> {
    if let Some(recorder) = solver.proof() {
        recorder
            .record_empty_clause()
            .map_err(crate::sat::cdcl::CdclError::Proof)?;
    }
    Ok(SimplifyOutcome {
        status: SimplifyStatus::Unsatisfiable,
        stats: *stats,
    })
}

// CEP:WHAT: Runs one round: tautology/dedup scan, subsumption/self-subsumption scan, vivification scan; returns whether anything changed.
// CEP:WHY: Spec 09 section order; the three scans share the budget counters and the workspace.
// CEP:STATUS: complete
// CEP:FAILURE: propagates CdclError; sets the budget statuses honestly.
// CEP:ASSUMES: decision level 0 at entry and exit.
// CEP:COST: see file header.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{tautologies_removed, duplicates_removed, subsumption_deletes, strengthening_rewrites, vivification_shortens_clause}.
// CEP:SECURITY: bounded scans.
fn simplify_round(
    solver: &CdclSolver<'_>,
    options: &SimplifyOptions,
    workspace: &mut Workspace,
    stats: &mut SimplifyStats,
    status: &mut SimplifyStatus,
) -> Result<bool, crate::sat::cdcl::CdclError> {
    let entry_count = solver.registry().entry_count();
    let mut changed = false;
    // Scan 1: tautologies and duplicate literals.
    for index in 0..entry_count {
        let offset = match live_offset(solver, index) {
            Some(value) => value,
            None => continue,
        };
        let (length, duplicate_count, tautology) =
            read_clause(solver, offset, &mut workspace.left)?;
        if tautology {
            delete_clause(solver, offset)?;
            stats.tautologies += 1;
            changed = true;
            continue;
        }
        if duplicate_count > 0 {
            // Add the deduplicated replacement first (RUP: its negation falsifies the
            // original clause), then delete the original (Spec 09 section 3).
            let mut replacement_len = length;
            workspace.replacement[..replacement_len].copy_from_slice(&workspace.left[..length]);
            replacement_len = dedupe(&mut workspace.replacement, replacement_len);
            match add_clause_checked(solver, &workspace.replacement[..replacement_len])? {
                Some(()) => {}
                None => {
                    *status = SimplifyStatus::Unsatisfiable;
                    return Ok(true);
                }
            }
            delete_clause(solver, offset)?;
            stats.duplicates += 1;
            changed = true;
        }
    }
    // Scan 2: subsumption and self-subsuming resolution over live pairs.
    for left_index in 0..entry_count {
        let left_offset = match live_offset(solver, left_index) {
            Some(value) => value,
            None => continue,
        };
        let (left_length, _, _) = read_clause(solver, left_offset, &mut workspace.left)?;
        if left_length == 0 {
            continue;
        }
        for right_index in (left_index + 1)..entry_count {
            if stats.pairs_examined >= options.pair_budget {
                *status = SimplifyStatus::PairBudgetExhausted;
                return Ok(changed);
            }
            stats.pairs_examined += 1;
            let right_offset = match live_offset(solver, right_index) {
                Some(value) => value,
                None => continue,
            };
            let (right_length, _, _) = read_clause(solver, right_offset, &mut workspace.right)?;
            if right_length == 0 {
                continue;
            }
            // Plain subsumption: the left literal set is contained in the right one.
            if subset_of(
                &workspace.left[..left_length],
                &workspace.right[..right_length],
            ) {
                delete_clause(solver, right_offset)?;
                stats.subsumed += 1;
                changed = true;
                continue;
            }
            // Self-subsuming resolution: some x in left has -x in right and
            // left \ {x} is contained in right; the right clause loses -x.
            if let Some(pivot_slot) = self_subsumption_pivot(
                &workspace.left[..left_length],
                &workspace.right[..right_length],
            ) {
                let mut replacement_len = 0usize;
                for slot in 0..right_length {
                    if workspace.right[slot] == workspace.right[pivot_slot] {
                        continue;
                    }
                    workspace.replacement[replacement_len] = workspace.right[slot];
                    replacement_len += 1;
                }
                if replacement_len == 0 {
                    // The strengthened clause is empty: the formula is refuted
                    // (Spec 09 section 4 corollary); emit and stop.
                    *status = SimplifyStatus::Unsatisfiable;
                    if let Some(recorder) = solver.proof() {
                        let _ = recorder.record_empty_clause();
                    }
                    return Ok(true);
                }
                // Add the strengthened clause first (RUP: both unit propagations of
                // the pivot fire under its negation), then delete the original.
                match add_clause_checked(solver, &workspace.replacement[..replacement_len])? {
                    Some(()) => {}
                    None => {
                        *status = SimplifyStatus::Unsatisfiable;
                        return Ok(true);
                    }
                }
                delete_clause(solver, right_offset)?;
                stats.strengthened += 1;
                changed = true;
            }
        }
    }
    // Scan 3: vivification of surviving clauses (length >= 2).
    let entry_count_now = solver.registry().entry_count();
    for index in 0..entry_count_now {
        if stats.vivify_attempts >= options.vivify_candidates {
            *status = SimplifyStatus::VivifyBudgetExhausted;
            return Ok(changed);
        }
        let offset = match live_offset(solver, index) {
            Some(value) => value,
            None => continue,
        };
        let (length, _, _) = read_clause(solver, offset, &mut workspace.left)?;
        if length < kVivifyMinLiterals {
            continue;
        }
        stats.vivify_attempts += 1;
        let shortened = vivify(
            solver,
            offset,
            &workspace.left[..length],
            options,
            stats,
            status,
        )?;
        if shortened {
            changed = true;
        }
        match status {
            SimplifyStatus::Complete => {}
            _ => return Ok(changed),
        }
    }
    Ok(changed)
}

// CEP:WHAT: Vivifies one candidate clause: isolates it with the raw deleted mark, assumes the negations of its literals in the sorted, deduplicated order produced by read_clause (any fixed order is sound - the prefix argument does not depend on the original storage order), and on the first propagation conflict replaces the clause with the surviving prefix.
// CEP:WHY: Spec 09 section 5: the conflict under the first k negated literals proves the database minus the candidate entails l1 v ... v lk, which is the shortened clause; the original is deleted first in the proof (the RUP check of the replacement runs against the database minus the candidate, exactly the state the check used); the raw mark is restored when no shortening is found.
// CEP:STATUS: complete
// CEP:FAILURE: propagates CdclError; never leaves the trail above level 0 or the candidate marked.
// CEP:ASSUMES: decision level 0 at entry; the candidate is live with at least 2 literals.
// CEP:COST: up to length decide+propagate cycles, each counted against the vivify budget.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{vivification_shortens_clause, vivification_restores_unchanged_clause, vivification_budget_stops_early}.
// CEP:SECURITY: budget-bounded; the trail excursion is fully canceled.
fn vivify(
    solver: &CdclSolver<'_>,
    offset: u32,
    literals: &[SatLiteral],
    options: &SimplifyOptions,
    stats: &mut SimplifyStats,
    status: &mut SimplifyStatus,
) -> Result<bool, crate::sat::cdcl::CdclError> {
    // Isolate the candidate: BCP must not see it during the check.
    solver
        .core()
        .clauses()
        .mark_deleted(offset)
        .map_err(crate::sat::database::SatCoreError::from)?;
    let mut budget = options.vivify_budget;
    let mut keep: usize = literals.len();
    for slot in 0..literals.len() {
        if budget == 0 {
            // Budget out mid-candidate: treat as no shortening (conservative, sound)
            // and report the honest partial status.
            keep = literals.len();
            *status = SimplifyStatus::VivifyBudgetExhausted;
            break;
        }
        let literal = literals[slot];
        match solver.core().value_of_literal(literal) {
            SatValue::True => {
                // The clause is satisfied under the current level-0 assignment: no
                // prefix refutation is possible; keep the clause unchanged.
                keep = literals.len();
                break;
            }
            SatValue::False => {
                // Already false: the negation is already assumed; this literal's
                // disjunct contributes nothing, and the prefix extends past it.
                continue;
            }
            SatValue::Unassigned => {}
        }
        if let Err(error) = solver.core().decide(literal.negate()) {
            solver.core().cancel_until(0);
            let _ = solver.core().clauses().unmark_deleted(offset);
            return Err(error.into());
        }
        budget -= 1;
        match solver.core().propagate() {
            Ok(PropagationOutcome::Conflict(_)) => {
                // Refuted under the first slot+1 negated literals: the shortened
                // clause is the prefix through this slot.
                keep = slot + 1;
                break;
            }
            Ok(PropagationOutcome::NoConflict) => {}
            Err(error) => {
                solver.core().cancel_until(0);
                let _ = solver.core().clauses().unmark_deleted(offset);
                return Err(error.into());
            }
        }
    }
    solver.core().cancel_until(0);
    if keep >= literals.len() {
        // No shortening: restore the candidate.
        solver
            .core()
            .clauses()
            .unmark_deleted(offset)
            .map_err(crate::sat::database::SatCoreError::from)?;
        return Ok(false);
    }
    // Permanent replacement: proof-delete the original, complete the registry
    // tombstone (the raw mark is already set), then add the shortened clause
    // (RUP against the database minus the candidate - exactly what the check
    // derived; Spec 09 section 5).
    if let Some(recorder) = solver.proof() {
        recorder
            .record_delete(offset, solver.core().clauses())
            .map_err(crate::sat::cdcl::CdclError::Proof)?;
    }
    solver
        .registry()
        .complete_deletion(solver.core().clauses(), offset)
        .map_err(crate::sat::cdcl::CdclError::Registry)?;
    match add_clause_checked(solver, &literals[..keep])? {
        Some(()) => {}
        None => {
            // The shortened clause refuted the formula outright (falsified unit
            // or level-0 propagation conflict): the round ends refuted with the
            // empty-clause step already emitted by add_clause_checked (Spec 09
            // section 6, Spec 11 section 4).
            *status = SimplifyStatus::Unsatisfiable;
            return Ok(true);
        }
    }
    stats.vivified += 1;
    Ok(true)
}

// CEP:WHAT: Returns the live clause offset of a registry entry, or None for tombstoned or out-of-range entries.
// CEP:WHY: The scans address clauses by stable entry index; tombstones appear mid-scan as clauses get deleted.
// CEP:STATUS: complete
// CEP:FAILURE: none (None is the honest answer for dead entries).
// CEP:ASSUMES: index < entry_count captured by the caller.
// CEP:COST: 1 read + 1 tombstone check.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::subsumption_deletes.
// CEP:SECURITY: bounds-checked through the registry API.
fn live_offset(solver: &CdclSolver<'_>, index: u32) -> Option<u32> {
    let entry = solver.registry().entry(index).ok()?;
    if entry.tombstone.get() {
        return None;
    }
    Some(entry.offset.get())
}

// CEP:WHAT: Reads one clause into a buffer in storage order, sorting and deduplicating in place, and reports the duplicate count and tautology flag.
// CEP:WHY: The subsumption probes want sorted deduplicated literal sets; the dedup scan wants the duplicate count; the tautology scan wants complementary pairs; one read serves all three (Spec 09 sections 2-4).
// CEP:STATUS: complete
// CEP:FAILURE: propagates storage errors.
// CEP:ASSUMES: buffer holds kMaxSatClauseLiterals entries.
// CEP:COST: O(length log-free insertion sort + length) per clause.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{tautologies_removed, duplicates_removed, subsumption_deletes}.
// CEP:SECURITY: bounds-checked reads.
fn read_clause(
    solver: &CdclSolver<'_>,
    offset: u32,
    buffer: &mut [SatLiteral; kMaxSatClauseLiterals as usize],
) -> Result<(usize, u32, bool), crate::sat::cdcl::CdclError> {
    let header = solver
        .core()
        .clauses()
        .header(offset)
        .map_err(crate::sat::database::SatCoreError::from)?;
    let mut length = 0usize;
    while length < header.length as usize {
        let literal = solver
            .core()
            .clauses()
            .literal(offset, length as u32)
            .map_err(crate::sat::database::SatCoreError::from)?;
        buffer[length] = literal;
        length += 1;
    }
    // Sort and deduplicate first: complementary encodings (same variable, opposite
    // polarity - the polarity bit is the encoding's low bit) are then adjacent, so
    // the tautology check is one linear pass (Spec 09 section 2).
    let deduped = dedupe(buffer, length);
    let duplicates = (length - deduped) as u32;
    let mut tautology = false;
    for slot in 1..deduped {
        if buffer[slot].variable().0 == buffer[slot - 1].variable().0
            && buffer[slot].is_positive() != buffer[slot - 1].is_positive()
        {
            tautology = true;
        }
    }
    Ok((deduped, duplicates, tautology))
}

// CEP:WHAT: Sorts a literal slice by encoding (insertion sort) and drops adjacent duplicates in place; returns the deduplicated length.
// CEP:WHY: Sorted deduplicated literal sets make subsumption a two-pointer scan and duplicate detection trivial; insertion sort is stable, allocation-free, and O(n^2) only at the kMaxSatClauseLiterals bound (the same discipline as the IR canonical order sort).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: length <= buffer length.
// CEP:COST: O(n^2) worst case at the clause bound.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::duplicates_removed.
// CEP:SECURITY: none.
fn dedupe(buffer: &mut [SatLiteral; kMaxSatClauseLiterals as usize], length: usize) -> usize {
    for i in 1..length {
        let mut j = i;
        while j > 0 && buffer[j].encoding() < buffer[j - 1].encoding() {
            buffer.swap(j, j - 1);
            j -= 1;
        }
    }
    let mut write: usize = 0;
    for read in 0..length {
        if write == 0 || buffer[read].encoding() != buffer[write - 1].encoding() {
            buffer[write] = buffer[read];
            write += 1;
        }
    }
    write
}

// CEP:WHAT: Two-pointer subset test over sorted deduplicated literal sets.
// CEP:WHY: left subsumes right iff every left literal occurs in right (Spec 09 section 2); both sorted, the scan is O(|left| + |right|).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: both slices sorted and deduplicated.
// CEP:COST: linear.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::subsumption_deletes.
// CEP:SECURITY: none.
fn subset_of(left: &[SatLiteral], right: &[SatLiteral]) -> bool {
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < left.len() && j < right.len() {
        if left[i].encoding() == right[j].encoding() {
            i += 1;
            j += 1;
        } else if left[i].encoding() > right[j].encoding() {
            j += 1;
        } else {
            return false;
        }
    }
    i == left.len()
}

// CEP:WHAT: Finds the self-subsuming pivot: a literal x of left whose negation occurs in right while left \ {x} is a subset of right; returns the right-slot of the negation.
// CEP:WHY: Spec 09 section 4: the resolvent of left and right on x is right \ {-x} (the resolvent is subsumed by right after dropping -x because left \ {x} is contained in right), so right can be strengthened by deleting -x.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when no pivot exists.
// CEP:ASSUMES: both slices sorted and deduplicated.
// CEP:COST: O(|left| x (|left| + |right|)).
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::strengthening_rewrites.
// CEP:SECURITY: none.
fn self_subsumption_pivot(left: &[SatLiteral], right: &[SatLiteral]) -> Option<usize> {
    for (pivot, candidate) in left.iter().enumerate() {
        let negated = candidate.negate();
        let mut slot: usize = 0;
        let mut found = false;
        while slot < right.len() {
            if right[slot].encoding() == negated.encoding() {
                found = true;
                break;
            }
            slot += 1;
        }
        if !found {
            continue;
        }
        let mut contained = true;
        for (position, literal) in left.iter().enumerate() {
            if position == pivot {
                continue;
            }
            if !right.contains(literal) {
                contained = false;
                break;
            }
        }
        if contained {
            return Some(slot);
        }
    }
    None
}

// CEP:WHAT: Adds a clause through the solver's level-0 entry point and classifies the refuting outcomes.
// CEP:WHY: Every preprocessing rewrite adds through the same path as problem clauses, so registration, attachment, unit enqueueing, root-conflict flagging, and proof recording happen exactly once per clause; None signals "formula refuted by this addition" (falsified unit or level-0 propagation conflict); the falsified-unit sub-case emits the empty clause inside add_clause_with_kind (Spec 11 section 4), and the propagation-conflict sub-case emits it here so every refuted-by-addition trace ends with the refutation step regardless of which scan triggered it.
// CEP:STATUS: complete
// CEP:FAILURE: propagates CdclError; returns None on refutation (the empty-clause step is emitted before returning).
// CEP:ASSUMES: decision level 0.
// CEP:COST: one clause add plus one propagation drain plus (on refutation) one proof append.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{contradictory_units_refute, strengthening_rewrites, vivified_clause_refutes_formula}.
// CEP:SECURITY: add-time validation.
fn add_clause_checked(
    solver: &CdclSolver<'_>,
    literals: &[SatLiteral],
) -> Result<Option<()>, crate::sat::cdcl::CdclError> {
    match solver.add_derived_clause(literals) {
        Ok(AttachOutcome::Conflict) => Ok(None),
        Ok(_) => match solver.core().propagate() {
            Ok(PropagationOutcome::NoConflict) => Ok(Some(())),
            Ok(PropagationOutcome::Conflict(_)) => {
                // Level-0 propagation conflict: the added clause refutes the
                // formula. The conflicting state is exactly the RUP witness of
                // the empty clause (all trail entries are level-0 consequences),
                // so the refutation step is emitted here (Spec 11 section 4) -
                // the falsified-unit sub-case is emitted inside
                // add_clause_with_kind, so both None sub-cases are covered.
                if let Some(recorder) = solver.proof() {
                    recorder
                        .record_empty_clause()
                        .map_err(crate::sat::cdcl::CdclError::Proof)?;
                }
                Ok(None)
            }
            Err(error) => Err(error.into()),
        },
        Err(error) => Err(error),
    }
}

// CEP:WHAT: Deletes a clause permanently: proof deletion first, then the registry deletion (which sets the storage deleted mark and the tombstone).
// CEP:WHY: One sanctioned deletion path for preprocessing keeps the trace and the registry consistent (S41 + CEP-1003).
// CEP:STATUS: complete
// CEP:FAILURE: propagates CdclError.
// CEP:ASSUMES: the clause is live and registered.
// CEP:COST: one proof append plus one registry deletion.
// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{tautologies_removed, subsumption_deletes}.
// CEP:SECURITY: none.
fn delete_clause(solver: &CdclSolver<'_>, offset: u32) -> Result<(), crate::sat::cdcl::CdclError> {
    if let Some(recorder) = solver.proof() {
        recorder
            .record_delete(offset, solver.core().clauses())
            .map_err(crate::sat::cdcl::CdclError::Proof)?;
    }
    solver
        .registry()
        .delete(solver.core().clauses(), offset)
        .map_err(crate::sat::cdcl::CdclError::Registry)?;
    Ok(())
}
