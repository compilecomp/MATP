// CEP:FILE: hot/search/generate.rs
// CEP:WHAT: The bounded given-clause inference generator (design 10.3): enumerates all inferences between one given clause and the active set through resumable phases (factoring, equality rules, resolution, superposition-into, superposition-from - each inter-clause phase an active-array scan with a head-symbol prefilter) under the kMaxInferencesPerClause budget with buffer-full deferral.
// CEP:WHY: Design 10.3 fixes the generation strategy - all inferences between the given clause and the active set, computed lazily at selection time, bounded per clause with deferral - and design 15.1 step 5 consumes them; the generator owns every bound (conclusion length, per-clause budget, buffer capacity) so the rules stay pure, and the cursor makes generation resumable across loop iterations: the search calls generate_step repeatedly for one given clause until the phase machine reaches Done, with the buffer filling at most kInferenceBufferClauses conclusions per call; standardize-apart (Spec 02 section 5) renames every ACTIVE premise into the window above the given clause's variables before any rule call, with the namespace bound checked per pair; soundness of the emitted conclusions is each rule's theorem (Spec 07), so the generator adds only bookkeeping.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SearchError on structural failures; Ok(GenerationStatus::MoreRemaining) defers (buffer full, budget not yet exhausted); Ok(GenerationStatus::Complete) ends the given clause; dropped candidates and over-long conclusions are counted, never silent (CEP&CC Law 6).
// CEP:ASSUMES: The given clause's literals are the stored ones (flags computed); the active set's trees and slots are consistent; the substitution trail is at the search's baseline depth between calls - the ABORT DISCIPLINE: a rule's Err (for example ArenaFull during conclusion materialization after a successful unification) propagates out of generate_step and ends the whole search, so the partially-bound trail a rule may leak on an Err path is never read again; rules unwind only on their Ok(None) paths.
// CEP:COST: per call: O(active) scan steps with one constant head-symbol prefilter per pair, bounded by the per-clause budget overall (the residual unindexed scans are the Phase 3 state, tickets CEP-1027 for indexed retrieval); measured in bench CEP-BENCH-0010, artifact benches/artifacts/atp_resolution_step.json.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced, retrieval_overflow_counts_drops, generation_is_deterministic}; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force}.
// CEP:SECURITY: every loop is bounded by a named constant (CEP&CC 22.10).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; phases, literals, candidates, slots, and paths advance in index order, and rule outcomes are pure functions of the premises.
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 6 fixes the phase machine, the budget semantics (buffer-full defers within the per-clause cap; cap exhaustion ends the clause and marks the abandoned tail with one drop - the enumeration stops at the cap, unvisited candidates are not individually enumerated by design), and the standardize-apart discipline; the property tests verify the loop end-to-end against the SAT solver and brute force.

use crate::inference::factoring::{equality_factor, factor};
use crate::inference::resolution::resolve;
use crate::inference::superposition::kMaxPathLength;
use crate::inference::superposition::{equality_resolve, superpose};
use crate::inference::InferenceContext;
use crate::ir::clause::{ClauseStore, InferenceRule};
use crate::ir::literal::Literal;
use crate::ir::term::{TermStore, TermTag};
use crate::search::active::ActiveSet;
use mapt_config::limits::{
    kInferenceBufferClauses, kInferenceClauseLiterals, kMaxClauseLiterals, kMaxInferencesPerClause,
};

// CEP:WHAT: Parent-id slots of one buffered conclusion (the given clause and one partner premise).
// CEP:WHY: Every inter-clause rule is binary (two premises); the buffer entry's parent array names its width instead of a bare 2 at every site (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: intra-clause rules pass the given clause id twice or zero for the second slot.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, inference_deferral_resumes}.
// CEP:SECURITY: none.
const kRulePremiseSlots: usize = 2;
use super::SearchError;

/// CEP:WHAT: The generation phases of one given clause, in processing order.
/// CEP:WHY: A fixed order makes generation deterministic and the cursor's phase component meaningful: intra-clause rules first (factoring, equality resolution, equality factoring - cheap and clause-local), then the three inter-clause scans (resolution, superposition-into, superposition-from - each an active-array scan with a head-symbol prefilter; indexed retrieval is ticket CEP-1027).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{generation_is_deterministic, inference_deferral_resumes}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenerationPhase {
    /// CEP:WHAT: Intra-clause factoring pairs.
    /// CEP:WHY: Design 10.1 factoring.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::factoring_fires.
    /// CEP:SECURITY: none.
    Factoring,
    /// CEP:WHAT: Intra-clause equality resolution singles then equality factoring pairs.
    /// CEP:WHY: Design 10.1 equality resolution and equality factoring.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::equality_rules_fire.
    /// CEP:SECURITY: none.
    EqualityRules,
    /// CEP:WHAT: Resolution of the given clause's literals against active candidates by scan.
    /// CEP:WHY: Design 10.1 binary/ordered resolution; the discrimination tree's flat-sequence retrieval cannot see all unifiable pairs (documented at the scan and in Spec 08 section 6), so the phase scans the active array with a head-symbol prefilter (indexed retrieval is ticket CEP-1027).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires; unit/hot/inference_test.rs::resolution_candidates_retrieved.
    /// CEP:SECURITY: none.
    Resolution,
    /// CEP:WHAT: Superposition of active equations into the given clause's non-root subterm positions, by scan.
    /// CEP:WHY: Design 10.1 superposition, into direction; the scan enumerates the given clause's literal atoms' subterm positions and pairs each with every active positive equation whose left side's head matches (indexed retrieval is ticket CEP-1027).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_into_fires.
    /// CEP:SECURITY: none.
    SuperpositionInto,
    /// CEP:WHAT: Superposition of the given clause's equations into active clauses (the unindexed scan).
    /// CEP:WHY: Design 10.1 superposition, from direction; the subterm/prefix index that would make this indexed is ticket CEP-1027.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_from_fires.
    /// CEP:SECURITY: none.
    SuperpositionFrom,
    /// CEP:WHAT: The given clause's generation is finished.
    /// CEP:WHY: Terminal phase; further calls are no-ops.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    /// CEP:SECURITY: none.
    Done,
}

/// CEP:WHAT: Status of one generate_step call.
/// CEP:WHY: CEP&CC Law 6: the two outcomes are distinct facts - MoreRemaining defers with the cursor advanced (the loop calls again next iteration), Complete ends the given clause.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenerationStatus {
    /// CEP:WHAT: Conclusions were emitted into the buffer; more work remains for this given clause.
    /// CEP:WHY: The deferral outcome (buffer full or step boundary).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the cursor advanced past the emitted work.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    /// CEP:SECURITY: none.
    MoreRemaining,
    /// CEP:WHAT: The given clause's generation is finished (all phases done or the per-clause budget exhausted).
    /// CEP:WHY: The terminal outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::per_clause_bound_enforced.
    /// CEP:SECURITY: none.
    Complete,
}

/// CEP:WHAT: One buffered conclusion: the literal extent, the rule, and up to two parent clause ids.
/// CEP:WHY: The search materializes buffered conclusions into clause records with derivation steps (design 5.4), so the buffer carries exactly what new_clause needs; the fixed inline literal array (kInferenceClauseLiterals) keeps the buffer a fixed stack structure with no allocation.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: count <= kInferenceClauseLiterals.
/// CEP:COST: 528 bytes.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, factoring_fires}.
/// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub struct GeneratedClause {
    /// CEP:WHAT: The conclusion's literals.
    /// CEP:WHY: The clause body.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: slots beyond count are filler.
    /// CEP:COST: kInferenceClauseLiterals x 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub literals: [Literal; kInferenceClauseLiterals],
    /// CEP:WHAT: Literal count.
    /// CEP:WHY: Extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kInferenceClauseLiterals.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub count: u16,
    /// CEP:WHAT: The inference rule label for the derivation step.
    /// CEP:WHY: Proof-graph edge label (design 5.4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: closed enum.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub rule: InferenceRule,
    /// CEP:WHAT: Parent clause ids (0 = absent).
    /// CEP:WHY: Proof-graph parents.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kInvalidClauseId (0) marks absent.
    /// CEP:COST: 16 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub parents: [u64; kRulePremiseSlots],
}

/// CEP:WHAT: The conclusion buffer: kInferenceBufferClauses inline conclusions plus the fill counter.
/// CEP:WHY: Design 10.3's bounded emission: when the buffer fills, generation defers (the loop drains it into the passive set and calls again); the fixed arrays keep the structure stack-allocated and copy-free.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: entries beyond count are filler.
/// CEP:COST: about 34 KiB.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced}.
/// CEP:SECURITY: none.
pub struct InferenceBuffer {
    /// CEP:WHAT: The conclusions.
    /// CEP:WHY: Emission storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: kInferenceBufferClauses x 528 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    /// CEP:SECURITY: none.
    pub clauses: [GeneratedClause; kInferenceBufferClauses],
    /// CEP:WHAT: Number of buffered conclusions.
    /// CEP:WHY: Fill level.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= clauses.len().
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    /// CEP:SECURITY: none.
    pub count: usize,
}

impl Default for InferenceBuffer {
    // CEP:WHAT: The empty buffer (manual Default: the inline clause array exceeds the derived-Default size limit).
    // CEP:WHY: The lint discipline (len/is_empty, Default::default ergonomics) without relying on array Default (CEP&CC 22.6).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    // CEP:SECURITY: none.
    fn default() -> Self {
        InferenceBuffer::new()
    }
}

impl InferenceBuffer {
    // CEP:WHAT: Constructs an empty buffer.
    // CEP:WHY: Explicit initialization with filler literals (the count governs reads).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    // CEP:SECURITY: none.
    pub fn new() -> InferenceBuffer {
        InferenceBuffer {
            clauses: [GeneratedClause {
                literals: [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                    kInferenceClauseLiterals],
                count: 0,
                rule: InferenceRule::Input,
                parents: [0; kRulePremiseSlots],
            }; kInferenceBufferClauses],
            count: 0,
        }
    }
}

/// CEP:WHAT: The resumable generation cursor: phase, indices, subterm path, and the per-clause counters.
/// CEP:WHY: Design 10.3's deferral needs an explicit resume point; the cursor encodes the phase machine's position (literal index, candidate index, active slot, partner literal, subterm path) and the budget counters (conclusions emitted, candidates dropped); a fresh cursor starts at the first phase and Done is sticky.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: the search keeps the cursor for the in-progress given clause only.
/// CEP:COST: 160 bytes.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced, generation_is_deterministic}.
/// CEP:SECURITY: none.
pub struct GenerationCursor {
    /// CEP:WHAT: Current phase.
    /// CEP:WHY: The phase machine's state.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: Done is sticky.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    /// CEP:SECURITY: none.
    pub phase: GenerationPhase,
    /// CEP:WHAT: Current given-clause literal index (factoring first partner, resolution query, superposition-from equation).
    /// CEP:WHY: The outer enumeration index of the literal-addressed phases.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= given literal count.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{factoring_fires, resolution_fires}.
    /// CEP:SECURITY: none.
    pub literal: u32,
    /// CEP:WHAT: Current partner index (factoring second literal, retrieval candidate position, equality-rules substate).
    /// CEP:WHY: The inner enumeration index.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: phase-specific meaning.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{factoring_fires, resolution_fires}.
    /// CEP:SECURITY: none.
    pub partner: u32,
    /// CEP:WHAT: Current active slot (superposition-from scan).
    /// CEP:WHY: The unindexed scan's outer index.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= active slot count.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_from_fires.
    /// CEP:SECURITY: none.
    pub slot: u32,
    /// CEP:WHAT: Current partner literal index inside the active clause (superposition-from).
    /// CEP:WHY: The scan's literal index.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= the slot clause's literal count.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_from_fires.
    /// CEP:SECURITY: none.
    pub partner_literal: u32,
    /// CEP:WHAT: Current subterm path (superposition phases).
    /// CEP:WHY: The position enumeration of the into-side atom.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: path_len <= kMaxPathLength.
    /// CEP:COST: 128 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{superposition_into_fires, superposition_from_fires}.
    /// CEP:SECURITY: none.
    pub path: [u16; kMaxPathLength],
    /// CEP:WHAT: Path length.
    /// CEP:WHY: Extent of path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxPathLength.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_into_fires.
    /// CEP:SECURITY: none.
    pub path_len: u32,
    /// CEP:WHAT: Conclusions emitted for this given clause so far.
    /// CEP:WHY: The kMaxInferencesPerClause budget counter.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: budget exhaustion ends the clause.
    /// CEP:ASSUMES: cumulative across calls.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::per_clause_bound_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub inferences: u64,
    /// CEP:WHAT: Candidates and conclusions dropped so far (retrieval overflow, namespace overflow, over-long conclusions).
    /// CEP:WHY: CEP&CC Law 4: bounded drops are counted, never silent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: cumulative across calls.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{retrieval_overflow_counts_drops, per_clause_bound_enforced}.
    /// CEP:SECURITY: none.
    pub dropped: u64,
}

impl Default for GenerationCursor {
    // CEP:WHAT: The fresh cursor (manual Default: the path array exceeds the derived-Default size limit).
    // CEP:WHY: The lint discipline without relying on array Default.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, per_clause_bound_enforced}.
    // CEP:SECURITY: none.
    fn default() -> Self {
        GenerationCursor::new()
    }
}

impl GenerationCursor {
    // CEP:WHAT: Constructs a fresh cursor at the first phase.
    // CEP:WHY: The search creates one per given clause.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, generation_is_deterministic}.
    // CEP:SECURITY: none.
    pub fn new() -> GenerationCursor {
        GenerationCursor {
            phase: GenerationPhase::Factoring,
            literal: 0,
            // The first factoring pair is (0, 1): pairs are strictly ascending
            // (i < j), so a literal never pairs with itself (Spec 07 section 5).
            partner: 1,
            slot: 0,
            partner_literal: 0,
            path: [0; kMaxPathLength],
            path_len: 0,
            inferences: 0,
            dropped: 0,
        }
    }

    // CEP:WHAT: Returns whether the given clause's generation is finished.
    // CEP:WHY: The search checks between iterations.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::inference_deferral_resumes.
    // CEP:SECURITY: none.
    pub fn is_done(&self) -> bool {
        self.phase == GenerationPhase::Done
    }
}

// CEP:WHAT: Advances a subterm path to the next DFS position of an atom (pre-order, child-index order), skipping the empty root path.
// CEP:WHY: The superposition phases enumerate every non-root position of the into atom; the odometer walk (descend to child 0 when possible, else increment the last component, else backtrack) is the standard deterministic enumeration, and variables are kept (the rules reject them cheaply) so the walk stays structure-blind and resumable.
// CEP:STATUS: complete
// CEP:FAILURE: returns false when no further position exists.
// CEP:ASSUMES: path[..path_len] addresses a valid position or is the root position (path_len == 0).
// CEP:COST: O(path length) per step.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{superposition_into_fires, superposition_from_fires}.
// CEP:SECURITY: depth-bounded by kMaxPathLength.
pub fn advance_path(
    terms: &TermStore<'_>,
    atom: crate::ir::term::TermPtr,
    path: &mut [u16; kMaxPathLength],
    path_len: &mut u32,
) -> bool {
    // Try to descend: append child 0 when the current node has children and depth remains.
    let current = match crate::inference::superposition::subterm_at_public(
        terms,
        atom,
        &path[..*path_len as usize],
    ) {
        Some(value) => value,
        None => return false,
    };
    if let Ok(view) = terms.term(current) {
        if view.child_count() > 0 && (*path_len as usize) < path.len() {
            path[*path_len as usize] = 0;
            *path_len += 1;
            return true;
        }
    }
    // Odometer: increment the last component while it stays below the parent's child
    // count, else backtrack.
    while *path_len > 0 {
        let last = *path_len as usize - 1;
        let parent =
            match crate::inference::superposition::subterm_at_public(terms, atom, &path[..last]) {
                Some(value) => value,
                None => return false,
            };
        let parent_children = match terms.term(parent) {
            Ok(view) => view.child_count(),
            Err(_) => return false,
        };
        if (path[last] as u32) + 1 < parent_children as u32 {
            path[last] += 1;
            return true;
        }
        *path_len -= 1;
    }
    false
}

// CEP:WHAT: Workspace of one generate_step call: premise buffers and the retrieval buffer.
// CEP:WHY: Fixed stack structures keep the step allocation-free; the active premise is renamed into premise_buffer before rule calls and conclusions are staged in the output buffer.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: about 20 KiB of stack.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, superposition_into_fires}.
// CEP:SECURITY: none.
pub(crate) struct GenerationWorkspace {
    /// CEP:WHAT: Renamed active premise literals.
    /// CEP:WHY: The standardize-apart right-hand side.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 KiB.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    premise: [Literal; kMaxClauseLiterals as usize],
    /// CEP:WHAT: Raw active premise literals before renaming.
    /// CEP:WHY: Read from the store, then renamed into premise.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 KiB.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    raw_premise: [Literal; kMaxClauseLiterals as usize],
}

impl GenerationWorkspace {
    // CEP:WHAT: Constructs a zeroed workspace.
    // CEP:WHY: Explicit init.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    // CEP:SECURITY: none.
    fn new() -> GenerationWorkspace {
        GenerationWorkspace {
            premise: [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                kMaxClauseLiterals as usize],
            raw_premise: [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                kMaxClauseLiterals as usize],
        }
    }
}

// CEP:WHAT: The bundled inputs of the scan phases: the inference context, the clause store, the active set, the given clause, its id, and the shared workspace.
// CEP:WHY: The scan phases share identical parameter sets; bundling keeps every function within the argument-count discipline (CEP&CC Law 5) and makes the phase machine's call sites uniform.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the given clause's flags are computed; the active set is consistent.
// CEP:COST: references only.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, superposition_into_fires, superposition_from_fires}.
// CEP:SECURITY: none.
pub(crate) struct ScanInputs<'a> {
    /// CEP:WHAT: The inference context.
    /// CEP:WHY: Rules and renaming need it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: reference.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) context: &'a InferenceContext<'a>,
    /// CEP:WHAT: The clause store.
    /// CEP:WHY: Premise reads.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: reference.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) store: &'a ClauseStore<'a>,
    /// CEP:WHAT: The active set.
    /// CEP:WHY: The scan source.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consistent.
    /// CEP:COST: reference.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) active: &'a ActiveSet<'a>,
    /// CEP:WHAT: The given clause's literals.
    /// CEP:WHY: The inference's left premise.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: flags computed.
    /// CEP:COST: reference.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) given: &'a [Literal],
    /// CEP:WHAT: The given clause's id.
    /// CEP:WHY: Derivation parent labels.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) given_id: u64,
    /// CEP:WHAT: The shared workspace.
    /// CEP:WHY: Premise staging buffers.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one per generate_step call.
    /// CEP:COST: reference.
    /// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
    /// CEP:SECURITY: none.
    pub(crate) workspace: &'a mut GenerationWorkspace,
}

// CEP:WHAT: Runs one bounded generation step for the given clause and fills the buffer.
// CEP:WHY: The composition point of design 10.3: phases advance in order, each rule attempt is side-condition-checked inside the rule, conclusions append to the buffer with their derivation labels, and every bound defers or drops with a counter; the search calls this until Complete.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError on structural failures; never panics.
// CEP:ASSUMES: given literals carry computed flags; the active set is consistent; buffer and cursor belong to the same given clause.
// CEP:COST: see file header; measured in bench CEP-BENCH-0010.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs; property/given_clause_property_test.rs::{loop_agrees_with_sat_solver, loop_agrees_with_brute_force}; bench CEP-BENCH-0010.
// CEP:SECURITY: all loops bounded.
pub fn generate_step(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    active: &ActiveSet<'_>,
    given_literals: &[Literal],
    given_id: u64,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<GenerationStatus, SearchError> {
    buffer.count = 0;
    if cursor.is_done() {
        return Ok(GenerationStatus::Complete);
    }
    let mut workspace = GenerationWorkspace::new();
    let mut inputs = ScanInputs {
        context,
        store,
        active,
        given: given_literals,
        given_id,
        workspace: &mut workspace,
    };
    let mut emitted_this_call = false;
    loop {
        if cursor.inferences >= kMaxInferencesPerClause as u64 {
            // Budget exhaustion: the remaining phase work is abandoned. The
            // tail is marked with one drop so the abandonment is never silent
            // (Law 4); the not-yet-visited candidates are not individually
            // enumerable - stopping there is the bound's purpose.
            cursor.dropped += 1;
            cursor.phase = GenerationPhase::Done;
            return Ok(finish(buffer, emitted_this_call));
        }
        if buffer.count >= buffer.clauses.len() {
            return Ok(GenerationStatus::MoreRemaining);
        }
        match cursor.phase {
            GenerationPhase::Factoring => {
                let advance = step_factoring(context, given_literals, given_id, cursor, buffer)?;
                if !advance {
                    cursor.phase = GenerationPhase::EqualityRules;
                    cursor.literal = 0;
                    cursor.partner = 0;
                }
            }
            GenerationPhase::EqualityRules => {
                let advance =
                    step_equality_rules(context, given_literals, given_id, cursor, buffer)?;
                if !advance {
                    cursor.phase = GenerationPhase::Resolution;
                    cursor.literal = 0;
                    cursor.partner = 0;
                    cursor.partner_literal = 0;
                }
            }
            GenerationPhase::Resolution => {
                let advance = step_resolution(&mut inputs, cursor, buffer)?;
                if !advance {
                    cursor.phase = GenerationPhase::SuperpositionInto;
                    cursor.literal = 0;
                    cursor.partner = 0;
                    cursor.path_len = 0;
                }
            }
            GenerationPhase::SuperpositionInto => {
                let advance = step_superposition_into(&mut inputs, cursor, buffer)?;
                if !advance {
                    cursor.phase = GenerationPhase::SuperpositionFrom;
                    cursor.literal = 0;
                    cursor.slot = 0;
                    cursor.partner_literal = 0;
                    cursor.path_len = 0;
                }
            }
            GenerationPhase::SuperpositionFrom => {
                let advance = step_superposition_from(&mut inputs, cursor, buffer)?;
                if !advance {
                    cursor.phase = GenerationPhase::Done;
                    return Ok(finish(buffer, emitted_this_call));
                }
            }
            GenerationPhase::Done => {
                return Ok(finish(buffer, emitted_this_call));
            }
        }
        if buffer.count > 0 {
            emitted_this_call = true;
        }
    }
}

// CEP:WHAT: Finalizes a step's status (MoreRemaining when anything was emitted and the machine is not Done, else Complete).
// CEP:WHY: The loop contract: the search keeps calling while the status is MoreRemaining.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced}.
// CEP:SECURITY: none.
fn finish(buffer: &InferenceBuffer, emitted: bool) -> GenerationStatus {
    if buffer.count == 0 && !emitted {
        GenerationStatus::Complete
    } else {
        GenerationStatus::MoreRemaining
    }
}

// CEP:WHAT: Appends one conclusion to the buffer and advances the budget counter.
// CEP:WHY: The single emission point (Law 3: budget accounting in one place).
// CEP:STATUS: complete
// CEP:FAILURE: returns false when the buffer is full (the caller defers).
// CEP:ASSUMES: count <= kInferenceClauseLiterals.
// CEP:COST: one copy.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, inference_deferral_resumes}.
// CEP:SECURITY: none.
fn append(
    buffer: &mut InferenceBuffer,
    literals: &[Literal],
    rule: InferenceRule,
    parents: [u64; kRulePremiseSlots],
    cursor: &mut GenerationCursor,
) -> bool {
    if buffer.count >= buffer.clauses.len() {
        return false;
    }
    let slot = buffer.count;
    let entry = &mut buffer.clauses[slot];
    for (index, literal) in literals.iter().enumerate() {
        entry.literals[index] = *literal;
    }
    entry.count = literals.len() as u16;
    entry.rule = rule;
    entry.parents = parents;
    buffer.count += 1;
    cursor.inferences += 1;
    true
}

// CEP:WHAT: One factoring attempt per call iteration: the pair (literal, partner) over the given clause.
// CEP:WHY: Enumerates ascending pairs; true when the cursor advanced within the phase.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; over-long conclusions count as drops.
// CEP:ASSUMES: cursor.literal < partner ordering.
// CEP:COST: one rule call.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::factoring_fires.
// CEP:SECURITY: none.
fn step_factoring(
    context: &InferenceContext<'_>,
    given: &[Literal],
    given_id: u64,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<bool, SearchError> {
    if given.is_empty() {
        return Ok(false);
    }
    let literal_index = cursor.literal as usize;
    if literal_index >= given.len() {
        return Ok(false);
    }
    let partner_index = cursor.partner as usize;
    if partner_index >= given.len() {
        cursor.literal += 1;
        cursor.partner = cursor.literal + 1;
        return Ok(cursor.literal < given.len() as u32);
    }
    // Ascending-pairs invariant: partner > literal at every attempt (Spec 07
    // section 5's i < j; a self-pair would "factor" a literal away and produce a
    // false empty clause).
    debug_assert!(partner_index > literal_index);
    cursor.partner += 1;
    let mut output: [Literal; kInferenceClauseLiterals] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kInferenceClauseLiterals];
    match factor(context, given, literal_index, partner_index, &mut output) {
        Ok(crate::inference::factoring::FactoringOutcome::Concluded(count)) => {
            if !append(
                buffer,
                &output[..count],
                InferenceRule::Factoring,
                [given_id, 0],
                cursor,
            ) {
                cursor.partner -= 1;
                return Ok(true);
            }
        }
        Ok(crate::inference::factoring::FactoringOutcome::None) => {}
        Err(crate::inference::InferenceError::ConclusionTooLong) => {
            cursor.dropped += 1;
        }
        Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
            cursor.dropped += 1;
        }
        // CEP-1050: materialization bound errors are dropped, not fatal. The rules
        // restore the pre-unification trail on every Err, so the search resumes
        // with a clean substitution and the candidate is counted (Law 4).
        Err(crate::inference::InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        )) => {
            cursor.dropped += 1;
        }
        Err(crate::inference::InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::WeightExceeded,
        )) => {
            cursor.dropped += 1;
        }
        Err(error) => return Err(SearchError::Inference(error)),
    }
    Ok(true)
}

// CEP:WHAT: One equality-rule attempt per call iteration: equality resolution singles (partner == 0 marker), then equality factoring pairs.
// CEP:WHY: The substate is encoded in cursor.partner: 0 means "equality resolution at cursor.literal", k+1 means "equality factoring pair (literal, k)".
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; drops counted.
// CEP:ASSUMES: none.
// CEP:COST: one rule call.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::equality_rules_fire.
// CEP:SECURITY: none.
fn step_equality_rules(
    context: &InferenceContext<'_>,
    given: &[Literal],
    given_id: u64,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<bool, SearchError> {
    if given.is_empty() {
        return Ok(false);
    }
    let literal_index = cursor.literal as usize;
    if literal_index >= given.len() {
        return Ok(false);
    }
    let mut output: [Literal; kInferenceClauseLiterals] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kInferenceClauseLiterals];
    if cursor.partner == 0 {
        // Equality resolution at this literal; advance to the factoring substate.
        cursor.partner = 1;
        match equality_resolve(context, given, literal_index, &mut output) {
            Ok(crate::inference::superposition::SuperpositionOutcome::Concluded(count)) => {
                if !append(
                    buffer,
                    &output[..count],
                    InferenceRule::EqualityResolution,
                    [given_id, 0],
                    cursor,
                ) {
                    cursor.partner = 0;
                    return Ok(true);
                }
            }
            Ok(crate::inference::superposition::SuperpositionOutcome::None) => {}
            Err(crate::inference::InferenceError::ConclusionTooLong) => {
                cursor.dropped += 1;
            }
            Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
                cursor.dropped += 1;
            }
            // CEP-1050: materialization bound errors are dropped, not fatal (the
            // rules restore the pre-unification trail on every Err).
            Err(crate::inference::InferenceError::Structural(
                crate::unification::substitution::SubstitutionError::DepthExceeded,
            )) => {
                cursor.dropped += 1;
            }
            Err(crate::inference::InferenceError::Structural(
                crate::unification::substitution::SubstitutionError::WeightExceeded,
            )) => {
                cursor.dropped += 1;
            }
            Err(error) => return Err(SearchError::Inference(error)),
        }
        return Ok(true);
    }
    let partner_index = (cursor.partner - 1) as usize;
    if partner_index >= given.len() {
        cursor.literal += 1;
        cursor.partner = 0;
        return Ok(cursor.literal < given.len() as u32);
    }
    cursor.partner += 1;
    // Equality-factoring pairs are distinct (i != j): skip the self pair.
    if partner_index == literal_index {
        return Ok(true);
    }
    match equality_factor(context, given, literal_index, partner_index, &mut output) {
        Ok(crate::inference::factoring::FactoringOutcome::Concluded(count)) => {
            if !append(
                buffer,
                &output[..count],
                InferenceRule::EqualityFactoring,
                [given_id, 0],
                cursor,
            ) {
                cursor.partner -= 1;
                return Ok(true);
            }
        }
        Ok(crate::inference::factoring::FactoringOutcome::None) => {}
        Err(crate::inference::InferenceError::ConclusionTooLong) => {
            cursor.dropped += 1;
        }
        Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
            cursor.dropped += 1;
        }
        // CEP-1050: materialization bound errors are dropped, not fatal (the
        // rules restore the pre-unification trail on every Err).
        Err(crate::inference::InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        )) => {
            cursor.dropped += 1;
        }
        Err(crate::inference::InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::WeightExceeded,
        )) => {
            cursor.dropped += 1;
        }
        Err(error) => return Err(SearchError::Inference(error)),
    }
    Ok(true)
}

// CEP:WHAT: Reads one active clause's literals into the raw buffer and renames them into the shared namespace above the given clause's variable count.
// CEP:WHY: The standardize-apart step shared by the inter-clause phases; the namespace bound failure counts as a drop (the pair is skipped, not an error - the clauses are legal, just too variable-heavy to pair).
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when the clause cannot be read or the namespace overflows (counted by the caller).
// CEP:ASSUMES: the clause is live in the store.
// CEP:COST: O(clause literals x term nodes).
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, superposition_from_fires}; unit/hot/inference_test.rs::premises_renamed_apart.
// CEP:SECURITY: none.
fn load_renamed_premise(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    offset: u32,
    given_variable_count: usize,
    workspace: &mut GenerationWorkspace,
) -> Option<usize> {
    let clause = match store.clause(crate::ir::clause::ClausePtr::from_u32(offset)) {
        Ok(value) => value,
        Err(_) => return None,
    };
    if clause.literal_count as usize > workspace.raw_premise.len() {
        return None;
    }
    for position in 0..clause.literal_count {
        match store.literal(clause, position) {
            Ok(value) => workspace.raw_premise[position as usize] = value,
            Err(_) => return None,
        }
    }
    let renamed = crate::inference::rename_clause_apart(
        context.terms,
        context.symbols,
        &workspace.raw_premise[..clause.literal_count as usize],
        given_variable_count as u32,
        &mut workspace.premise,
    );
    match renamed {
        Ok(_) => Some(clause.literal_count as usize),
        Err(_) => None,
    }
}

// CEP:WHAT: Resolution candidates by active-array scan: for the given literal, every active clause literal with complementary polarity and a matching atom head is a candidate.
// CEP:WHY: The discrimination tree's flat-sequence retrieval matches only equal-length flattenings, so a stored literal p(x) is invisible to the query p(f(a)) even though they unify - the tree cannot be a complete candidate source for unification retrieval (documented at the tree and in Spec 08 section 6; indexed retrieval with subtree semantics is ticket CEP-1027); the scan is O(active x literals) with a constant head-symbol and polarity prefilter per pair, bounded by the active capacity and the per-clause budget, and is the same cost class as the superposition-from scan; candidate completeness is what the loop's fairness claims rest on, so Phase 3 pays the scan.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; namespace overflow counts as drops.
// CEP:ASSUMES: the given clause's flags are computed; the active set is consistent.
// CEP:COST: O(active x literals) prefilters plus one rule call per surviving pair.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{resolution_fires, inference_deferral_resumes}; unit/hot/inference_test.rs::resolution_candidates_retrieved.
// CEP:SECURITY: bounded by the active capacity and the per-clause budget.
fn step_resolution(
    inputs: &mut ScanInputs<'_>,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<bool, SearchError> {
    let ScanInputs {
        context,
        store,
        active,
        given,
        given_id,
        workspace,
    } = &mut *inputs;
    let context: &InferenceContext<'_> = context;
    let store: &ClauseStore<'_> = store;
    let active: &ActiveSet<'_> = active;
    let given: &[Literal] = given;
    let given_id: u64 = *given_id;
    let workspace: &mut GenerationWorkspace = workspace;
    if given.is_empty() {
        return Ok(false);
    }
    while cursor.literal < given.len() as u32 {
        let literal_index = cursor.literal as usize;
        let given_literal = given[literal_index];
        while cursor.partner < active.len() {
            let slot_index = cursor.partner;
            let slot = match active.slot(slot_index) {
                Some(value) => value,
                None => {
                    cursor.partner += 1;
                    cursor.partner_literal = 0;
                    continue;
                }
            };
            let given_variables = crate::inference::count_clause_variables(context.terms, given)
                .map_err(SearchError::Inference)?;
            let premise_len =
                match load_renamed_premise(context, store, slot.offset, given_variables, workspace)
                {
                    Some(value) => value,
                    None => {
                        cursor.dropped += 1;
                        cursor.partner += 1;
                        cursor.partner_literal = 0;
                        continue;
                    }
                };
            let partner_clause =
                match store.clause(crate::ir::clause::ClausePtr::from_u32(slot.offset)) {
                    Ok(value) => value,
                    Err(_) => {
                        cursor.dropped += 1;
                        cursor.partner += 1;
                        cursor.partner_literal = 0;
                        continue;
                    }
                };
            while (cursor.partner_literal as usize) < premise_len {
                // Advance-after-completion discipline: the pair cursor moves only
                // after the pair is fully processed (appended, rejected, or
                // dropped); a buffer-full return leaves the cursor AT the current
                // pair so the resumed call re-attempts exactly it (Spec 08
                // section 6; the pre-fix rollback decremented the wrong cursor
                // component and silently skipped one pair per deferral).
                let literal_position = cursor.partner_literal as usize;
                let candidate = workspace.premise[literal_position];
                if candidate.is_positive() == given_literal.is_positive() {
                    cursor.partner_literal += 1;
                    continue;
                }
                if !heads_match(context, given_literal.atom(), candidate.atom()) {
                    cursor.partner_literal += 1;
                    continue;
                }
                let mut output: [Literal; kInferenceClauseLiterals] =
                    [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                        kInferenceClauseLiterals];
                let outcome = resolve(
                    context,
                    given,
                    literal_index,
                    &workspace.premise[..premise_len],
                    literal_position,
                    &mut output,
                );
                match outcome {
                    Ok(crate::inference::resolution::ResolutionOutcome::Concluded(count)) => {
                        if !append(
                            buffer,
                            &output[..count],
                            InferenceRule::Resolution,
                            [given_id, partner_clause.id.0],
                            cursor,
                        ) {
                            return Ok(true);
                        }
                    }
                    Ok(crate::inference::resolution::ResolutionOutcome::None) => {}
                    Err(crate::inference::InferenceError::ConclusionTooLong) => {
                        cursor.dropped += 1;
                    }
                    Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
                        cursor.dropped += 1;
                    }
                    // CEP-1050: materialization bound errors are dropped, not fatal
                    // (the rules restore the pre-unification trail on every Err).
                    Err(crate::inference::InferenceError::Structural(
                        crate::unification::substitution::SubstitutionError::DepthExceeded,
                    )) => {
                        cursor.dropped += 1;
                    }
                    Err(crate::inference::InferenceError::Structural(
                        crate::unification::substitution::SubstitutionError::WeightExceeded,
                    )) => {
                        cursor.dropped += 1;
                    }
                    Err(error) => return Err(SearchError::Inference(error)),
                }
                cursor.partner_literal += 1;
                if buffer.count >= buffer.clauses.len() {
                    return Ok(true);
                }
            }
            cursor.partner += 1;
            cursor.partner_literal = 0;
        }
        cursor.literal += 1;
        cursor.partner = 0;
        cursor.partner_literal = 0;
    }
    Ok(false)
}

// CEP:WHAT: Head-symbol equality prefilter for resolution candidates.
// CEP:WHY: Two atoms can unify only when their heads agree (predicate symbol or the equality tag); the constant check prunes the scan cheaply.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: both atoms are store-interned.
// CEP:COST: two view reads.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::resolution_fires.
// CEP:SECURITY: none.
fn heads_match(
    context: &InferenceContext<'_>,
    left: crate::ir::term::TermPtr,
    right: crate::ir::term::TermPtr,
) -> bool {
    let left_view = match context.terms.term(left) {
        Ok(value) => value,
        Err(_) => return false,
    };
    let right_view = match context.terms.term(right) {
        Ok(value) => value,
        Err(_) => return false,
    };
    if left_view.tag() != right_view.tag() {
        return false;
    }
    if left_view.tag() == TermTag::Equality {
        return true;
    }
    left_view.symbol() == right_view.symbol()
}

// CEP:WHAT: Superposition-into candidates by active-array scan: for each subterm position of the given clause's literals, every active positive equation whose left side's head matches the subterm's head is a candidate.
// CEP:WHY: As with resolution, the rule tree's flat-length retrieval cannot see left sides whose variables would bind to subterms of the query (f(x) misses the query f(f(a))); the scan with a head prefilter is candidate-complete and bounded (CEP-1027 for indexed retrieval).
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; drops counted.
// CEP:ASSUMES: none.
// CEP:COST: O(positions x active x equations) prefilters plus one rule call per surviving pair.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_into_fires.
// CEP:SECURITY: bounded.
fn step_superposition_into(
    inputs: &mut ScanInputs<'_>,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<bool, SearchError> {
    let ScanInputs {
        context,
        store,
        active,
        given,
        given_id,
        workspace,
    } = &mut *inputs;
    let context: &InferenceContext<'_> = context;
    let store: &ClauseStore<'_> = store;
    let active: &ActiveSet<'_> = active;
    let given: &[Literal] = given;
    let given_id: u64 = *given_id;
    let workspace: &mut GenerationWorkspace = workspace;
    if given.is_empty() {
        return Ok(false);
    }
    // The given clause is fixed for the whole scan: count its variables once
    // instead of once per active partner.
    let given_variables = crate::inference::count_clause_variables(context.terms, given)
        .map_err(SearchError::Inference)?;
    while cursor.literal < given.len() as u32 {
        let literal_index = cursor.literal as usize;
        let atom = given[literal_index].atom();
        // Enter the literal at its first non-root position: the rule contracts
        // address subterm positions only (the atom root is never an into
        // target); an atom with no subterm positions moves to the next
        // literal.
        if cursor.path_len == 0
            && !advance_path(context.terms, atom, &mut cursor.path, &mut cursor.path_len)
        {
            cursor.path_len = 0;
            cursor.literal += 1;
            cursor.partner = 0;
            cursor.partner_literal = 0;
            continue;
        }
        while let Some(target) = crate::inference::superposition::subterm_at_public(
            context.terms,
            atom,
            &cursor.path[..cursor.path_len as usize],
        ) {
            while cursor.partner < active.len() {
                let slot_index = cursor.partner;
                let slot = match active.slot(slot_index) {
                    Some(value) => value,
                    None => {
                        cursor.partner += 1;
                        cursor.partner_literal = 0;
                        continue;
                    }
                };
                let premise_len = match load_renamed_premise(
                    context,
                    store,
                    slot.offset,
                    given_variables,
                    workspace,
                ) {
                    Some(value) => value,
                    None => {
                        cursor.dropped += 1;
                        cursor.partner += 1;
                        cursor.partner_literal = 0;
                        continue;
                    }
                };
                let partner_clause =
                    match store.clause(crate::ir::clause::ClausePtr::from_u32(slot.offset)) {
                        Ok(value) => value,
                        Err(_) => {
                            cursor.dropped += 1;
                            cursor.partner += 1;
                            cursor.partner_literal = 0;
                            continue;
                        }
                    };
                while (cursor.partner_literal as usize) < premise_len {
                    // Advance-after-completion (see step_resolution).
                    let literal_position = cursor.partner_literal as usize;
                    let candidate = workspace.premise[literal_position];
                    if !candidate.is_positive() {
                        cursor.partner_literal += 1;
                        continue;
                    }
                    let sides = match crate::inference::factoring::equality_sides(
                        context.terms,
                        candidate.atom(),
                    ) {
                        Some(value) => value,
                        None => {
                            cursor.partner_literal += 1;
                            continue;
                        }
                    };
                    // Head prefilter: the equation's left side and the target subterm
                    // must share their head symbol (or the left side is a variable,
                    // which can never orient - skipped by the orientation check in
                    // the rule).
                    if !heads_match(context, sides.0, target) {
                        cursor.partner_literal += 1;
                        continue;
                    }
                    let mut output: [Literal; kInferenceClauseLiterals] =
                        [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                            kInferenceClauseLiterals];
                    let outcome = superpose(
                        context,
                        &workspace.premise[..premise_len],
                        literal_position,
                        given,
                        literal_index,
                        &cursor.path[..cursor.path_len as usize],
                        &mut output,
                    );
                    match outcome {
                        Ok(crate::inference::superposition::SuperpositionOutcome::Concluded(
                            count,
                        )) => {
                            if !append(
                                buffer,
                                &output[..count],
                                InferenceRule::Superposition,
                                [given_id, partner_clause.id.0],
                                cursor,
                            ) {
                                return Ok(true);
                            }
                        }
                        Ok(crate::inference::superposition::SuperpositionOutcome::None) => {}
                        Err(crate::inference::InferenceError::ConclusionTooLong) => {
                            cursor.dropped += 1;
                        }
                        Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
                            cursor.dropped += 1;
                        }
                        // CEP-1050: materialization bound errors are dropped, not
                        // fatal (the rules restore the pre-unification trail on
                        // every Err).
                        Err(crate::inference::InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::DepthExceeded,
                        )) => {
                            cursor.dropped += 1;
                        }
                        Err(crate::inference::InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::WeightExceeded,
                        )) => {
                            cursor.dropped += 1;
                        }
                        Err(error) => return Err(SearchError::Inference(error)),
                    }
                    cursor.partner_literal += 1;
                    if buffer.count >= buffer.clauses.len() {
                        return Ok(true);
                    }
                }
                cursor.partner += 1;
                cursor.partner_literal = 0;
            }
            cursor.partner = 0;
            cursor.partner_literal = 0;
            if !advance_path(context.terms, atom, &mut cursor.path, &mut cursor.path_len) {
                cursor.path_len = 0;
                break;
            }
        }
        cursor.literal += 1;
        cursor.path_len = 0;
        cursor.partner = 0;
        cursor.partner_literal = 0;
    }
    Ok(false)
}

// CEP:WHAT: One superposition-from attempt per call iteration: the given clause's equation cursor.literal superposed into (cursor.slot, cursor.partner_literal, cursor.path) of the active scan.
// CEP:WHY: The unindexed from-direction (ticket CEP-1027 for the subterm index): for each positive equation literal of the given clause, scan active slots in order, and for each literal and non-root subterm position try superposition; the head prefilter (the from side's left term and the into target must share their head symbol, mirroring the into-scan) prunes the scan before the rule call; the cursor (slot, partner_literal, path) makes the scan resumable.
// CEP:STATUS: complete
// CEP:FAILURE: propagates SearchError; drops counted.
// CEP:ASSUMES: none.
// CEP:COST: one head prefilter plus one rule call per surviving (slot, literal, position); the scan is O(active) across the clause's generation.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::superposition_from_fires.
// CEP:SECURITY: bounded by the active capacity and the per-clause budget.
fn step_superposition_from(
    inputs: &mut ScanInputs<'_>,
    cursor: &mut GenerationCursor,
    buffer: &mut InferenceBuffer,
) -> Result<bool, SearchError> {
    let ScanInputs {
        context,
        store,
        active,
        given,
        given_id,
        workspace,
    } = &mut *inputs;
    let context: &InferenceContext<'_> = context;
    let store: &ClauseStore<'_> = store;
    let active: &ActiveSet<'_> = active;
    let given: &[Literal] = given;
    let given_id: u64 = *given_id;
    let workspace: &mut GenerationWorkspace = workspace;
    if given.is_empty() {
        return Ok(false);
    }
    // The given clause is fixed for the whole scan: count its variables once
    // instead of once per active slot (the renamed premises extend this
    // namespace per partner).
    let given_variables = crate::inference::count_clause_variables(context.terms, given)
        .map_err(SearchError::Inference)?;
    while cursor.literal < given.len() as u32 {
        let equation_index = cursor.literal as usize;
        // Only positive equations can be from-side premises.
        let is_equation = given[equation_index].is_positive()
            && matches!(
                context.terms.term(given[equation_index].atom()),
                Ok(view) if view.tag() == TermTag::Equality
            );
        if !is_equation {
            cursor.literal += 1;
            cursor.slot = 0;
            cursor.partner_literal = 0;
            cursor.path_len = 0;
            continue;
        }
        // The from side is fixed for this equation: hoist its sides for the
        // head prefilter (None means a malformed equation - defensive skip,
        // counted, never a panic).
        let from_sides = match crate::inference::factoring::equality_sides(
            context.terms,
            given[equation_index].atom(),
        ) {
            Some(value) => value,
            None => {
                cursor.dropped += 1;
                cursor.literal += 1;
                cursor.slot = 0;
                cursor.partner_literal = 0;
                cursor.path_len = 0;
                continue;
            }
        };
        while cursor.slot < active.len() {
            let slot = match active.slot(cursor.slot) {
                Some(value) => value,
                None => break,
            };
            let premise_len =
                match load_renamed_premise(context, store, slot.offset, given_variables, workspace)
                {
                    Some(value) => value,
                    None => {
                        cursor.dropped += 1;
                        cursor.slot += 1;
                        cursor.partner_literal = 0;
                        cursor.path_len = 0;
                        continue;
                    }
                };
            let partner_clause =
                match store.clause(crate::ir::clause::ClausePtr::from_u32(slot.offset)) {
                    Ok(value) => value,
                    Err(_) => {
                        cursor.dropped += 1;
                        cursor.slot += 1;
                        cursor.partner_literal = 0;
                        cursor.path_len = 0;
                        continue;
                    }
                };
            while (cursor.partner_literal as usize) < premise_len {
                let into_index = cursor.partner_literal as usize;
                let atom = workspace.premise[into_index].atom();
                // Enter the literal at its first non-root position: the rule
                // contracts address subterm positions only (the atom root is
                // never an into target); an atom with no subterm positions
                // moves straight to the next partner literal.
                if cursor.path_len == 0
                    && !advance_path(context.terms, atom, &mut cursor.path, &mut cursor.path_len)
                {
                    cursor.path_len = 0;
                    cursor.partner_literal += 1;
                    continue;
                }
                while let Some(target) = crate::inference::superposition::subterm_at_public(
                    context.terms,
                    atom,
                    &cursor.path[..cursor.path_len as usize],
                ) {
                    // Head prefilter (mirrors the into-scan): the from side's
                    // left term and the into target must share their head
                    // symbol (a variable left side never matches here and can
                    // never orient in the rule).
                    if !heads_match(context, from_sides.0, target) {
                        if !advance_path(
                            context.terms,
                            atom,
                            &mut cursor.path,
                            &mut cursor.path_len,
                        ) {
                            cursor.path_len = 0;
                            break;
                        }
                        continue;
                    }
                    let mut output: [Literal; kInferenceClauseLiterals] =
                        [Literal::new(crate::ir::term::TermPtr::invalid(), true);
                            kInferenceClauseLiterals];
                    let outcome = superpose(
                        context,
                        given,
                        equation_index,
                        &workspace.premise[..premise_len],
                        into_index,
                        &cursor.path[..cursor.path_len as usize],
                        &mut output,
                    );
                    match outcome {
                        Ok(crate::inference::superposition::SuperpositionOutcome::Concluded(
                            count,
                        )) => {
                            if !append(
                                buffer,
                                &output[..count],
                                InferenceRule::Superposition,
                                [given_id, partner_clause.id.0],
                                cursor,
                            ) {
                                // Advance-after-completion: the path cursor stays AT
                                // this position for the resumed call.
                                return Ok(true);
                            }
                        }
                        Ok(crate::inference::superposition::SuperpositionOutcome::None) => {}
                        Err(crate::inference::InferenceError::ConclusionTooLong) => {
                            cursor.dropped += 1;
                        }
                        Err(crate::inference::InferenceError::VariableBudgetExceeded) => {
                            cursor.dropped += 1;
                        }
                        // CEP-1050: materialization bound errors are dropped, not
                        // fatal (the rules restore the pre-unification trail on
                        // every Err).
                        Err(crate::inference::InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::DepthExceeded,
                        )) => {
                            cursor.dropped += 1;
                        }
                        Err(crate::inference::InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::WeightExceeded,
                        )) => {
                            cursor.dropped += 1;
                        }
                        Err(error) => return Err(SearchError::Inference(error)),
                    }
                    if buffer.count >= buffer.clauses.len() {
                        return Ok(true);
                    }
                    if !advance_path(context.terms, atom, &mut cursor.path, &mut cursor.path_len) {
                        cursor.path_len = 0;
                        break;
                    }
                }
                cursor.partner_literal += 1;
                cursor.path_len = 0;
            }
            cursor.slot += 1;
            cursor.partner_literal = 0;
            cursor.path_len = 0;
        }
        cursor.literal += 1;
        cursor.slot = 0;
        cursor.partner_literal = 0;
        cursor.path_len = 0;
    }
    Ok(false)
}
