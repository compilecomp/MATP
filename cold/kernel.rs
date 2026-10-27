// CEP:FILE: cold/kernel/mod.rs
// CEP:WHAT: Certified proof kernel module (Formal Spec 19): the internal step-by-step verifier behind check_proof - the derivation-DAG walk, the bounded replay engine, and the per-rule verification arms (resolution and superposition with standardize-apart replay, factoring, equality resolution/factoring, exact per-step demodulation over the CEP-1036 chain, AVATAR split replay, SatLearn shape checks, conjecture reductio, parentless theory introductions; deletion-rule derivations are rejected).
// CEP:WHY: Design 18.4: "an ATP that produces an invalid proof is worse than one that produces no proof" - the kernel is the single trusted verifier every proof passes through before MAPT claims Theorem or emits TSTP output; it replays the PRODUCTION rule functions between the recorded parents (not a parallel reimplementation), charges every replay attempt against a named budget (CEP&CC 23: measured cost, 22.10: DoS bound), and reports either Valid, a rejection naming the offending clause id and reason, or a loud budget error (CEP&CC 34.3: injectable budgets so tests exercise exhaustion on the production path).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring and the kernel vocabulary only.
// CEP:ASSUMES: cold code runs after the hot search, never inside it; the caller's inference context shares the store that recorded the derivation.
// CEP:COST: compile-time only; per-step costs are documented in kernel.rs.
// CEP:EVIDENCE: unit/cold/kernel_test.rs; unit/cold/tstp_test.rs (the kernel-backed checker); property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: the kernel is the trust boundary of design 18.4: every rejection names its step, budget exhaustion is an error, and no arm ever trusts the derivation record's own claim without replaying it.

// CEP:FILE: cold/kernel.rs
// CEP:WHAT: The certified proof kernel (Formal Spec 19): the derivation-DAG walk, the bounded replay state, and the per-rule verification arms that re-run the PRODUCTION inference functions between the recorded parents of every reachable derivation step.
// CEP:WHY: Design 18.4 and Spec 19: proof validation is the soundness certification of the search - a proof MAPT cannot internally re-verify is not a proof; the kernel walks the derivation DAG from the refuting empty clause (monotonic clause ids make one descending pass exact, Spec 14 section 2), then verifies every reachable step by replaying the production rule functions (resolve, superpose, factor, equality_factor, equality_resolve, demodulate, try_split_with) over the recorded parents and accepting a step exactly when some legal application reproduces the recorded conclusion modulo the loop's restandardize/dedupe pipeline; resolution and superposition replays standardize apart exactly like the generator (the CEP-1054 rename-apart repair: the renamed premise is replayed at its FULL literal count, not the variable count the rename returns), demodulation replays the CEP-1036 chain EXACTLY per step (a Demodulation derivation whose rule parent is unrecorded is rejected as UnrecordedRule), AVATAR splits replay the production split decision and compare each restandardized component multiset (the pre-Phase-5 pointer-equality check falsely rejected components restandardized into their own dense namespaces), SatLearn lemmas must have the assertion-atom shape (0-ary predicate atoms; conflict lemmas additionally all-negative over an empty anchor), and deletion-rule derivations are rejected outright (DeletedRuleDerivation - deletion removes clauses, it never derives records).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Verification outcomes are the KernelVerdict/KernelError vocabulary: Valid, Invalid { clause_id, rejection } (a rejected step names itself), or KernelError::ReplayBudgetExhausted (the verification could not finish - an error, never a rejection); no arm panics and no arm trusts the derivation record without replaying it.
// CEP:ASSUMES: the caller's inference context shares the term store and symbol table that recorded the derivation; the context's substitution is at baseline depth on entry (every replay unwinds per attempt, mirroring the generator's discipline).
// CEP:COST: the walk is O(max id) with one record read per marked ancestor; verification charges one unit per walked id and one unit per replayed rule attempt against the injectable budget (CEP&CC 23: the measured cost of the trust decision; 22.10: bounded adversarial work).
// CEP:EVIDENCE: unit/cold/kernel_test.rs::{accepts_loop_refutation, rejects_broken_resolution, resolution_replay_renames_apart, rejects_deletion_rule_derivation, rejects_budget_exhaustion, rejects_non_monotonic_derivation, tstp_wrapper_maps_rejections}; unit/cold/tstp_test.rs (the kernel-backed checker); property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: the kernel is the trust boundary of design 18.4: budgets bound the work, every rejection names its step, and budget exhaustion is loud.
// CEP:UNSAFE: none; this file is safe Rust.

use mapt_config::limits::{
    kAvatarMinComponentSize, kFirstClauseId, kInvalidClauseId, kMaxClauseLiterals,
};
use mapt_hot::inference::demodulation::{demodulate, unit_equation_sides};
use mapt_hot::inference::factoring::{equality_factor, factor};
use mapt_hot::inference::resolution::{resolve, ResolutionOutcome};
use mapt_hot::inference::superposition::{equality_resolve, superpose, SuperpositionOutcome};
use mapt_hot::inference::InferenceContext;
use mapt_hot::ir::clause::{ClauseId, ClauseStore, InferenceRule};
use mapt_hot::ir::literal::Literal;
use mapt_hot::ir::term::TermPtr;
use mapt_hot::search::generate::advance_path;

/// CEP:WHAT: Reasons the kernel rejects one derivation step.
/// CEP:WHY: CEP&CC Law 6: every rejection names its reason; the vocabulary distinguishes "the replay found no legal application" (Broken*) from "the derivation record is structurally unusable" (NonMonotonicDerivation, UnreadableClause, UnrecordedRule, DeletedRuleDerivation, UnknownRule, BrokenIntroduction).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the rejection vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/kernel_test.rs (one rejection per arm).
/// CEP:SECURITY: rejections are the corruption reports of design 18.4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelRejection {
    /// CEP:WHAT: A parent id is not strictly older than its child (or a required parent slot is unrecorded for the walk).
    /// CEP:WHY: Monotonic clause ids make parents strictly older (Spec 14 section 2); a violation is a corrupted derivation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_non_monotonic_derivation.
    /// CEP:SECURITY: corruption detection.
    NonMonotonicDerivation,
    /// CEP:WHAT: A clause record in the derivation could not be read.
    /// CEP:WHY: The walk and the arms resolve parents by id; an unresolvable id cannot be replayed.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::proof_walk_resolves_parents.
    /// CEP:SECURITY: bounds-checked reads surface here.
    UnreadableClause,
    /// CEP:WHAT: The derivation claims a deletion rule (forward/backward subsumption, subsumption resolution, tautology deletion, condensation).
    /// CEP:WHY: Deletion removes clauses; it never derives a stored record, so such a derivation is corrupt by construction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_deletion_rule_derivation.
    /// CEP:SECURITY: corruption detection.
    DeletedRuleDerivation,
    /// CEP:WHAT: A Demodulation derivation whose rule parent (derivation parent 1) is unrecorded.
    /// CEP:WHY: The CEP-1036 chain records the demodulating rule clause id per step; without it the exact per-step replay is impossible, so the step is rejected (the pre-Phase-5 structural variant acceptance is gone).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::checker_rejects_unrecorded_demodulation.
    /// CEP:SECURITY: proof validation.
    UnrecordedRule,
    /// CEP:WHAT: A parentless introduction claims parents.
    /// CEP:WHY: Input, NegatedConjecture, the induction schemes, ConjectureNegation, and TheoryLemma are axioms or recorded introductions; existence is checked by the walk and parents would be a corrupt label.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenIntroduction,
    /// CEP:WHAT: No legal resolution application between the renamed parents reproduces the conclusion.
    /// CEP:WHY: The arm replays the production resolve() over every complementary eligible pair.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_broken_resolution.
    /// CEP:SECURITY: proof validation.
    BrokenResolution,
    /// CEP:WHAT: No legal factoring application reproduces the conclusion.
    /// CEP:WHY: The arm replays the production factor() over every ascending literal pair.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenFactoring,
    /// CEP:WHAT: No legal superposition application in either premise order reproduces the conclusion.
    /// CEP:WHY: The arm replays the production superpose() over every equation, target literal, and non-root subterm path with the standardize-apart rename of the active parent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenSuperposition,
    /// CEP:WHAT: No legal equality-resolution application reproduces the conclusion.
    /// CEP:WHY: The arm replays the production equality_resolve() over every literal.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenEqualityResolution,
    /// CEP:WHAT: No legal equality-factoring application reproduces the conclusion.
    /// CEP:WHY: The arm replays the production equality_factor() over every ordered distinct literal pair.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenEqualityFactoring,
    /// CEP:WHAT: No legal demodulation application of the recorded rule reproduces the conclusion.
    /// CEP:WHY: The arm replays the production demodulate() with the recorded rule over every literal and non-root position of the chain parent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::checker_rejects_unrecorded_demodulation.
    /// CEP:SECURITY: proof validation.
    BrokenDemodulation,
    /// CEP:WHAT: The recorded component clause is not a component of the production split of its parent.
    /// CEP:WHY: The arm replays try_split_with and compares each restandardized component multiset (the pointer-equality check was a false rejector, fixed in Phase 5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
    /// CEP:SECURITY: proof validation.
    BrokenAvatarSplit,
    /// CEP:WHAT: A SatLearn lemma without the assertion-atom shape (0-ary predicate atoms), or a conflict lemma that is not all-negative over an empty anchor.
    /// CEP:WHY: Spec 18 section 5: the two SatLearn shapes are the only legal introductions of assertion atoms; any other shape is a corrupt label.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::{conflict_lemma_staged_and_verifiable, transfer_learnts_enter_passive}.
    /// CEP:SECURITY: proof validation.
    BrokenSatLearn,
    /// CEP:WHAT: The reductio shape fails (wrong parent roles, non-complement negation, non-empty subproof, or detached ancestry).
    /// CEP:WHY: Spec 17 section 4: the ConjectureLemma rule is a reductio over the negation premise and the subproof's empty clause.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::checker_accepts_conjecture_lemma.
    /// CEP:SECURITY: proof validation.
    BrokenReductio,
    /// CEP:WHAT: A TheoryLemma record claims parents.
    /// CEP:WHY: Theory lemmas are recorded introductions (Spec 19 section 5); the walk checks existence, the arm checks the parentless shape.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: proof validation.
    BrokenTheoryLemma,
}

/// CEP:WHAT: The kernel's verdict on one proof: Valid, or Invalid with the offending clause id and rejection reason.
/// CEP:WHY: Design 18.4: an invalid step rejects the whole proof; the payload names the step so diagnostics and the TSTP wrapper can report precisely.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/kernel_test.rs (the whole file).
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelVerdict {
    /// CEP:WHAT: Every reachable step replayed successfully.
    /// CEP:WHY: The trust decision.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
    /// CEP:SECURITY: none.
    Valid,
    /// CEP:WHAT: One step was rejected; the payload names the clause id and the reason.
    /// CEP:WHY: The corruption report.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the id is the rejected step's clause id (or the offending parent's).
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_broken_resolution.
    /// CEP:SECURITY: none.
    Invalid {
        /// CEP:WHAT: The rejected step's clause id (or the offending parent's id for walk-level rejections).
        /// CEP:WHY: Diagnostics.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 8 bytes.
        /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_non_monotonic_derivation.
        /// CEP:SECURITY: none.
        clause_id: u64,
        /// CEP:WHAT: The rejection reason.
        /// CEP:WHY: CEP&CC Law 6.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: enum copy.
        /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_deletion_rule_derivation.
        /// CEP:SECURITY: none.
        rejection: KernelRejection,
    },
}

/// CEP:WHAT: The kernel's process-level failures: the verification could not finish.
/// CEP:WHY: CEP&CC 34.3: budget exhaustion is an ERROR (the caller decides what to do - the proof is neither verified nor rejected), never silently mapped onto a rejection.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the error vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
/// CEP:SECURITY: the budget is the DoS bound (22.10).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelError {
    /// CEP:WHAT: The replay budget (the injectable bound, production default kKernelReplayBudget) was exhausted before verification finished.
    /// CEP:WHY: Bounded verification work (CEP&CC 23).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
    /// CEP:SECURITY: denial-of-service bound.
    ReplayBudgetExhausted,
}

/// CEP:WHAT: The bounded replay state: the spent action count against the injectable budget.
/// CEP:WHY: One accounting point (CEP&CC Law 3): the walk charges one unit per visited id and every arm charges one unit per replayed rule attempt; exhaustion is KernelError, not a rejection.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: charge returns KernelError::ReplayBudgetExhausted when the spend would exceed the budget.
/// CEP:ASSUMES: one state per verification call.
/// CEP:COST: one add and one compare per charge.
/// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
/// CEP:SECURITY: the DoS bound (22.10).
struct ReplayState {
    /// CEP:WHAT: The spent action count.
    /// CEP:WHY: The accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
    /// CEP:SECURITY: none.
    spent: u64,
    /// CEP:WHAT: The injectable budget.
    /// CEP:WHY: CEP&CC 34.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
    /// CEP:SECURITY: none.
    budget: u64,
}

impl ReplayState {
    // CEP:WHAT: Charges cost actions, failing loudly when the budget would be exceeded.
    // CEP:WHY: The single accounting point.
    // CEP:STATUS: complete
    // CEP:FAILURE: KernelError::ReplayBudgetExhausted.
    // CEP:ASSUMES: none.
    // CEP:COST: one add and one compare.
    // CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
    // CEP:SECURITY: none.
    fn charge(&mut self, cost: u64) -> Result<(), KernelError> {
        self.spent += cost;
        if self.spent > self.budget {
            return Err(KernelError::ReplayBudgetExhausted);
        }
        Ok(())
    }
}

// CEP:WHAT: Reads one record's literals into a Vec.
// CEP:WHY: The arms and the writer consume literal slices; one reader keeps the bounds-checked record reads in one place.
// CEP:STATUS: complete
// CEP:FAILURE: None on an unreadable literal (the caller rejects or errors).
// CEP:ASSUMES: the record belongs to the store.
// CEP:COST: O(literals).
// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
// CEP:SECURITY: bounds-checked reads.
fn read_literals(
    store: &ClauseStore<'_>,
    record: &mapt_hot::ir::clause::Clause,
) -> Option<Vec<Literal>> {
    let mut literals = Vec::with_capacity(record.literal_count as usize);
    for index in 0..record.literal_count {
        literals.push(store.literal(record, index).ok()?);
    }
    Some(literals)
}

// CEP:WHAT: Walks the derivation DAG from the refutation and collects the reachable clause ids, ascending.
// CEP:WHY: Design 18.2 step 1-2: traverse from the empty clause to the axioms and prune everything unreachable; parents are strictly older than children (monotonic ids, Spec 14 section 2), so one descending pass marks the ancestry exactly and a parent-above-child violation is a corrupted derivation (NonMonotonicDerivation); the kernel owns the walk and the TSTP writer delegates to it (Spec 19 section 3).
// CEP:STATUS: complete
// CEP:FAILURE: Err((offending id, NonMonotonicDerivation)) for a parent id not strictly below its child, Err((offending id, UnreadableClause)) for an unresolvable id.
// CEP:ASSUMES: refutation is a store-produced offset; the store has an id side table.
// CEP:COST: O(max id) scan plus O(ancestry) record reads.
// CEP:EVIDENCE: unit/cold/kernel_test.rs::{accepts_loop_refutation, rejects_non_monotonic_derivation}; unit/cold/tstp_test.rs::{proof_walk_resolves_parents, cycle_detected, prunes_unreachable_steps}.
// CEP:SECURITY: all reads bounds-checked.
pub fn walk_proof_dag(
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<Vec<u64>, (u64, KernelRejection)> {
    let root = store
        .clause(mapt_hot::ir::clause::ClausePtr::from_u32(refutation))
        .map_err(|_| (0, KernelRejection::UnreadableClause))?;
    let max_id = root.id.0;
    if max_id < kFirstClauseId {
        return Err((max_id, KernelRejection::UnreadableClause));
    }
    let span = (max_id - kFirstClauseId + 1) as usize;
    let mut marked: Vec<bool> = vec![false; span];
    marked[(max_id - kFirstClauseId) as usize] = true;
    let mut id = max_id;
    loop {
        if marked[(id - kFirstClauseId) as usize] {
            let record = store
                .clause_by_id(ClauseId(id))
                .map_err(|_| (id, KernelRejection::UnreadableClause))?;
            for parent in record.derivation.parents.iter() {
                if *parent == kInvalidClauseId {
                    continue;
                }
                if *parent >= id || *parent < kFirstClauseId {
                    return Err((*parent, KernelRejection::NonMonotonicDerivation));
                }
                marked[(*parent - kFirstClauseId) as usize] = true;
            }
        }
        if id == kFirstClauseId {
            break;
        }
        id -= 1;
    }
    let mut reachable: Vec<u64> = Vec::new();
    for (index, flag) in marked.iter().enumerate() {
        if *flag {
            reachable.push(kFirstClauseId + index as u64);
        }
    }
    Ok(reachable)
}

// CEP:WHAT: Shorthand for an Invalid verdict.
// CEP:WHY: The rejection sites read as one word.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum construction.
// CEP:EVIDENCE: unit/cold/kernel_test.rs.
// CEP:SECURITY: none.
fn invalid(clause_id: u64, rejection: KernelRejection) -> KernelVerdict {
    KernelVerdict::Invalid {
        clause_id,
        rejection,
    }
}

// CEP:WHAT: Applies the loop's conclusion pipeline to a replayed conclusion: restandardize, dedupe.
// CEP:WHY: The search stores conclusions after restandardize_clause + dedupe (Spec 08 section 6); the kernel must compare through the same pipeline or every replay would mismatch.
// CEP:STATUS: complete
// CEP:FAILURE: a restandardization failure is a Broken* rejection of the step under verification.
// CEP:ASSUMES: literals.len() <= kMaxClauseLiterals.
// CEP:COST: O(n^2).
// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
// CEP:SECURITY: none.
fn pipeline(
    context: &InferenceContext<'_>,
    literals: &mut [Literal],
    count: usize,
) -> Result<usize, KernelRejection> {
    mapt_hot::inference::restandardize_clause(
        context.terms,
        context.symbols,
        &mut literals[..count],
    )
    .map_err(|_| KernelRejection::BrokenResolution)?;
    // Dedupe (the loop's dedupe_literals semantics: drop exact (atom, polarity) repeats).
    let mut write: usize = 0;
    for read in 0..count {
        let duplicate = (0..write).any(|slot| {
            literals[slot].atom() == literals[read].atom()
                && literals[slot].is_positive() == literals[read].is_positive()
        });
        if !duplicate {
            literals[write] = literals[read];
            write += 1;
        }
    }
    Ok(write)
}

// CEP:WHAT: Compares two literal multisets for equality (atom pointer and polarity).
// CEP:WHY: The store's records are canonically sorted and hash-consing makes atom pointer equality atom equality (design 5.1), so multiset equality is canonical-order equality after both sides pass the same restandardize/dedupe pipeline.
// CEP:STATUS: complete
// CEP:FAILURE: none; returns the boolean.
// CEP:ASSUMES: both slices passed the same pipeline.
// CEP:COST: O(n^2) worst case (n <= 512, typical < 10).
// CEP:EVIDENCE: unit/cold/kernel_test.rs::accepts_loop_refutation.
// CEP:SECURITY: none.
fn same_multiset(left: &[Literal], right: &[Literal]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut used: Vec<bool> = vec![false; right.len()];
    for literal in left.iter() {
        let mut found = false;
        for (index, other) in right.iter().enumerate() {
            if !used[index]
                && other.atom() == literal.atom()
                && other.is_positive() == literal.is_positive()
            {
                used[index] = true;
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

// CEP:WHAT: Walks the derivation DAG from one clause id looking for an ancestor id.
// CEP:WHY: The ConjectureLemma reductio arm (Spec 17 section 4) must verify that the negation premise is an ancestor of the subproof's empty clause; parents are strictly older than children (monotonic ids, Spec 14 section 2), so the walk terminates at parentless introductions; a visited bitmap indexed by (id - kFirstClauseId) keeps the walk linear in the id span.
// CEP:STATUS: complete
// CEP:FAILURE: None for an unreadable record on the path; Ok(false) when the target is not an ancestor.
// CEP:ASSUMES: both ids are valid store ids.
// CEP:COST: O(id span) bitmap plus O(visited ancestors) record reads.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::checker_accepts_conjecture_lemma (the accept and detached-reject paths).
// CEP:SECURITY: all reads bounds-checked.
fn ancestor_of(store: &ClauseStore<'_>, from_id: u64, target_id: u64) -> Option<bool> {
    if from_id == target_id {
        return Some(true);
    }
    if from_id < kFirstClauseId || target_id < kFirstClauseId || target_id >= from_id {
        return Some(false);
    }
    let span = (from_id - kFirstClauseId + 1) as usize;
    let mut visited: Vec<u8> = vec![0; span];
    let mut stack: Vec<u64> = vec![from_id];
    while let Some(current) = stack.pop() {
        if current < kFirstClauseId || current > from_id {
            continue;
        }
        let slot = (current - kFirstClauseId) as usize;
        if visited[slot] != 0 {
            continue;
        }
        visited[slot] = 1;
        if current == target_id {
            return Some(true);
        }
        let record = store.clause_by_id(ClauseId(current)).ok()?;
        for slot_index in 0..record.derivation.parent_count as usize {
            let parent = record.derivation.parents[slot_index];
            if parent != kInvalidClauseId && parent >= kFirstClauseId {
                stack.push(parent);
            }
        }
    }
    Some(false)
}

// CEP:WHAT: Renames the active premise into the window above the base clause's variables and returns the FULL renamed literal slice.
// CEP:WHY: The generator standardizes apart before every rule call (Spec 02 section 5); the kernel replays the same rename. The rename function returns the VARIABLE count of the source, not its literal count - slicing the renamed buffer at the returned count silently truncated ground premises to zero literals (the CEP-1054 latent defect); the kernel slices at the source's literal count.
// CEP:STATUS: complete
// CEP:FAILURE: None when the rename fails (namespace bound) - the caller skips the replay order, matching the generator's drop.
// CEP:ASSUMES: literals.len() <= kMaxClauseLiterals.
// CEP:COST: O(total term nodes).
// CEP:EVIDENCE: unit/cold/kernel_test.rs::resolution_replay_renames_apart.
// CEP:SECURITY: none.
fn renamed_apart(
    context: &InferenceContext<'_>,
    base: &[Literal],
    active: &[Literal],
) -> Option<Vec<Literal>> {
    let base_variables = mapt_hot::inference::count_clause_variables(context.terms, base).ok()?;
    let mut renamed: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); active.len()];
    mapt_hot::inference::rename_clause_apart(
        context.terms,
        context.symbols,
        active,
        base_variables as u32,
        &mut renamed,
    )
    .ok()?;
    Some(renamed)
}

// CEP:WHAT: Verifies one derivation step by replaying its rule between its recorded parents.
// CEP:WHY: Spec 19 section 4: one arm per InferenceRule variant; the replay uses the PRODUCTION rule functions, the conclusion comparison goes through the loop's pipeline, and every replay attempt charges the budget.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(()) on acceptance; Err(rejection) names the failed check; budget exhaustion propagates as KernelError.
// CEP:ASSUMES: the parents resolve through the store; the step id is valid; the context's substitution is at baseline depth.
// CEP:COST: one unit per replay attempt plus the rule's own cost.
// CEP:EVIDENCE: unit/cold/kernel_test.rs (the whole file).
// CEP:SECURITY: a tampered derivation or conclusion is rejected.
fn verify_step(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    id: u64,
    state: &mut ReplayState,
) -> Result<Result<(), KernelRejection>, KernelError> {
    state.charge(1)?;
    let record = match store.clause_by_id(ClauseId(id)) {
        Ok(value) => value,
        Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
    };
    let conclusion = match read_literals(store, record) {
        Some(value) => value,
        None => return Ok(Err(KernelRejection::UnreadableClause)),
    };
    let parent_count = record.derivation.parent_count as usize;
    // Load the parents (monotonicity is checked per loaded parent; the walk has
    // already checked the whole ancestry, but verify_clause_step bypasses it).
    let mut left: Vec<Literal> = Vec::new();
    let mut right: Vec<Literal> = Vec::new();
    for slot in 0..parent_count.min(record.derivation.parents.len()) {
        let parent_id = record.derivation.parents[slot];
        if parent_id == kInvalidClauseId {
            continue;
        }
        if parent_id >= id || parent_id < kFirstClauseId {
            return Ok(Err(KernelRejection::NonMonotonicDerivation));
        }
        let parent = match store.clause_by_id(ClauseId(parent_id)) {
            Ok(value) => value,
            Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
        };
        let parent_literals = match read_literals(store, parent) {
            Some(value) => value,
            None => return Ok(Err(KernelRejection::UnreadableClause)),
        };
        if slot == 0 {
            left = parent_literals;
        } else {
            right = parent_literals;
        }
    }
    match record.derivation.rule {
        InferenceRule::Input
        | InferenceRule::NegatedConjecture
        | InferenceRule::StructuralInduction
        | InferenceRule::WellFoundedInduction
        | InferenceRule::ConjectureNegation => {
            // Axioms and recorded parentless introductions (Spec 19 section 5):
            // existence is checked by the walk; the shape must be parentless.
            if parent_count != 0 {
                return Ok(Err(KernelRejection::BrokenIntroduction));
            }
            Ok(Ok(()))
        }
        InferenceRule::TheoryLemma => {
            if parent_count != 0 {
                return Ok(Err(KernelRejection::BrokenTheoryLemma));
            }
            Ok(Ok(()))
        }
        InferenceRule::ForwardSubsumption
        | InferenceRule::BackwardSubsumption
        | InferenceRule::SubsumptionResolution
        | InferenceRule::TautologyDeletion
        | InferenceRule::Condensation => {
            // Deletion never derives a stored record (Spec 19 section 4).
            Ok(Err(KernelRejection::DeletedRuleDerivation))
        }
        InferenceRule::Resolution => {
            if parent_count != 2 || left.is_empty() || right.is_empty() {
                return Ok(Err(KernelRejection::BrokenResolution));
            }
            // Standardize-apart replay (CEP-1054): the active parent (derivation
            // parent 1) is renamed above the given parent's variables, exactly
            // like the generator, and replayed at its FULL literal count.
            let renamed = match renamed_apart(context, &left, &right) {
                Some(value) => value,
                None => return Ok(Err(KernelRejection::BrokenResolution)),
            };
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            for left_index in 0..left.len() {
                for right_index in 0..renamed.len() {
                    state.charge(1)?;
                    let outcome = resolve(
                        context,
                        &left,
                        left_index,
                        &renamed,
                        right_index,
                        &mut replay,
                    );
                    if let Ok(ResolutionOutcome::Concluded(count)) = outcome {
                        let piped = match pipeline(context, &mut replay, count) {
                            Ok(value) => value,
                            Err(rejection) => return Ok(Err(rejection)),
                        };
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(Ok(()));
                        }
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenResolution))
        }
        InferenceRule::Factoring => {
            if parent_count != 1 || left.is_empty() {
                return Ok(Err(KernelRejection::BrokenFactoring));
            }
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            for first in 0..left.len() {
                for second in (first + 1)..left.len() {
                    state.charge(1)?;
                    let outcome = factor(context, &left, first, second, &mut replay);
                    if let Ok(mapt_hot::inference::factoring::FactoringOutcome::Concluded(count)) =
                        outcome
                    {
                        let piped = match pipeline(context, &mut replay, count) {
                            Ok(value) => value,
                            Err(rejection) => return Ok(Err(rejection)),
                        };
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(Ok(()));
                        }
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenFactoring))
        }
        InferenceRule::Superposition => {
            if parent_count != 2 || left.is_empty() || right.is_empty() {
                return Ok(Err(KernelRejection::BrokenSuperposition));
            }
            // Both premise orders replay with the active parent (parent 1)
            // renamed above the given parent's variables (Spec 19 section 4):
            // the into-direction runs from the renamed active clause into the
            // given clause, the from-direction runs from the given clause into
            // the renamed active clause; the full renamed slice is used (the
            // CEP-1054 repair).
            let renamed = match renamed_apart(context, &left, &right) {
                Some(value) => value,
                None => return Ok(Err(KernelRejection::BrokenSuperposition)),
            };
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            // Order A: from = renamed active, into = given (SuperpositionInto).
            for equation_index in 0..renamed.len() {
                for target_index in 0..left.len() {
                    let atom = left[target_index].atom();
                    let mut path: [u16; mapt_hot::inference::superposition::kMaxPathLength] =
                        [0; mapt_hot::inference::superposition::kMaxPathLength];
                    let mut path_len: u32 = 0;
                    while advance_path(context.terms, atom, &mut path, &mut path_len) {
                        state.charge(1)?;
                        let outcome = superpose(
                            context,
                            &renamed,
                            equation_index,
                            &left,
                            target_index,
                            &path[..path_len as usize],
                            &mut replay,
                        );
                        if let Ok(SuperpositionOutcome::Concluded(count)) = outcome {
                            let piped = match pipeline(context, &mut replay, count) {
                                Ok(value) => value,
                                Err(rejection) => return Ok(Err(rejection)),
                            };
                            if same_multiset(&replay[..piped], &conclusion) {
                                return Ok(Ok(()));
                            }
                        }
                    }
                }
            }
            // Order B: from = given, into = renamed active (SuperpositionFrom).
            for equation_index in 0..left.len() {
                for target_index in 0..renamed.len() {
                    let atom = renamed[target_index].atom();
                    let mut path: [u16; mapt_hot::inference::superposition::kMaxPathLength] =
                        [0; mapt_hot::inference::superposition::kMaxPathLength];
                    let mut path_len: u32 = 0;
                    while advance_path(context.terms, atom, &mut path, &mut path_len) {
                        state.charge(1)?;
                        let outcome = superpose(
                            context,
                            &left,
                            equation_index,
                            &renamed,
                            target_index,
                            &path[..path_len as usize],
                            &mut replay,
                        );
                        if let Ok(SuperpositionOutcome::Concluded(count)) = outcome {
                            let piped = match pipeline(context, &mut replay, count) {
                                Ok(value) => value,
                                Err(rejection) => return Ok(Err(rejection)),
                            };
                            if same_multiset(&replay[..piped], &conclusion) {
                                return Ok(Ok(()));
                            }
                        }
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenSuperposition))
        }
        InferenceRule::EqualityResolution => {
            if parent_count != 1 || left.is_empty() {
                return Ok(Err(KernelRejection::BrokenEqualityResolution));
            }
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            for index in 0..left.len() {
                state.charge(1)?;
                let outcome = equality_resolve(context, &left, index, &mut replay);
                if let Ok(SuperpositionOutcome::Concluded(count)) = outcome {
                    let piped = match pipeline(context, &mut replay, count) {
                        Ok(value) => value,
                        Err(rejection) => return Ok(Err(rejection)),
                    };
                    if same_multiset(&replay[..piped], &conclusion) {
                        return Ok(Ok(()));
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenEqualityResolution))
        }
        InferenceRule::EqualityFactoring => {
            if parent_count != 1 || left.is_empty() {
                return Ok(Err(KernelRejection::BrokenEqualityFactoring));
            }
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            for first in 0..left.len() {
                for second in 0..left.len() {
                    if first == second {
                        continue;
                    }
                    state.charge(1)?;
                    let outcome = equality_factor(context, &left, first, second, &mut replay);
                    if let Ok(mapt_hot::inference::factoring::FactoringOutcome::Concluded(count)) =
                        outcome
                    {
                        let piped = match pipeline(context, &mut replay, count) {
                            Ok(value) => value,
                            Err(rejection) => return Ok(Err(rejection)),
                        };
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(Ok(()));
                        }
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenEqualityFactoring))
        }
        InferenceRule::Demodulation => {
            // Exact per-step replay over the CEP-1036 chain: parent 0 is the
            // chain predecessor, parent 1 is the demodulating rule clause; an
            // unrecorded rule parent is rejected (UnrecordedRule).
            if parent_count != 2 || left.is_empty() {
                return Ok(Err(KernelRejection::BrokenDemodulation));
            }
            let rule_id = record.derivation.parents[1];
            if rule_id == kInvalidClauseId {
                return Ok(Err(KernelRejection::UnrecordedRule));
            }
            if rule_id >= id {
                return Ok(Err(KernelRejection::NonMonotonicDerivation));
            }
            let rule_record = match store.clause_by_id(ClauseId(rule_id)) {
                Ok(value) => value,
                Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
            };
            let rule_literals = match read_literals(store, rule_record) {
                Some(value) => value,
                None => return Ok(Err(KernelRejection::UnreadableClause)),
            };
            if rule_literals.len() != 1 {
                return Ok(Err(KernelRejection::BrokenDemodulation));
            }
            let (rule_left, rule_right) = match unit_equation_sides(context, rule_literals[0]) {
                Some(value) => value,
                None => return Ok(Err(KernelRejection::BrokenDemodulation)),
            };
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kMaxClauseLiterals as usize];
            for literal_index in 0..left.len() {
                let atom = left[literal_index].atom();
                let mut path: [u16; mapt_hot::inference::superposition::kMaxPathLength] =
                    [0; mapt_hot::inference::superposition::kMaxPathLength];
                let mut path_len: u32 = 0;
                while advance_path(context.terms, atom, &mut path, &mut path_len) {
                    state.charge(1)?;
                    let outcome = demodulate(
                        context,
                        &left,
                        literal_index,
                        &path[..path_len as usize],
                        rule_left,
                        rule_right,
                        &mut replay,
                    );
                    if let Ok(mapt_hot::inference::demodulation::DemodulationOutcome::Rewritten(
                        count,
                    )) = outcome
                    {
                        let piped = match pipeline(context, &mut replay, count) {
                            Ok(value) => value,
                            Err(rejection) => return Ok(Err(rejection)),
                        };
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(Ok(()));
                        }
                    }
                }
            }
            Ok(Err(KernelRejection::BrokenDemodulation))
        }
        InferenceRule::AvatarSplit => {
            // Spec 12 Lemma 1 replayed through the production splitter: the
            // recorded component must be one of the restandardized components
            // of the production split decision over the parent (the pointer-
            // equality check falsely rejected restandardized components).
            if parent_count != 1 || left.is_empty() {
                return Ok(Err(KernelRejection::BrokenAvatarSplit));
            }
            state.charge(1)?;
            match mapt_hot::avatar::splitter::try_split_with(
                context.terms,
                &left,
                kAvatarMinComponentSize,
            ) {
                mapt_hot::avatar::splitter::SplitDecision::Unsplittable => {
                    Ok(Err(KernelRejection::BrokenAvatarSplit))
                }
                mapt_hot::avatar::splitter::SplitDecision::Splittable(view) => {
                    let mut component: Vec<Literal> = Vec::new();
                    for component_index in 0..view.component_count as usize {
                        component.clear();
                        for (position, literal) in left.iter().enumerate() {
                            if view.literal_component[position] as usize == component_index {
                                component.push(*literal);
                            }
                        }
                        if component.is_empty() {
                            continue;
                        }
                        if mapt_hot::inference::restandardize_clause(
                            context.terms,
                            context.symbols,
                            &mut component,
                        )
                        .is_err()
                        {
                            return Ok(Err(KernelRejection::BrokenAvatarSplit));
                        }
                        if same_multiset(&component, &conclusion) {
                            return Ok(Ok(()));
                        }
                    }
                    Ok(Err(KernelRejection::BrokenAvatarSplit))
                }
            }
        }
        InferenceRule::SatLearn => {
            // Spec 18 section 5: the two SatLearn shapes.
            // - Conflict lemma: one parent, the empty anchor clause of the
            //   round's refutation; the lemma is all-negative.
            // - Transfer lemma: parentless (the SAT registry entry it mirrors
            //   is verified by the SAT engine's own DRAT discipline).
            // Both shapes carry only assertion atoms: 0-ary predicate
            // applications (the reserved symbols of reserve_assertion_symbols).
            for literal in conclusion.iter() {
                state.charge(1)?;
                let view = match context.terms.term(literal.atom()) {
                    Ok(value) => value,
                    Err(_) => return Ok(Err(KernelRejection::BrokenSatLearn)),
                };
                if view.tag() != mapt_hot::ir::term::TermTag::Predicate || view.child_count() != 0 {
                    return Ok(Err(KernelRejection::BrokenSatLearn));
                }
            }
            match parent_count {
                0 => Ok(Ok(())),
                1 => {
                    let anchor_id = record.derivation.parents[0];
                    if anchor_id == kInvalidClauseId || anchor_id >= id {
                        return Ok(Err(KernelRejection::NonMonotonicDerivation));
                    }
                    let anchor = match store.clause_by_id(ClauseId(anchor_id)) {
                        Ok(value) => value,
                        Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
                    };
                    if anchor.literal_count != 0 {
                        return Ok(Err(KernelRejection::BrokenSatLearn));
                    }
                    if conclusion.iter().any(|literal| literal.is_positive()) {
                        return Ok(Err(KernelRejection::BrokenSatLearn));
                    }
                    Ok(Ok(()))
                }
                _ => Ok(Err(KernelRejection::BrokenSatLearn)),
            }
        }
        InferenceRule::ConjectureLemma => {
            // Reductio rule (Spec 17 section 4): parent 0 is the negation
            // premise (the literal-wise complement of the lemma), parent 1 is
            // the empty clause of the same subproof, and the negation is an
            // ancestor of the empty clause.
            if parent_count != 2 {
                return Ok(Err(KernelRejection::BrokenReductio));
            }
            let negation_id = record.derivation.parents[0];
            let empty_id = record.derivation.parents[1];
            if negation_id == kInvalidClauseId
                || empty_id == kInvalidClauseId
                || negation_id >= id
                || empty_id >= id
            {
                return Ok(Err(KernelRejection::BrokenReductio));
            }
            let negation = match store.clause_by_id(ClauseId(negation_id)) {
                Ok(value) => value,
                Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
            };
            if negation.derivation.rule != InferenceRule::ConjectureNegation
                || negation.literal_count != record.literal_count
            {
                return Ok(Err(KernelRejection::BrokenReductio));
            }
            // Complement shape: every lemma literal has its exact (atom, flipped
            // polarity) counterpart in the negation premise (multiset match).
            let negation_literals = match read_literals(store, negation) {
                Some(value) => value,
                None => return Ok(Err(KernelRejection::UnreadableClause)),
            };
            let mut used: Vec<bool> = vec![false; negation_literals.len()];
            for literal in conclusion.iter() {
                let mut found = false;
                for (index, used_slot) in used.iter_mut().enumerate() {
                    let other = &negation_literals[index];
                    if !*used_slot
                        && other.atom() == literal.atom()
                        && other.is_positive() != literal.is_positive()
                    {
                        *used_slot = true;
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Ok(Err(KernelRejection::BrokenReductio));
                }
            }
            let empty = match store.clause_by_id(ClauseId(empty_id)) {
                Ok(value) => value,
                Err(_) => return Ok(Err(KernelRejection::UnreadableClause)),
            };
            if empty.literal_count != 0 {
                return Ok(Err(KernelRejection::BrokenReductio));
            }
            match ancestor_of(store, empty_id, negation_id) {
                Some(true) => Ok(Ok(())),
                Some(false) => Ok(Err(KernelRejection::BrokenReductio)),
                None => Ok(Err(KernelRejection::UnreadableClause)),
            }
        }
    }
}

// CEP:WHAT: Verifies the whole proof reachable from the refutation under the given replay budget.
// CEP:WHY: Spec 19 section 3: walk, then verify every reachable step in ascending id order (parents precede children); the walk charges one unit per id and every replayed attempt charges one unit; exhaustion is an error, a failed step is a rejection naming it.
// CEP:STATUS: complete
// CEP:FAILURE: Err(KernelError::ReplayBudgetExhausted) when the budget runs out; Ok(Invalid { .. }) names the rejected step.
// CEP:ASSUMES: the context's substitution is at baseline depth (every replay unwinds per attempt); budget >= 1.
// CEP:COST: O(walk) + O(charged attempts) bounded by the budget.
// CEP:EVIDENCE: unit/cold/kernel_test.rs::{accepts_loop_refutation, rejects_budget_exhaustion}; property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: bounded verification work (CEP&CC 22.10).
pub fn verify_refutation_with_budget(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    refutation: u32,
    budget: u64,
) -> Result<KernelVerdict, KernelError> {
    let mut state = ReplayState { spent: 0, budget };
    // A walk-level failure (non-monotonic derivation, unreadable ancestor) is a
    // rejection verdict naming the offending id - not a budget error.
    let ids = match walk_proof_dag(store, refutation) {
        Ok(ids) => ids,
        Err((clause_id, rejection)) => return Ok(invalid(clause_id, rejection)),
    };
    for id in ids.iter() {
        state.charge(1)?;
        match verify_step(context, store, *id, &mut state)? {
            Ok(()) => {}
            Err(rejection) => return Ok(invalid(*id, rejection)),
        }
    }
    Ok(KernelVerdict::Valid)
}

// CEP:WHAT: Verifies ONE derivation step (existence and rule replay) under the given budget.
// CEP:WHY: Diagnostics and the clause-learning tests verify a staged lemma outside a whole-proof walk (Spec 18 section 6); the same arms run, so a step verdict equals the step's verdict inside a full verification.
// CEP:STATUS: complete
// CEP:FAILURE: Err(KernelError::ReplayBudgetExhausted); Ok(Invalid { .. }) names the rejection.
// CEP:ASSUMES: id is a valid store id; the context's substitution is at baseline depth.
// CEP:COST: one unit per replay attempt bounded by the budget.
// CEP:EVIDENCE: unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
// CEP:SECURITY: bounded verification work.
pub fn verify_clause_step(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    id: u64,
    budget: u64,
) -> Result<KernelVerdict, KernelError> {
    let mut state = ReplayState { spent: 0, budget };
    if store.clause_by_id(ClauseId(id)).is_err() {
        return Ok(invalid(id, KernelRejection::UnreadableClause));
    }
    match verify_step(context, store, id, &mut state)? {
        Ok(()) => Ok(KernelVerdict::Valid),
        Err(rejection) => Ok(invalid(id, rejection)),
    }
}
