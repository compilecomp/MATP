// CEP:FILE: hot/conjecture/filter.rs
// CEP:WHAT: The bounded refutation filter and the proof-DAG import (Spec 16 sections 5-6, Spec 17 sections 3-4): for one candidate lemma, a fresh mini search space over the shared arena re-adds the problem's input range (axioms and schemes), introduces the candidate's negation as a ConjectureNegation premise, saturates under kConjectureRefuteInferences, and on an empty clause whose ancestry contains the negation imports the whole reachable subproof into the main store (input clauses map to their main originals, derived clauses are recreated with translated parents) and adds the lemma as a ConjectureLemma reductio step.
// CEP:WHY: Soundness by construction (Spec 16 section 6 theorem): a lemma is added ONLY when its negation was refuted from the problem's own axiom range by the production inference rules - the import carries that refutation clause by clause into the main proof DAG with parents translated, so the main proof contains the complete subproof and the TSTP checker's reductio rule (negation premise is the literal-wise complement of the lemma, second parent is the empty clause, negation is an ancestor of the empty clause) accepts exactly what this filter produced; failure isolation (Spec 16 section 5): a discarded candidate leaves the main space untouched because the mini space is a separate ClauseStore over the same arena - the main store, passive set, and active set are never read-modified by the attempt; boundedness (CEP&CC 22.10, 23, 39.1): the mini capacities and inference budget are named constants, the import's fixed buffers are sized by the mini id-table capacity, and the ancestry-contains-negation requirement rejects vacuous refutations (axioms alone contradictory) that would otherwise produce uncheckable lemmas.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: CandidateOutcome::Aborted when the mini space cannot be constructed (arena pressure - the harvest stops trying further candidates); SearchError propagates only for MAIN-store operations (the lemma add); the filter itself never panics.
// CEP:ASSUMES: the main space's input range [kFirstClauseId, kFirstClauseId + input_count) is exactly the axiom set (inputs plus schemes; the plain saturate loop takes no AVATAR materializations between harvests); the candidate is a positive unit-equation literal with an interned atom.
// CEP:COST: per candidate: one mini-space construction (arena-bounded arrays), input_count clause re-adds, at most kConjectureRefuteInferences inferences, and on success an O(subproof) import; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, unprovable_candidate_adds_nothing, refute_budget_discards_unprovable, vacuous_refutation_discarded}; property/conjecture_property_test.rs::{only_proved_lemmas_added, harvest_preserves_existing_clauses}.
// CEP:SECURITY: every buffer is a fixed array sized by a named constant; all store reads are bounds-checked; the import walks only reachable ids.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic: the mini space's construction, input order, assumption placement, strategy, and inference budget are fixed functions of the main space state; the saturate loop's determinism (Spec 08 section 7) carries to the mini run; the import walks ascending ids.
// CEP:HPC-PASS-LEGALITY: Formal Spec 16 sections 5-6 fix the mini-run contract, the failure-isolation theorem, and the reductio import; Spec 17 sections 3-4 fix the id-translation invariants (monotonicity and ancestry preservation) and the checker's reductio rule; the property tests verify the invariants executably.

use crate::inference::InferenceContext;
use crate::ir::clause::{ClauseId, DerivationStep, InferenceRule};
use crate::ir::literal::Literal;
use crate::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};
use crate::search::SearchError;
use mapt_config::limits::{
    kConjectureActiveCapacity, kConjectureIdOffsets, kConjectureMaxAxioms,
    kConjecturePassiveCapacity, kConjecturePoolWords, kConjectureRefuteInferences,
    kConjectureTreeEntries, kConjectureTreeNodes, kFirstClauseId, kInvalidClauseId,
    kInvalidSubstitutionOffset, kMaxClauseLiterals, kMaxDerivationParents,
};

/// CEP:WHAT: The mini-space budgets of one refutation attempt: the six capacity bounds and the inference bound.
/// CEP:WHY: CEP&CC 34.3: every budget injectable for the exhaustion tests at small scales on the production path; production() supplies the named constants (kConjecturePassiveCapacity, kConjectureActiveCapacity, kConjectureTreeNodes, kConjectureTreeEntries, kConjecturePoolWords, kConjectureIdOffsets, kConjectureRefuteInferences), and the bounds tests inject tiny values to pin each exhaustion path.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record.
/// CEP:ASSUMES: capacities >= 1; refute_inferences >= 1.
/// CEP:COST: plain data, 32 bytes.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::{mini_passive_capacity_discards, mini_active_capacity_discards, mini_id_table_discards}; unit/hot/conjecture_test.rs::refute_budget_discards_unprovable.
/// CEP:NOTE: every capacity's exhaustion path is exercised at small scale in tests/security/induction_conjecture_bounds_test.rs; the production values are pinned by unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
/// CEP:SECURITY: the budgets are the speculative-work denial-of-service bounds under test.
pub struct MiniCapacities {
    /// CEP:WHAT: Mini passive-set capacity.
    /// CEP:WHY: Production: kConjecturePassiveCapacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
    /// CEP:SECURITY: memory bound.
    pub passive: u32,
    /// CEP:WHAT: Mini active-set capacity.
    /// CEP:WHY: Production: kConjectureActiveCapacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_active_capacity_discards.
    /// CEP:SECURITY: memory bound.
    pub active: u32,
    /// CEP:WHAT: Mini discrimination-tree node budget.
    /// CEP:WHY: Production: kConjectureTreeNodes.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
    /// CEP:SECURITY: memory bound.
    pub tree_nodes: u32,
    /// CEP:WHAT: Mini discrimination-tree entry budget.
    /// CEP:WHY: Production: kConjectureTreeEntries.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
    /// CEP:SECURITY: memory bound.
    pub tree_entries: u32,
    /// CEP:WHAT: Mini feature-vector pool words.
    /// CEP:WHY: Production: kConjecturePoolWords.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
    /// CEP:SECURITY: memory bound.
    pub pool_words: u32,
    /// CEP:WHAT: Mini clause-id offset-table capacity.
    /// CEP:WHY: Production: kConjectureIdOffsets; also the import buffers' size bound (the fixed bitmap, stack, and translation arrays are sized by it).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_id_table_discards.
    /// CEP:SECURITY: memory bound.
    pub id_offsets: u32,
    /// CEP:WHAT: Mini inference budget.
    /// CEP:WHY: Production: kConjectureRefuteInferences.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refute_budget_discards_unprovable.
    /// CEP:SECURITY: denial-of-service bound.
    pub refute_inferences: u64,
}

impl MiniCapacities {
    // CEP:WHAT: The production budgets (the named constants).
    // CEP:WHY: One constructor names the production configuration (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the constants satisfy the static assertions in config/limits.rs.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    // CEP:SECURITY: none.
    pub fn production() -> MiniCapacities {
        MiniCapacities {
            passive: kConjecturePassiveCapacity,
            active: kConjectureActiveCapacity,
            tree_nodes: kConjectureTreeNodes,
            tree_entries: kConjectureTreeEntries,
            pool_words: kConjecturePoolWords,
            id_offsets: kConjectureIdOffsets,
            refute_inferences: kConjectureRefuteInferences,
        }
    }
}

/// CEP:WHAT: The ConjectureLemma rule's parent count (the negation premise and the empty clause).
// CEP:WHY: The reductio step's shape names its arity (CEP&CC 11.3) instead of a bare 2.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: Spec 17 section 4 fixes the two-parent shape.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, checker_accepts_conjecture_lemma}.
// CEP:SECURITY: none.
const kLemmaParents: u8 = 2;

// CEP:WHAT: The outcome of one candidate's refutation attempt.
/// CEP:WHY: Law 6 vocabulary for the harvest loop: Imported means the lemma now exists in the main space with its complete subproof; Discarded means the mini run ended without a usable refutation and the main space is untouched; Aborted means the mini space could not be constructed (arena pressure) and the harvest should stop.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, unprovable_candidate_adds_nothing}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandidateOutcome {
    /// CEP:WHAT: The negation was refuted and the lemma was imported with its subproof.
    /// CEP:WHY: The harvest's success path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the lemma's parents are the imported negation premise and empty clause.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
    /// CEP:SECURITY: none.
    Imported,
    /// CEP:WHAT: The mini run gave up, saturated, or refuted without using the negation; nothing was added.
    /// CEP:WHY: The honest failure: unprovable candidates cost their bounded budget and vanish.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the main space is byte-identical to before the attempt.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{unprovable_candidate_adds_nothing, vacuous_refutation_discarded}.
    /// CEP:SECURITY: none.
    Discarded,
    /// CEP:WHAT: The mini space could not be constructed (arena pressure); the harvest should stop.
    /// CEP:WHY: Speculation must never kill the main search (Spec 16 section 5): construction failures abort the harvest, not the search.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the main arena is nearly exhausted; the main search will surface its own budget shortly.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
    /// CEP:SECURITY: none.
    Aborted,
}

// CEP:WHAT: True when the derivation rule marks a harvest-premise clause (an axiom of the problem: input, negated conjecture, or an induction scheme).
// CEP:WHY: Spec 16 section 5's premise contract: the mini refutation's axiom set is the RULE-IDENTIFIED staged clauses, never an id range - the Task 26 sev-0 review showed that the first import's age consumption shifts any id-range reading onto proof-only clauses (the imported negation premise and, with drift, the empty clause itself), which both unsoundly widens later mini premise sets and eventually discards every candidate; the rule test is position-independent and cannot drift.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum comparisons.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::two_harvests_stay_sound; property/conjecture_property_test.rs::only_proved_lemmas_added.
// CEP:SECURITY: the soundness boundary of the premise set.
fn is_axiom_rule(rule: InferenceRule) -> bool {
    matches!(
        rule,
        InferenceRule::Input
            | InferenceRule::NegatedConjecture
            | InferenceRule::StructuralInduction
            | InferenceRule::WellFoundedInduction
    )
}

// CEP:WHAT: Collects the harvest-visible axiom ids ascending, below the proof watermark, into a fixed array; returns the fill level.
// CEP:WHY: The premise set for every mini refutation: the ids are bounded by the import watermark (proof-only clauses excluded by construction), identified by rule (derived and lemma clauses excluded), and the array is capped at kConjectureMaxAxioms - a prefix truncation that is SOUND (a lemma proved from a subset of the axioms is proved from the full set) and deterministic (ascending prefix).
// CEP:STATUS: complete
// CEP:FAILURE: returns a fill level below the true axiom count on overflow (the prefix is used; the truncation is the documented bound, not an error).
// CEP:ASSUMES: the store's id side table is consistent.
// CEP:COST: O(ids below the watermark) rule reads per candidate.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{two_harvests_stay_sound, proof_watermark_bounds_harvest_scans}; config/limits.rs (kConjectureMaxAxioms).
// CEP:SECURITY: bounded buffer; the watermark bound.
fn collect_axiom_ids(main: &SearchSpace<'_>, axioms: &mut [u64; kConjectureMaxAxioms]) -> usize {
    let mut count: usize = 0;
    let bound = main.proof_base();
    let mut id = kFirstClauseId;
    while id < bound && count < axioms.len() {
        if let Ok(record) = main.store.clause_by_id(ClauseId(id)) {
            if is_axiom_rule(record.derivation.rule) {
                axioms[count] = id;
                count += 1;
            }
        }
        id += 1;
    }
    count
}

// CEP:WHAT: Runs one candidate's bounded mini refutation and imports the lemma on success.
// CEP:WHY: The filter's driver (Spec 16 section 5): fresh mini space, input re-add in order (so mini input i maps to main id kFirstClauseId + i - the trivial translation the import relies on), assumption add, saturate under the named budget with harvesting disabled (no nested speculation), and on Theorem the ancestry check plus the import.
// CEP:STATUS: complete
// CEP:FAILURE: CandidateOutcome values; SearchError propagates only from MAIN-store operations (the lemma add).
// CEP:ASSUMES: as file header; the mini options copy the main strategy/ordering/selection.
// CEP:COST: as file header; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, unprovable_candidate_adds_nothing, refute_budget_discards_unprovable}.
// CEP:SECURITY: budgets enforced by the mini options and capacities.
pub fn refute_and_maybe_import(
    main: &SearchSpace<'_>,
    main_context: &InferenceContext<'_>,
    main_options: &SearchOptions,
    candidate: Literal,
    budgets: &MiniCapacities,
) -> Result<CandidateOutcome, SearchError> {
    // The templates emit positive unit-equation candidates by construction;
    // a non-positive candidate would be "refuted" by its own copy, so the
    // filter refuses it loudly as a discard (Task 26 sev-3(5) repair).
    if !candidate.is_positive() {
        return Ok(CandidateOutcome::Discarded);
    }
    let mini_options = SearchOptions {
        strategy: main_options.strategy,
        ordering: main_options.ordering,
        selection: main_options.selection,
        inference_budget: budgets.refute_inferences,
        conjecture: false,
    };
    let mini = match SearchSpace::new_with(
        main.arena,
        &mini_options,
        budgets.passive,
        budgets.active,
        budgets.tree_nodes,
        budgets.tree_entries,
        budgets.pool_words,
        budgets.id_offsets,
    ) {
        Ok(mini) => mini,
        Err(_) => return Ok(CandidateOutcome::Aborted),
    };
    let mini_context = InferenceContext {
        terms: main_context.terms,
        symbols: main_context.symbols,
        substitution: &mini.substitution,
        precedence: main_context.precedence,
        ordering: main_context.ordering,
    };
    // Re-add the harvest-visible axioms in ascending id order: mini input i
    // <-> axiom_ids[i] (the positional mapping the import translates through).
    // The set is rule-identified and watermark-bounded (Spec 16 section 5,
    // Task 26 sev-0 repair): proof-only import clauses, derived clauses, and
    // lemmas are excluded by construction, so the premise set cannot drift.
    let mut axiom_ids: [u64; kConjectureMaxAxioms] = [kInvalidClauseId; kConjectureMaxAxioms];
    let axiom_count = collect_axiom_ids(main, &mut axiom_ids);
    let mut staging: [Literal; kMaxClauseLiterals as usize] =
        [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
    for axiom_id in axiom_ids[..axiom_count].iter() {
        let record = match main.store.clause_by_id(ClauseId(*axiom_id)) {
            Ok(record) => record,
            Err(_) => return Ok(CandidateOutcome::Discarded),
        };
        if record.literal_count as usize > staging.len() {
            return Ok(CandidateOutcome::Discarded);
        }
        for literal_index in 0..record.literal_count {
            let literal = match main.store.literal(record, literal_index) {
                Ok(literal) => literal,
                Err(_) => return Ok(CandidateOutcome::Discarded),
            };
            staging[literal_index as usize] = literal;
        }
        let slice_len = record.literal_count as usize;
        if mini
            .add_input_clause(&mini_context, &mini_options, &staging[..slice_len])
            .is_err()
        {
            return Ok(CandidateOutcome::Discarded);
        }
    }
    // The negated candidate as an assumption premise.
    let negation_literal = Literal::new(candidate.atom(), false);
    let negation_offset =
        match mini.add_assumption_clause(&mini_context, &mini_options, &[negation_literal]) {
            Ok(offset) => offset,
            Err(_) => return Ok(CandidateOutcome::Discarded),
        };
    let negation_mini_id = match mini
        .store
        .clause(crate::ir::clause::ClausePtr::from_u32(negation_offset))
    {
        Ok(record) => record.id.0,
        Err(_) => return Ok(CandidateOutcome::Discarded),
    };
    // The bounded run: the inference budget is the only stop condition.
    let never_stop = |_iterations: u64| false;
    let mut mini_stats = SearchStats::default();
    let outcome = match saturate(
        &mini,
        &mini_context,
        &mini_options,
        &never_stop,
        &mut mini_stats,
    ) {
        Ok(outcome) => outcome,
        Err(_) => return Ok(CandidateOutcome::Discarded),
    };
    let empty_offset = match outcome {
        SearchOutcome::Theorem { refutation } => refutation,
        _ => return Ok(CandidateOutcome::Discarded),
    };
    // Import: the reachable set must contain the negation (a refutation of the
    // axioms alone is vacuous and would produce an uncheckable lemma).
    let (negation_main_id, empty_main_id) = match import_refutation(
        main,
        main_context,
        main_options,
        &mini,
        empty_offset,
        negation_mini_id,
        &axiom_ids[..axiom_count],
        budgets.id_offsets,
    )? {
        Some(pair) => pair,
        None => return Ok(CandidateOutcome::Discarded),
    };
    // The lemma: reductio over the imported subproof.
    let derivation = DerivationStep {
        rule: InferenceRule::ConjectureLemma,
        parent_count: kLemmaParents,
        reserved: 0,
        parents: [
            negation_main_id,
            empty_main_id,
            kInvalidClauseId,
            kInvalidClauseId,
        ],
        substitution: kInvalidSubstitutionOffset,
    };
    main.add_derived_clause(main_context, main_options, &[candidate], derivation)?;
    Ok(CandidateOutcome::Imported)
}

// CEP:WHAT: Imports a mini refutation's reachable subproof into the main store; returns the translated (negation, empty) id pair, or None when the negation is not in the empty clause's ancestry (a vacuous refutation).
// CEP:WHY: Spec 17 section 3: the reachable set is the ancestry closure of the mini empty clause (a fixed bitmap over the mini id range, DFS with a fixed stack, all bounded by kConjectureIdOffsets); the ascending walk is topological because mini ids are monotonic (Spec 14 section 2's argument), so every parent is translated before its child; mini INPUT clauses translate to their main originals (the order-preserving re-add), every other reachable clause is recreated in the main store through add_proof_clause with the SAME rule and age and the TRANSLATED parents, so the imported chain is exactly the mini chain; the derivation substitution field stays kInvalidSubstitutionOffset everywhere (the production discipline: derivations never record trail offsets, the replay checker recomputes).
// CEP:STATUS: complete
// CEP:FAILURE: None on the vacuous case; SearchError from main-store operations.
// CEP:ASSUMES: the mini store's ids are dense in [kFirstClauseId, kFirstClauseId + live); the input re-add preserved order.
// CEP:COST: O(reachable clauses) creations plus O(mini id span) bitmap.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, vacuous_refutation_discarded}; property/conjecture_property_test.rs::{only_proved_lemmas_added, harvest_preserves_existing_clauses}.
// CEP:SECURITY: fixed buffers; only reachable ids are created (proof-only clauses never enter the main passive set).
// CEP:WHAT: Clippy allowance for the eight import parameters (one per documented input: the two spaces, the two context pieces, the two identity anchors, and the two bounds).
// CEP:WHY: CEP&CC 34.3 requires every bound injectable on the production path; an options struct would hide which caller supplies which bound, so the parameter list is the documented interface (the same discipline as SearchSpace::new_with).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refuted_candidate_imports_proof.
// CEP:SECURITY: none.
#[allow(clippy::too_many_arguments)]
fn import_refutation(
    main: &SearchSpace<'_>,
    main_context: &InferenceContext<'_>,
    main_options: &SearchOptions,
    mini: &SearchSpace<'_>,
    empty_offset: u32,
    negation_mini_id: u64,
    axiom_ids: &[u64],
    id_table_capacity: u32,
) -> Result<Option<(u64, u64)>, SearchError> {
    let mini_next = mini.store.next_clause_id().0;
    if mini_next <= kFirstClauseId || mini_next - kFirstClauseId > id_table_capacity as u64 {
        return Ok(None);
    }
    let span = (mini_next - kFirstClauseId) as usize;
    // The fixed buffers are sized by the production capacity (a compile-time
    // constant; runtime-injected smaller capacities discard earlier through
    // the span check below).
    const kImportBuffers: usize = kConjectureIdOffsets as usize;
    if span > kImportBuffers {
        return Ok(None);
    }
    // Reachability bitmap and DFS stack over the mini id range.
    let mut reachable: [bool; kImportBuffers] = [false; kImportBuffers];
    let mut stack: [u64; kImportBuffers] = [0; kImportBuffers];
    let mut stack_depth: usize = 0;
    let empty_record = match mini
        .store
        .clause(crate::ir::clause::ClausePtr::from_u32(empty_offset))
    {
        Ok(record) => record,
        Err(_) => return Ok(None),
    };
    let empty_mini_id = empty_record.id.0;
    stack[stack_depth] = empty_mini_id;
    stack_depth += 1;
    while stack_depth > 0 {
        stack_depth -= 1;
        let id = stack[stack_depth];
        if id < kFirstClauseId || id >= mini_next {
            continue;
        }
        let slot = (id - kFirstClauseId) as usize;
        if reachable[slot] {
            continue;
        }
        reachable[slot] = true;
        let record = match mini.store.clause_by_id(ClauseId(id)) {
            Ok(record) => record,
            Err(_) => return Ok(None),
        };
        for parent_slot in 0..record.derivation.parent_count as usize {
            let parent = record.derivation.parents[parent_slot];
            if parent != kInvalidClauseId
                && parent >= kFirstClauseId
                && parent < mini_next
                && stack_depth < stack.len()
            {
                stack[stack_depth] = parent;
                stack_depth += 1;
            }
        }
    }
    let negation_slot = (negation_mini_id - kFirstClauseId) as usize;
    if negation_mini_id < kFirstClauseId
        || negation_mini_id >= mini_next
        || !reachable[negation_slot]
    {
        // Vacuous refutation: the axioms alone are contradictory; the main
        // search will refute on its own, and a lemma without its negation in
        // the subproof would fail the reductio check.
        return Ok(None);
    }
    // Translation table: mini id -> main id.
    let mut translation: [u64; kImportBuffers] = [kInvalidClauseId; kImportBuffers];
    let mut negation_main_id = kInvalidClauseId;
    let mut empty_main_id = kInvalidClauseId;
    for slot in 0..span {
        if !reachable[slot] {
            continue;
        }
        let mini_id = kFirstClauseId + slot as u64;
        if slot < axiom_ids.len() {
            // A re-added axiom: translate to its main original (the positional
            // mapping of the rule-identified premise set), no creation.
            translation[slot] = axiom_ids[slot];
            continue;
        }
        let record = match mini.store.clause_by_id(ClauseId(mini_id)) {
            Ok(record) => record,
            Err(_) => return Ok(None),
        };
        if record.literal_count as usize > kMaxClauseLiterals as usize {
            return Ok(None);
        }
        let mut literals: [Literal; kMaxClauseLiterals as usize] =
            [Literal::new(crate::ir::term::TermPtr::invalid(), true); kMaxClauseLiterals as usize];
        for literal_index in 0..record.literal_count {
            let literal = match mini.store.literal(record, literal_index) {
                Ok(literal) => literal,
                Err(_) => return Ok(None),
            };
            literals[literal_index as usize] = literal;
        }
        let mut parents = [kInvalidClauseId; kMaxDerivationParents];
        let mut all_parents_translated = true;
        for (parent_slot, parent) in record.derivation.parents
            [..record.derivation.parent_count as usize]
            .iter()
            .enumerate()
        {
            let parent = *parent;
            if parent == kInvalidClauseId {
                continue;
            }
            if parent < kFirstClauseId || parent >= mini_next {
                all_parents_translated = false;
                break;
            }
            let translated = translation[(parent - kFirstClauseId) as usize];
            if translated == kInvalidClauseId {
                all_parents_translated = false;
                break;
            }
            parents[parent_slot] = translated;
        }
        if !all_parents_translated {
            // A parent outside the reachable closure cannot happen (the bitmap
            // is the closure); treat defensively as a discard, never a silent
            // gap (Law 6).
            return Ok(None);
        }
        let derivation = DerivationStep {
            rule: record.derivation.rule,
            parent_count: record.derivation.parent_count,
            reserved: 0,
            parents,
            substitution: kInvalidSubstitutionOffset,
        };
        let new_offset = main.add_proof_clause(
            main_context,
            main_options,
            &literals[..record.literal_count as usize],
            record.age,
            derivation,
        )?;
        let new_id = match main
            .store
            .clause(crate::ir::clause::ClausePtr::from_u32(new_offset))
        {
            Ok(record) => record.id.0,
            Err(_) => return Ok(None),
        };
        translation[slot] = new_id;
        if mini_id == negation_mini_id {
            negation_main_id = new_id;
        }
        if mini_id == empty_mini_id {
            empty_main_id = new_id;
        }
    }
    if negation_main_id == kInvalidClauseId || empty_main_id == kInvalidClauseId {
        return Ok(None);
    }
    Ok(Some((negation_main_id, empty_main_id)))
}
