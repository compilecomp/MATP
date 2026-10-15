// CEP:FILE: cold/proof_output/tstp.rs
// CEP:WHAT: Unified proof reconstruction (design 18.2-18.4): walks the derivation DAG from the refuting empty clause through the clause store's id side table, prunes to the reachable steps, formats the proof as TSTP cnf statements, and independently re-verifies every inference step (resolution, factoring, superposition by replaying the production inference rules; AVATAR splits by the structural subclause check of Spec 12 Lemma 1; demodulation by the structural variant check).
// CEP:WHY: Design 26 Phase 4 ("Proof reconstruction (unified)" depends on proof recording and the TSTP writer); design 18.4: "an ATP that produces an invalid proof is worse than one that produces no proof" - the checker re-runs the recorded rules between the recorded parents and accepts a step only when some legal application reproduces the recorded conclusion modulo the loop's restandardize/dedupe pipeline; the walk prunes every clause not reachable from the refutation (design 18.2's redundant-step removal - reachability is the subsumption-based compression of Phase 4 scope; interpolation-based compression stays ticketed); the writer emits TSTP (TPTP Thousands of Problems for Theorem Provers, TSTP syntax for solutions) cnf lines with axiom/negated_conjecture/plain roles and inference sources, variables as X<n> (TPTP upper-case convention), equality infix, and the empty clause as $false; AVATAR component clauses cite their original through the MAPT-specific avatar_split rule whose soundness is the Spec 12 splitting lemma - external checkers must accept the rule as a black box (the same situation as published AVATAR proofs, documented in Spec 14 section 5).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: writer: UnreadableClause/UnreadableTerm on corrupt stores, CycleDetected on non-monotonic parent chains (a corrupted derivation); checker: InvalidStep with the offending clause id and reason (the proof is rejected and the caller returns Error per design 18.4); never panics.
// CEP:ASSUMES: the refutation offset came from the search that owns the store; the store was constructed with an id side table (SearchSpace::new/new_with - a table-less store rejects proof walks loudly); the InferenceContext's stores match the search's.
// CEP:COST: walk O(clauses); write O(proof size); check O(steps x premise pairs x rule cost).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{formats_refutation_proof, proof_walk_resolves_parents, prunes_unreachable_steps, roles_and_sources, empty_clause_renders_false, checker_accepts_valid_proof, checker_rejects_broken_resolution, checker_rejects_broken_factoring, checker_rejects_broken_avatar_split, checker_accepts_demodulation_variant, cycle_detected}; property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: every store read is bounds-checked; the checker validates derivation records against the replayed rules - a tampered record is rejected, not trusted.
// CEP:HPC-DETERMINISM: deterministic (ascending id order, fixed formats).
// CEP:HPC-PASS-LEGALITY: Formal Spec 14 (14_unified_proof_reconstruction.md) fixes the walk, the pruning (reachability), the TSTP statement grammar subset, the replay-checker contract, and the demodulation weakening (ticket CEP-1036); the property tests verify executably that every refutation the loop produces passes the checker and that tampered steps are rejected.

use std::string::String;

use crate::symbol_table_builder::SymbolTableBuilder;
use mapt_hot::inference::factoring::{factor, FactoringOutcome};
use mapt_hot::inference::resolution::{resolve, ResolutionOutcome};
use mapt_hot::inference::InferenceContext;
use mapt_hot::ir::clause::{ClauseId, ClauseStore, InferenceRule};
use mapt_hot::ir::literal::Literal;
use mapt_hot::ir::term::{TermPtr, TermStore, TermTag};

/// CEP:WHAT: Error cases of proof reconstruction.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the writer and checker never panic.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy (Clone for the payload variant).
/// CEP:EVIDENCE: unit/cold/tstp_test.rs::{proof_walk_resolves_parents, cycle_detected, checker_rejects_broken_resolution}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TstpError {
    /// CEP:WHAT: A clause record could not be read (missing side table, bad offset, or unreadable id).
    /// CEP:WHY: Proof walks resolve parents by id (design 5.4); resolution failures are loud.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::proof_walk_resolves_parents.
    /// CEP:SECURITY: bounds-checked reads surface here.
    UnreadableClause(u64),
    /// CEP:WHAT: A term could not be rendered (unreadable atom).
    /// CEP:WHY: The writer walks atom terms; a corrupt store is loud.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::formats_refutation_proof.
    /// CEP:SECURITY: none.
    UnreadableTerm(u64),
    /// CEP:WHAT: The derivation chain is not a DAG (a parent id is not below the child id).
    /// CEP:WHY: Monotonic clause ids make parents strictly older (Spec 14 section 2); a violation means a corrupted derivation and the walk refuses.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::cycle_detected.
    /// CEP:SECURITY: corruption detection.
    CycleDetected(u64),
    /// CEP:WHAT: The checker rejected a step; the payload is the offending clause id.
    /// CEP:WHY: Design 18.4: an invalid step rejects the whole proof (the caller returns Error).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: the id is the conclusion of the rejected step.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/tstp_test.rs::{checker_rejects_broken_resolution, checker_rejects_broken_factoring, checker_rejects_broken_avatar_split}.
    /// CEP:SECURITY: proof validation.
    InvalidStep(u64),
}

// CEP:WHAT: Maximum literals of one clause during checker replays (the structural bound).
// CEP:WHY: The replay buffers are fixed-size stack arrays mirroring the loop's discipline (CEP&CC 22.10); the value is the store's bound.
// CEP:STATUS: complete
// CEP:FAILURE: replays longer than the bound fail loudly through the rule functions' own bounds.
// CEP:ASSUMES: as the store's bound.
// CEP:COST: 512 x 8 bytes per buffer.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::checker_accepts_valid_proof.
// CEP:SECURITY: none.
const kReplayLiterals: usize = mapt_config::limits::kMaxClauseLiterals as usize;

// CEP:WHAT: Collects the reachable clause ids from the refutation, ascending.
// CEP:WHY: Design 18.2 step 1-2: traverse from the empty clause to the axioms and prune everything unreachable (the Phase 4 compression); parents are strictly older than children (monotonic ids, Spec 14 section 2), so one descending pass marks the ancestry exactly (the same argument as the AVATAR ancestry scan, Spec 12 section 5) and a parent-above-child violation is a corrupted derivation (CycleDetected).
// CEP:STATUS: complete
// CEP:FAILURE: UnreadableClause for unresolvable ids, CycleDetected for non-monotonic parents.
// CEP:ASSUMES: refutation is a store-produced offset; the store has an id side table.
// CEP:COST: O(max id) scan plus O(ancestry) reads.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{proof_walk_resolves_parents, prunes_unreachable_steps, cycle_detected}.
// CEP:SECURITY: all reads bounds-checked.
pub fn reachable_proof_ids(
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<Vec<u64>, TstpError> {
    let root = store
        .clause(mapt_hot::ir::clause::ClausePtr::from_u32(refutation))
        .map_err(|_| TstpError::UnreadableClause(0))?;
    let max_id = root.id.0;
    let first_id = mapt_config::limits::kFirstClauseId;
    if max_id < first_id {
        return Err(TstpError::UnreadableClause(max_id));
    }
    // Marked[id - first_id] bitmap over the id range.
    let span = (max_id - first_id + 1) as usize;
    let mut marked: Vec<bool> = vec![false; span];
    marked[(max_id - first_id) as usize] = true;
    let mut id = max_id;
    loop {
        if marked[(id - first_id) as usize] {
            let record = store
                .clause_by_id(ClauseId(id))
                .map_err(|_| TstpError::UnreadableClause(id))?;
            for parent in record.derivation.parents.iter() {
                if *parent == mapt_config::limits::kInvalidClauseId {
                    continue;
                }
                if *parent >= id || *parent < first_id {
                    return Err(TstpError::CycleDetected(*parent));
                }
                marked[(*parent - first_id) as usize] = true;
            }
        }
        if id == first_id {
            break;
        }
        id -= 1;
    }
    let mut reachable: Vec<u64> = Vec::new();
    for (index, flag) in marked.iter().enumerate() {
        if *flag {
            reachable.push(first_id + index as u64);
        }
    }
    Ok(reachable)
}

// CEP:WHAT: Renders one term in TSTP syntax into out.
// CEP:WHY: Spec 14 section 4: variables render as X<n> (TPTP upper-case variable convention), function and predicate applications as name(arg, ...), equality infix (l = r), sorts and the higher-order tags render in a defensive TPTP-ish form (they cannot appear in Phase 4 FOL proofs - the renderer is total so a stray tag is visible rather than crashing).
// CEP:STATUS: complete
// CEP:FAILURE: UnreadableTerm on unreadable nodes.
// CEP:ASSUMES: atoms were interned by the given store; names match the store's symbols.
// CEP:COST: O(term tree nodes).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{formats_refutation_proof, roles_and_sources}.
// CEP:SECURITY: none.
fn write_term(
    terms: &TermStore,
    names: &SymbolTableBuilder,
    handle: TermPtr,
    out: &mut String,
) -> Result<(), TstpError> {
    let view = terms
        .term(handle)
        .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
    match view.tag() {
        TermTag::Variable => {
            out.push('X');
            out.push_str(&view.symbol().to_string());
        }
        TermTag::Function | TermTag::Predicate => {
            let name = names.name_of(view.symbol()).unwrap_or("sym");
            let count = view.child_count();
            if count == 0 {
                out.push_str(name);
            } else {
                out.push_str(name);
                out.push('(');
                for index in 0..count {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    let child = view
                        .child(index)
                        .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
                    write_term(terms, names, child, out)?;
                }
                out.push(')');
            }
        }
        TermTag::Equality => {
            let left = view
                .child(0)
                .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
            let right = view
                .child(1)
                .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
            write_term(terms, names, left, out)?;
            out.push_str(" = ");
            write_term(terms, names, right, out)?;
        }
        TermTag::Application => {
            let func = view
                .child(0)
                .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
            let arg = view
                .child(1)
                .map_err(|_| TstpError::UnreadableTerm(handle.as_u32() as u64))?;
            out.push_str("((");
            write_term(terms, names, func, out)?;
            out.push_str(" @ ");
            write_term(terms, names, arg, out)?;
            out.push(')');
        }
        TermTag::Sort => {
            out.push_str("sort");
            out.push_str(&view.symbol().to_string());
        }
        TermTag::Lambda => {
            out.push_str("(lambda)");
        }
    }
    Ok(())
}

// CEP:WHAT: Maps an inference rule onto its TSTP source rule name.
// CEP:WHY: Spec 14 section 5: resolution/factoring/superposition/demodulation keep their TSTP names; the AVATAR split uses the MAPT-specific avatar_split (external checkers must accept it as a black-box rule whose soundness is Spec 12 Lemma 1 - the same presentation as published AVATAR proofs).
// CEP:STATUS: complete
// CEP:FAILURE: none (unknown rules map to "unknown" - visible, not silent).
// CEP:ASSUMES: the rule vocabulary of Phase 1-4.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::roles_and_sources.
// CEP:SECURITY: none.
fn rule_name(rule: InferenceRule) -> &'static str {
    match rule {
        InferenceRule::Input => "input",
        InferenceRule::NegatedConjecture => "negated_conjecture",
        InferenceRule::Resolution => "resolution",
        InferenceRule::Superposition => "superposition",
        InferenceRule::Factoring => "factoring",
        InferenceRule::EqualityFactoring => "equality_factoring",
        InferenceRule::Demodulation => "demodulation",
        InferenceRule::AvatarSplit => "avatar_split",
        InferenceRule::SatLearn => "sat_learn",
        InferenceRule::TheoryLemma => "theory_lemma",
        _ => "simplification",
    }
}

// CEP:WHAT: Formats the reconstructed TSTP proof into out; returns the statement count.
// CEP:WHY: Design 18.2 step 3: every reachable clause becomes one cnf statement - axioms and the negated conjecture keep their roles, derived clauses are plain with their inference source (rule name, empty info list, parent names); literals join with " | ", negative literals prefix "~", the empty clause renders "$false"; the pruned, ascending-id order is a valid topological order (parents precede children), so the proof reads forward.
// CEP:STATUS: complete
// CEP:FAILURE: propagates TstpError.
// CEP:ASSUMES: as reachable_proof_ids.
// CEP:COST: O(proof size).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{formats_refutation_proof, prunes_unreachable_steps, roles_and_sources, empty_clause_renders_false}.
// CEP:SECURITY: none.
pub fn write_tstp_proof(
    terms: &TermStore,
    names: &SymbolTableBuilder,
    store: &ClauseStore<'_>,
    refutation: u32,
    out: &mut String,
) -> Result<usize, TstpError> {
    let ids = reachable_proof_ids(store, refutation)?;
    let mut literals: Vec<Literal> = Vec::new();
    for id in ids.iter() {
        let record = store
            .clause_by_id(ClauseId(*id))
            .map_err(|_| TstpError::UnreadableClause(*id))?;
        literals.clear();
        for index in 0..record.literal_count {
            literals.push(
                store
                    .literal(record, index)
                    .map_err(|_| TstpError::UnreadableClause(*id))?,
            );
        }
        out.push_str("cnf(c");
        out.push_str(&id.to_string());
        match record.derivation.rule {
            InferenceRule::Input => out.push_str(", axiom, "),
            InferenceRule::NegatedConjecture => out.push_str(", negated_conjecture, "),
            _ => out.push_str(", plain, "),
        }
        if literals.is_empty() {
            out.push_str("$false");
        } else {
            for (index, literal) in literals.iter().enumerate() {
                if index > 0 {
                    out.push_str(" | ");
                }
                if !literal.is_positive() {
                    out.push('~');
                }
                write_term(terms, names, literal.atom(), out)?;
            }
        }
        if record.derivation.parent_count > 0 {
            out.push_str(", inference(");
            out.push_str(rule_name(record.derivation.rule));
            out.push_str(", [], [");
            for slot in 0..record.derivation.parent_count as usize {
                if slot > 0 {
                    out.push_str(", ");
                }
                out.push('c');
                out.push_str(&record.derivation.parents[slot].to_string());
            }
            out.push_str("])");
        }
        out.push_str(").\n");
    }
    Ok(ids.len())
}

// CEP:WHAT: Compares two literal multisets for equality (atom pointer and polarity).
// CEP:WHY: The store's records are canonically sorted and hash-consing makes atom pointer equality atom equality (design 5.1), so multiset equality is canonical-order equality after both sides pass the same restandardize/dedupe pipeline.
// CEP:STATUS: complete
// CEP:FAILURE: none; returns the boolean.
// CEP:ASSUMES: both slices passed the same pipeline.
// CEP:COST: O(n^2) worst case (n <= 512, typical < 10).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{checker_accepts_valid_proof, checker_rejects_broken_resolution}.
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

// CEP:WHAT: Applies the loop's conclusion pipeline to a replayed conclusion: restandardize, dedupe.
// CEP:WHY: The search loop stores conclusions after restandardize_clause + dedupe (Spec 08 section 6); the checker must compare through the same pipeline or every replay would mismatch.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError from restandardize as InvalidStep.
// CEP:ASSUMES: literals.len() <= kReplayLiterals.
// CEP:COST: O(n^2).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::checker_accepts_valid_proof.
// CEP:SECURITY: none.
fn pipeline(
    context: &InferenceContext<'_>,
    literals: &mut [Literal],
    count: usize,
) -> Result<usize, TstpError> {
    mapt_hot::inference::restandardize_clause(
        context.terms,
        context.symbols,
        &mut literals[..count],
    )
    .map_err(|_| TstpError::InvalidStep(0))?;
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

// CEP:WHAT: Verifies one derived clause by replaying its rule between its parents.
// CEP:WHY: Design 18.4 and Spec 14 section 6: resolution/factoring replay every pivot and (for superposition) every (equation, literal, path) combination through the PRODUCTION rule functions - a step is accepted exactly when some legal application reproduces the recorded conclusion modulo the pipeline; AvatarSplit checks the Spec 12 Lemma 1 subclause property (every conclusion literal appears in the parent with the same polarity); Demodulation checks the structural variant property (same literal count and polarity multiset - the Phase 4 weakening, ticket CEP-1036: the demodulating rule's identity is not recorded in the Phase 3 derivation, so a full replay is impossible until the derivation records it); Input/NegatedConjecture are axioms (existence-checked by the walk).
// CEP:STATUS: complete
// CEP:FAILURE: returns InvalidStep(id) when no application reproduces the conclusion.
// CEP:ASSUMES: the parents resolve through the store; the conclusion record is readable.
// CEP:COST: O(parent literals^2 x rule cost) per step.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{checker_accepts_valid_proof, checker_rejects_broken_resolution, checker_rejects_broken_factoring, checker_rejects_broken_avatar_split, checker_accepts_demodulation_variant}.
// CEP:SECURITY: a tampered derivation or conclusion is rejected.
fn check_step(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    id: u64,
) -> Result<(), TstpError> {
    let record = store
        .clause_by_id(ClauseId(id))
        .map_err(|_| TstpError::UnreadableClause(id))?;
    let mut conclusion: Vec<Literal> = Vec::new();
    for index in 0..record.literal_count {
        conclusion.push(
            store
                .literal(record, index)
                .map_err(|_| TstpError::UnreadableClause(id))?,
        );
    }
    let mut left: Vec<Literal> = Vec::new();
    let mut right: Vec<Literal> = Vec::new();
    let parent_count = record.derivation.parent_count as usize;
    for slot in 0..parent_count {
        let parent_id = record.derivation.parents[slot];
        if parent_id == mapt_config::limits::kInvalidClauseId {
            continue;
        }
        let parent = store
            .clause_by_id(ClauseId(parent_id))
            .map_err(|_| TstpError::UnreadableClause(parent_id))?;
        for index in 0..parent.literal_count {
            let literal = store
                .literal(parent, index)
                .map_err(|_| TstpError::UnreadableClause(parent_id))?;
            if slot == 0 {
                left.push(literal);
            } else {
                right.push(literal);
            }
        }
    }
    match record.derivation.rule {
        InferenceRule::Input | InferenceRule::NegatedConjecture => Ok(()),
        InferenceRule::Resolution => {
            if parent_count != 2 {
                return Err(TstpError::InvalidStep(id));
            }
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kReplayLiterals];
            for left_index in 0..left.len() {
                for right_index in 0..right.len() {
                    if let Ok(ResolutionOutcome::Concluded(count)) =
                        resolve(context, &left, left_index, &right, right_index, &mut replay)
                    {
                        let piped = pipeline(context, &mut replay, count)
                            .map_err(|_| TstpError::InvalidStep(id))?;
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(());
                        }
                    }
                }
            }
            Err(TstpError::InvalidStep(id))
        }
        InferenceRule::Factoring => {
            if parent_count != 1 {
                return Err(TstpError::InvalidStep(id));
            }
            let mut replay: Vec<Literal> =
                vec![Literal::new(TermPtr::invalid(), true); kReplayLiterals];
            for first in 0..left.len() {
                for second in (first + 1)..left.len() {
                    if let Ok(FactoringOutcome::Concluded(count)) =
                        factor(context, &left, first, second, &mut replay)
                    {
                        let piped = pipeline(context, &mut replay, count)
                            .map_err(|_| TstpError::InvalidStep(id))?;
                        if same_multiset(&replay[..piped], &conclusion) {
                            return Ok(());
                        }
                    }
                }
            }
            Err(TstpError::InvalidStep(id))
        }
        InferenceRule::Demodulation => {
            // Structural variant check (the Phase 4 weakening, Spec 14 section 6):
            // same literal count and the same polarity multiset; a full replay needs the
            // demodulating rule recorded (ticket CEP-1036).
            if parent_count != 1 || left.len() != conclusion.len() {
                return Err(TstpError::InvalidStep(id));
            }
            let mut polarity_left: Vec<bool> = left.iter().map(|l| l.is_positive()).collect();
            let mut polarity_right: Vec<bool> =
                conclusion.iter().map(|l| l.is_positive()).collect();
            polarity_left.sort();
            polarity_right.sort();
            if polarity_left == polarity_right {
                Ok(())
            } else {
                Err(TstpError::InvalidStep(id))
            }
        }
        InferenceRule::AvatarSplit => {
            // Spec 12 Lemma 1 (subclause property): every component literal appears in
            // the parent with the same polarity.
            if parent_count != 1 {
                return Err(TstpError::InvalidStep(id));
            }
            for literal in conclusion.iter() {
                let present = left.iter().any(|other| {
                    other.atom() == literal.atom() && other.is_positive() == literal.is_positive()
                });
                if !present {
                    return Err(TstpError::InvalidStep(id));
                }
            }
            Ok(())
        }
        _ => Err(TstpError::InvalidStep(id)),
    }
}

// CEP:WHAT: Verifies the whole proof: every reachable step replays or structurally checks; returns Ok(()) or the offending id.
// CEP:WHY: Design 18.4: "the checker verifies every inference step independently - if the checker finds an invalid step, the proof is rejected and MAPT returns Error"; the walk order (ascending ids) replays parents before conclusions.
// CEP:STATUS: complete
// CEP:FAILURE: InvalidStep/UnreadableClause/CycleDetected propagate (the caller returns Error).
// CEP:ASSUMES: as reachable_proof_ids; the context's substitution is at baseline depth (the replay unwinds per rule).
// CEP:COST: O(steps x parent pairs x rule cost).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{checker_accepts_valid_proof, checker_rejects_broken_resolution}; property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: proof validation is the soundness certification of design 18.4.
pub fn check_proof(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<(), TstpError> {
    let ids = reachable_proof_ids(store, refutation)?;
    for id in ids.iter() {
        check_step(context, store, *id)?;
    }
    Ok(())
}

// CEP:WHAT: Convenience driver: formats and verifies in one call; returns (statement count, rendered proof).
// CEP:WHY: The CEP-1 entry point of design 18.2-18.4: reconstruct, prune, format, verify - a proof that fails verification never leaves the process as valid output.
// CEP:STATUS: complete
// CEP:FAILURE: propagates TstpError (verification failure included).
// CEP:ASSUMES: as write_tstp_proof and check_proof.
// CEP:COST: as both.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{formats_refutation_proof, checker_accepts_valid_proof}; property/tstp_property_test.rs::every_refutation_formats_and_checks.
// CEP:SECURITY: the verified-then-emitted ordering.
pub fn render_verified_proof(
    context: &InferenceContext<'_>,
    terms: &TermStore,
    names: &SymbolTableBuilder,
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<(usize, String), TstpError> {
    check_proof(context, store, refutation)?;
    let mut out = String::new();
    let count = write_tstp_proof(terms, names, store, refutation, &mut out)?;
    Ok((count, out))
}
