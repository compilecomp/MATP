// CEP:FILE: cold/proof_output/tstp.rs
// CEP:WHAT: Unified proof reconstruction (design 18.2-18.4): walks the derivation DAG from the refuting empty clause through the clause store's id side table, prunes to the reachable steps, formats the proof as TSTP cnf statements, and independently re-verifies every inference step through the certified proof kernel (Spec 19): the walk and the per-rule replay arms (production rule functions, standardize-apart premise renaming, exact per-step demodulation over the CEP-1036 chain, production AVATAR split replay, SatLearn shape checks) live in cold/kernel and this module delegates to them.
// CEP:WHY: Design 26 Phase 4 ("Proof reconstruction (unified)" depends on proof recording and the TSTP writer); design 18.4: "an ATP that produces an invalid proof is worse than one that produces no proof" - the certified kernel re-runs the recorded rules between the recorded parents and accepts a step only when some legal application reproduces the recorded conclusion modulo the loop's restandardize/dedupe pipeline (Spec 19); the walk prunes every clause not reachable from the refutation (design 18.2's redundant-step removal); the writer emits TSTP (TPTP Thousands of Problems for Theorem Provers, TSTP syntax for solutions) cnf lines with axiom/negated_conjecture/plain roles and inference sources, variables as X<n> (TPTP upper-case convention), equality infix, and the empty clause as $false; AVATAR component clauses cite their original through the MAPT-specific avatar_split rule whose soundness is the Spec 12 splitting lemma - external checkers must accept the rule as a black box (the same situation as published AVATAR proofs, documented in Spec 14 section 5).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: writer: UnreadableClause/UnreadableTerm on corrupt stores, CycleDetected on non-monotonic parent chains (a corrupted derivation); checker: InvalidStep with the offending clause id and reason (the proof is rejected and the caller returns Error per design 18.4); never panics.
// CEP:ASSUMES: the refutation offset came from the search that owns the store; the store was constructed with an id side table (SearchSpace::new/new_with - a table-less store rejects proof walks loudly); the InferenceContext's stores match the search's.
// CEP:COST: walk O(clauses); write O(proof size); check O(steps x premise pairs x rule cost).
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{formats_refutation_proof, proof_walk_resolves_parents, prunes_unreachable_steps, roles_and_sources, empty_clause_renders_false, checker_accepts_valid_proof, checker_rejects_broken_resolution, checker_rejects_broken_factoring, checker_rejects_broken_avatar_split, checker_rejects_unrecorded_demodulation, cycle_detected}; property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: every store read is bounds-checked; the checker validates derivation records against the replayed rules - a tampered record is rejected, not trusted.
// CEP:HPC-DETERMINISM: deterministic (ascending id order, fixed formats).
// CEP:HPC-PASS-LEGALITY: Formal Spec 14 (14_unified_proof_reconstruction.md) fixes the walk, the pruning (reachability), the TSTP statement grammar subset, the replay-checker contract, and the demodulation weakening (ticket CEP-1036); the property tests verify executably that every refutation the loop produces passes the checker and that tampered steps are rejected.

use std::string::String;

use crate::kernel::{
    verify_refutation_with_budget, walk_proof_dag, KernelError, KernelRejection, KernelVerdict,
};
use crate::symbol_table_builder::SymbolTableBuilder;
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
    /// CEP:WHAT: The certified kernel's replay budget was exhausted before verification finished (Spec 19).
    /// CEP:WHY: Budget exhaustion is an ERROR, never a rejection (CEP&CC 34.3): the proof is neither verified nor condemned; the caller returns Error per design 18.4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/kernel_test.rs::rejects_budget_exhaustion.
    /// CEP:SECURITY: bounded verification work.
    BudgetExhausted,
}

// CEP:WHAT: Collects the reachable clause ids from the refutation, ascending, through the certified kernel's DAG walk (Spec 19).
// CEP:WHY: Design 18.2 step 1-2 and Spec 19 section 3: one walk owner - the kernel's descending pass marks the ancestry exactly (parents strictly older than children, monotonic ids, Spec 14 section 2), reports non-monotonic parents as CycleDetected and unresolvable records as UnreadableClause, and the writer and the checker share the same walk so the pruned, ascending-id order is a valid topological order.
// CEP:STATUS: complete
// CEP:FAILURE: UnreadableClause for unresolvable ids, CycleDetected for non-monotonic parents (both mapped from the kernel's rejection verdict).
// CEP:ASSUMES: refutation is a store-produced offset; the store has an id side table.
// CEP:COST: O(max id) scan plus O(ancestry) reads.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{proof_walk_resolves_parents, prunes_unreachable_steps, cycle_detected}; unit/cold/kernel_test.rs::{accepts_loop_refutation, rejects_non_monotonic_derivation}.
// CEP:SECURITY: all reads bounds-checked.
pub fn reachable_proof_ids(
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<Vec<u64>, TstpError> {
    match walk_proof_dag(store, refutation) {
        Ok(ids) => Ok(ids),
        Err((clause_id, rejection)) => match rejection {
            KernelRejection::NonMonotonicDerivation => Err(TstpError::CycleDetected(clause_id)),
            _ => Err(TstpError::UnreadableClause(clause_id)),
        },
    }
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
        InferenceRule::StructuralInduction => "structural_induction",
        InferenceRule::WellFoundedInduction => "well_founded_induction",
        InferenceRule::ConjectureNegation => "conjecture_negation",
        InferenceRule::ConjectureLemma => "conjecture_lemma",
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
            InferenceRule::StructuralInduction | InferenceRule::WellFoundedInduction => {
                out.push_str(", axiom, ")
            }
            InferenceRule::ConjectureLemma => out.push_str(", lemma, "),
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

// CEP:WHAT: Verifies the whole proof through the certified kernel (Spec 19): every reachable step replays its production rule between its recorded parents under the kKernelReplayBudget.
// CEP:WHY: Design 18.4: "the checker verifies every inference step independently - if the checker finds an invalid step, the proof is rejected and MAPT returns Error"; the kernel owns the arms (Spec 19 section 4), the walk order (ascending ids) replays parents before conclusions, and a rejection verdict maps onto InvalidStep with the offending clause id while budget exhaustion maps onto BudgetExhausted (an error, never a rejection).
// CEP:STATUS: complete
// CEP:FAILURE: InvalidStep/UnreadableClause/CycleDetected/BudgetExhausted propagate (the caller returns Error).
// CEP:ASSUMES: as the kernel's verify_refutation_with_budget; the context's substitution is at baseline depth (every replay unwinds per attempt).
// CEP:COST: bounded by kKernelReplayBudget charged actions.
// CEP:EVIDENCE: unit/cold/tstp_test.rs::{checker_accepts_valid_proof, checker_rejects_broken_resolution, checker_rejects_unrecorded_demodulation}; unit/cold/kernel_test.rs (the whole file); property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}.
// CEP:SECURITY: proof validation is the soundness certification of design 18.4, executed by the kernel.
pub fn check_proof(
    context: &InferenceContext<'_>,
    store: &ClauseStore<'_>,
    refutation: u32,
) -> Result<(), TstpError> {
    // CEP:WHAT: The kernel verdict mapping (check_proof_via_kernel).
    // CEP:WHY: Spec 19 section 6: the TSTP layer never re-implements an arm; Valid passes, a rejection becomes InvalidStep (the TSTP error vocabulary keeps its payload contract), a budget error becomes BudgetExhausted.
    // CEP:STATUS: complete
    // CEP:FAILURE: see check_proof.
    // CEP:ASSUMES: none.
    // CEP:COST: the kernel's bounded cost.
    // CEP:EVIDENCE: unit/cold/kernel_test.rs::tstp_wrapper_maps_rejections.
    // CEP:SECURITY: none.
    match verify_refutation_with_budget(
        context,
        store,
        refutation,
        mapt_config::limits::kKernelReplayBudget,
    ) {
        Ok(KernelVerdict::Valid) => Ok(()),
        Ok(KernelVerdict::Invalid {
            clause_id,
            rejection: _,
        }) => Err(TstpError::InvalidStep(clause_id)),
        Err(KernelError::ReplayBudgetExhausted) => Err(TstpError::BudgetExhausted),
    }
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
