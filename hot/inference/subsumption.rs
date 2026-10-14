// CEP:FILE: hot/inference/subsumption.rs
// CEP:WHAT: Subsumption (Plotkin 1972; design 10.1): decides whether one clause subsumes another - exists sigma with C sigma a subset of D - via literal-by-literal one-directional matching over a shared, trail-disciplined substitution.
// CEP:WHY: Design 10.4's redundancy criterion in practice: forward subsumption (an active clause subsumes the given clause, which is then discarded) and backward subsumption (the given clause subsumes active clauses, which are then removed) both reduce the search space without losing completeness (subsumption deletion preserves refutational completeness, BG 2001); the check is matching-based (sigma instantiates only the subsumer's variables), literal reuse across the target is allowed because subset-hood is a set condition (C = P(x) v P(y) subsumes D = P(a) v Q(b): both x and y map to a and the collapsed instance {P(a)} is a subset of D), and the trail discipline (snapshot depth, unwind per literal backtrack, unwind at exit) makes the check non-destructive on the shared substitution (Spec 02 section 4).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) is the only negative answer; Err only on structural failures; never panics.
// CEP:ASSUMES: Both literal slices belong to clauses with dense variable namespaces; the caller is responsible for renaming apart when the two clauses share the namespace (the search's forward/backward checks run candidate-against-given with the candidate renamed into the given's window by the caller).
// CEP:COST: exponential backtrack in the worst case (literal assignment search), bounded in practice by the feature-vector and discrimination-tree pre-filters and structurally by kMaxClauseLiterals; measured within bench CEP-BENCH-0012, artifact benches/artifacts/atp_subsumption_verify.json.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_ground_subset, subsumption_instantiates, subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::{subsumption_agrees_with_brute_force, subsumption_filter_admits_all_true_subsumptions}.
// CEP:SECURITY: the backtrack depth is bounded by the literal count (CEP&CC 22.10 discipline).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; literals pair in index order and the trail discipline fixes the matcher.
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 2 fixes the subsumption definition (exists sigma, C sigma a subset of D as literal sets) and the matching-based decision procedure; the property test verifies the decision against a brute-force oracle over ground instances.

use crate::ir::literal::Literal;
use crate::unification::match_terms;

use super::InferenceContext;

// CEP:WHAT: Decides whether candidate subsumes target.
// CEP:WHY: Spec 08 section 2: a necessary size condition (|C| <= |D|) short-circuits, then a backtracking search assigns each candidate literal a target literal of the same polarity whose atom it matches, extending one shared substitution; success means sigma exists and the candidate subsumes the target.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) when no sigma exists; Err propagates structural failures; the substitution trail is unwound to the entry depth on both outcomes.
// CEP:ASSUMES: both namespaces are dense; the caller renamed apart when needed.
// CEP:COST: backtracking matching, worst case exponential in the literal count (bounded by the pre-filters upstream).
// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_ground_subset, subsumption_instantiates, subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::subsumption_agrees_with_brute_force.
// CEP:SECURITY: bounded backtrack.
pub fn subsumes(
    context: &InferenceContext<'_>,
    candidate: &[Literal],
    target: &[Literal],
) -> Result<bool, super::InferenceError> {
    if candidate.len() > target.len() {
        return Ok(false);
    }
    if candidate.is_empty() {
        // The empty clause subsumes everything (and only it subsumes the empty clause).
        return Ok(true);
    }
    let entry_depth = context.substitution.trail_depth();
    let result = assign_literal(context, candidate, 0, target);
    context.substitution.undo_to(entry_depth);
    result
}

// CEP:WHAT: Recursive literal-assignment search: tries every same-polarity target literal for candidate[position] and recurses on success.
// CEP:WHY: The backtracking heart of the subsumption check; target literals are REUSABLE across candidate positions because subset-hood is a set condition (C = P(x) v P(y) subsumes D = P(a) with x and y both mapped to a), so no used-marks exist; termination is the finite recursion depth (|candidate|) with a finite scan per level (|target|) - exponential worst case at the clause-literal bound, pruned upstream by the feature-vector filter and the discrimination tree.
// CEP:STATUS: complete
// CEP:FAILURE: Err propagates structural failures; every failed match branch unwinds its own bindings (match_terms' contract) before the next attempt.
// CEP:ASSUMES: candidate is non-empty at the top call.
// CEP:COST: O(|target|^|candidate|) worst case.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::subsumption_agrees_with_brute_force.
// CEP:SECURITY: recursion depth bounded by kMaxClauseLiterals.
fn assign_literal(
    context: &InferenceContext<'_>,
    candidate: &[Literal],
    position: usize,
    target: &[Literal],
) -> Result<bool, super::InferenceError> {
    if position == candidate.len() {
        return Ok(true);
    }
    let literal = &candidate[position];
    for other in target.iter() {
        if other.is_positive() != literal.is_positive() {
            continue;
        }
        let entry_depth = context.substitution.trail_depth();
        let matched = match_terms(
            context.terms,
            context.symbols,
            context.substitution,
            literal.atom(),
            other.atom(),
        )?;
        if matched && assign_literal(context, candidate, position + 1, target)? {
            return Ok(true);
        }
        context.substitution.undo_to(entry_depth);
    }
    Ok(false)
}

// CEP:WHAT: Ground tautology check: a clause containing two literals with pointer-equal atoms and opposite polarity.
// CEP:WHY: Design 10.1 tautology deletion and design 10.4: hash-consing makes structural atom equality pointer equality (design 5.1), so the check is exact and allocation-free; unifiable-but-distinct atoms (P(x) v not P(y)) are NOT tautologies (x and y can differ) and the check correctly keeps them.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: atoms interned by one store.
// CEP:COST: O(n^2) pointer comparisons.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{tautology_detected, near_tautology_kept}.
// CEP:SECURITY: none.
pub fn is_tautology(literals: &[Literal]) -> bool {
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            if literals[i].atom() == literals[j].atom()
                && literals[i].is_positive() != literals[j].is_positive()
            {
                return true;
            }
        }
    }
    false
}
