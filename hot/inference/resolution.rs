// CEP:FILE: hot/inference/resolution.rs
// CEP:WHAT: Binary resolution (Robinson 1965; design 10.1) with the ordered side conditions (design 10.2): resolves two complementary eligible literals of two renamed-apart premises through their MGU.
// CEP:WHY: Design 26 Phase 3 build order and Spec 07 section 4: the resolvent (C \\ {L}) sigma u (D \\ {M}) sigma is a logical consequence of the premises whenever sigma is the MGU of the two atoms (resolution is unconditionally sound - the ordering restrictions only prune for completeness); the side conditions follow the ordered calculus (the positive side literal is strictly maximal or selected, the negative side literal is maximal or selected), which keeps the search finite-ish and the calculus refutationally complete together with factoring (BG 2001 theorem 4.9).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when the side conditions or complementarity fail or the atoms do not unify (legitimate no-inference outcomes); Err only on structural failures; never panics.
// CEP:ASSUMES: left and right literals are renamed apart into one shared namespace (the generator's contract); the flags were computed on each premise's own literal slice BEFORE renaming (flags ride along with the literals).
// CEP:COST: one unification O(|s| + |t|) plus O(premise lengths) applications for the conclusion; measured in bench CEP-BENCH-0010, artifact benches/artifacts/atp_resolution_step.json.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{binary_resolution_ground, resolution_applies_mgu, resolution_side_conditions, resolution_rejects_ineligible}; property/inference_property_test.rs::{resolution_is_sound, resolution_side_conditions}.
// CEP:SECURITY: depth-bounded unification (CEP&CC 22.10).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; literal order and trail discipline fix the MGU.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 4 fixes the rule and its soundness proof (the resolvent is the disjunction of the premises' remainders under the MGU, entailed by resolution's soundness) and the eligibility restrictions (section 3); the property test verifies entailment executably over ground instances.

use crate::ir::literal::Literal;
use crate::unification::unify;

use super::builder::apply_literal;
use super::InferenceContext;

/// CEP:WHAT: Result of one resolution attempt: no inference, or the conclusion's literal count with the literals written to the output buffer.
/// CEP:WHY: A vocabulary type keeps the Option<(usize)> honest and self-documenting at call sites.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/inference_test.rs::{binary_resolution_ground, resolution_applies_mgu}.
/// CEP:SECURITY: none.
pub enum ResolutionOutcome {
    /// CEP:WHAT: No inference (side conditions, complementarity, or unification failed).
    /// CEP:WHY: The common outcome of candidate pairs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::resolution_rejects_ineligible.
    /// CEP:SECURITY: none.
    None,
    /// CEP:WHAT: The resolvent with the given literal count.
    /// CEP:WHY: The conclusion.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: literals are in the caller's buffer.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::binary_resolution_ground.
    /// CEP:SECURITY: none.
    Concluded(usize),
}

// CEP:WHAT: Attempts binary resolution of left[left_index] against right[right_index] and writes the resolvent into out.
// CEP:WHY: Spec 07 section 4: complementarity (opposite polarity), MGU of the atoms, eligibility (strictly-maximal-or-selected on the positive side, maximal-or-selected on the negative side), conclusion = the MGU-applied remainders.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on any failed side condition (the MGU is unwound to entry depth first, Spec 02 section 4); Err propagates structural failures with the trail left at its current depth - safe because Err is terminal for the whole search (the generator's abort discipline: the trail is never read after an Err), never resumed.
// CEP:ASSUMES: premises renamed apart; flags computed per premise; out holds kMaxClauseLiterals slots.
// CEP:COST: one unification plus O(premise lengths) applications.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{binary_resolution_ground, resolution_applies_mgu, resolution_side_conditions, resolution_rejects_ineligible}; property/inference_property_test.rs::resolution_is_sound; bench CEP-BENCH-0010.
// CEP:SECURITY: depth-bounded unification.
pub fn resolve(
    context: &InferenceContext<'_>,
    left: &[Literal],
    left_index: usize,
    right: &[Literal],
    right_index: usize,
    out: &mut [Literal],
) -> Result<ResolutionOutcome, super::InferenceError> {
    let left_literal = &left[left_index];
    let right_literal = &right[right_index];
    if left_literal.is_positive() == right_literal.is_positive() {
        return Ok(ResolutionOutcome::None);
    }
    // Eligibility: the positive side strictly maximal or selected; the negative side
    // maximal or selected (Spec 07 section 3).
    if left_literal.is_positive() {
        if !super::eligible_positive(context, left, left_index) {
            return Ok(ResolutionOutcome::None);
        }
        if !super::eligible_negative(right, right_index) {
            return Ok(ResolutionOutcome::None);
        }
    } else {
        if !super::eligible_negative(left, left_index) {
            return Ok(ResolutionOutcome::None);
        }
        if !super::eligible_positive(context, right, right_index) {
            return Ok(ResolutionOutcome::None);
        }
    }
    let entry_depth = context.substitution.trail_depth();
    let unified = unify(
        context.terms,
        context.substitution,
        left_literal.atom(),
        right_literal.atom(),
    )?;
    if !unified {
        return Ok(ResolutionOutcome::None);
    }
    // Materialize the conclusion: apply the MGU to every surviving literal.
    let mut count: usize = 0;
    let mut overflow = false;
    for (index, literal) in left.iter().enumerate() {
        if index == left_index {
            continue;
        }
        if count >= out.len() {
            overflow = true;
            break;
        }
        out[count] = apply_literal(
            context.terms,
            context.symbols,
            context.substitution,
            *literal,
        )?;
        count += 1;
    }
    if !overflow {
        for (index, literal) in right.iter().enumerate() {
            if index == right_index {
                continue;
            }
            if count >= out.len() {
                overflow = true;
                break;
            }
            out[count] = apply_literal(
                context.terms,
                context.symbols,
                context.substitution,
                *literal,
            )?;
            count += 1;
        }
    }
    // The MGU's bindings belong to this attempt; unwind so the next attempt starts
    // from the generator's snapshot (Spec 02 section 4 trail discipline).
    context.substitution.undo_to(entry_depth);
    if overflow {
        return Err(super::InferenceError::ConclusionTooLong);
    }
    Ok(ResolutionOutcome::Concluded(count))
}
