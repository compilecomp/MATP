// CEP:FILE: hot/inference/demodulation.rs
// CEP:WHAT: Demodulation (Bachmair & Ganzinger 1994; design 10.1/10.2): rewrites a clause's non-variable subterm by an oriented unit equation s = t with s strictly greater than t, requiring the rewritten atom to strictly decrease under the ordering.
// CEP:WHY: Design 10.3 step 1 (simplify the given clause using the active set - demodulation and subsumption) and design 10.2's demodulation conditions: orientation s greater than t, matching (not unification - the rule must instantiate only its own variables), and the target subterm not a variable; the strict-decrease condition on the containing atom is the standard termination guarantee (a clause can only be rewritten finitely often before reaching a normal form, because the atom ordering is well-founded on ground terms and each rewrite strictly decreases the atom); demodulation is sound unconditionally (rewriting with an equation preserves the clause's models) and simplification-deletion (replacing a clause by its demodulant) is sound by the redundancy criterion (design 10.4).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when no rewrite applies or the decrease condition fails; Err only on structural failures; never panics.
// CEP:ASSUMES: The rule is a positive unit equation interned by the context's store; the clause literals belong to the given clause; flags are irrelevant here (demodulation ignores selection).
// CEP:COST: one matching pass plus one comparison plus one rebuild per (rule, position) pair; bounded by the caller's rewrite rounds (kMaxSimplifyRounds).
// CEP:EVIDENCE: unit/hot/inference_test.rs::{demodulation_rewrites_terms, demodulation_requires_orientation, demodulation_requires_decrease}; unit/hot/given_clause_test.rs::demodulation_simplifies; property/inference_property_test.rs::demodulation_is_sound.
// CEP:SECURITY: depth-bounded matching and rebuild.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; rules and positions are index-ordered by the caller.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 7 fixes the demodulation rule, the three side conditions (orientation, matching, non-variable target), and the strict-decrease termination argument; the property test verifies soundness executably.

use crate::ir::literal::Literal;
use crate::ir::term::{TermPtr, TermTag};
use crate::unification::match_terms;

use super::builder::{apply_unwind, restore_trail};
use super::factoring::equality_sides;
use super::superposition::{replace_at, subterm_at};
use super::{InferenceContext, InferenceError};

// CEP:WHAT: Result of one demodulation attempt.
// CEP:WHY: Shared no-inference / conclusion vocabulary.
// CEP:STATUS: complete
// CEP:FAILURE: none; a vocabulary type.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{demodulation_rewrites_terms, demodulation_requires_orientation}.
// CEP:SECURITY: none.
pub enum DemodulationOutcome {
    /// CEP:WHAT: No rewrite applied.
    /// CEP:WHY: Failed match, orientation, or decrease.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::demodulation_requires_orientation.
    /// CEP:SECURITY: none.
    None,
    /// CEP:WHAT: The rewritten clause with the given literal count.
    /// CEP:WHY: The demodulant.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: literals are in the caller's buffer.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::demodulation_rewrites_terms.
    /// CEP:SECURITY: none.
    Rewritten(usize),
}

// CEP:WHAT: Attempts to rewrite literals[literal_index]'s atom at the position path with the oriented unit equation (rule_left = rule_right), copying the clause with the single rewritten literal into out.
// CEP:WHY: Spec 07 section 7: the rule's left side must MATCH the target subterm (sigma instantiates only the rule's variables), the rule must be oriented rule_left strictly greater than rule_right (checked on the applied sides when sigma is non-empty), the target must be a non-variable, and the rewritten atom must be strictly smaller than the original atom (termination).
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on failed conditions (the matcher is unwound first, Spec 02 section 4); Err on structural failures or an over-long output, with the trail restored to the entry depth (CEP-1050: the applied-side reads and the rebuild unwind through the restore helpers), so the generator's drop-and-resume policy can skip the candidate safely.
// CEP:ASSUMES: rule_left and rule_right are the sides of a positive unit equation; out holds kMaxClauseLiterals slots.
// CEP:COST: one matching pass, one comparison, one rebuild.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{demodulation_rewrites_terms, demodulation_requires_orientation, demodulation_requires_decrease}; property/inference_property_test.rs::demodulation_is_sound.
// CEP:SECURITY: depth-bounded recursion.
pub fn demodulate(
    context: &InferenceContext<'_>,
    literals: &[Literal],
    literal_index: usize,
    path: &[u16],
    rule_left: TermPtr,
    rule_right: TermPtr,
    out: &mut [Literal],
) -> Result<DemodulationOutcome, InferenceError> {
    let literal = &literals[literal_index];
    let target = match subterm_at(context.terms, literal.atom(), path) {
        Some(value) => value,
        None => return Ok(DemodulationOutcome::None),
    };
    if let Ok(view) = context.terms.term(target) {
        if view.tag() == TermTag::Variable {
            return Ok(DemodulationOutcome::None);
        }
    } else {
        return Ok(DemodulationOutcome::None);
    }
    let entry_depth = context.substitution.trail_depth();
    let matched = match_terms(
        context.terms,
        context.symbols,
        context.substitution,
        rule_left,
        target,
    )?;
    if !matched {
        return Ok(DemodulationOutcome::None);
    }
    // Orientation under the matcher: the applied left side strictly greater than the
    // applied right side (design 10.2 "Orientation: s > t"; applied because the
    // matcher may instantiate the rule's variables). Both applications unwind the
    // trail on failure (CEP-1050).
    let applied_left = apply_unwind(
        context.terms,
        context.symbols,
        context.substitution,
        rule_left,
        entry_depth,
    )?;
    let applied_right = apply_unwind(
        context.terms,
        context.symbols,
        context.substitution,
        rule_right,
        entry_depth,
    )?;
    let oriented = match context.compare(applied_left, applied_right) {
        Ok(crate::ordering::OrderingComparison::Greater) => true,
        Ok(_) => false,
        Err(_) => false,
    };
    if !oriented {
        context.substitution.undo_to(entry_depth);
        return Ok(DemodulationOutcome::None);
    }
    // Termination condition: the rewritten atom strictly smaller than the original.
    // The rebuild unwinds the trail on failure (CEP-1050).
    let rewritten_atom = restore_trail(
        context.substitution,
        entry_depth,
        replace_at(context, literal.atom(), path, applied_right, 0),
    )?;
    let decreased = match context.compare(literal.atom(), rewritten_atom) {
        Ok(crate::ordering::OrderingComparison::Greater) => true,
        Ok(_) => false,
        Err(_) => false,
    };
    if !decreased {
        context.substitution.undo_to(entry_depth);
        return Ok(DemodulationOutcome::None);
    }
    if literals.len() > out.len() {
        context.substitution.undo_to(entry_depth);
        return Err(InferenceError::ConclusionTooLong);
    }
    for (index, other) in literals.iter().enumerate() {
        out[index] = if index == literal_index {
            Literal::new(rewritten_atom, other.is_positive())
        } else {
            *other
        };
    }
    context.substitution.undo_to(entry_depth);
    Ok(DemodulationOutcome::Rewritten(literals.len()))
}

// CEP:WHAT: Reads the two sides of a positive unit equation literal, or None when the literal is not a positive equality.
// CEP:WHY: The demodulation rule source is the active set's unit equations; one shared reader keeps the tag and polarity check in one place.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) for non-equation or negative literals.
// CEP:ASSUMES: the literal is store-interned.
// CEP:COST: one view read.
// CEP:EVIDENCE: unit/hot/inference_test.rs::demodulation_rewrites_terms.
// CEP:SECURITY: none.
pub fn unit_equation_sides(
    context: &InferenceContext<'_>,
    literal: Literal,
) -> Option<(TermPtr, TermPtr)> {
    if !literal.is_positive() {
        return None;
    }
    equality_sides(context.terms, literal.atom())
}
