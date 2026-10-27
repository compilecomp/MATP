// CEP:FILE: hot/inference/factoring.rs
// CEP:WHAT: Factoring (Bachmair & Ganzinger 1994; design 10.1) and equality factoring (Nieuwenhuis & Rubio 2001; design 10.1): merges two unifiable same-polarity literals of one clause, respectively two positive equations sharing a unifiable left side.
// CEP:WHY: Spec 07 section 5: positive factoring is required for refutational completeness of ordered resolution (BG 2001) - without it, clauses like P(x) v P(f(y)) cannot collapse; the factored clause (C \\ {L1, L2}) sigma u {L1 sigma} is a logical consequence of the premise (factoring is unconditionally sound: it is one resolution step simulated inside the clause); equality factoring from C v (s = t) v (s' = t') with sigma = MGU(s, s') concludes (C \\ {both}) sigma u {(s = t) sigma} u {not (t sigma = t' sigma)}, which is sound by the standard equality-factoring argument (NR01 section 4.2) and required for completeness of the superposition calculus.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when side conditions fail or the atoms do not unify; Err only on structural failures; never panics.
// CEP:ASSUMES: the literals belong to one clause (no renaming needed - one namespace); flags were computed for the clause.
// CEP:COST: one unification per candidate pair plus O(length) applications for the conclusion.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{factoring_merges_unifiable_literals, factoring_rejects_opposite_polarity, factoring_side_conditions, equality_factoring_concludes}; property/inference_property_test.rs::{factoring_is_sound, equality_factoring_is_sound}.
// CEP:SECURITY: depth-bounded unification.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; pair enumeration is index-ordered.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 5 fixes both rules and their soundness proofs; the property tests verify entailment executably over ground instances.

use crate::ir::literal::Literal;
use crate::ir::term::{TermStore, TermTag};
use crate::unification::unify;

use super::builder::{apply_literal_unwind, apply_unwind, restore_trail};
use super::{InferenceContext, InferenceError};

// CEP:WHAT: Result of one factoring attempt.
// CEP:WHY: Mirrors the resolution outcome vocabulary for symmetry at call sites.
// CEP:STATUS: complete
// CEP:FAILURE: none; a vocabulary type.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{factoring_merges_unifiable_literals, equality_factoring_concludes}.
// CEP:SECURITY: none.
pub enum FactoringOutcome {
    /// CEP:WHAT: No inference.
    /// CEP:WHY: Failed side conditions or unification.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::factoring_rejects_opposite_polarity.
    /// CEP:SECURITY: none.
    None,
    /// CEP:WHAT: The factored clause with the given literal count.
    /// CEP:WHY: The conclusion.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: literals are in the caller's buffer.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::factoring_merges_unifiable_literals.
    /// CEP:SECURITY: none.
    Concluded(usize),
}

// CEP:WHAT: Attempts factoring of literals[first] with literals[second] (same polarity, unifiable atoms, first eligible) and writes the factored clause into out.
// CEP:WHY: Spec 07 section 5: the conclusion keeps one applied copy of the merged literal and the applied remainders; eligibility requires the merged literal selected or (nothing selected and) strictly maximal - the standard restriction that makes factoring + ordered resolution complete.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on failed side conditions or unification; Err on structural failures or an over-long conclusion; the substitution trail is unwound on every path.
// CEP:ASSUMES: first < second in index order (the generator enumerates ascending pairs); out holds kMaxClauseLiterals slots.
// CEP:COST: one unification plus O(length) applications.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{factoring_merges_unifiable_literals, factoring_rejects_opposite_polarity, factoring_side_conditions}; property/inference_property_test.rs::{factoring_is_sound, factoring_side_conditions}.
// CEP:SECURITY: depth-bounded unification.
pub fn factor(
    context: &InferenceContext<'_>,
    literals: &[Literal],
    first: usize,
    second: usize,
    out: &mut [Literal],
) -> Result<FactoringOutcome, InferenceError> {
    let first_literal = &literals[first];
    let second_literal = &literals[second];
    if first_literal.is_positive() != second_literal.is_positive() {
        return Ok(FactoringOutcome::None);
    }
    // Eligibility of the kept literal: selected, or nothing selected and strictly
    // maximal (positive factoring's completeness restriction, Spec 07 section 5);
    // eligible_positive already accounts for selection.
    if !super::eligible_positive(context, literals, first) {
        return Ok(FactoringOutcome::None);
    }
    let entry_depth = context.substitution.trail_depth();
    let unified = unify(
        context.terms,
        context.substitution,
        first_literal.atom(),
        second_literal.atom(),
    )?;
    if !unified {
        return Ok(FactoringOutcome::None);
    }
    let mut count: usize = 0;
    let mut overflow = false;
    for (index, literal) in literals.iter().enumerate() {
        if index == second {
            continue;
        }
        if count >= out.len() {
            overflow = true;
            break;
        }
        out[count] = apply_literal_unwind(
            context.terms,
            context.symbols,
            context.substitution,
            *literal,
            entry_depth,
        )?;
        count += 1;
    }
    context.substitution.undo_to(entry_depth);
    if overflow {
        return Err(InferenceError::ConclusionTooLong);
    }
    Ok(FactoringOutcome::Concluded(count))
}

// CEP:WHAT: Reads the two sides of an equality atom.
// CEP:WHY: Equality atoms are tag-fixed terms with exactly two children (design 5.1); one shared reader keeps the tag check in one place.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when the atom is not an equality term.
// CEP:ASSUMES: atom interned by the store.
// CEP:COST: one view read.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{equality_factoring_concludes, equality_resolution_concludes}.
// CEP:SECURITY: none.
pub fn equality_sides(
    terms: &TermStore<'_>,
    atom: crate::ir::term::TermPtr,
) -> Option<(crate::ir::term::TermPtr, crate::ir::term::TermPtr)> {
    let view = terms.term(atom).ok()?;
    if view.tag() != TermTag::Equality {
        return None;
    }
    Some((view.child(0).ok()?, view.child(1).ok()?))
}

// CEP:WHAT: Attempts equality factoring of two positive equation literals literals[first] (s = t) and literals[second] (s' = t'): sigma = MGU(s, s') concludes the remainders plus (s = t)sigma plus not(t sigma = t' sigma).
// CEP:WHY: NR01 section 4.2 (Spec 07 section 5): equality factoring resolves the two equations on their left sides and keeps the disequality of the right sides, which is what makes the superposition calculus complete on non-unit equalities.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on failed side conditions (both positive, both equations, first eligible) or unification; Err on structural failures; trail unwound on every path.
// CEP:ASSUMES: literals belong to one clause; out holds kMaxClauseLiterals slots.
// CEP:COST: one unification plus O(length) applications plus one disequality atom construction.
// CEP:EVIDENCE: unit/hot/inference_test.rs::equality_factoring_concludes; property/inference_property_test.rs::equality_factoring_is_sound.
// CEP:SECURITY: depth-bounded unification.
pub fn equality_factor(
    context: &InferenceContext<'_>,
    literals: &[Literal],
    first: usize,
    second: usize,
    out: &mut [Literal],
) -> Result<FactoringOutcome, InferenceError> {
    let first_literal = &literals[first];
    let second_literal = &literals[second];
    if !first_literal.is_positive() || !second_literal.is_positive() {
        return Ok(FactoringOutcome::None);
    }
    let (first_left, first_right) = match equality_sides(context.terms, first_literal.atom()) {
        Some(value) => value,
        None => return Ok(FactoringOutcome::None),
    };
    let (second_left, second_right) = match equality_sides(context.terms, second_literal.atom()) {
        Some(value) => value,
        None => return Ok(FactoringOutcome::None),
    };
    if !super::eligible_positive(context, literals, first) {
        return Ok(FactoringOutcome::None);
    }
    let entry_depth = context.substitution.trail_depth();
    let unified = unify(context.terms, context.substitution, first_left, second_left)?;
    if !unified {
        return Ok(FactoringOutcome::None);
    }
    let mut count: usize = 0;
    let mut overflow = false;
    for (index, literal) in literals.iter().enumerate() {
        if index == first || index == second {
            continue;
        }
        if count >= out.len() {
            overflow = true;
            break;
        }
        out[count] = apply_literal_unwind(
            context.terms,
            context.symbols,
            context.substitution,
            *literal,
            entry_depth,
        )?;
        count += 1;
    }
    if !overflow {
        if count >= out.len() {
            overflow = true;
        } else {
            // Keep (s = t) under sigma.
            out[count] = apply_literal_unwind(
                context.terms,
                context.symbols,
                context.substitution,
                *first_literal,
                entry_depth,
            )?;
            count += 1;
        }
    }
    if !overflow {
        if count >= out.len() {
            overflow = true;
        } else {
            // Add not (t sigma = t' sigma): apply sigma to both right sides, build
            // the disequality atom, negate. Both applications unwind the trail on
            // failure (CEP-1050), and so does the atom intern.
            let applied_first_right = apply_unwind(
                context.terms,
                context.symbols,
                context.substitution,
                first_right,
                entry_depth,
            )?;
            let applied_second_right = apply_unwind(
                context.terms,
                context.symbols,
                context.substitution,
                second_right,
                entry_depth,
            )?;
            let atom = restore_trail(
                context.substitution,
                entry_depth,
                context
                    .terms
                    .intern_eq(context.symbols, applied_first_right, applied_second_right)
                    .map_err(|_| {
                        InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::InvalidPointer,
                        )
                    }),
            )?;
            out[count] = Literal::new(atom, false);
            count += 1;
        }
    }
    context.substitution.undo_to(entry_depth);
    if overflow {
        return Err(InferenceError::ConclusionTooLong);
    }
    Ok(FactoringOutcome::Concluded(count))
}
