// CEP:FILE: hot/inference/superposition.rs
// CEP:WHAT: Superposition left and right (Bachmair & Ganzinger 1994; design 10.1) and equality resolution (Nieuwenhuis & Rubio 2001; design 10.1): rewriting a non-variable subterm of one premise's literal by a positive eligible equation of the other premise, respectively collapsing a negative equation with unifiable sides.
// CEP:WHY: Spec 07 section 6: superposition is the equality engine - from C v (s = t) and D v L[w] with sigma = MGU(w, s), the conclusion (C \\ {s = t}) sigma u (D \\ {L}) sigma u {L sigma[w sigma <- t sigma]} is a logical consequence of the premises (superposition is unconditionally sound: it is an equality-elimination argument on the instantiated equation); the side conditions follow the ordered calculus - the equation is eligible and oriented s sigma strictly greater than t sigma (design 10.2 "Ordering: s sigma > t sigma"), the target subterm w sigma is not a variable (design 10.2 "Variable restriction"), and the target literal is eligible - which together with eq resolution and eq factoring gives the standard complete superposition calculus (NR01 section 4); equality resolution from C v not (s = t) with MGU(s, t) = sigma concludes C sigma and is what closes reflexive disequalities.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when side conditions fail, the MGU does not exist, or the orientation check fails; Err only on structural failures; never panics.
// CEP:ASSUMES: from_literals and into_literals are renamed apart into one namespace; the equation literal is positive with an equality atom; the position path addresses a subterm of the into literal's atom; flags were computed per premise.
// CEP:COST: one unification, one orientation comparison (KBO/LPO with step budget), one term rebuild of the into atom, plus O(premise lengths) applications; measured within bench CEP-BENCH-0010, artifact benches/artifacts/atp_resolution_step.json.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, superposition_into_positive, superposition_orients_equations, superposition_rejects_variable_targets, equality_resolution_concludes}; property/inference_property_test.rs::{superposition_is_sound, equality_resolution_is_sound}.
// CEP:SECURITY: depth-bounded unification and rebuild.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; position paths are index-ordered by the generator.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 6 fixes both rules, their side conditions (eligibility, strict orientation, non-variable target), and their soundness proofs; the property tests verify entailment executably over ground instances.

use crate::ir::literal::Literal;
use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::unification::unify;

use super::builder::apply_literal;
use super::factoring::equality_sides;
use super::{InferenceContext, InferenceError};

// CEP:WHAT: Maximum path length of one subterm position (the term depth bound).
// CEP:WHY: Position paths are fixed stack arrays; the term depth bound is the structural maximum (CEP&CC 11.3 named size).
// CEP:STATUS: complete
// CEP:FAILURE: positions deeper than the bound cannot exist (intern-enforced).
// CEP:ASSUMES: kMaxTermDepth as usize.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, superposition_into_positive}.
// CEP:SECURITY: none.
pub const kMaxPathLength: usize = mapt_config::limits::kMaxTermDepth as usize;

// CEP:WHAT: Crate-public alias of subterm_at for the search generator.
// CEP:WHY: The generator (hot/search/generate.rs) enumerates subterm positions; the reader stays in the inference module with its rule and the alias keeps the visibility explicit (CEP&CC 33.2 minimal surface).
// CEP:STATUS: complete
// CEP:FAILURE: as subterm_at.
// CEP:ASSUMES: as subterm_at.
// CEP:COST: as subterm_at.
// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{superposition_into_fires, superposition_from_fires}.
// CEP:SECURITY: bounds-checked.
pub(crate) fn subterm_at_public(
    terms: &TermStore<'_>,
    term: TermPtr,
    path: &[u16],
) -> Option<TermPtr> {
    subterm_at(terms, term, path)
}

// CEP:WHAT: Result of one superposition or equality-resolution attempt.
// CEP:WHY: Shared no-inference / conclusion vocabulary.
// CEP:STATUS: complete
// CEP:FAILURE: none; a vocabulary type.
// CEP:ASSUMES: none.
// CEP:COST: enum copy.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, equality_resolution_concludes}.
// CEP:SECURITY: none.
pub enum SuperpositionOutcome {
    /// CEP:WHAT: No inference.
    /// CEP:WHY: Failed side conditions, unification, or orientation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_rejects_variable_targets, superposition_orients_equations}.
    /// CEP:SECURITY: none.
    None,
    /// CEP:WHAT: The conclusion with the given literal count.
    /// CEP:WHY: The conclusion.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: literals are in the caller's buffer.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::superposition_into_negative.
    /// CEP:SECURITY: none.
    Concluded(usize),
}

// CEP:WHAT: Reads the subterm of a term at a position path (child indices from the root).
// CEP:WHY: The generator addresses rewrite targets by path; one shared reader keeps the walk in one place.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when the path leaves the term (shorter term or non-compound node).
// CEP:ASSUMES: path is non-empty in rule use; the term is store-interned.
// CEP:COST: O(path length) reads.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, superposition_into_positive}.
// CEP:SECURITY: bounds-checked child reads.
pub(crate) fn subterm_at(terms: &TermStore<'_>, term: TermPtr, path: &[u16]) -> Option<TermPtr> {
    let mut current = term;
    for step in path.iter() {
        let view = terms.term(current).ok()?;
        if view.child_count() <= *step {
            return None;
        }
        current = view.child(*step).ok()?;
    }
    Some(current)
}

// CEP:WHAT: Rebuilds a term with the subterm at the position path replaced by the replacement.
// CEP:WHY: Conclusion construction for superposition and demodulation; the rebuild is depth-bounded and hash-consed so the rewritten atom shares structure with the original.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError on intern failure or depth exhaustion.
// CEP:ASSUMES: the path addresses a subterm of the term (the caller checked via subterm_at).
// CEP:COST: O(term nodes above and at the path).
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, superposition_into_positive}; unit/hot/inference_test.rs::demodulation_rewrites_terms.
// CEP:SECURITY: depth-bounded recursion.
pub(crate) fn replace_at(
    context: &InferenceContext<'_>,
    term: TermPtr,
    path: &[u16],
    replacement: TermPtr,
    depth: u32,
) -> Result<TermPtr, InferenceError> {
    if depth > mapt_config::limits::kMaxTermDepth as u32 {
        return Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        ));
    }
    if path.is_empty() {
        return Ok(replacement);
    }
    let view = context.terms.term(term).map_err(|_| {
        InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::InvalidPointer,
        )
    })?;
    let step = path[0];
    if view.child_count() <= step {
        return Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::InvalidPointer,
        ));
    }
    match view.tag() {
        TermTag::Function | TermTag::Predicate => {
            let mut children: [TermPtr; 32] = [TermPtr::invalid(); 32];
            let count = view.child_count();
            if count as usize > children.len() {
                return Err(InferenceError::Structural(
                    crate::unification::substitution::SubstitutionError::DepthExceeded,
                ));
            }
            for index in 0..count {
                let child = view.child(index)?;
                children[index as usize] = if index == step {
                    replace_at(context, child, &path[1..], replacement, depth + 1)?
                } else {
                    child
                };
            }
            if view.tag() == TermTag::Function {
                context
                    .terms
                    .intern_fun(context.symbols, view.symbol(), &children[..count as usize])
                    .map_err(|_| {
                        InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::InvalidPointer,
                        )
                    })
            } else {
                context
                    .terms
                    .intern_pred(context.symbols, view.symbol(), &children[..count as usize])
                    .map_err(|_| {
                        InferenceError::Structural(
                            crate::unification::substitution::SubstitutionError::InvalidPointer,
                        )
                    })
            }
        }
        TermTag::Equality => {
            let left = view.child(0)?;
            let right = view.child(1)?;
            let (new_left, new_right) = if step == 0 {
                (
                    replace_at(context, left, &path[1..], replacement, depth + 1)?,
                    right,
                )
            } else {
                (
                    left,
                    replace_at(context, right, &path[1..], replacement, depth + 1)?,
                )
            };
            context
                .terms
                .intern_eq(context.symbols, new_left, new_right)
                .map_err(|_| {
                    InferenceError::Structural(
                        crate::unification::substitution::SubstitutionError::InvalidPointer,
                    )
                })
        }
        TermTag::Variable | TermTag::Application | TermTag::Lambda | TermTag::Sort => {
            Err(InferenceError::Structural(
                crate::unification::substitution::SubstitutionError::InvalidPointer,
            ))
        }
    }
}

// CEP:WHAT: Attempts superposition of the positive equation from_literals[equation_index] (s = t) into the subterm at path of into_literals[into_index]'s atom, writing the conclusion into out.
// CEP:WHY: Spec 07 section 6: sigma = MGU(w, s) with the design 10.2 side conditions - the equation literal eligible (strictly maximal or selected), oriented s sigma strictly greater than t sigma, the target subterm w sigma not a variable, and the into literal eligible (selected, or nothing selected and maximal; the negative-side eligibility for negative literals, positive-side for positive literals - the standard superposition restrictions) - concluding the applied remainders plus the rewritten into literal.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on any failed side condition or unification; Err on structural failures or an over-long conclusion; the substitution trail is unwound on every path.
// CEP:ASSUMES: premises renamed apart; the equation atom is an equality; the path addresses a subterm of the into atom; out holds kMaxClauseLiterals slots.
// CEP:COST: one unification, one comparison, one rebuild, O(length) applications.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{superposition_into_negative, superposition_into_positive, superposition_orients_equations, superposition_rejects_variable_targets, superposition_side_conditions}; property/inference_property_test.rs::{superposition_is_sound, superposition_side_conditions}.
// CEP:SECURITY: depth-bounded recursion.
pub fn superpose(
    context: &InferenceContext<'_>,
    from_literals: &[Literal],
    equation_index: usize,
    into_literals: &[Literal],
    into_index: usize,
    path: &[u16],
    out: &mut [Literal],
) -> Result<SuperpositionOutcome, InferenceError> {
    let equation = &from_literals[equation_index];
    if !equation.is_positive() {
        return Ok(SuperpositionOutcome::None);
    }
    let (equation_left, equation_right) = match equality_sides(context.terms, equation.atom()) {
        Some(value) => value,
        None => return Ok(SuperpositionOutcome::None),
    };
    let into_literal = &into_literals[into_index];
    let target = match subterm_at(context.terms, into_literal.atom(), path) {
        Some(value) => value,
        None => return Ok(SuperpositionOutcome::None),
    };
    // Variable restriction (design 10.2): the target subterm must not be a variable.
    if let Ok(view) = context.terms.term(target) {
        if view.tag() == TermTag::Variable {
            return Ok(SuperpositionOutcome::None);
        }
    } else {
        return Ok(SuperpositionOutcome::None);
    }
    // Eligibility: the equation strictly maximal or selected; the into literal
    // eligible on its polarity side (Spec 07 sections 3 and 6).
    if !super::eligible_positive(context, from_literals, equation_index) {
        return Ok(SuperpositionOutcome::None);
    }
    let into_eligible = if into_literal.is_positive() {
        super::eligible_positive(context, into_literals, into_index)
    } else {
        super::eligible_negative(into_literals, into_index)
    };
    if !into_eligible {
        return Ok(SuperpositionOutcome::None);
    }
    let entry_depth = context.substitution.trail_depth();
    let unified = unify(context.terms, context.substitution, target, equation_left)?;
    if !unified {
        return Ok(SuperpositionOutcome::None);
    }
    // Orientation (design 10.2): s sigma strictly greater than t sigma.
    let applied_left = context
        .substitution
        .apply(context.terms, equation_left, context.symbols)?;
    let applied_right =
        context
            .substitution
            .apply(context.terms, equation_right, context.symbols)?;
    let oriented = match context.compare(applied_left, applied_right) {
        Ok(crate::ordering::OrderingComparison::Greater) => true,
        Ok(_) => false,
        Err(_) => {
            context.substitution.undo_to(entry_depth);
            return Ok(SuperpositionOutcome::None);
        }
    };
    if !oriented {
        context.substitution.undo_to(entry_depth);
        return Ok(SuperpositionOutcome::None);
    }
    // The target under sigma must still be a non-variable (sigma could instantiate
    // around it; the standard restriction is on w sigma, Spec 07 section 6).
    let applied_target = context
        .substitution
        .apply(context.terms, target, context.symbols)?;
    if let Ok(view) = context.terms.term(applied_target) {
        if view.tag() == TermTag::Variable {
            context.substitution.undo_to(entry_depth);
            return Ok(SuperpositionOutcome::None);
        }
    }
    // Conclusion: applied remainders plus the rewritten into literal.
    let rewritten_atom = replace_at(context, into_literal.atom(), path, applied_right, 0)?;
    let rewritten = Literal::new(rewritten_atom, into_literal.is_positive());
    let mut count: usize = 0;
    let mut overflow = false;
    for (index, literal) in from_literals.iter().enumerate() {
        if index == equation_index {
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
        for (index, literal) in into_literals.iter().enumerate() {
            if index == into_index {
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
    if !overflow {
        if count >= out.len() {
            overflow = true;
        } else {
            out[count] = apply_literal(
                context.terms,
                context.symbols,
                context.substitution,
                rewritten,
            )?;
            count += 1;
        }
    }
    context.substitution.undo_to(entry_depth);
    if overflow {
        return Err(InferenceError::ConclusionTooLong);
    }
    Ok(SuperpositionOutcome::Concluded(count))
}

// CEP:WHAT: Attempts equality resolution on the negative equation literals[index] (not (s = t)) with unifiable sides, concluding the applied remainders.
// CEP:WHY: NR01 section 4.3 (Spec 07 section 6): when sigma = MGU(s, t) exists, the literal is trivially contradictory under sigma and is dropped; soundness is the equality-elimination instance of resolution.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) on failed side conditions or unification; Err on structural failures; trail unwound on every path.
// CEP:ASSUMES: literals belong to one clause; out holds kMaxClauseLiterals slots.
// CEP:COST: one unification plus O(length) applications.
// CEP:EVIDENCE: unit/hot/inference_test.rs::equality_resolution_concludes; property/inference_property_test.rs::equality_resolution_is_sound.
// CEP:SECURITY: depth-bounded unification.
pub fn equality_resolve(
    context: &InferenceContext<'_>,
    literals: &[Literal],
    index: usize,
    out: &mut [Literal],
) -> Result<SuperpositionOutcome, InferenceError> {
    let literal = &literals[index];
    if literal.is_positive() {
        return Ok(SuperpositionOutcome::None);
    }
    let (left, right) = match equality_sides(context.terms, literal.atom()) {
        Some(value) => value,
        None => return Ok(SuperpositionOutcome::None),
    };
    if !super::eligible_negative(literals, index) {
        return Ok(SuperpositionOutcome::None);
    }
    let entry_depth = context.substitution.trail_depth();
    let unified = unify(context.terms, context.substitution, left, right)?;
    if !unified {
        return Ok(SuperpositionOutcome::None);
    }
    let mut count: usize = 0;
    let mut overflow = false;
    for (position, other) in literals.iter().enumerate() {
        if position == index {
            continue;
        }
        if count >= out.len() {
            overflow = true;
            break;
        }
        out[count] = apply_literal(context.terms, context.symbols, context.substitution, *other)?;
        count += 1;
    }
    context.substitution.undo_to(entry_depth);
    if overflow {
        return Err(InferenceError::ConclusionTooLong);
    }
    Ok(SuperpositionOutcome::Concluded(count))
}
