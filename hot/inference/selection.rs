// CEP:FILE: hot/inference/selection.rs
// CEP:WHAT: Literal selection and maximality (design 10.1 "literal selection", 10.2 side conditions): computes the selected and maximal flags of every literal of a clause under the term ordering, and the eligibility predicates the resolution and superposition rules consume.
// CEP:WHY: Ordered calculi restrict inferences to eligible literals so the search space stays finite-ish and the calculus stays refutationally complete (Bachmair & Ganzinger 2001): a literal is eligible when it is selected (the selection function overrides maximality, design 10.2 "Selection: if the literal is selected, superposition is allowed regardless of maximality") or, when nothing is selected, when it is maximal among the clause's atoms; the flags are cached on the stored Literal records (design 5.2) at clause creation so inference generation never re-compares; maximality compares the literal ATOMS under KBO/LPO with the equality pseudo-symbol at the bottom of the precedence (Phase 2 precedence tables), which is the standard atom ordering of the superposition calculus (Nieuwenhuis & Rubio 2001 section 4.2).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: compute_selection_flags propagates InferenceError::Structural on unreadable atoms or ordering failures; a comparison error marks the literal non-maximal conservatively only when the terms are unreadable - unreadable atoms cannot occur for store-interned clauses (Law 3), so errors surface loudly instead.
// CEP:ASSUMES: Literal atoms were interned by the context's term store; the clause has at least one literal.
// CEP:COST: O(literals^2) ordering comparisons per clause (bounded by kMaxClauseLiterals^2 = 262_144 at the structural bound, typical clauses are single digits); measured within bench CEP-BENCH-0011, artifact benches/artifacts/atp_selection_flags.json.
// CEP:EVIDENCE: unit/hot/selection_test.rs::{maximality_computed, selection_overrides_maximality, first_negative_selects, empty_clause_flags}; property/inference_property_test.rs::{ordering_eligibility_respects_selection, resolution_side_conditions}.
// CEP:SECURITY: ordering step budgets bound every comparison (CEP&CC 22.10).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; comparisons are pure functions of term structure and the frozen precedence.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 3 fixes the eligibility definitions (maximal: no strictly greater atom in the clause; strictly maximal: maximal and no equal atom besides itself; eligible: selected, or no literal selected and maximal) and cites the completeness restrictions of the ordered resolution and superposition calculi the implementation follows.

use crate::ir::literal::Literal;
use crate::ordering::OrderingComparison;

use super::InferenceContext;

/// CEP:WHAT: The default selection function (None: pure maximality).
/// CEP:WHY: SearchOptions derives Default; no-selection is the default strategy.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: unit/hot/selection_test.rs::maximality_computed.
/// CEP:SECURITY: none.
impl Default for SelectionFunction {
    // CEP:WHAT: The default selection function (None).
    // CEP:WHY: Pure maximality is the default eligibility discipline.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/selection_test.rs::maximality_computed.
    // CEP:SECURITY: none.
    fn default() -> Self {
        SelectionFunction::None
    }
}

/// CEP:WHAT: The literal selection function (design 10.1).
/// CEP:WHY: Selection functions are the calculus's freedom lever: selecting negative literals before maximality restricts resolution and superposition exactly as BG94's calculus requires; the default (no selection) uses pure maximality, and FirstNegative selects the first negative literal if any (a standard complete selection for Horn-friendly problems).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/selection_test.rs::{selection_overrides_maximality, first_negative_selects}.
/// CEP:SECURITY: none.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectionFunction {
    /// CEP:WHAT: No literal is ever selected; eligibility is pure maximality.
    /// CEP:WHY: The default strategy.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/selection_test.rs::maximality_computed.
    /// CEP:SECURITY: none.
    None,
    /// CEP:WHAT: The first negative literal is selected when the clause has one.
    /// CEP:WHY: A standard complete selection (resolution happens on the selected negative literal only).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/selection_test.rs::first_negative_selects.
    /// CEP:SECURITY: none.
    FirstNegative,
}

// CEP:WHAT: Computes and sets the selected and maximal flags of every literal of a clause in place.
// CEP:WHY: Design 5.2: the flags are cached on the literal records at clause creation; selection runs first (design 10.2: selection overrides maximality), then maximality compares atoms pairwise (a literal is maximal when no other atom is strictly greater; the strictly-maximal test in eligibility additionally rejects equals).
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError::Structural when an atom is unreadable or a comparison errors (loud, never conservative-silent).
// CEP:ASSUMES: literals is non-empty in search use (the empty clause skips flag computation entirely).
// CEP:COST: O(n^2) comparisons for n literals.
// CEP:EVIDENCE: unit/hot/selection_test.rs::{maximality_computed, selection_overrides_maximality, first_negative_selects, ties_are_maximal_but_not_strict}.
// CEP:SECURITY: ordering budgets bound the work.
pub fn compute_selection_flags(
    context: &InferenceContext<'_>,
    selection: SelectionFunction,
    literals: &mut [Literal],
) -> Result<(), super::InferenceError> {
    // Selection pass.
    let mut selected_index: Option<usize> = None;
    if let SelectionFunction::FirstNegative = selection {
        for (index, literal) in literals.iter().enumerate() {
            if !literal.is_positive() {
                selected_index = Some(index);
                break;
            }
        }
    }
    for (index, literal) in literals.iter_mut().enumerate() {
        // The selected literal (if any) is the only inference site; maximality flags
        // are still computed for every literal because demodulation ignores selection.
        literal.set_selected(selected_index == Some(index));
        literal.set_maximal(false);
    }
    // Maximality pass: literal i is maximal iff no j has atom_j strictly greater.
    for i in 0..literals.len() {
        let mut maximal = true;
        for j in 0..literals.len() {
            if i == j {
                continue;
            }
            match context.compare(literals[j].atom(), literals[i].atom()) {
                Ok(OrderingComparison::Greater) => {
                    maximal = false;
                    break;
                }
                Ok(_) => {}
                Err(_) => {
                    // Ordering failures on store-interned atoms are structural faults;
                    // surfacing them loudly beats a silently wrong eligibility flag.
                    return Err(super::InferenceError::Structural(
                        crate::unification::substitution::SubstitutionError::InvalidPointer,
                    ));
                }
            }
        }
        literals[i].set_maximal(maximal);
    }
    Ok(())
}

// CEP:WHAT: Eligibility of the positive-side literal of a resolution or superposition inference: selected, or nothing selected and strictly maximal.
// CEP:WHY: Spec 07 section 3: the ordered calculus resolves/factors on strictly maximal positive literals (strictness breaks symmetric pairs), and selection overrides; the strictly-maximal test rejects equal atoms (identical literals are handled by factoring, not double resolution).
// CEP:STATUS: complete
// CEP:FAILURE: none (bool answer over cached flags).
// CEP:ASSUMES: flags were computed by compute_selection_flags on this literal slice.
// CEP:COST: O(n) for the strictness scan.
// CEP:EVIDENCE: unit/hot/selection_test.rs::{ties_are_maximal_but_not_strict}; unit/hot/inference_test.rs::resolution_side_conditions.
// CEP:SECURITY: none.
pub fn eligible_positive(
    context: &InferenceContext<'_>,
    literals: &[Literal],
    index: usize,
) -> bool {
    let literal = &literals[index];
    if literal.is_selected() {
        return true;
    }
    if literals.iter().any(|other| other.is_selected()) {
        return false;
    }
    if !literal.is_maximal() {
        return false;
    }
    // Strict maximality: no other atom equal to this one.
    for (other_index, other) in literals.iter().enumerate() {
        if other_index == index {
            continue;
        }
        if let Ok(OrderingComparison::Equal) = context.compare(other.atom(), literal.atom()) {
            return false;
        }
    }
    true
}

// CEP:WHAT: Eligibility of the negative-side literal of a resolution or superposition inference: selected, or nothing selected and maximal (non-strict).
// CEP:WHY: Spec 07 section 3: the negative side uses plain maximality (BG94 resolve on maximal or selected negative literals; ties are permitted because the positive side already enforces strictness).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: flags were computed by compute_selection_flags.
// CEP:COST: constant over cached flags.
// CEP:EVIDENCE: unit/hot/selection_test.rs::maximality_computed; unit/hot/inference_test.rs::resolution_side_conditions.
// CEP:SECURITY: none.
pub fn eligible_negative(literals: &[Literal], index: usize) -> bool {
    let literal = &literals[index];
    if literal.is_selected() {
        return true;
    }
    if literals.iter().any(|other| other.is_selected()) {
        return false;
    }
    literal.is_maximal()
}
