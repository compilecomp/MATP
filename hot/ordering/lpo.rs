// CEP:FILE: hot/ordering/lpo.rs
// CEP:WHAT: Lexicographic Path Ordering: the strict greater-than predicate of Kamin and Reddy's recursion scheme (subterm, precedence, and lexicographic cases), wrapped into a four-valued comparison.
// CEP:WHY: Design 8.3: LPO is the configurable alternative to KBO (Kamin & Redy 1994 formulation, Baader & Nipkow presentation); superposition side conditions need it as a simplification ordering whose subterm property holds without weight conditions; Formal Spec 03 section 3 fixes the definition and the totality-on-ground-terms theorem.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns OrderingError::StepBudgetExceeded past kMaxOrderingSteps, InvalidPointer for unreadable terms, UnknownSymbol for out-of-table heads, UnsupportedHead for Application/Lambda heads (Phase 5); never panics.
// CEP:ASSUMES: the precedence table covers all symbols of the compared terms; variable occurrence checks are raw structural scans (no substitution is involved in ordering).
// CEP:COST: the strict predicate recursion is bounded by the step budget; measured 22.22 cycles median for a nested ground subterm-case comparison on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0007, artifact benches/artifacts/ordering_lpo.json.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::{lpo_subterm_case, lpo_precedence_and_lex_cases, lpo_variable_case, lpo_ground_totality}; property/ordering_property_test.rs::subterm_property_both_orderings.
// CEP:SECURITY: recursion depth and step count bounded (CEP&CC 22.10); all reads bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; comparisons depend only on term structure and the frozen precedence, in index order.
// CEP:HPC-PASS-LEGALITY: Formal Spec 03 section 3 fixes the LPO definition (variable case, subterm case, precedence case, lexicographic case) and its theorems (simplification order, totality on ground terms under total precedence) that the property tests verify.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: lpo_greater runs once per direction without memoizing sub-results; a comparison cache keyed by term-offset pairs would shorten repeated subterm checks in saturation workloads; deferred pending Phase 3 measurements; ticket CEP-1026.

use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::ordering::kbo::{head_rank, map_term_error};
use crate::ordering::precedence::PrecedenceTable;
use crate::ordering::{kOrderingDepthLimit, OrderingComparison, OrderingError, StepBudget};

/// CEP:WHAT: Compares two terms under LPO: Greater, Less, Equal (pointer-equal terms), or Incomparable.
/// CEP:WHY: The public entry point of the LPO component (design 8.3); the four-valued result shares the ordering contract with KBO so selection functions can be ordering-agnostic.
/// CEP:STATUS: complete
/// CEP:FAILURE: see OrderingError; comparisons never panic.
/// CEP:ASSUMES: see file header.
/// CEP:COST: two strict-predicate evaluations in the worst case (both directions); measured in bench CEP-BENCH-0007.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs::{lpo_subterm_case, lpo_ground_totality}; property/ordering_property_test.rs::{ordering_irreflexive, ordering_transitive_ground, ordering_total_on_ground, subterm_property_both_orderings}.
/// CEP:SECURITY: step budget bounds total work.
pub fn compare_lpo(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
) -> Result<OrderingComparison, OrderingError> {
    if left == right {
        return Ok(OrderingComparison::Equal);
    }
    let mut budget = StepBudget::new();
    if lpo_greater(terms, precedence, left, right, 0, &mut budget)? {
        return Ok(OrderingComparison::Greater);
    }
    if lpo_greater(terms, precedence, right, left, 0, &mut budget)? {
        return Ok(OrderingComparison::Less);
    }
    Ok(OrderingComparison::Incomparable)
}

/// CEP:WHAT: Compares two terms under LPO with an explicit step budget (production callers use compare_lpo with kMaxOrderingSteps).
/// CEP:WHY: Security tests must exercise the StepBudgetExceeded path at small, fast scales; the entry point shares the entire comparison code with the production path (CEP&CC 34.3: test the mechanism).
/// CEP:STATUS: complete
/// CEP:FAILURE: as compare_lpo; budgets below the comparison cost return StepBudgetExceeded.
/// CEP:ASSUMES: budget >= 1.
/// CEP:COST: as compare_lpo.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
/// CEP:SECURITY: denial-of-service bound enforcement.
pub fn compare_lpo_with_budget(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
    budget: u32,
) -> Result<OrderingComparison, OrderingError> {
    if left == right {
        return Ok(OrderingComparison::Equal);
    }
    let mut steps = StepBudget::with_limit(budget);
    if lpo_greater(terms, precedence, left, right, 0, &mut steps)? {
        return Ok(OrderingComparison::Greater);
    }
    if lpo_greater(terms, precedence, right, left, 0, &mut steps)? {
        return Ok(OrderingComparison::Less);
    }
    Ok(OrderingComparison::Incomparable)
}

// CEP:WHAT: The strict LPO greater-than predicate: is left strictly greater than right?
// CEP:WHY: Spec 03 section 3: left > right iff right is a variable occurring in left, or left is compound and (a) some left child is >= right, or (b) left's head precedes right's head and left > every right child, or (c) heads are equal and left is lexicographically greater at the first differing child; the case order is the definition's, and every case consumes budget so pathological pairs fail loudly.
// CEP:STATUS: complete
// CEP:FAILURE: propagates OrderingError; returns false when the relation does not hold (a comparison outcome, not an error).
// CEP:ASSUMES: left != right as pointers (callers check).
// CEP:COST: O(|left| x |right|) worst case, budget-bounded.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::{lpo_subterm_case, lpo_precedence_and_lex_cases, lpo_variable_case}.
// CEP:SECURITY: depth- and step-bounded recursion.
fn lpo_greater(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
    depth: u32,
    budget: &mut StepBudget,
) -> Result<bool, OrderingError> {
    budget.consume()?;
    if depth > kOrderingDepthLimit {
        return Err(OrderingError::DepthExceeded);
    }
    let right_view = terms.term(right).map_err(map_term_error)?;
    if right_view.tag() == TermTag::Variable {
        // Variable case: left > x iff x occurs in left and left is not x itself.
        return occurs_raw(terms, right_view.symbol(), left, depth);
    }
    let left_view = terms.term(left).map_err(map_term_error)?;
    if left_view.tag() == TermTag::Variable {
        // A variable is never greater than a compound term.
        return Ok(false);
    }
    if left_view.tag() == TermTag::Application
        || left_view.tag() == TermTag::Lambda
        || right_view.tag() == TermTag::Application
        || right_view.tag() == TermTag::Lambda
    {
        return Err(OrderingError::UnsupportedHead);
    }
    // Case (a): some left child is equal to or greater than right.
    for index in 0..left_view.child_count() {
        let child = left_view.child(index).map_err(map_term_error)?;
        if child == right {
            return Ok(true);
        }
        if lpo_greater(terms, precedence, child, right, depth + 1, budget)? {
            return Ok(true);
        }
    }
    let left_rank = head_rank(precedence, &left_view)?;
    let right_rank = head_rank(precedence, &right_view)?;
    let heads_equal =
        left_view.tag() == right_view.tag() && left_view.symbol() == right_view.symbol();
    if !heads_equal {
        // Case (b): left's head precedes right's head and left dominates every right child.
        if left_rank > right_rank {
            for index in 0..right_view.child_count() {
                let child = right_view.child(index).map_err(map_term_error)?;
                if !lpo_greater(terms, precedence, left, child, depth + 1, budget)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        return Ok(false);
    }
    // Case (c): equal heads, lexicographic decision at the first differing child.
    for index in 0..left_view.child_count() {
        let left_child = left_view.child(index).map_err(map_term_error)?;
        let right_child = right_view.child(index).map_err(map_term_error)?;
        if left_child == right_child {
            continue;
        }
        return lpo_greater(
            terms,
            precedence,
            left_child,
            right_child,
            depth + 1,
            budget,
        );
    }
    // Same head and all children pointer-equal contradicts left != right (hash-consing).
    Ok(false)
}

// CEP:WHAT: Raw structural occurrence check: does the variable index occur in the term?
// CEP:WHY: LPO's variable case needs variable membership without any substitution (ordering compares raw terms); a dedicated scan keeps the semantics explicit and depth-bounded.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InvalidPointer and DepthExceeded.
// CEP:ASSUMES: variable indices below kMaxVariablesPerClause.
// CEP:COST: O(|term|) with early exit.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::lpo_variable_case.
// CEP:SECURITY: depth-bounded recursion.
fn occurs_raw(
    terms: &TermStore<'_>,
    variable: u32,
    term: TermPtr,
    depth: u32,
) -> Result<bool, OrderingError> {
    if depth > kOrderingDepthLimit {
        return Err(OrderingError::DepthExceeded);
    }
    let view = terms.term(term).map_err(map_term_error)?;
    match view.tag() {
        TermTag::Variable => Ok(view.symbol() == variable),
        _ => {
            for index in 0..view.child_count() {
                let child = view.child(index).map_err(map_term_error)?;
                if occurs_raw(terms, variable, child, depth + 1)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}
