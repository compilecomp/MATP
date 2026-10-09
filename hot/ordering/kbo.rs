// CEP:FILE: hot/ordering/kbo.rs
// CEP:WHAT: Knuth-Bendix Ordering: weight-first comparison using the cached term weights, precedence fallback on weight ties, and a lazily-verified variable-occurrence condition.
// CEP:WHY: Design 8.3: KBO is the default ordering for superposition (Knuth & Bendix 1970); the comparison is on the hot path of every superposition and resolution side condition, so it must be OPT-0: compare cached header weights first (O(1)) and recurse only on ties, exactly as the design prescribes ("compare term headers first (symbol ID, weight), recurse only on tie"); Formal Spec 03 fixes the definition and admissibility argument.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns OrderingError::StepBudgetExceeded past kMaxOrderingSteps comparisons, InvalidPointer for unreadable terms, UnknownSymbol for out-of-table heads, UnsupportedHead for Application/Lambda heads (Phase 5); never panics.
// CEP:ASSUMES: Term weights are cached at intern (term.rs, design 8.3), every symbol weight is at least one (validated at symbol-table freeze, so the admissibility simplification property holds without the unary-weight exception), and the precedence table covers all symbols of the compared terms.
// CEP:COST: weight-differing ground pairs are O(1) (two header loads and compares); ties pay O(size) variable counting and lexicographic recursion, bounded by the step budget; measured 111.00 cycles median for the weight-dominance fast path and 238.18 for the equal-weight lexicographic path on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0007, artifacts benches/artifacts/ordering_kbo_weight.json and ordering_kbo_lex.json.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::{kbo_weight_dominates, kbo_precedence_case, kbo_lexicographic_case, kbo_variable_condition_gates, kbo_ground_totality}; property/ordering_property_test.rs.
// CEP:SECURITY: recursion depth and step count bounded (CEP&CC 22.10); all reads bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; comparisons depend only on term structure, cached weights, and the frozen precedence, in index order.
// CEP:HPC-PASS-LEGALITY: Formal Spec 03 section 2 fixes the KBO definition (weight dominance with variable condition, then precedence or lexicographic tie-break) and its theorems (irreflexivity, transitivity, totality on ground terms, subterm property, stability under substitution) that the property tests verify.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: variable counting is a full O(size) traversal per comparison level; caching variable-occurrence counts on term headers (or a bitset signature) would shorten the equal-weight path; deferred pending Phase 3 inference measurements; ticket CEP-1025.

use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::ordering::precedence::PrecedenceTable;
use crate::ordering::{kOrderingDepthLimit, OrderingComparison, OrderingError, StepBudget};
use mapt_config::limits::kMaxVariablesPerClause;

/// CEP:WHAT: Compares two terms under KBO: Greater, Less, Equal (pointer-equal terms), or Incomparable (variable condition failure or unsupported heads).
/// CEP:WHY: The public entry point of the KBO component (design 8.3); Equal is a distinct outcome because literal selection treats equality differently from incomparability.
/// CEP:STATUS: complete
/// CEP:FAILURE: see OrderingError; comparisons never panic.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header; measured in bench CEP-BENCH-0007.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs::{kbo_weight_dominates, kbo_ground_totality}; property/ordering_property_test.rs::{ordering_irreflexive, ordering_transitive_ground, ordering_total_on_ground}.
/// CEP:SECURITY: step budget bounds total work.
pub fn compare_kbo(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
) -> Result<OrderingComparison, OrderingError> {
    let mut budget = StepBudget::new();
    compare_bounded(terms, precedence, left, right, 0, &mut budget)
}

/// CEP:WHAT: Compares two terms under KBO with an explicit step budget (production callers use compare_kbo with kMaxOrderingSteps).
/// CEP:WHY: Security tests must exercise the StepBudgetExceeded path at small, fast scales; the entry point shares the entire comparison code with the production path (CEP&CC 34.3: test the mechanism).
/// CEP:STATUS: complete
/// CEP:FAILURE: as compare_kbo; budgets below the comparison cost return StepBudgetExceeded.
/// CEP:ASSUMES: budget >= 1.
/// CEP:COST: as compare_kbo.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
/// CEP:SECURITY: denial-of-service bound enforcement.
pub fn compare_kbo_with_budget(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
    budget: u32,
) -> Result<OrderingComparison, OrderingError> {
    let mut steps = StepBudget::with_limit(budget);
    compare_bounded(terms, precedence, left, right, 0, &mut steps)
}

// CEP:WHAT: Recursive KBO core with depth and step guards.
// CEP:WHY: The KBO case analysis (Spec 03 section 2): pointer-equal terms are Equal (hash-consing); weight dominance decides immediately when the variable condition holds; weight ties fall through to precedence (different heads) or lexicographic comparison of children (same head), with the variable condition verified lazily in the winning direction.
// CEP:STATUS: complete
// CEP:FAILURE: as compare_kbo.
// CEP:ASSUMES: ancestor frames left budget consistent.
// CEP:COST: O(1) on weight-differing pairs; O(size) counting plus recursion on ties.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::{kbo_weight_dominates, kbo_precedence_case, kbo_lexicographic_case, kbo_variable_condition_gates}.
// CEP:SECURITY: depth- and step-bounded.
fn compare_bounded(
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
    depth: u32,
    budget: &mut StepBudget,
) -> Result<OrderingComparison, OrderingError> {
    budget.consume()?;
    if depth > kOrderingDepthLimit {
        return Err(OrderingError::DepthExceeded);
    }
    if left == right {
        return Ok(OrderingComparison::Equal);
    }
    let left_view = terms.term(left).map_err(map_term_error)?;
    let right_view = terms.term(right).map_err(map_term_error)?;
    let left_weight = left_view.weight();
    let right_weight = right_view.weight();
    if left_weight > right_weight {
        return if variable_counts_dominate(terms, left, right, depth)? {
            Ok(OrderingComparison::Greater)
        } else {
            Ok(OrderingComparison::Incomparable)
        };
    }
    if right_weight > left_weight {
        return if variable_counts_dominate(terms, right, left, depth)? {
            Ok(OrderingComparison::Less)
        } else {
            Ok(OrderingComparison::Incomparable)
        };
    }
    // Equal weights: variables never relate to anything (Spec 03 section 2 lemma).
    if left_view.tag() == TermTag::Variable || right_view.tag() == TermTag::Variable {
        return Ok(OrderingComparison::Incomparable);
    }
    if left_view.tag() == TermTag::Application
        || left_view.tag() == TermTag::Lambda
        || right_view.tag() == TermTag::Application
        || right_view.tag() == TermTag::Lambda
    {
        return Err(OrderingError::UnsupportedHead);
    }
    let left_rank = head_rank(precedence, &left_view)?;
    let right_rank = head_rank(precedence, &right_view)?;
    if left_view.tag() != right_view.tag() || left_view.symbol() != right_view.symbol() {
        if left_rank > right_rank {
            return if variable_counts_dominate(terms, left, right, depth)? {
                Ok(OrderingComparison::Greater)
            } else {
                Ok(OrderingComparison::Incomparable)
            };
        }
        if right_rank > left_rank {
            return if variable_counts_dominate(terms, right, left, depth)? {
                Ok(OrderingComparison::Less)
            } else {
                Ok(OrderingComparison::Incomparable)
            };
        }
        return Ok(OrderingComparison::Incomparable);
    }
    // Same head and arity: first differing child decides lexicographically.
    for index in 0..left_view.child_count() {
        let left_child = left_view.child(index).map_err(map_term_error)?;
        let right_child = right_view.child(index).map_err(map_term_error)?;
        if left_child == right_child {
            continue;
        }
        let child = compare_bounded(
            terms,
            precedence,
            left_child,
            right_child,
            depth + 1,
            budget,
        )?;
        return match child {
            OrderingComparison::Greater => {
                if variable_counts_dominate(terms, left, right, depth)? {
                    Ok(OrderingComparison::Greater)
                } else {
                    Ok(OrderingComparison::Incomparable)
                }
            }
            OrderingComparison::Less => {
                if variable_counts_dominate(terms, right, left, depth)? {
                    Ok(OrderingComparison::Less)
                } else {
                    Ok(OrderingComparison::Incomparable)
                }
            }
            OrderingComparison::Equal => Ok(OrderingComparison::Equal),
            OrderingComparison::Incomparable => Ok(OrderingComparison::Incomparable),
        };
    }
    // Same head and all children pointer-equal contradicts left != right after hash-consing;
    // reported as Equal defensively (structural identity by the interning invariant).
    Ok(OrderingComparison::Equal)
}

// CEP:WHAT: Verifies the KBO variable condition: every variable occurs at least as often in the left term as in the right term.
// CEP:WHY: Spec 03 section 2: without the occurrence condition KBO would not be a simplification order (f(x) must not dominate g(x, x) even on weight ties); counting both terms per call keeps each comparison level self-contained and correct under the lexicographic recursion.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InvalidPointer and depth errors from the counting traversals.
// CEP:ASSUMES: variable indices are below kMaxVariablesPerClause (guaranteed by intern_var).
// CEP:COST: O(|left| + |right|) per call, one frame per level.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::kbo_variable_condition_gates; property/ordering_property_test.rs::kbo_stable_under_substitution.
// CEP:SECURITY: depth-bounded traversal.
fn variable_counts_dominate(
    terms: &TermStore<'_>,
    left: TermPtr,
    right: TermPtr,
    depth: u32,
) -> Result<bool, OrderingError> {
    let mut left_counts = VariableCounts::default();
    let mut right_counts = VariableCounts::default();
    count_variables(terms, left, &mut left_counts, depth)?;
    count_variables(terms, right, &mut right_counts, depth)?;
    for index in 0..kMaxVariablesPerClause as usize {
        if right_counts.0[index] > left_counts.0[index] {
            return Ok(false);
        }
    }
    Ok(true)
}

// CEP:WHAT: Flat per-variable occurrence counter (one u32 per variable slot).
/// CEP:WHY: KBO's variable condition is multiset containment of variable occurrences; a dense array indexed by variable ID is the no-hashing representation mandated by design 5.5 for substitution lookups and reused here.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data structure.
/// CEP:ASSUMES: variable indices below kMaxVariablesPerClause.
/// CEP:COST: 256 bytes on the stack per counting call.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs::kbo_variable_condition_gates.
/// CEP:SECURITY: bounds-checked indexing.
#[derive(Clone, Copy)]
struct VariableCounts([u32; kMaxVariablesPerClause as usize]);

// CEP:WHAT: Zeroed variable counts (const-context constructor).
// CEP:WHY: Default trait impls in no_std derive cannot const-zero arrays of this size ergonomically; an explicit impl keeps construction deterministic.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant-time zeroing.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::kbo_variable_condition_gates.
// CEP:SECURITY: none.
impl Default for VariableCounts {
    fn default() -> VariableCounts {
        VariableCounts([0; kMaxVariablesPerClause as usize])
    }
}

// CEP:WHAT: Accumulates variable occurrences of a term into the counter.
// CEP:WHY: The counting traversal of the KBO variable condition; index-ordered and depth-guarded so the result is deterministic and bounded.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InvalidPointer and DepthExceeded.
// CEP:ASSUMES: none.
// CEP:COST: O(|term|).
// CEP:EVIDENCE: unit/hot/ordering_test.rs::kbo_variable_condition_gates.
// CEP:SECURITY: depth-bounded recursion.
fn count_variables(
    terms: &TermStore<'_>,
    term: TermPtr,
    counts: &mut VariableCounts,
    depth: u32,
) -> Result<(), OrderingError> {
    if depth > kOrderingDepthLimit {
        return Err(OrderingError::DepthExceeded);
    }
    let view = terms.term(term).map_err(map_term_error)?;
    match view.tag() {
        TermTag::Variable => {
            let index = view.symbol() as usize;
            if index >= counts.0.len() {
                return Err(OrderingError::InvalidPointer);
            }
            counts.0[index] += 1;
            Ok(())
        }
        _ => {
            for child_index in 0..view.child_count() {
                let child = view.child(child_index).map_err(map_term_error)?;
                count_variables(terms, child, counts, depth + 1)?;
            }
            Ok(())
        }
    }
}

// CEP:WHAT: Resolves the precedence rank of a term head, mapping the equality tag to the pseudo-entry.
// CEP:WHY: Equality atoms carry the reserved symbol zero which must not alias real symbol zero; the shared resolver keeps KBO and LPO identical on head ranking.
// CEP:STATUS: complete
// CEP:FAILURE: Returns UnknownSymbol for out-of-table symbols.
// CEP:ASSUMES: Application/Lambda heads were rejected by the caller.
// CEP:COST: 1 bounds check + 1 load.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::id_order_is_default.
// CEP:SECURITY: bounds-checked.
pub(crate) fn head_rank(
    precedence: &PrecedenceTable<'_>,
    view: &crate::ir::term::TermView<'_>,
) -> Result<u32, OrderingError> {
    match view.tag() {
        TermTag::Equality => Ok(precedence.equality_rank()),
        _ => precedence
            .rank(view.symbol())
            .map_err(|_| OrderingError::UnknownSymbol),
    }
}

// CEP:WHAT: Maps term-store errors onto the ordering error vocabulary.
// CEP:WHY: CEP&CC 33.18: single translation point between the term store and the ordering component.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::invalid_terms_rejected.
// CEP:SECURITY: none.
pub(crate) fn map_term_error(_error: crate::ir::term::TermError) -> OrderingError {
    // All term-store failures (unreadable offset, truncated record, exhausted table) are the
    // same event for the ordering: the compared term cannot be read. A single mapping keeps
    // the translation auditable (CEP&CC 33.18).
    OrderingError::InvalidPointer
}
