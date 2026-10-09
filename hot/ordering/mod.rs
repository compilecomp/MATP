// CEP:FILE: hot/ordering/mod.rs
// CEP:WHAT: Term ordering module: the frozen precedence table, the Knuth-Bendix Ordering, and the Lexicographic Path Ordering, with the shared comparison vocabulary and step budget.
// CEP:WHY: Design 8.3 and 26 (Phase 2): superposition and resolution side conditions need a simplification ordering on terms; KBO is the default and LPO the configurable alternative, both OPT-0 with cached-weight fast paths; the module isolates the shared vocabulary so both orderings obey one contract (Formal Spec 03).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring and shared types only.
// CEP:ASSUMES: comparisons are pure functions of term structure, cached weights, and the frozen precedence.
// CEP:COST: compile-time only; the orderings' costs are documented in their files.
// CEP:EVIDENCE: unit/hot/ordering_test.rs; property/ordering_property_test.rs; bench CEP-BENCH-0007.
// CEP:SECURITY: step budgets bound all comparison work (CEP&CC 22.10).
// CEP:HPC-DETERMINISM: deterministic; no mutable shared state, index-ordered traversal.

pub mod kbo;
pub mod lpo;
pub mod precedence;

pub use kbo::{compare_kbo, compare_kbo_with_budget};
pub use lpo::{compare_lpo, compare_lpo_with_budget};
pub use precedence::{PrecedenceError, PrecedenceTable};

use mapt_config::limits::{kMaxOrderingSteps, kMaxTermDepth};

/// CEP:WHAT: Four-valued comparison outcome of a term ordering.
/// CEP:WHY: Simplification orderings on terms with variables are partial (the variable condition or path structure can leave terms unrelated), so Less/Greater/Equal cannot cover all cases; conflating Incomparable with Equal would make literal selection unsound (design 10.2 side conditions distinguish them).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: on ground first-order terms the orderings never return Incomparable (property-tested).
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: property/ordering_property_test.rs::{ordering_total_on_ground, ordering_irreflexive}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingComparison {
    /// CEP:WHAT: Left term strictly greater.
    Greater,
    /// CEP:WHAT: Left term strictly smaller.
    Less,
    /// CEP:WHAT: Pointer-equal terms (hash-consing makes structural equality pointer equality).
    Equal,
    /// CEP:WHY: Distinct outcome because selection functions must distinguish equal from unrelated.
    /// CEP:STATUS: complete
    /// CEP:WHAT: The terms are unrelated by the ordering.
    Incomparable,
}

/// CEP:WHAT: Error cases of the ordering component.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; comparisons never panic and never silently continue past their resource bounds.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs::{invalid_terms_rejected, unsupported_heads_rejected}; security/phase2_bounds_test.rs::ordering_step_budget_enforced.
/// CEP:SECURITY: budget errors are the denial-of-service boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingError {
    /// CEP:WHAT: The comparison exceeded kMaxOrderingSteps recursive examinations.
    StepBudgetExceeded,
    /// CEP:WHAT: A referenced term is unreadable or a variable index is illegal.
    InvalidPointer,
    /// CEP:WHAT: A term head is not covered by the precedence table.
    UnknownSymbol,
    /// CEP:WHAT: An Application or Lambda head was compared (higher-order orderings are Phase 5).
    UnsupportedHead,
    /// CEP:WHAT: The recursion depth exceeded the term depth bound.
    DepthExceeded,
}

// CEP:WHAT: Depth limit shared by the ordering recursions, as u32.
// CEP:WHY: kMaxTermDepth is u16 in config; the ordering recursion compares against a u32 counter, and the conversion belongs in one named place (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: matches the intern-time depth bound.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/ordering_test.rs.
// CEP:SECURITY: none.
pub(crate) const kOrderingDepthLimit: u32 = kMaxTermDepth as u32;

// CEP:WHAT: Static sanity check: the step budget dominates the depth limit.
// CEP:WHY: A budget smaller than the depth bound would reject straight-line traversals; CEP&CC Law 3 enforces the invariant mechanically.
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on violation.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/config/limits_test.rs::limit_invariants.
// CEP:SECURITY: none.
const _: () = assert!(kMaxOrderingSteps >= kOrderingDepthLimit);

/// CEP:WHAT: Step budget for one top-level comparison: decremented at every recursive examination, erroring at zero.
/// CEP:WHY: LPO case (b) re-descends the left term against every right child, which can multiply work exponentially on adversarial pairs; the budget turns that into OrderingError::StepBudgetExceeded (CEP&CC 22.10 unbounded-work ban) while leaving every realistic comparison unaffected.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: consume() returns StepBudgetExceeded when exhausted.
/// CEP:ASSUMES: one budget per public comparison call.
/// CEP:COST: one compare and decrement per step.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
/// CEP:SECURITY: denial-of-service bound.
pub(crate) struct StepBudget {
    /// CEP:WHAT: Remaining steps.
    /// CEP:WHY: The counter itself.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: initialized from kMaxOrderingSteps.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
    /// CEP:SECURITY: none.
    remaining: u32,
}

// CEP:WHAT: Budget construction and consumption.
// CEP:WHY: Keeping the counter private forces every decrement through the checked consume().
// CEP:STATUS: complete
// CEP:FAILURE: consume errors at zero.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
// CEP:SECURITY: none.
impl StepBudget {
    // CEP:WHAT: Creates a fully charged budget.
    // CEP:WHY: Entry-point constructor.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs.
    // CEP:SECURITY: none.
    pub(crate) fn new() -> StepBudget {
        StepBudget::with_limit(kMaxOrderingSteps)
    }

    // CEP:WHAT: Creates a budget with an explicit step limit.
    // CEP:WHY: The budget-limited comparison entry points (compare_kbo_with_budget, compare_lpo_with_budget) let security tests exercise the exhaustion path at small, fast scales; production callers use new() with the named constant (CEP&CC 34.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: limit >= 1.
    // CEP:COST: constant.
    // CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
    // CEP:SECURITY: none.
    pub(crate) fn with_limit(limit: u32) -> StepBudget {
        StepBudget { remaining: limit }
    }

    // CEP:WHAT: Consumes one step, erroring when the budget is exhausted.
    // CEP:WHY: The single enforcement point of the ordering resource bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns StepBudgetExceeded at zero remaining.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare + 1 decrement.
    // CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
    // CEP:SECURITY: denial-of-service enforcement.
    pub(crate) fn consume(&mut self) -> Result<(), OrderingError> {
        if self.remaining == 0 {
            return Err(OrderingError::StepBudgetExceeded);
        }
        self.remaining -= 1;
        Ok(())
    }
}
