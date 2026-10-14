// CEP:FILE: hot/inference/mod.rs
// CEP:WHAT: Inference engine module (design 10): literal selection and maximality, binary and ordered resolution, factoring, equality factoring, equality resolution, superposition left and right, demodulation, subsumption, and the bounded given-clause inference generator.
// CEP:WHY: Design 26 Phase 3 build order ("Superposition + resolution + factoring") over the Phase 2 unification and ordering engines: every rule implements the design 10.2 side conditions with the ordering (KBO/LPO) and the shared substitution namespace; rules are pure functions over premise literal slices so the generator (and only the generator) owns bounds and deferral (design 10.3); soundness of every rule is unconditional (resolution, factoring, superposition, and demodulation are sound without ordering restrictions), and the ordering side conditions are the standard completeness restrictions fixed in Formal Spec 07 with their references (Bachmair & Ganzinger 1994; Nieuwenhuis & Rubio 2001; Robinson 1965).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring and the shared error vocabulary only.
// CEP:ASSUMES: premise literal slices are variable-renamed apart by the caller (the shared substitution namespace bound kMaxInferenceVariables is enforced by the generator before any rule call).
// CEP:COST: compile-time only; per-rule costs are documented in their files.
// CEP:EVIDENCE: unit/hot/inference_test.rs; unit/hot/selection_test.rs; property/inference_property_test.rs.
// CEP:SECURITY: all term reads are bounds-checked; recursion is depth-bounded (CEP&CC 22.10).
// CEP:HPC-DETERMINISM: deterministic; literal and subterm enumeration are index-ordered, no clocks or addresses.

pub mod builder;
pub mod demodulation;
pub mod factoring;
pub mod resolution;
pub mod selection;
pub mod subsumption;
pub mod superposition;

pub use builder::{
    apply_literal, count_clause_variables, remap_variables, rename_apart, rename_clause_apart,
    restandardize_clause,
};
pub use selection::{
    compute_selection_flags, eligible_negative, eligible_positive, SelectionFunction,
};

use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::TermStore;
use crate::ordering::precedence::PrecedenceTable;
use crate::unification::substitution::{Substitution, SubstitutionError};

/// CEP:WHAT: Error cases of the inference engine.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; rules never panic and never exceed their structural bounds silently.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/inference_test.rs::{namespace_budget_enforced, premises_renamed_apart, conclusion_too_long_rejected}.
/// CEP:SECURITY: budget errors are the resource boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InferenceError {
    /// CEP:WHAT: A structural failure from the substitution or term engines (depth, bounds, unreadable terms).
    /// CEP:WHY: One carrier for the shared vocabulary (CEP&CC 33.18).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs.
    /// CEP:SECURITY: none.
    Structural(SubstitutionError),
    /// CEP:WHAT: The conclusion exceeds kMaxClauseLiterals literals.
    /// CEP:WHY: The clause record bound (design 5.3); a longer conclusion is reported to the generator, which counts and drops it, never stores it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::conclusion_too_long_rejected.
    /// CEP:SECURITY: memory bound.
    ConclusionTooLong,
    /// CEP:WHAT: A premise pair cannot share the substitution namespace (vars(left) + vars(right) > kMaxInferenceVariables).
    /// CEP:WHY: Spec 02 section 5: the substitution engine namespaces variables by dense per-clause index; the generator enforces the standardize-apart bound before calling any rule.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::namespace_budget_enforced.
    /// CEP:SECURITY: soundness precondition.
    VariableBudgetExceeded,
}

impl From<crate::ir::term::TermError> for InferenceError {
    // CEP:WHAT: Converts term-engine errors into the inference vocabulary.
    // CEP:WHY: CEP&CC 33.18: one translation point for term reads and interns inside the rules and builders.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/inference_test.rs::{rename_preserves_structure, rename_shifts_variables}.
    // CEP:SECURITY: none.
    fn from(_error: crate::ir::term::TermError) -> InferenceError {
        InferenceError::Structural(SubstitutionError::InvalidPointer)
    }
}

impl From<SubstitutionError> for InferenceError {
    // CEP:WHAT: Converts substitution-engine errors into the inference vocabulary.
    // CEP:WHY: CEP&CC 33.18: one explicit translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/inference_test.rs.
    // CEP:SECURITY: none.
    fn from(error: SubstitutionError) -> InferenceError {
        InferenceError::Structural(error)
    }
}

/// CEP:WHAT: The default ordering (KBO, design 8.3).
/// CEP:WHY: SearchOptions derives Default; KBO is the documented default.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs.
/// CEP:SECURITY: none.
impl Default for OrderingKind {
    // CEP:WHAT: The default ordering kind (Kbo).
    // CEP:WHY: Design 8.3.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs.
    // CEP:SECURITY: none.
    fn default() -> Self {
        OrderingKind::Kbo
    }
}

/// CEP:WHAT: Which term ordering the search uses for side conditions.
/// CEP:WHY: Design 8.3: KBO is the default and LPO the configurable alternative; the inference context dispatches comparisons through this tag so every rule is ordering-agnostic (a match, not dyn dispatch - CEP-0 discipline).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: the precedence table is valid for the chosen ordering.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs; unit/hot/inference_test.rs::superposition_orients_equations.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingKind {
    /// CEP:WHAT: Knuth-Bendix Ordering (default).
    /// CEP:WHY: Design 8.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/ordering_test.rs.
    /// CEP:SECURITY: none.
    Kbo,
    /// CEP:WHAT: Lexicographic Path Ordering.
    /// CEP:WHY: Design 8.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/ordering_test.rs.
    /// CEP:SECURITY: none.
    Lpo,
}

/// CEP:WHAT: The inference context: the term store, symbol table, substitution, precedence table, and ordering choice every rule shares.
/// CEP:WHY: One borrowed bundle keeps rule signatures small and makes the shared-substitution discipline explicit (one Substitution per generation step, trail-disciplined across rule attempts); comparisons dispatch on OrderingKind through compare().
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a context record.
/// CEP:ASSUMES: all fields refer to the same arena-backed state.
/// CEP:COST: plain references.
/// CEP:EVIDENCE: unit/hot/inference_test.rs; unit/hot/selection_test.rs.
/// CEP:SECURITY: none.
pub struct InferenceContext<'a> {
    /// CEP:WHAT: The term store backing all atoms.
    /// CEP:WHY: Rules read and construct terms.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: same store that interned the premises.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs.
    /// CEP:SECURITY: bounds-checked reads.
    pub terms: &'a TermStore<'a>,
    /// CEP:WHAT: The frozen symbol table.
    /// CEP:WHY: Substitution application and arity checks.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: frozen.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs.
    /// CEP:SECURITY: none.
    pub symbols: &'a SymbolTable<'a>,
    /// CEP:WHAT: The shared substitution (trail-disciplined).
    /// CEP:WHY: Rules extend it with MGUs and materialize conclusions through it; the generator snapshots the trail depth around attempts.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one instance per search; failure unwinding is the rules' contract.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs; contract/unification_trail_contract_test.rs.
    /// CEP:SECURITY: none.
    pub substitution: &'a Substitution<'a>,
    /// CEP:WHAT: The frozen precedence table.
    /// CEP:WHY: Ordering comparisons.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: frozen.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/selection_test.rs.
    /// CEP:SECURITY: none.
    pub precedence: &'a PrecedenceTable<'a>,
    /// CEP:WHAT: The ordering choice.
    /// CEP:WHY: compare() dispatch.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: matches the precedence table.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/hot/inference_test.rs::superposition_orients_equations.
    /// CEP:SECURITY: none.
    pub ordering: OrderingKind,
}

impl<'a> InferenceContext<'a> {
    // CEP:WHAT: Compares two terms under the configured ordering.
    // CEP:WHY: One dispatch point for every side condition; errors surface (never guessed past).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates OrderingError.
    // CEP:ASSUMES: terms interned by the context's store.
    // CEP:COST: as compare_kbo / compare_lpo.
    // CEP:EVIDENCE: unit/hot/inference_test.rs::superposition_orients_equations; unit/hot/selection_test.rs.
    // CEP:SECURITY: step budgets bound the comparison work.
    pub fn compare(
        &self,
        left: crate::ir::term::TermPtr,
        right: crate::ir::term::TermPtr,
    ) -> Result<crate::ordering::OrderingComparison, crate::ordering::OrderingError> {
        match self.ordering {
            OrderingKind::Kbo => {
                crate::ordering::compare_kbo(self.terms, self.precedence, left, right)
            }
            OrderingKind::Lpo => {
                crate::ordering::compare_lpo(self.terms, self.precedence, left, right)
            }
        }
    }
}
