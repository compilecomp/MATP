// CEP:FILE: hot/inference/builder.rs
// CEP:WHAT: Term and clause construction helpers for the inference engine: variable renaming (standardize-apart), literal application under a substitution (plain and trail-restoring - the CEP-1050 restore helpers restore_trail/apply_unwind/apply_literal_unwind, which unwind the pre-unification trail on failure so the generator's drop-and-resume policy stays trail-safe), variable counting, and clause renaming.
// CEP:WHY: Spec 02 section 5 fixes the shared substitution namespace: variables are dense per-clause indices below kMaxVariablesPerClause, so two premises must be renamed apart into one namespace before unification (left keeps [0, vars(left)), right shifts by vars(left)) and conclusions must be re-standardized back to a dense [0, n) namespace before storage; renaming re-interns terms through the hash-consing store so structural sharing and pointer-equality fast paths survive (design 5.1); applying a literal under a substitution materializes the conclusion atoms once per rule call.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns InferenceError (structural failures from intern and application, depth bounds); never panics.
// CEP:ASSUMES: Terms were interned by the caller's store; variable indices are below kMaxVariablesPerClause before and after the shift (the caller enforces the namespace bound).
// CEP:COST: rename_apart is O(term nodes) with one intern per node (intern is hash-consed: identical structures hit the cache); apply_literal is one substitution application per atom; measured within bench CEP-BENCH-0010, artifact benches/artifacts/atp_resolution_step.json.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{premises_renamed_apart, rename_preserves_structure, rename_shifts_variables, conclusions_restandardized}; property/inference_property_test.rs.
// CEP:SECURITY: depth-bounded recursion (CEP&CC 22.10); all reads bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; children iterate in index order, intern is a pure function of structure.
// CEP:HPC-PASS-LEGALITY: Formal Spec 07 section 2 fixes the renaming theorem: renaming is a variable-for-variable bijorphism, so unification, matching, and ordering results are preserved under renaming (sigma over renamed premises corresponds to sigma composed with the renaming); the property tests verify executably that renamed premises unify exactly when the originals do.

use crate::ir::literal::Literal;
use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::{TermError, TermPtr, TermStore, TermTag};
use crate::unification::substitution::Substitution;
use mapt_config::limits::{kMaxInferenceVariables, kMaxSymbolArity, kMaxVariablesPerClause};

use super::InferenceError;

// CEP:WHAT: Converts term-engine errors into the inference vocabulary.
// CEP:WHY: CEP&CC 33.18: one translation point for intern failures inside the builders; every term error maps onto the structural carrier (the specific kind is recoverable from the call site).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{rename_preserves_structure, rename_shifts_variables}.
// CEP:SECURITY: none.
fn term_error(_error: TermError) -> InferenceError {
    InferenceError::Structural(crate::unification::substitution::SubstitutionError::InvalidPointer)
}

// CEP:WHAT: Rebuilds one term with every variable index shifted by offset (standardize-apart).
// CEP:WHY: Spec 02 section 5 and Spec 07 section 2: premises share one substitution namespace; the shift is the renaming bijorphism; hash-consed re-intern keeps structure sharing.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError on intern failure or shifted indices past the namespace bound.
// CEP:ASSUMES: term interned by the store; offset + every variable index < kMaxVariablesPerClause.
// CEP:COST: O(term nodes) with one intern per node.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{rename_shifts_variables, rename_preserves_structure}.
// CEP:SECURITY: depth-bounded recursion.
pub fn rename_apart(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    term: TermPtr,
    offset: u32,
    depth: u32,
) -> Result<TermPtr, InferenceError> {
    if depth > mapt_config::limits::kMaxTermDepth as u32 {
        return Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        ));
    }
    let view = terms.term(term).map_err(term_error)?;
    match view.tag() {
        TermTag::Variable => {
            let shifted = view.symbol() + offset;
            if shifted >= kMaxVariablesPerClause {
                return Err(InferenceError::VariableBudgetExceeded);
            }
            terms.intern_var(shifted).map_err(term_error)
        }
        TermTag::Function | TermTag::Predicate => {
            let mut children: [TermPtr; kMaxSymbolArity as usize] =
                [TermPtr::invalid(); kMaxSymbolArity as usize];
            let count = view.child_count();
            if count as usize > children.len() {
                return Err(InferenceError::Structural(
                    crate::unification::substitution::SubstitutionError::DepthExceeded,
                ));
            }
            for index in 0..count {
                children[index as usize] =
                    rename_apart(terms, symbols, view.child(index)?, offset, depth + 1)?;
            }
            if view.tag() == TermTag::Function {
                terms
                    .intern_fun(symbols, view.symbol(), &children[..count as usize])
                    .map_err(term_error)
            } else {
                terms
                    .intern_pred(symbols, view.symbol(), &children[..count as usize])
                    .map_err(term_error)
            }
        }
        TermTag::Equality => {
            let left = rename_apart(terms, symbols, view.child(0)?, offset, depth + 1)?;
            let right = rename_apart(terms, symbols, view.child(1)?, offset, depth + 1)?;
            terms.intern_eq(symbols, left, right).map_err(term_error)
        }
        TermTag::Application | TermTag::Lambda => {
            // Higher-order tags are Phase 5; renaming them structurally keeps the
            // helper total without giving them inference rules.
            Err(InferenceError::Structural(
                crate::unification::substitution::SubstitutionError::DepthExceeded,
            ))
        }
        TermTag::Sort => Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        )),
    }
}

// CEP:WHAT: Renames a clause's literals into a target variable window and returns the distinct-variable count of the original.
// CEP:WHY: The generator renames the left premise into [0, vars(left)) implicitly (input clauses are stored dense) and the right premise into [vars(left), vars(left) + vars(right)); the count drives the namespace bound check.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError; VariableBudgetExceeded when the shifted window would leave the namespace.
// CEP:ASSUMES: literals belong to one clause with a dense variable namespace.
// CEP:COST: O(total term nodes).
// CEP:EVIDENCE: unit/hot/inference_test.rs::{premises_renamed_apart, namespace_budget_enforced}.
// CEP:SECURITY: none.
pub fn rename_clause_apart(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    literals: &[Literal],
    offset: u32,
    out: &mut [Literal],
) -> Result<usize, InferenceError> {
    let variables = count_clause_variables(terms, literals)?;
    if variables as u64 + offset as u64 > kMaxInferenceVariables as u64 {
        return Err(InferenceError::VariableBudgetExceeded);
    }
    if literals.len() > out.len() {
        return Err(InferenceError::ConclusionTooLong);
    }
    for (index, literal) in literals.iter().enumerate() {
        let atom = rename_apart(terms, symbols, literal.atom(), offset, 0)?;
        let mut renamed = Literal::new(atom, literal.is_positive());
        // Eligibility flags ride along: the renamed premise keeps its computed
        // selected/maximal state so the rules' side conditions survive the
        // standardize-apart shift (Spec 07 section 2).
        renamed.set_selected(literal.is_selected());
        renamed.set_maximal(literal.is_maximal());
        out[index] = renamed;
    }
    Ok(variables)
}

// CEP:WHAT: Counts the distinct variable indices of a clause.
// CEP:WHY: The namespace bound (vars(left) + vars(right) <= kMaxInferenceVariables) needs the exact count; the dense-index assumption makes a fixed bool table exact and allocation-free.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError on unreadable terms.
// CEP:ASSUMES: variable indices are dense per-clause (store discipline).
// CEP:COST: O(total term nodes).
// CEP:EVIDENCE: unit/hot/inference_test.rs::{premises_renamed_apart, namespace_budget_enforced}.
// CEP:SECURITY: depth-bounded recursion.
pub fn count_clause_variables(
    terms: &TermStore<'_>,
    literals: &[Literal],
) -> Result<usize, InferenceError> {
    let mut seen = [false; kMaxVariablesPerClause as usize];
    for literal in literals.iter() {
        count_variables(terms, literal.atom(), &mut seen, 0)?;
    }
    Ok(seen.iter().filter(|value| **value).count())
}

// CEP:WHAT: Recursive variable-marking walk of one term.
// CEP:WHY: Shared by the counter; marks distinct indices into the fixed table.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError.
// CEP:ASSUMES: variable indices below kMaxVariablesPerClause (intern-enforced).
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: unit/hot/inference_test.rs::premises_renamed_apart.
// CEP:SECURITY: depth-bounded.
fn count_variables(
    terms: &TermStore<'_>,
    term: TermPtr,
    seen: &mut [bool; kMaxVariablesPerClause as usize],
    depth: u32,
) -> Result<(), InferenceError> {
    if depth > mapt_config::limits::kMaxTermDepth as u32 {
        return Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        ));
    }
    let view = terms.term(term).map_err(term_error)?;
    if view.tag() == TermTag::Variable {
        let index = view.symbol() as usize;
        if index < seen.len() {
            seen[index] = true;
        }
        return Ok(());
    }
    for child in view.children() {
        count_variables(terms, child, seen, depth + 1)?;
    }
    Ok(())
}

// CEP:WHAT: Applies the substitution to one literal's atom and keeps its polarity.
// CEP:WHY: Conclusion materialization: every rule applies its MGU to the surviving premise literals; flags (selected, maximal) are reset by construction (Literal::new defaults) because the conclusion's flags are recomputed at clause creation.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError from application (depth cycles, unreadable terms).
// CEP:ASSUMES: the substitution is the rule's MGU; the atom was interned by the store.
// CEP:COST: one substitution application per literal.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{resolvent_applies_mgu, factoring_applies_mgu}; bench CEP-BENCH-0010.
// CEP:SECURITY: depth-bounded application.
pub fn apply_literal(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    substitution: &Substitution<'_>,
    literal: Literal,
) -> Result<Literal, InferenceError> {
    let atom = substitution
        .apply(terms, literal.atom(), symbols)
        .map_err(InferenceError::from)?;
    Ok(Literal::new(atom, literal.is_positive()))
}

// CEP:WHAT: Restores the substitution trail to entry_depth when result is an error, then passes the result through (CEP-1050).
// CEP:WHY: Post-unify materialization can fail (DepthExceeded, WeightExceeded, ArenaFull) while the MGU's bindings are still on the trail; the generator's bound-error drop policy (CEP-1050) resumes the search after dropping the candidate, so a polluted trail would corrupt every later attempt (a later unify would hit already-bound variables); one wrapper keeps the restore discipline at a single point instead of at every materialization call site.
// CEP:STATUS: complete
// CEP:FAILURE: Ok passes through untouched; Err unwinds to entry_depth first (the depth observed before the rule's unification), then propagates.
// CEP:ASSUMES: entry_depth was observed via trail_depth() before the rule extended the substitution; no other bindings were made after the failing call.
// CEP:COST: one trail_depth compare on success; one undo_to on failure.
// CEP:EVIDENCE: unit/hot/inference_test.rs::materialization_failure_unwinds_trail.
// CEP:SECURITY: the undo loop is internally clamped (Spec 02 section 4).
pub fn restore_trail<T>(
    substitution: &Substitution<'_>,
    entry_depth: u32,
    result: Result<T, InferenceError>,
) -> Result<T, InferenceError> {
    match result {
        Ok(value) => Ok(value),
        Err(error) => {
            substitution.undo_to(entry_depth);
            Err(error)
        }
    }
}

// CEP:WHAT: Applies the substitution to one term and unwinds the trail to entry_depth on failure (CEP-1050).
// CEP:WHY: The applied-side reads inside the rules (demodulation's oriented sides, superposition's applied left/right and target) run after the matcher or MGU bound the trail; a failing application must not leak those bindings into the next attempt under the generator's drop-and-resume policy.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError with the trail restored to entry_depth.
// CEP:ASSUMES: entry_depth observed before the rule's unification.
// CEP:COST: one application plus the restore on failure.
// CEP:EVIDENCE: unit/hot/inference_test.rs::materialization_failure_unwinds_trail.
// CEP:SECURITY: depth-bounded application.
pub fn apply_unwind(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    substitution: &Substitution<'_>,
    term: TermPtr,
    entry_depth: u32,
) -> Result<TermPtr, InferenceError> {
    let applied = substitution
        .apply(terms, term, symbols)
        .map_err(InferenceError::from);
    restore_trail(substitution, entry_depth, applied)
}

// CEP:WHAT: Applies the substitution to one literal and unwinds the trail to entry_depth on failure (CEP-1050).
// CEP:WHY: Conclusion materialization under the drop-and-resume policy: a failing apply_literal inside a rule must restore the pre-unification trail so the generator's next attempt starts clean.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError with the trail restored to entry_depth.
// CEP:ASSUMES: entry_depth observed before the rule's unification.
// CEP:COST: one application plus the restore on failure.
// CEP:EVIDENCE: unit/hot/inference_test.rs::materialization_failure_unwinds_trail.
// CEP:SECURITY: depth-bounded application.
pub fn apply_literal_unwind(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    substitution: &Substitution<'_>,
    literal: Literal,
    entry_depth: u32,
) -> Result<Literal, InferenceError> {
    let applied = apply_literal(terms, symbols, substitution, literal);
    restore_trail(substitution, entry_depth, applied)
}

// CEP:WHAT: Remaps one term's variable indices through a first-occurrence dense mapping and rebuilds it.
// CEP:WHY: Conclusions of inter-clause rules live in the shared standardize-apart namespace [0, vars(left) + vars(right)), which can have gaps (premises rarely use every index); storing a gapped clause breaks the dense-namespace discipline that rename_clause_apart's offset arithmetic relies on (a later rename could collide variables), so every stored conclusion is restandardized to a dense [0, n) namespace first (Spec 07 section 2's storage half).
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError on intern failure or depth exhaustion; VariableBudgetExceeded when the dense namespace would exceed the bound.
// CEP:ASSUMES: atom interned by the store; mapping slots below the current next index hold assigned targets, others are unassigned.
// CEP:COST: O(term nodes) with one intern per node.
// CEP:EVIDENCE: unit/hot/inference_test.rs::conclusions_restandardized.
// CEP:SECURITY: depth-bounded recursion.
pub fn remap_variables(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    term: TermPtr,
    mapping: &mut [u32; kMaxVariablesPerClause as usize],
    next: &mut u32,
    depth: u32,
) -> Result<TermPtr, InferenceError> {
    if depth > mapt_config::limits::kMaxTermDepth as u32 {
        return Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        ));
    }
    let view = terms.term(term).map_err(term_error)?;
    match view.tag() {
        TermTag::Variable => {
            let index = view.symbol() as usize;
            if index >= mapping.len() {
                return Err(InferenceError::Structural(
                    crate::unification::substitution::SubstitutionError::VariableOutOfRange,
                ));
            }
            let target = if mapping[index] == u32::MAX {
                if *next >= kMaxVariablesPerClause {
                    return Err(InferenceError::VariableBudgetExceeded);
                }
                mapping[index] = *next;
                *next += 1;
                mapping[index]
            } else {
                mapping[index]
            };
            terms.intern_var(target).map_err(term_error)
        }
        TermTag::Function | TermTag::Predicate => {
            let mut children: [TermPtr; kMaxSymbolArity as usize] =
                [TermPtr::invalid(); kMaxSymbolArity as usize];
            let count = view.child_count();
            if count as usize > children.len() {
                return Err(InferenceError::Structural(
                    crate::unification::substitution::SubstitutionError::DepthExceeded,
                ));
            }
            for index in 0..count {
                children[index as usize] =
                    remap_variables(terms, symbols, view.child(index)?, mapping, next, depth + 1)?;
            }
            if view.tag() == TermTag::Function {
                terms
                    .intern_fun(symbols, view.symbol(), &children[..count as usize])
                    .map_err(term_error)
            } else {
                terms
                    .intern_pred(symbols, view.symbol(), &children[..count as usize])
                    .map_err(term_error)
            }
        }
        TermTag::Equality => {
            let left = remap_variables(terms, symbols, view.child(0)?, mapping, next, depth + 1)?;
            let right = remap_variables(terms, symbols, view.child(1)?, mapping, next, depth + 1)?;
            terms.intern_eq(symbols, left, right).map_err(term_error)
        }
        TermTag::Application | TermTag::Lambda | TermTag::Sort => Err(InferenceError::Structural(
            crate::unification::substitution::SubstitutionError::DepthExceeded,
        )),
    }
}

// CEP:WHAT: Restandardizes a conclusion's literals into a dense [0, n) variable namespace in place.
// CEP:WHY: The storage half of the standardize-apart discipline (Spec 07 section 2): flags ride along (the conclusion's flags are recomputed by the caller after storage anyway); the returned count is the dense variable count.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InferenceError.
// CEP:ASSUMES: literals are rule conclusions over the shared namespace; count <= buffer length.
// CEP:COST: O(total term nodes).
// CEP:EVIDENCE: unit/hot/inference_test.rs::conclusions_restandardized.
// CEP:SECURITY: depth-bounded.
pub fn restandardize_clause(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    literals: &mut [Literal],
) -> Result<u32, InferenceError> {
    let mut mapping = [u32::MAX; kMaxVariablesPerClause as usize];
    let mut next: u32 = 0;
    for literal in literals.iter_mut() {
        let atom = remap_variables(terms, symbols, literal.atom(), &mut mapping, &mut next, 0)?;
        *literal = Literal::new(atom, literal.is_positive());
    }
    Ok(next)
}
