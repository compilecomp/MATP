// CEP:FILE: hot/unification/unify.rs
// CEP:WHAT: Robinson unification with occurs check (Martelli & Montanari 1982 transformation style) and one-directional matching over the flat-array substitution engine, with an explicit compose operation building materialized composition records in the arena.
// CEP:WHY: Design 8.2 and 26 (Phase 2): unification and matching are called millions of times per second by resolution, superposition, factoring, and demodulation, so they must be OPT-0 on the Phase 1 substitution engine (flat-array lookup at 1.96 cycles, trail-disciplined bind, no allocation); the occurs check is mandatory for soundness (x = f(x) must fail, else every subsequent inference is unsound); matching skips the occurs check per Formal Spec 02 section 5 but pays one application pass as a soundness witness because MAPT shares one variable namespace across clauses.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SubstitutionError (shared vocabulary of the unification component, CEP&CC 33.18): DepthExceeded past kMaxUnificationDepth, InvalidPointer for unreadable terms, VariableOutOfRange / TrailFull from the substitution engine; unification and matching FAILURE are Ok(false), never errors. Never panics.
// CEP:ASSUMES: Terms are interned by the caller's TermStore (hash-consing invariant); the substitution is over dense per-clause variable IDs below kMaxVariablesPerClause; pattern and subject of a match may share the variable namespace (the final application witness makes that case sound); the caller drives the bind/undo trail discipline for speculative attempts.
// CEP:COST: unification is O(|s| + |t|) expected with one bind per touched variable; matching is O(|p|) plus one application pass O(|p|) as the soundness witness; both bounded by kMaxUnificationDepth guards; measured 14.40 cycles median for the ground-identical fast path, 101.88 for a one-binding-per-side unification with undo, 42.35 for a failed occurs check, and 118.27 for a successful match with witness, on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0006, artifacts benches/artifacts/unify_ground_identical.json, unify_bind_pair.json, unify_occurs_reject.json, match_witness_success.json.
// CEP:EVIDENCE: unit/hot/unify_test.rs; property/unify_property_test.rs; bench CEP-BENCH-0006; contract/unification_trail_contract_test.rs.
// CEP:SECURITY: all term reads are bounds-checked; recursion and dereference chains are depth-bounded (CEP&CC 22.10); no allocation on the unification path itself.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; variable and child iteration are index-ordered, the hash-consing fast path is pointer equality, and no clocks, randomness, or addresses participate.
// CEP:HPC-PASS-LEGALITY: Formal Spec 02 section 5 fixes the definitions this file implements: a unifier sigma satisfies hat-sigma(s) = hat-sigma(t), an MGU dominates every unifier by right-composition, and a matcher of pattern p onto subject t satisfies hat-sigma(p) = t with dom(sigma) subset of vars(p); the occurs check implements the well-foundedness side condition of the Robinson theorem.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: the match-time application witness doubles the traversal cost of a successful match; a cheaper witness (variable-disjointness precondition with a per-clause namespace map) is deferred pending measurement on Phase 3 inference workloads; ticket CEP-1024.

use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::unification::substitution::{Substitution, SubstitutionError};
use mapt_config::limits::{kMaxUnificationDepth, kMaxVariablesPerClause};

// CEP:WHAT: Composes two substitutions sigma and tau: the result maps x to hat-sigma(hat-tau(x)) on the union of the domains, materialized as an arena record.
// CEP:WHY: Design 5.5 requires explicit composition allocating into the arena, and Formal Spec 02 section 3 fixes the semantics (apply tau first, then sigma); composition is what makes MGU chains from nested inferences shareable through derivation steps.
// CEP:STATUS: complete
// CEP:FAILURE: Propagates SubstitutionError from application (DepthExceeded on cyclic inputs, InvalidPointer, ArenaFull when the record does not fit); a cyclic input substitution is caller misuse and errors loudly rather than looping.
// CEP:ASSUMES: both substitutions are over the same variable namespace and the same term store; identity mappings (x -> x) are dropped from the record per Spec 02 section 1.
// CEP:COST: O(bound variables) with one or two application passes per composed entry; two arena allocations for the record.
// CEP:EVIDENCE: unit/hot/unify_test.rs::{compose_union_of_domains, compose_drops_identity, compose_applies_tau_first}.
// CEP:SECURITY: binding count bounded by kMaxVariablesPerClause; record writes bounds-checked.
pub fn compose(
    sigma: &Substitution<'_>,
    tau: &Substitution<'_>,
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
) -> Result<u32, SubstitutionError> {
    let mut pairs: [(u32, u32); kComposedPairBound as usize] =
        [(0, 0); kComposedPairBound as usize];
    let mut count: usize = 0;
    for variable in 0..kMaxVariablesPerClause {
        let tau_bound = tau.lookup(variable)?;
        let sigma_bound = sigma.lookup(variable)?;
        if tau_bound.is_none() && sigma_bound.is_none() {
            continue;
        }
        // x composed = hat-sigma(hat-tau(x)) for x in dom(tau); hat-sigma(x) otherwise
        // (Spec 02 section 3); the sigma application chases sigma's own bindings.
        let identity = var_term(terms, variable)?;
        let value = match tau_bound {
            Some(binding) => {
                let applied = tau.apply(terms, binding, symbols)?;
                sigma.apply(terms, applied, symbols)?
            }
            None => sigma.apply(terms, identity, symbols)?,
        };
        if value != identity {
            if count >= pairs.len() {
                return Err(SubstitutionError::VariableOutOfRange);
            }
            pairs[count] = (variable, value.as_u32());
            count += 1;
        }
    }
    sigma.write_record(&pairs[..count])
}

// CEP:WHAT: Upper bound on composed binding pairs (one per variable slot).
// CEP:WHY: Named array size instead of reusing kMaxVariablesPerClause inline in the type (CEP&CC 11.3); equals the variable bound by construction.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kMaxVariablesPerClause slots suffice; enforced by static assertion.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/unify_test.rs::compose_union_of_domains.
// CEP:SECURITY: none.
const kComposedPairBound: u32 = kMaxVariablesPerClause;
const _: () = assert!(kComposedPairBound == kMaxVariablesPerClause);

// CEP:WHAT: Unifies two terms: extends the substitution with an MGU of left and right, or returns false with all of this call's bindings undone.
// CEP:WHY: Design 8.2 and Phase 2 build order: the MGU engine behind resolution, superposition, and factoring; the entry point records the trail depth so failure is fully backtrackable (Spec 02 section 4) and success leaves the MGU in place for materialization into derivation steps (Spec 02 section 5d).
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) on clash, occurs-check failure, or arity/symbol mismatch (legitimate unification outcomes); SubstitutionError on depth, bounds, or structural failures; on Ok(false) every binding made by this call is undone.
// CEP:ASSUMES: see file header; the caller observes the entry trail depth is preserved on failure.
// CEP:COST: O(|s| + |t|) expected; one bind per newly touched variable; measured in bench CEP-BENCH-0006.
// CEP:EVIDENCE: unit/hot/unify_test.rs::{unify_ground_identical, unify_one_binding, occurs_check_rejects_cycle, clash_returns_false, failure_unwinds_trail}; property/unify_property_test.rs::{mgu_is_unifier, mgu_is_idempotent}.
// CEP:SECURITY: dereference chains and recursion are bounded by kMaxUnificationDepth.
pub fn unify(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    left: TermPtr,
    right: TermPtr,
) -> Result<bool, SubstitutionError> {
    let entry_depth = substitution.trail_depth();
    match unify_bounded(terms, substitution, left, right, 0) {
        Ok(unified) => {
            if !unified {
                // Failure unwinds this call's bindings (Spec 02 section 4 trail discipline);
                // success keeps the MGU in place for materialization.
                substitution.undo_to(entry_depth);
            }
            Ok(unified)
        }
        Err(error) => {
            substitution.undo_to(entry_depth);
            Err(error)
        }
    }
}

// CEP:WHAT: Matches pattern onto subject: extends the substitution with a matcher, or returns false with this call's bindings undone.
// CEP:WHY: Design 8.2 and Phase 2 build order: matching drives demodulation and subsumption (one-directional, pattern variables only, no occurs check per Spec 02 section 5); the final application witness verifies hat-sigma(pattern) = subject exactly, which keeps matching sound even when pattern and subject share the variable namespace.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) on structural mismatch, on binding conflicts, or when the witness application shows the bindings do not reproduce the subject (including the cycle case, converted from DepthExceeded to a plain failure); SubstitutionError on genuine structural failures; failure undoes this call's bindings.
// CEP:ASSUMES: see file header; the subject is treated as ground with respect to the substitution.
// CEP:COST: O(|p|) matching plus one O(|p|) application witness on success; measured in bench CEP-BENCH-0006.
// CEP:EVIDENCE: unit/hot/unify_test.rs::{match_ground_pattern, match_binds_pattern_variables, match_rejects_subject_variables, match_witness_rejects_namespace_overlap}; property/unify_property_test.rs::matcher_reproduces_subject.
// CEP:SECURITY: witness application is depth-bounded; bindings bounded by the substitution engine.
pub fn match_terms(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    substitution: &Substitution<'_>,
    pattern: TermPtr,
    subject: TermPtr,
) -> Result<bool, SubstitutionError> {
    let entry_depth = substitution.trail_depth();
    let matched = match_bounded(terms, substitution, pattern, subject, 0);
    match matched {
        Ok(false) => {
            substitution.undo_to(entry_depth);
            Ok(false)
        }
        Ok(true) => {
            // Soundness witness (Spec 02 section 5): hat-sigma(pattern) must equal subject.
            // A DepthExceeded here means the bindings form a cycle (a pattern variable was
            // bound into a term containing that variable's chain), which is a match failure.
            let witness = substitution.apply(terms, pattern, symbols);
            match witness {
                Ok(applied) => {
                    if applied == subject {
                        Ok(true)
                    } else {
                        substitution.undo_to(entry_depth);
                        Ok(false)
                    }
                }
                Err(SubstitutionError::DepthExceeded) => {
                    substitution.undo_to(entry_depth);
                    Ok(false)
                }
                Err(error) => {
                    substitution.undo_to(entry_depth);
                    Err(error)
                }
            }
        }
        Err(error) => {
            substitution.undo_to(entry_depth);
            Err(error)
        }
    }
}

// CEP:WHAT: Recursive unification core with an explicit depth guard.
// CEP:WHY: The Robinson case analysis: dereference both sides through current bindings, take the hash-consing fast path on pointer equality, then decompose, bind, or clash; the depth guard turns pathological nesting into a loud error (CEP&CC 22.10 unbounded-recursion ban) exactly like the Phase 1 application engine.
// CEP:STATUS: complete
// CEP:FAILURE: as unify(); Ok(false) is a legitimate unification outcome.
// CEP:ASSUMES: bindings made by ancestors of this frame remain valid on entry.
// CEP:COST: one dereference pair plus one case step per recursion level; O(|s| + |t|) expected total.
// CEP:EVIDENCE: unit/hot/unify_test.rs; property/unify_property_test.rs.
// CEP:SECURITY: depth-bounded recursion; all reads bounds-checked.
fn unify_bounded(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    left: TermPtr,
    right: TermPtr,
    depth: u32,
) -> Result<bool, SubstitutionError> {
    if depth > kMaxUnificationDepth {
        return Err(SubstitutionError::DepthExceeded);
    }
    let left = deref(terms, substitution, left)?;
    let right = deref(terms, substitution, right)?;
    if left == right {
        return Ok(true);
    }
    let left_view = terms.term(left).map_err(map_term_error)?;
    let right_view = terms.term(right).map_err(map_term_error)?;
    match (left_view.tag(), right_view.tag()) {
        (TermTag::Variable, _) => bind_variable(terms, substitution, left_view.symbol(), right),
        (_, TermTag::Variable) => bind_variable(terms, substitution, right_view.symbol(), left),
        (left_tag, right_tag) => {
            if left_tag != right_tag
                || left_view.symbol() != right_view.symbol()
                || left_view.child_count() != right_view.child_count()
            {
                return Ok(false);
            }
            for index in 0..left_view.child_count() {
                let left_child = left_view.child(index).map_err(map_term_error)?;
                let right_child = right_view.child(index).map_err(map_term_error)?;
                if !unify_bounded(terms, substitution, left_child, right_child, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}

// CEP:WHAT: Binds an unbound variable to a term after the occurs check, chasing bindings on both sides.
// CEP:WHY: The bind step of the Robinson algorithm; the occurs check must look through existing bindings (a variable bound to x occurring inside the candidate term is still an occurrence), otherwise cyclic substitutions could be built and every later application would be unsound (Spec 02 section 5 well-foundedness).
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) when the occurs check rejects; propagates bind errors (VariableOutOfRange, TrailFull).
// CEP:ASSUMES: the variable is unbound after dereference (the caller dereferenced both sides).
// CEP:COST: occurs check O(|t|); bind is 3 compares + 2 stores (measured in bench CEP-BENCH-0004).
// CEP:EVIDENCE: unit/hot/unify_test.rs::{occurs_check_rejects_cycle, occurs_check_looks_through_bindings}.
// CEP:SECURITY: occurs traversal is depth-bounded.
fn bind_variable(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    variable: u32,
    target: TermPtr,
) -> Result<bool, SubstitutionError> {
    if occurs(terms, substitution, variable, target, 0)? {
        return Ok(false);
    }
    match substitution.bind(variable, target) {
        Ok(()) => Ok(true),
        Err(SubstitutionError::VariableOutOfRange)
            if substitution.is_bound(variable) == Ok(true) =>
        {
            // Already bound to a different term: after dereference this is unreachable in
            // well-formed use; surfaced as a plain failure instead of an error.
            Ok(false)
        }
        Err(error) => Err(error),
    }
}

// CEP:WHAT: Recursive occurs check: does the variable occur in the term, looking through current bindings?
// CEP:WHY: The well-foundedness guard of the Robinson theorem (Spec 02 section 5): without it, x unifies with f(x) and produces a cyclic substitution whose application never terminates; the check dereferences at every level so chains (x -> y -> f(x)) are caught too.
// CEP:STATUS: complete
// CEP:FAILURE: propagates DepthExceeded past kMaxUnificationDepth and InvalidPointer; returns the occurrence answer.
// CEP:ASSUMES: the variable is a legal dense index.
// CEP:COST: O(|t|) with early exit; one depth-guarded frame per term level.
// CEP:EVIDENCE: unit/hot/unify_test.rs::{occurs_check_rejects_cycle, occurs_check_looks_through_bindings}; property/unify_property_test.rs::occurs_check_matches_naive_scan.
// CEP:SECURITY: depth-bounded recursion.
fn occurs(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    variable: u32,
    term: TermPtr,
    depth: u32,
) -> Result<bool, SubstitutionError> {
    if depth > kMaxUnificationDepth {
        return Err(SubstitutionError::DepthExceeded);
    }
    let term = deref(terms, substitution, term)?;
    let view = terms.term(term).map_err(map_term_error)?;
    match view.tag() {
        TermTag::Variable => Ok(view.symbol() == variable),
        TermTag::Sort => Ok(false),
        _ => {
            for index in 0..view.child_count() {
                let child = view.child(index).map_err(map_term_error)?;
                if occurs(terms, substitution, variable, child, depth + 1)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
    }
}

// CEP:WHAT: Recursive matching core with an explicit depth guard.
// CEP:WHY: One-directional pattern matching: pattern variables bind to subject subterms, subject variables are constants (a pattern non-variable can never match a subject variable), structural decomposition requires identical symbols and arities; no occurs check per Spec 02 section 5, soundness restored by the caller's application witness.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) on any mismatch; propagates structural errors.
// CEP:ASSUMES: the subject is not modified and never dereferenced through the substitution.
// CEP:COST: O(|p|) with one bind per pattern variable.
// CEP:EVIDENCE: unit/hot/unify_test.rs::{match_ground_pattern, match_binds_pattern_variables, match_rejects_subject_variables}.
// CEP:SECURITY: depth-bounded recursion; all reads bounds-checked.
fn match_bounded(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    pattern: TermPtr,
    subject: TermPtr,
    depth: u32,
) -> Result<bool, SubstitutionError> {
    if depth > kMaxUnificationDepth {
        return Err(SubstitutionError::DepthExceeded);
    }
    let pattern = deref(terms, substitution, pattern)?;
    if pattern == subject {
        // Hash-consing fast path: identical terms match under the identity part of sigma.
        return Ok(true);
    }
    let pattern_view = terms.term(pattern).map_err(map_term_error)?;
    let subject_view = terms.term(subject).map_err(map_term_error)?;
    match pattern_view.tag() {
        TermTag::Variable => match substitution.lookup(pattern_view.symbol())? {
            Some(bound) => Ok(bound == subject),
            None => match substitution.bind(pattern_view.symbol(), subject) {
                Ok(()) => Ok(true),
                Err(error) => Err(error),
            },
        },
        TermTag::Sort
        | TermTag::Function
        | TermTag::Predicate
        | TermTag::Equality
        | TermTag::Application
        | TermTag::Lambda => {
            if pattern_view.tag() != subject_view.tag()
                || pattern_view.symbol() != subject_view.symbol()
                || pattern_view.child_count() != subject_view.child_count()
            {
                return Ok(false);
            }
            for index in 0..pattern_view.child_count() {
                let pattern_child = pattern_view.child(index).map_err(map_term_error)?;
                let subject_child = subject_view.child(index).map_err(map_term_error)?;
                if !match_bounded(terms, substitution, pattern_child, subject_child, depth + 1)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}

// CEP:WHAT: Dereferences a term through current bindings: returns the first non-variable term on the binding chain, or the unbound variable itself.
// CEP:WHY: The Robinson dereference step: every case analysis must operate on binding-free representatives, both for the hash-consing fast path and for correct occurs checks; the step counter bounds chains (legitimate chains are shorter than the variable count, cycles are caller misuse and stop at the guard).
// CEP:STATUS: complete
// CEP:FAILURE: Returns DepthExceeded when a chain exceeds kMaxUnificationDepth (cyclic substitution or pathological caller state).
// CEP:ASSUMES: bindings reference interned terms.
// CEP:COST: one lookup per chain link (1.96 cycles median each, bench CEP-BENCH-0004).
// CEP:EVIDENCE: unit/hot/unify_test.rs::{unify_one_binding, occurs_check_looks_through_bindings}.
// CEP:SECURITY: bounded loop; no out-of-range access possible (lookup bounds-checks).
fn deref(
    terms: &TermStore<'_>,
    substitution: &Substitution<'_>,
    term: TermPtr,
) -> Result<TermPtr, SubstitutionError> {
    let mut current = term;
    let mut steps: u32 = 0;
    loop {
        if steps > kMaxUnificationDepth {
            return Err(SubstitutionError::DepthExceeded);
        }
        let view = terms.term(current).map_err(map_term_error)?;
        if view.tag() != TermTag::Variable {
            return Ok(current);
        }
        match substitution.lookup(view.symbol())? {
            Some(next) => {
                current = next;
                steps += 1;
            }
            None => return Ok(current),
        }
    }
}

// CEP:WHAT: Interns the variable term for a dense variable index.
// CEP:WHY: compose needs the canonical variable term to apply substitutions to x itself (Spec 02 section 3); hash-consing makes repeated construction a cheap probe hit.
// CEP:STATUS: complete
// CEP:FAILURE: propagates VariableOutOfRange and store errors.
// CEP:ASSUMES: variable < kMaxVariablesPerClause.
// CEP:COST: one intern probe (37.9 cycles median hit, bench CEP-BENCH-0002).
// CEP:EVIDENCE: unit/hot/unify_test.rs::compose_union_of_domains.
// CEP:SECURITY: index bound enforced by intern_var.
fn var_term(terms: &TermStore<'_>, variable: u32) -> Result<TermPtr, SubstitutionError> {
    terms.intern_var(variable).map_err(map_term_error)
}

// CEP:WHAT: Maps term-store errors onto the substitution error vocabulary.
// CEP:WHY: The unification component shares the substitution error type (CEP&CC 33.18 component-specific vocabulary); a single mapping point keeps the translation auditable, mirroring substitution.rs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/unify_test.rs::invalid_term_refused.
// CEP:SECURITY: none.
fn map_term_error(error: crate::ir::term::TermError) -> SubstitutionError {
    match error {
        crate::ir::term::TermError::ArenaFull | crate::ir::term::TermError::TableFull => {
            SubstitutionError::ArenaFull
        }
        crate::ir::term::TermError::VariableOutOfRange => SubstitutionError::VariableOutOfRange,
        _ => SubstitutionError::InvalidPointer,
    }
}
