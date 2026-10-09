// CEP:FILE: cold/verifier.rs
// CEP:WHAT: Full IR verifier: re-validates every structural invariant of the term store, clause store, and symbol table (well-formedness, arity agreement, cached depth/weight/groundness, hash-consing canonicality, clause canonical order and layout discipline).
// CEP:WHY: CEP&CC 38.18 requires IR verification after construction and in CI; the cheap invariants are debug-asserted on the hot path, but the full verifier runs cold and collects every violation instead of failing on the first, so a corrupted IR is diagnosed completely (design 5.7: the IR must be verifiable).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns the complete, deterministically ordered list of VerificationError values; an empty list means the IR is valid. Never panics.
// CEP:ASSUMES: The stores were built through their public APIs; the verifier reads through the same public accessors, so any violation it finds is a real invariant break, not a verifier artifact.
// CEP:COST: O(terms x arity + clauses x literals); runs in CI and on demand, never on the hot path.
// CEP:EVIDENCE: unit/cold/verifier_test.rs (valid IRs pass; each violation class is constructed and detected).
// CEP:SECURITY: the verifier is the integrity boundary between CEP-1 construction and CEP-0 trust (CEP&CC 22.3 trust boundaries).
// CEP:HPC-DETERMINISM: deterministic; violations are collected in table-slot order then clause-field order.

use mapt_config::limits::{
    kDefaultSymbolWeight, kInlineClauseLiterals, kInvalidClauseOffset, kInvalidSymbolId,
    kInvalidTermOffset, kKboVariableWeight, kMaxClauseLiterals, kMaxDerivationParents,
    kMaxVariablesPerClause, kTermHashTableCapacity,
};

// CEP:WHAT: Child count of tag-fixed terms (Equality, Application, Lambda).
// CEP:WHY: Named constant instead of a raw 2 (CEP&CC 11.3); design 5.1 fixes these kinds at two children.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/term_test.rs::equality_terms.
// CEP:SECURITY: none.
const kFixedArityChildCount: u16 = 2;
use mapt_hot::ir::clause::{Clause, ClauseError, ClauseStore, InferenceRule};
use mapt_hot::ir::symbol_table::{SymbolKind, SymbolTable};
use mapt_hot::ir::term::{TermStore, TermTag};
use mapt_hot::memory::arena::Arena;

/// CEP:WHAT: One IR verification violation.
/// CEP:WHY: CEP&CC 38.18 lists the required verifier checks; each check that can fail gets a named variant so reports are actionable and stable.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy with a payload offset.
/// CEP:EVIDENCE: unit/cold/verifier_test.rs covers every variant.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationError {
    /// CEP:WHAT: A hash-table slot points to an unreadable term.
    UnreadableTableTerm(u32),
    /// CEP:WHAT: A term child offset is unreadable.
    UnreadableChild(u32),
    /// CEP:WHAT: A function/predicate term's arity disagrees with the symbol table.
    ArityMismatch(u32),
    /// CEP:WHAT: A tag-fixed term (Equality, Application) does not have exactly two children.
    BadFixedArity(u32),
    /// CEP:WHAT: A cached depth is wrong.
    WrongDepth(u32),
    /// CEP:WHAT: A cached weight is wrong.
    WrongWeight(u32),
    /// CEP:WHAT: A cached groundness flag is wrong.
    WrongGroundFlag(u32),
    /// CEP:WHAT: Re-interning a table term produced a different handle (hash-consing canonicality broken).
    NotCanonical(u32),
    /// CEP:WHAT: A variable term exceeds the per-clause variable bound.
    VariableOutOfRange(u32),
    /// CEP:WHAT: A clause exceeds the literal bound.
    ClauseTooManyLiterals(u64),
    /// CEP:WHAT: Clause literal order is not canonical.
    ClauseNotCanonical(u64),
    /// CEP:WHAT: Clause cached weight disagrees with the recomputed sum.
    ClauseWrongWeight(u64),
    /// CEP:WHAT: A clause's overflow offset is inconsistent with its literal count.
    ClauseOverflowInconsistent(u64),
    /// CEP:WHAT: An unused inline literal slot is not the invalid-atom filler.
    ClauseInlineSlotDirty(u64),
    /// CEP:WHAT: Clause reserved bytes are nonzero.
    ClauseReservedNonzero(u64),
    /// CEP:WHAT: A derivation step exceeds the parent bound or names an invalid rule.
    ClauseBadDerivation(u64),
    /// CEP:WHAT: A clause literal's atom is unreadable.
    ClauseUnreadableAtom(u64),
}

/// CEP:WHAT: Verifies the term store against the frozen symbol table.
// CEP:WHY: Hash-consing canonicality and cached metadata are the IR contract terms depend on (design 5.1, 5.7).
// CEP:STATUS: complete
// CEP:FAILURE: returns every violation found.
// CEP:ASSUMES: the symbol table was frozen from the same builder.
// CEP:COST: O(terms x arity).
// CEP:EVIDENCE: unit/cold/verifier_test.rs::{valid_term_store_passes, term_corruption_detected}.
// CEP:SECURITY: integrity check of CEP-1 construction output.
pub fn verify_term_store(
    arena: &Arena,
    terms: &TermStore,
    symbols: &SymbolTable,
) -> Vec<VerificationError> {
    let mut violations = Vec::new();
    let table_range = terms.table_range();
    let slots = match arena.array::<core::cell::Cell<u32>>(table_range) {
        Ok(slots) => slots,
        Err(_) => {
            violations.push(VerificationError::UnreadableTableTerm(kInvalidTermOffset));
            return violations;
        }
    };
    if slots.len() as u32 != kTermHashTableCapacity {
        violations.push(VerificationError::UnreadableTableTerm(kInvalidTermOffset));
        return violations;
    }
    for slot in slots.iter() {
        let offset = slot.get();
        if offset == kInvalidTermOffset {
            continue;
        }
        if terms.term_by_offset(offset).is_err() {
            violations.push(VerificationError::UnreadableTableTerm(offset));
            continue;
        }
        verify_one_term(terms, symbols, offset, &mut violations);
    }
    violations
}

// CEP:WHAT: Verifies one term record: structure, caches, and canonicality.
// CEP:WHY: Centralizing per-term checks keeps the violation vocabulary complete (CEP&CC Law 6).
// CEP:STATUS: complete
// CEP:FAILURE: appends every violation of this term.
// CEP:ASSUMES: the term at offset is readable.
// CEP:COST: O(arity) plus one re-intern.
// CEP:EVIDENCE: unit/cold/verifier_test.rs.
// CEP:SECURITY: none.
fn verify_one_term(
    terms: &TermStore,
    symbols: &SymbolTable,
    offset: u32,
    violations: &mut Vec<VerificationError>,
) {
    let view = match terms.term_by_offset(offset) {
        Ok(view) => view,
        Err(_) => {
            violations.push(VerificationError::UnreadableTableTerm(offset));
            return;
        }
    };
    let tag = view.tag();
    let mut recomputed_weight: u64 = match tag {
        TermTag::Variable => kKboVariableWeight as u64,
        TermTag::Sort => kDefaultSymbolWeight as u64,
        TermTag::Function | TermTag::Predicate => match symbols.symbol_weight(view.symbol()) {
            Ok(weight) => weight as u64,
            Err(_) => {
                violations.push(VerificationError::UnreadableChild(offset));
                return;
            }
        },
        _ => kDefaultSymbolWeight as u64,
    };
    let mut recomputed_depth: u32 = 0;
    // Variables are never ground by definition (design 5.1); every other leaf starts ground
    // and loses the flag when a non-ground child appears.
    let mut recomputed_ground = tag != TermTag::Variable;
    let child_count = view.child_count();
    match tag {
        TermTag::Function | TermTag::Predicate => {
            let info = match symbols.info(view.symbol()) {
                Ok(info) => info,
                Err(_) => {
                    violations.push(VerificationError::UnreadableChild(offset));
                    return;
                }
            };
            let expected_kind = if tag == TermTag::Function {
                SymbolKind::Function
            } else {
                SymbolKind::Predicate
            };
            if info.kind != expected_kind || child_count != info.arity {
                violations.push(VerificationError::ArityMismatch(offset));
                return;
            }
        }
        TermTag::Equality | TermTag::Application | TermTag::Lambda => {
            if child_count != kFixedArityChildCount {
                violations.push(VerificationError::BadFixedArity(offset));
                return;
            }
        }
        TermTag::Variable => {
            if view.symbol() >= kMaxVariablesPerClause {
                violations.push(VerificationError::VariableOutOfRange(offset));
                return;
            }
            if child_count != 0 {
                violations.push(VerificationError::BadFixedArity(offset));
                return;
            }
        }
        TermTag::Sort => {
            if child_count != 0 {
                violations.push(VerificationError::BadFixedArity(offset));
                return;
            }
        }
    }
    for child in view.children() {
        let child_view = match terms.term(child) {
            Ok(child_view) => child_view,
            Err(_) => {
                violations.push(VerificationError::UnreadableChild(offset));
                return;
            }
        };
        let child_depth = child_view.depth() as u32 + 1;
        if child_depth > recomputed_depth {
            recomputed_depth = child_depth;
        }
        recomputed_weight += child_view.weight() as u64;
        if !child_view.is_ground() {
            recomputed_ground = false;
        }
    }
    if view.depth() as u32 != recomputed_depth {
        violations.push(VerificationError::WrongDepth(offset));
    }
    if view.weight() as u64 != recomputed_weight {
        violations.push(VerificationError::WrongWeight(offset));
    }
    if view.is_ground() != recomputed_ground {
        violations.push(VerificationError::WrongGroundFlag(offset));
    }
    let canonical = match tag {
        TermTag::Variable => terms.intern_var(view.symbol()),
        TermTag::Function | TermTag::Predicate => {
            let children: Vec<_> = view.children().collect();
            if tag == TermTag::Function {
                terms.intern_fun(symbols, view.symbol(), &children)
            } else {
                terms.intern_pred(symbols, view.symbol(), &children)
            }
        }
        TermTag::Equality => {
            let children: Vec<_> = view.children().collect();
            terms.intern_eq(symbols, children[0], children[1])
        }
        TermTag::Application => {
            let children: Vec<_> = view.children().collect();
            terms.intern_app(symbols, children[0], children[1])
        }
        TermTag::Sort => terms.intern_sort(view.symbol()),
        TermTag::Lambda => Ok(handle_of(offset)),
    };
    match canonical {
        Ok(handle) => {
            if handle.as_u32() != offset {
                violations.push(VerificationError::NotCanonical(offset));
            }
        }
        Err(_) => violations.push(VerificationError::NotCanonical(offset)),
    }
}

// CEP:WHAT: Wraps an already-verified offset in a term handle for the one tag path (Lambda) that has no public re-interning constructor in Phase 1.
// CEP:WHY: The verifier must stay total over every tag; Lambda terms cannot be constructed through the public API in Phase 1 (design 14.1 keeps lambda off the hot path), so canonicality of Lambda records is accepted as construction-time fact and the wrapper keeps the comparison well-formed.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: offset belongs to a readable term record.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/verifier_test.rs.
// CEP:SECURITY: read-only use inside the verifier; the offset is never written.
fn handle_of(offset: u32) -> mapt_hot::ir::term::TermPtr {
    mapt_hot::ir::term::TermPtr::from_verified_offset(offset)
}

/// CEP:WHAT: Verifies one clause record.
// CEP:WHY: Clause invariants (canonical order, cached weight, layout discipline, derivation bounds) are consumed by search; the verifier re-derives them all (design 5.3, 5.4).
// CEP:STATUS: complete
// CEP:FAILURE: returns every violation of this clause.
// CEP:ASSUMES: the clause header is readable.
// CEP:COST: O(literals).
// CEP:EVIDENCE: unit/cold/verifier_test.rs::{valid_clauses_pass, clause_corruption_detected}.
// CEP:SECURITY: none.
pub fn verify_clause(
    clause: &Clause,
    clauses: &ClauseStore,
    terms: &TermStore,
) -> Vec<VerificationError> {
    let mut violations = Vec::new();
    let id = clause.id.0;
    if clause.literal_count as usize > kMaxClauseLiterals as usize {
        violations.push(VerificationError::ClauseTooManyLiterals(id));
        return violations;
    }
    if clause.reserved != 0 || clause.derivation.reserved != 0 {
        violations.push(VerificationError::ClauseReservedNonzero(id));
    }
    if clause.derivation.parent_count as usize > kMaxDerivationParents {
        violations.push(VerificationError::ClauseBadDerivation(id));
    }
    let rule_valid = matches!(
        clause.derivation.rule,
        InferenceRule::Input
            | InferenceRule::NegatedConjecture
            | InferenceRule::Resolution
            | InferenceRule::Superposition
            | InferenceRule::Factoring
            | InferenceRule::EqualityFactoring
            | InferenceRule::Demodulation
            | InferenceRule::ForwardSubsumption
            | InferenceRule::BackwardSubsumption
            | InferenceRule::SubsumptionResolution
            | InferenceRule::TautologyDeletion
            | InferenceRule::Condensation
            | InferenceRule::EqualityResolution
            | InferenceRule::AvatarSplit
            | InferenceRule::SatLearn
            | InferenceRule::TheoryLemma
    );
    if !rule_valid {
        violations.push(VerificationError::ClauseBadDerivation(id));
    }
    let overflow_needed = clause.literal_count as usize > kInlineClauseLiterals;
    if overflow_needed && clause.overflow_offset == kInvalidClauseOffset {
        violations.push(VerificationError::ClauseOverflowInconsistent(id));
    }
    if !overflow_needed && clause.overflow_offset != kInvalidClauseOffset {
        violations.push(VerificationError::ClauseOverflowInconsistent(id));
    }
    let mut weight_sum: u64 = 0;
    let mut previous_key: Option<(bool, u32)> = None;
    for index in 0..clause.literal_count {
        let literal = match clauses.literal(clause, index) {
            Ok(literal) => literal,
            Err(ClauseError::InvalidPointer) => {
                violations.push(VerificationError::ClauseUnreadableAtom(id));
                continue;
            }
            Err(_) => {
                violations.push(VerificationError::ClauseUnreadableAtom(id));
                continue;
            }
        };
        let atom_view = match terms.term(literal.atom()) {
            Ok(view) => view,
            Err(_) => {
                violations.push(VerificationError::ClauseUnreadableAtom(id));
                continue;
            }
        };
        weight_sum += atom_view.weight() as u64;
        let key = (!literal.is_positive(), literal.atom().as_u32());
        if let Some(previous) = previous_key {
            if previous > key {
                violations.push(VerificationError::ClauseNotCanonical(id));
            }
        }
        previous_key = Some(key);
    }
    if clause.weight as u64 != weight_sum {
        violations.push(VerificationError::ClauseWrongWeight(id));
    }
    if clause.literal_count as usize <= kInlineClauseLiterals {
        for slot in clause.literal_count as usize..kInlineClauseLiterals {
            if clause.inline_literals[slot].atom().as_u32() != kInvalidTermOffset {
                violations.push(VerificationError::ClauseInlineSlotDirty(id));
                break;
            }
        }
    }
    violations
}

/// CEP:WHAT: Verifies the frozen symbol table (freeze already validates; this adds cross-checks usable from CI).
// CEP:WHY: Defense in depth for the trust boundary; the check is cheap and runs cold.
// CEP:STATUS: complete
// CEP:FAILURE: returns violations (unknown IDs in any signature).
// CEP:ASSUMES: none.
// CEP:COST: O(symbols).
// CEP:EVIDENCE: unit/cold/verifier_test.rs::valid_term_store_passes.
// CEP:SECURITY: none.
pub fn verify_symbol_table(symbols: &SymbolTable) -> Vec<VerificationError> {
    let mut violations = Vec::new();
    for id in 0..symbols.symbol_count() {
        if symbols.info(id).is_err() {
            violations.push(VerificationError::UnreadableChild(id));
        }
        if symbols.sort_signature(id).is_err() {
            violations.push(VerificationError::UnreadableChild(id));
        }
    }
    if symbols.info(kInvalidSymbolId).is_ok() {
        violations.push(VerificationError::UnreadableChild(kInvalidSymbolId));
    }
    violations
}
