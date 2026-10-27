// CEP:FILE: cold/symbol_table_builder.rs
// CEP:WHAT: Symbol table builder: CEP-1 construction of the frozen symbol table (dense IDs, names, arities, weights, sort signatures) with validation, finalized by writing entries and a sort pool into the arena for hot-side freeze.
// CEP:WHY: Design 5.6: the table is built during parsing and frozen before search; all name strings live here (cold storage) while the hot table holds only fixed-layout metadata, so the hot path never touches strings, allocation, or hashing on names.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns BuilderError::TooManySymbols past the bound, NameTooLong past the name bound, ArityExceeded past the arity bound, DuplicateName on redeclaration with a different signature, InvalidSort when a signature references an undeclared sort, and ArenaFull when finalization does not fit; never panics.
// CEP:ASSUMES: Symbol IDs are assigned in first-declaration order (deterministic for deterministic input); sort IDs are the symbol IDs of kind Sort declarations; the same name redeclared with an identical signature returns the existing ID.
// CEP:COST: declaration is O(1) expected (hash lookup by name); finalization is O(symbols + signature entries).
// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs; unit/hot/symbol_table_test.rs (freeze validation); security/symbol_bounds_test.rs.
// CEP:SECURITY: name length, symbol count, and arity are bounded (denial-of-service mitigation, CEP&CC 22.10); redeclaration mismatch is refused instead of silently merged.
// CEP:HPC-DETERMINISM: deterministic; IDs follow first-declaration order and finalization writes in ID order.

use mapt_config::limits::{
    kAvatarMaxAssertionSymbols, kDefaultSymbolWeight, kInvalidSymbolId, kMaxSymbolArity,
    kMaxSymbolCount,
};
use mapt_config::security_policy::{kMaxInputSymbolCount, kMaxSymbolNameBytes};
use mapt_hot::ir::symbol_table::{
    kSymbolFlagBuiltin, kSymbolFlagTheory, SortId, SymbolInfo, SymbolKind, SymbolTable,
};
use mapt_hot::memory::arena::Arena;
use std::collections::HashMap;

/// CEP:WHAT: Error cases of the builder.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the builder never panics.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs covers every variant.
/// CEP:SECURITY: count, name, and arity bounds are denial-of-service guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuilderError {
    /// CEP:WHAT: The symbol count would exceed kMaxInputSymbolCount (input-side bound).
    TooManySymbols,
    /// CEP:WHAT: A name exceeds kMaxSymbolNameBytes bytes.
    NameTooLong,
    /// CEP:WHAT: An arity exceeds kMaxSymbolArity.
    ArityExceeded,
    /// CEP:WHAT: The name is already declared with a different signature.
    DuplicateName,
    /// CEP:WHAT: A sort signature references an undeclared sort.
    InvalidSort,
    /// CEP:WHAT: Finalization did not fit the arena.
    ArenaFull,
    /// CEP:WHAT: A weight of zero was supplied (KBO requires at least 1).
    InvalidWeight,
    /// CEP:WHAT: The assertion-symbol reservation was refused: it exceeds kAvatarMaxAssertionSymbols, or the reservation was already made (one-shot), or a reserved name collides with an existing declaration.
    /// CEP:WHY: Spec 18 section 3: the learning assertion space is bounded and one-shot; a second reservation or a flood attempt is a configuration error, reported loudly.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS the failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum copy.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded.
    /// CEP:SECURITY: symbol-table flood guard.
    AssertionBudget,
}

/// CEP:WHAT: One declaration draft before finalization.
/// CEP:WHY: Keeping drafts in a Vec preserves first-declaration order (determinism) while signature vectors wait for the arena write.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: transient build-time data.
/// CEP:COST: one struct plus a signature Vec per symbol.
/// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs.
/// CEP:SECURITY: validated at declaration time.
struct SymbolDraft {
    /// CEP:WHAT: Kind of the symbol.
    /// CEP:WHY: Drives hot-side legality checks.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    kind: SymbolKind,
    /// CEP:WHAT: Arity.
    /// CEP:WHY: Term construction bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxSymbolArity.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: bounded.
    arity: u16,
    /// CEP:WHAT: Flag bits.
    /// CEP:WHY: Built-in and theory markers.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    flags: u16,
    /// CEP:WHAT: Clause-weight contribution.
    /// CEP:WHY: Design 15.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    weight: u32,
    /// CEP:WHAT: Argument sorts followed by the return sort.
    /// CEP:WHY: Design 5.6 sort signature.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length = arity + 1.
    /// CEP:COST: 4 bytes per entry.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: sort IDs validated.
    signature: Vec<SortId>,
}

/// CEP:WHAT: The CEP-1 symbol table builder.
/// CEP:WHY: See file header.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: see BuilderError.
/// CEP:ASSUMES: one builder per problem.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs.
/// CEP:SECURITY: all bounds enforced at declaration time.
pub struct SymbolTableBuilder {
    /// CEP:WHAT: The one-shot assertion-symbol reservation base (Spec 18 section 3).
    /// CEP:WHY: reserve_assertion_symbols records the base id of the mapt_assertion_<i> block; a second reservation is refused (AssertionBudget) so the dense base+n mapping stays exact.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: None until the first reservation.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded.
    /// CEP:SECURITY: none.
    assertion_base: Option<u32>,
    /// CEP:WHAT: Draft entries in first-declaration order.
    /// CEP:WHY: Deterministic ID assignment.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one entry per symbol.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    drafts: Vec<SymbolDraft>,
    /// CEP:WHAT: Name list parallel to IDs.
    /// CEP:WHY: Cold-side name storage (design 5.6: names live in cold storage).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: parallel to drafts.
    /// CEP:COST: one String per symbol.
    /// CEP:EVIDENCE: unit/cold/debug_printer_test.rs.
    /// CEP:SECURITY: names never reach the hot path.
    names: Vec<String>,
    /// CEP:WHAT: Name-to-ID index.
    /// CEP:WHY: O(1) expected duplicate detection and lookup; used for lookups only, so iteration order never influences output.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one entry per symbol.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    index: HashMap<String, u32>,
    /// CEP:WHAT: Sort names to sort IDs.
    /// CEP:WHY: Signature validation needs to know which IDs are declared sorts.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one entry per sort.
    /// CEP:EVIDENCE: builder tests.
    /// CEP:SECURITY: none.
    sorts: HashMap<String, u32>,
    /// CEP:WHAT: The reserved Boolean sort ID ("$o"), declared lazily on the first predicate declaration.
    /// CEP:WHY: Predicates return Booleans by construction; declaring the sort lazily keeps the builder total even for purely-sortal inputs while guaranteeing the Boolean sort exists whenever a predicate does.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: set at most once.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    boolean_sort: Option<u32>,
}

impl SymbolTableBuilder {
    // CEP:WHAT: Creates an empty builder.
    // CEP:WHY: Explicit construction point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: builder tests.
    // CEP:SECURITY: none.
    pub fn new() -> SymbolTableBuilder {
        SymbolTableBuilder {
            drafts: Vec::new(),
            names: Vec::new(),
            index: HashMap::new(),
            sorts: HashMap::new(),
            boolean_sort: None,
            assertion_base: None,
        }
    }

    // CEP:WHAT: Declares a sort and returns its ID.
    // CEP:WHY: TFF/THF support requires a sort universe before function signatures can reference sorts (design 5.6); sorts are symbols of kind Sort whose signature is themselves.
    // CEP:STATUS: complete
    // CEP:FAILURE: see declare_symbol.
    // CEP:ASSUMES: sort names are unique.
    // CEP:COST: O(1) expected.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_sort.
    // CEP:SECURITY: name bounds enforced.
    pub fn declare_sort(&mut self, name: &str) -> Result<u32, BuilderError> {
        let id = self.declare_symbol(name, SymbolKind::Sort, 0, kDefaultSymbolWeight, &[], None)?;
        self.sorts.insert(name.to_string(), id);
        Ok(id)
    }

    // CEP:WHAT: Declares a function symbol and returns its ID.
    // CEP:WHY: The main declaration path for first-order terms.
    // CEP:STATUS: complete
    // CEP:FAILURE: see declare_symbol.
    // CEP:ASSUMES: arg_sorts length equals arity.
    // CEP:COST: O(1) expected.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_function.
    // CEP:SECURITY: bounds enforced.
    pub fn declare_function(
        &mut self,
        name: &str,
        arity: u16,
        weight: u32,
        arg_sorts: &[SortId],
        return_sort: SortId,
    ) -> Result<u32, BuilderError> {
        self.declare_symbol(
            name,
            SymbolKind::Function,
            arity,
            weight,
            arg_sorts,
            Some(return_sort),
        )
    }

    // CEP:WHAT: Declares a predicate symbol and returns its ID.
    // CEP:WHY: Literal atoms are built on predicate symbols (design 5.2).
    // CEP:STATUS: complete
    // CEP:FAILURE: see declare_symbol.
    // CEP:ASSUMES: arg_sorts length equals arity; the return sort is the Boolean sort by construction.
    // CEP:COST: O(1) expected.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    // CEP:SECURITY: bounds enforced.
    pub fn declare_predicate(
        &mut self,
        name: &str,
        arity: u16,
        weight: u32,
        arg_sorts: &[SortId],
    ) -> Result<u32, BuilderError> {
        if self.boolean_sort.is_none() {
            let boolean = self.declare_symbol(
                Self::kBooleanSortName,
                SymbolKind::Sort,
                0,
                kDefaultSymbolWeight,
                &[],
                None,
            )?;
            self.sorts
                .insert(Self::kBooleanSortName.to_string(), boolean);
            self.boolean_sort = Some(boolean);
        }
        let boolean_sort = SortId(self.boolean_sort.unwrap_or(kInvalidSymbolId));
        self.declare_symbol(
            name,
            SymbolKind::Predicate,
            arity,
            weight,
            arg_sorts,
            Some(boolean_sort),
        )
    }

    /// CEP:WHAT: The reserved name of the Boolean sort.
    /// CEP:WHY: A named constant prevents accidental collisions with user symbols (CEP&CC 11.3); the TPTP convention names the Boolean sort $o.
    /// CEP:CLASS: CEP-1
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: user symbols are refused this exact name to avoid ambiguity (duplicate-signature rules apply).
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    pub const kBooleanSortName: &'static str = "$o";

    // CEP:WHAT: Returns the reserved Boolean sort ID if it exists.
    // CEP:WHY: Diagnostics and tests need the ID; declaration happens lazily with the first predicate.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; None when no predicate has been declared yet.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    // CEP:SECURITY: none.
    pub fn boolean_sort_id(&self) -> Option<SortId> {
        self.boolean_sort.map(SortId)
    }

    // CEP:WHAT: Shared declaration core: validates bounds and signature, deduplicates by name.
    // CEP:WHY: One validation point for every declaration path (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: see BuilderError; a redeclaration with an identical signature returns the existing ID (idempotence), any mismatch is DuplicateName.
    // CEP:ASSUMES: arg_sorts length equals arity for Function/Predicate.
    // CEP:COST: O(1) expected.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::{duplicate_detection, bound_enforcement}.
    // CEP:SECURITY: count, name-length, arity, and weight bounds enforced here.
    fn declare_symbol(
        &mut self,
        name: &str,
        kind: SymbolKind,
        arity: u16,
        weight: u32,
        arg_sorts: &[SortId],
        return_sort: Option<SortId>,
    ) -> Result<u32, BuilderError> {
        if name.len() > kMaxSymbolNameBytes as usize {
            return Err(BuilderError::NameTooLong);
        }
        if arity > kMaxSymbolArity {
            return Err(BuilderError::ArityExceeded);
        }
        if weight == 0 {
            return Err(BuilderError::InvalidWeight);
        }
        if self.drafts.len() >= kMaxInputSymbolCount.min(kMaxSymbolCount) as usize {
            return Err(BuilderError::TooManySymbols);
        }
        if let Some(existing) = self.index.get(name) {
            let draft = &self.drafts[*existing as usize];
            // Sorts carry no caller-provided signature (their signature is auto-populated with
            // themselves), so their dedup comparison covers kind and weight only.
            let signature_matches = if kind == SymbolKind::Sort {
                draft.kind == SymbolKind::Sort && draft.weight == weight
            } else {
                draft.kind == kind
                    && draft.arity == arity
                    && draft.weight == weight
                    && draft.signature.len() == arg_sorts.len() + usize::from(return_sort.is_some())
                    && arg_sorts
                        .iter()
                        .zip(draft.signature.iter())
                        .all(|(a, b)| a == b)
                    && match return_sort {
                        Some(sort) => draft.signature.last() == Some(&sort),
                        None => true,
                    }
            };
            if signature_matches {
                return Ok(*existing);
            }
            return Err(BuilderError::DuplicateName);
        }
        let mut signature: Vec<SortId> = Vec::with_capacity(arg_sorts.len() + 1);
        for sort in arg_sorts.iter() {
            if sort.0 as usize >= self.drafts.len() {
                return Err(BuilderError::InvalidSort);
            }
            if self.drafts[sort.0 as usize].kind != SymbolKind::Sort {
                return Err(BuilderError::InvalidSort);
            }
            signature.push(*sort);
        }
        if let Some(sort) = return_sort {
            if sort.0 as usize >= self.drafts.len() {
                return Err(BuilderError::InvalidSort);
            }
            if self.drafts[sort.0 as usize].kind != SymbolKind::Sort {
                return Err(BuilderError::InvalidSort);
            }
            signature.push(sort);
        }
        let id = self.drafts.len() as u32;
        if kind == SymbolKind::Sort && signature.is_empty() {
            signature.push(SortId(id));
        }
        self.drafts.push(SymbolDraft {
            kind,
            arity,
            flags: 0,
            weight,
            signature,
        });
        self.names.push(name.to_string());
        self.index.insert(name.to_string(), id);
        Ok(id)
    }

    // CEP:WHAT: Marks a symbol as built-in.
    // CEP:WHY: Design 5.6 flags; the equality pseudo-symbol discipline and future theory symbols use the marker.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; unknown IDs are ignored (the hot table validation owns that domain).
    // CEP:ASSUMES: called before finalize.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::flags.
    // CEP:SECURITY: none.
    pub fn mark_builtin(&mut self, symbol_id: u32) {
        if let Some(draft) = self.drafts.get_mut(symbol_id as usize) {
            draft.flags |= kSymbolFlagBuiltin;
        }
    }

    // CEP:WHAT: Marks a symbol as theory-laden.
    // CEP:WHY: Design 5.6 flags; Phase 5 theory reasoning.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; unknown IDs are ignored.
    // CEP:ASSUMES: called before finalize.
    // CEP:COST: constant.
    // CEP:EVIDENCE: reserved for Phase 5.
    // CEP:SECURITY: none.
    pub fn mark_theory(&mut self, symbol_id: u32) {
        if let Some(draft) = self.drafts.get_mut(symbol_id as usize) {
            draft.flags |= kSymbolFlagTheory;
        }
    }

    // CEP:WHAT: Returns the symbol count declared so far.
    // CEP:WHY: Diagnostics and bound checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: builder tests.
    // CEP:SECURITY: none.
    pub fn symbol_count(&self) -> u32 {
        self.drafts.len() as u32
    }

    // CEP:WHAT: Reserves the learning assertion space: declares count 0-ary predicates named mapt_assertion_<i> (deterministic names, i ascending from 0) and returns the base id.
    // CEP:WHY: Spec 18 section 3: the FOL copies of SAT-side clauses speak only through 0-ary assertion predicates; the reservation is ONE-SHOT (a second call returns AssertionBudget), bounded by kAvatarMaxAssertionSymbols, and dense (the symbols are declared back-to-back, so assertion atom for SAT slot i is base + i); a reserved-name collision with an existing declaration is refused so the density assumption cannot silently break.
    // CEP:STATUS: complete
    // CEP:FAILURE: BuilderError::AssertionBudget when count exceeds kAvatarMaxAssertionSymbols, when the reservation was already made, or when any mapt_assertion_<i> name already exists with a 0-ary predicate signature (declare_symbol would return the existing id and break the density); the TooManySymbols/DuplicateName errors of the underlying declaration propagate.
    // CEP:ASSUMES: called after the problem symbols are declared and before freeze; count >= 1.
    // CEP:COST: O(count) declarations plus one density check.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded; unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
    // CEP:SECURITY: the flood bound is the named constant.
    pub fn reserve_assertion_symbols(&mut self, count: u32) -> Result<u32, BuilderError> {
        if count == 0 || count > kAvatarMaxAssertionSymbols || self.assertion_base.is_some() {
            return Err(BuilderError::AssertionBudget);
        }
        // Collision refusal: any existing declaration named mapt_assertion_<i>
        // (with any signature) would make declare_symbol idempotent for that
        // name and break the dense base + slot mapping.
        for slot in 0..count {
            let name = assertion_symbol_name(slot);
            if self.index.contains_key(&name) {
                return Err(BuilderError::AssertionBudget);
            }
        }
        let base = self.symbol_count();
        for slot in 0..count {
            let name = assertion_symbol_name(slot);
            self.declare_predicate(&name, 0, kDefaultSymbolWeight, &[])?;
        }
        // Density check: the count declarations must all be fresh (the symbol
        // count advanced by exactly count); the collision pre-check makes this
        // structurally guaranteed, and the check keeps the invariant honest.
        if self.symbol_count() != base + count {
            return Err(BuilderError::AssertionBudget);
        }
        self.assertion_base = Some(base);
        Ok(base)
    }

    // CEP:WHAT: Returns the one-shot assertion reservation base, if made.
    // CEP:WHY: Diagnostics and tests pin the reserved block.
    // CEP:STATUS: complete
    // CEP:FAILURE: None before the first reservation.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded.
    // CEP:SECURITY: none.
    pub fn assertion_symbol_base(&self) -> Option<u32> {
        self.assertion_base
    }

    // CEP:WHAT: Returns the name of a symbol.
    // CEP:WHY: Cold diagnostics and the debug printer.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns None for unknown IDs.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/debug_printer_test.rs.
    // CEP:SECURITY: none.
    pub fn name_of(&self, symbol_id: u32) -> Option<&str> {
        self.names.get(symbol_id as usize).map(|name| name.as_str())
    }

    // CEP:WHAT: Writes entries and the sort pool into the arena and freezes the hot-side table.
    // CEP:WHY: Design 5.6: freeze is the trust boundary between CEP-1 construction and CEP-0 reads; writing in ID order keeps the layout deterministic.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull when the arrays do not fit; freeze itself revalidates every entry.
    // CEP:ASSUMES: the arena is the one the hot stores use.
    // CEP:COST: O(symbols + signature entries).
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate; unit/hot/symbol_table_test.rs.
    // CEP:SECURITY: freeze validates the entire written table before it becomes readable.
    pub fn finalize<'a>(&self, arena: &'a Arena) -> Result<SymbolTable<'a>, BuilderError> {
        let mut pool: Vec<SortId> = Vec::new();
        let mut entries: Vec<SymbolInfo> = Vec::with_capacity(self.drafts.len());
        for draft in self.drafts.iter() {
            let signature_offset = pool.len() as u32;
            pool.extend_from_slice(&draft.signature);
            entries.push(SymbolInfo {
                kind: draft.kind,
                arity: draft.arity,
                flags: draft.flags,
                weight: draft.weight,
                sort_signature: signature_offset,
                sort_signature_len: draft.signature.len() as u16,
                reserved: 0,
            });
        }
        let entries_range = arena
            .alloc_array::<SymbolInfo>(entries.len() as u32)
            .map_err(|_| BuilderError::ArenaFull)?;
        let entries_slot = arena
            .array_mut::<SymbolInfo>(entries_range)
            .map_err(|_| BuilderError::ArenaFull)?;
        entries_slot.copy_from_slice(&entries);
        let pool_range = arena
            .alloc_array::<SortId>(pool.len() as u32)
            .map_err(|_| BuilderError::ArenaFull)?;
        if !pool.is_empty() {
            let pool_slot = arena
                .array_mut::<SortId>(pool_range)
                .map_err(|_| BuilderError::ArenaFull)?;
            pool_slot.copy_from_slice(&pool);
        }
        SymbolTable::freeze(arena, entries_range, pool_range).map_err(|_| BuilderError::ArenaFull)
    }
}

// CEP:WHAT: Default constructor delegating to new.
// CEP:WHY: Clippy requires Default for types with a no-argument constructor; identical behavior.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_sort.
// CEP:SECURITY: none.
impl Default for SymbolTableBuilder {
    fn default() -> Self {
        Self::new()
    }
}

// CEP:WHAT: The deterministic reserved name of the assertion symbol for SAT slot i.
// CEP:WHY: Spec 18 section 3: the FOL copy of a SAT clause over component slots names its atoms mapt_assertion_<slot>; one name builder keeps the prefix consistent between the reservation, the controller's atom construction, and the kernel's shape documentation.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the prefix is MAPT-reserved (problem inputs must not declare it).
// CEP:COST: allocation-free formatting into the caller's string.
// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded.
// CEP:SECURITY: none.
pub fn assertion_symbol_name(slot: u32) -> std::string::String {
    std::format!("mapt_assertion_{}", slot)
}
