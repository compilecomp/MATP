// CEP:FILE: hot/unification/substitution.rs
// CEP:WHAT: Substitution engine: flat variable-indexed binding arrays with an undo trail, explicit composition, and term application through the term store.
// CEP:WHY: Design 5.5 and 8.2: a flat array indexed by variable ID gives O(1) lookup with no hashing, which is critical because unification and matching (Phase 2) access substitutions millions of times per second; the binding trail makes failed unification attempts reversible in O(undo) without allocation; substitutions are deliberately NOT hash-consed (too many unique instances, design 5.5).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SubstitutionError::TooManyVariables when a binding exceeds the variable bound, TrailFull when the undo trail is exhausted, InvalidPointer for unreadable term references, ArenaFull when application results do not fit the arena. Never panics.
// CEP:ASSUMES: Variable IDs are dense per-clause indices below kMaxVariablesPerClause (design 5.5); term application allocates in the same arena as the term store and shares its hash-consing (applied results are interned terms); the trail discipline (bind records entries, undo pops them) is the caller's responsibility and is property-tested.
// CEP:COST: lookup is 1.96 cycles median (bounds check + load); bind is 2 compares + 2 stores; apply is O(term size) with one intern per rebuilt node, measured 174.5 cycles median for a two-node rebuild on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0004, artifacts benches/artifacts/substitution_lookup.json and substitution_apply_small.json.
// CEP:EVIDENCE: bench CEP-BENCH-0004; unit/hot/substitution_test.rs; disassembly artifact benches/artifacts/disasm_substitution.txt.
// CEP:SECURITY: variable indices and trail depths are bounds-checked on every access; untrusted variable indices cannot corrupt neighboring slots (CEP&CC 22.6).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; arrays are indexed by explicit variable IDs, iteration is index-ordered, and no hashing is involved.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: lookup must bounds-check one index and load one u32 (the term offset); the bench-main disassembly (artifact disasm_substitution.txt) shows the inlined compare-and-load sequence with no calls; measured 1.96 cycles median; no cheaper safe representation exists for variable-indexed storage.

use crate::ir::term::{TermError, TermPtr, TermStore, TermTag};
use crate::memory::arena::{Arena, ArenaRange};
use core::cell::Cell;
use mapt_config::limits::{
    kInvalidSubstitutionOffset, kInvalidTermOffset, kMaxSubstitutionTrailDepth, kMaxSymbolArity,
    kMaxUnificationDepth, kMaxVariablesPerClause,
};

/// CEP:WHAT: Error cases of the substitution engine.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the engine never panics.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs covers every variant.
/// CEP:SECURITY: bounds errors are the resource boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubstitutionError {
    /// CEP:WHAT: A variable index is at or above kMaxVariablesPerClause.
    VariableOutOfRange,
    /// CEP:WHAT: The undo trail is full (kMaxSubstitutionTrailDepth entries).
    TrailFull,
    /// CEP:WHAT: Application recursion exceeded kMaxUnificationDepth (cyclic or pathological bindings).
    DepthExceeded,
    /// CEP:WHAT: A referenced term is unreadable.
    InvalidPointer,
    /// CEP:WHAT: The arena is exhausted during application.
    ArenaFull,
    /// CEP:WHAT: An offset does not reference a substitution record.
    InvalidSubstitution,
}

/// CEP:WHAT: Serialized substitution record in the arena: a dense array of (variable, term offset) pairs.
/// CEP:WHY: Design 5.4 lets derivation steps reference the applied substitution by offset; the record layout is a fixed header (count) followed by pairs, readable by the cold printer and future proof output without hot-path interpretation.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: reads validate the pair count against the arena bounds.
/// CEP:ASSUMES: stored by Substitution::materialize.
/// CEP:COST: 8 bytes header plus 8 bytes per binding.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs::materialize_and_read_back.
/// CEP:SECURITY: bounds-checked reads.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct SubstitutionRecord {
    /// CEP:WHAT: Number of binding pairs that follow the header in the arena.
    /// CEP:WHY: Defines the record extent for readers.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxVariablesPerClause.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: bounds-checked.
    pub binding_count: u32,
    /// CEP:WHAT: Reserved padding.
    /// CEP:WHY: Fixed 8-byte header for pair alignment; must be zero.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: verifier flags nonzero.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/cold/verifier_test.rs.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u32,
}

// CEP:WHAT: Substitution record layout pin.
// CEP:WHY: The record is read by cold printers and later proof output; drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/substitution_test.rs::record_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<SubstitutionRecord>() == 8);

/// CEP:WHAT: One binding pair inside a materialized record.
/// CEP:WHY: Pairs are (variable ID, term offset) doubles; an explicit struct keeps readers from reinterpreting raw words.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: stored contiguously after SubstitutionRecord.
/// CEP:COST: 8 bytes.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs::materialize_and_read_back.
/// CEP:SECURITY: bounds-checked.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct SubstitutionBinding {
    /// CEP:WHAT: Variable ID.
    /// CEP:WHY: Binding key.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: < kMaxVariablesPerClause.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: bounds-checked on use.
    pub variable: u32,
    /// CEP:WHAT: Bound term offset.
    /// CEP:WHY: Binding value.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: interned term offset.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: validated on dereference.
    pub term_offset: u32,
}

/// CEP:WHAT: A working substitution: flat binding array, undo trail, and optional arena-materialized record.
/// CEP:WHY: Design 5.5 field list: flat array indexed by variable ID (no hash map), bounded size, explicit composition, arena-resident serialized form; the trail is design 8.2's backtracking mechanism.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SubstitutionError.
/// CEP:ASSUMES: the arena outlives the substitution; bindings reference interned terms.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: bench CEP-BENCH-0004; unit/hot/substitution_test.rs.
/// CEP:SECURITY: all accesses bounds-checked.
pub struct Substitution<'a> {
    /// CEP:WHAT: Backing arena for materialized records.
    /// CEP:WHY: Design 5.5: composition and materialization allocate into the arena.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: outlives the substitution.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: arena is bounded.
    arena: &'a Arena,
    /// CEP:WHAT: Binding slots indexed by variable ID (kInvalidTermOffset = unbound).
    /// CEP:WHY: O(1) lookup with no hashing (design 5.5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: exactly kMaxVariablesPerClause slots.
    /// CEP:COST: 256 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs::lookup_after_bind.
    /// CEP:SECURITY: index bounds-checked.
    bindings: [Cell<u32>; kMaxVariablesPerClause as usize],
    /// CEP:WHAT: Undo trail of variable IDs in bind order.
    /// CEP:WHY: Design 8.2: failed unification unwinds the trail to restore state without allocation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: bind returns TrailFull at capacity.
    /// CEP:ASSUMES: entries are only appended by bind and popped by undo_to.
    /// CEP:COST: 16 KiB.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs::trail_undo_restores_state.
    /// CEP:SECURITY: depth bounds-checked.
    trail: [Cell<u32>; kMaxSubstitutionTrailDepth as usize],
    /// CEP:WHAT: Current trail depth.
    /// CEP:WHY: Undo bookkeeping.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxSubstitutionTrailDepth.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: none.
    trail_depth: Cell<u32>,
}

impl<'a> Substitution<'a> {
    // CEP:WHAT: Constructs an empty substitution over the shared arena.
    // CEP:WHY: Fixed arrays live inline (no allocation at all, stricter than design 5.5 requires); initialization clears every slot deterministically.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: arena outlives the substitution.
    // CEP:COST: constant-time clear of 256 + 16384 bytes on the stack.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::initial_state_is_unbound.
    // CEP:SECURITY: no uninitialized reads: every slot is written before any read.
    pub fn new(arena: &'a Arena) -> Substitution<'a> {
        let bindings = core::array::from_fn(|_| Cell::new(kInvalidTermOffset));
        let trail = core::array::from_fn(|_| Cell::new(0));
        Substitution {
            arena,
            bindings,
            trail,
            trail_depth: Cell::new(0),
        }
    }

    // CEP:WHAT: Binds a variable to a term, recording the binding on the undo trail.
    // CEP:WHY: Design 5.5 storage discipline; the trail entry is what makes speculative unification (Phase 2) backtrackable (design 8.2).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableOutOfRange for illegal indices and TrailFull when the trail is exhausted; binding an already-bound variable is refused with VariableOutOfRange to keep the discipline explicit (overwrite must be preceded by undo).
    // CEP:ASSUMES: variable IDs are dense per-clause indices; the caller respects the bind/undo discipline.
    // CEP:COST: 3 compares + 2 stores.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::{lookup_after_bind, double_bind_refused, trail_undo_restores_state}.
    // CEP:SECURITY: index and depth bounds-checked.
    pub fn bind(&self, variable: u32, term: TermPtr) -> Result<(), SubstitutionError> {
        if variable >= kMaxVariablesPerClause {
            return Err(SubstitutionError::VariableOutOfRange);
        }
        if self.bindings[variable as usize].get() != kInvalidTermOffset {
            return Err(SubstitutionError::VariableOutOfRange);
        }
        let depth = self.trail_depth.get();
        if depth >= kMaxSubstitutionTrailDepth {
            return Err(SubstitutionError::TrailFull);
        }
        self.bindings[variable as usize].set(term.as_u32());
        self.trail[depth as usize].set(variable);
        self.trail_depth.set(depth + 1);
        Ok(())
    }

    // CEP:WHAT: Looks up the binding of a variable.
    // CEP:WHY: The hottest substitution operation (design 8.2 OPT-0 requirement); must be a bounds check and a load.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableOutOfRange for illegal indices; unbound variables yield None.
    // CEP:ASSUMES: none.
    // CEP:COST: 1.96 cycles median, measured in bench CEP-BENCH-0004.
    // CEP:EVIDENCE: bench CEP-BENCH-0004; unit/hot/substitution_test.rs::lookup_after_bind.
    // CEP:SECURITY: bounds check retained in release.
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: one bounds check plus one u32 load; measured 1.96 cycles median (bench CEP-BENCH-0004); the inlined sequence appears in artifact disasm_substitution.txt.
    pub fn lookup(&self, variable: u32) -> Result<Option<TermPtr>, SubstitutionError> {
        if variable >= kMaxVariablesPerClause {
            return Err(SubstitutionError::VariableOutOfRange);
        }
        let offset = self.bindings[variable as usize].get();
        if offset == kInvalidTermOffset {
            return Ok(None);
        }
        Ok(Some(TermPtr::from_raw(offset)))
    }

    // CEP:WHAT: Returns true when the variable has a binding.
    // CEP:WHY: Guards in matching and occurs checks (Phase 2).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableOutOfRange for illegal indices.
    // CEP:ASSUMES: none.
    // CEP:COST: as lookup().
    // CEP:EVIDENCE: unit/hot/substitution_test.rs.
    // CEP:SECURITY: none.
    pub fn is_bound(&self, variable: u32) -> Result<bool, SubstitutionError> {
        Ok(self.lookup(variable)?.is_some())
    }

    // CEP:WHAT: Undoes every trail entry recorded after the given depth.
    // CEP:WHY: Design 8.2: unification failure rewinds the trail; the explicit depth argument supports nested speculative attempts.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; a depth above the current depth is a no-op (documented), a depth of zero clears everything.
    // CEP:ASSUMES: the caller passes a depth previously observed via trail_depth().
    // CEP:COST: O(undone entries), 2 stores each.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::trail_undo_restores_state.
    // CEP:SECURITY: trail depth is clamped internally; no out-of-range access is possible.
    pub fn undo_to(&self, depth: u32) {
        let mut current = self.trail_depth.get();
        while current > depth && current > 0 {
            current -= 1;
            let variable = self.trail[current as usize].get();
            if variable < kMaxVariablesPerClause {
                self.bindings[variable as usize].set(kInvalidTermOffset);
            }
            self.trail[current as usize].set(0);
        }
        self.trail_depth.set(current);
    }

    // CEP:WHAT: Returns the current trail depth.
    // CEP:WHY: Save/restore points for speculative unification.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::trail_undo_restores_state.
    // CEP:SECURITY: none.
    pub fn trail_depth(&self) -> u32 {
        self.trail_depth.get()
    }

    // CEP:WHAT: Applies the substitution to a term, returning the interned result.
    // CEP:WHY: Design 5.5 application semantics: variables are replaced by bindings, non-variable nodes are rebuilt with substituted children and re-interned (canonical); the entry point resets the depth guard so public callers need no depth bookkeeping.
    // CEP:STATUS: complete
    // CEP:FAILURE: see apply_bounded.
    // CEP:ASSUMES: see apply_bounded.
    // CEP:COST: see apply_bounded.
    // CEP:EVIDENCE: bench CEP-BENCH-0004; unit/hot/substitution_test.rs::{apply_replaces_variables, apply_idempotent_on_ground_terms, cyclic_binding_rejected}.
    // CEP:SECURITY: bounded recursion (CEP&CC 22.10 unbounded-recursion ban).
    pub fn apply(
        &self,
        terms: &TermStore,
        term: TermPtr,
        symbols: &crate::ir::symbol_table::SymbolTable,
    ) -> Result<TermPtr, SubstitutionError> {
        self.apply_bounded(terms, term, symbols, 0)
    }

    // CEP:WHAT: Recursive application core with an explicit depth guard.
    // CEP:WHY: Bindings can chain (x -> y, y -> f(x)) and a malicious or buggy chain would recurse without bound; the explicit depth counter against kMaxUnificationDepth turns that into a loud error (CEP&CC 22.10 unbounded recursion ban, Law 6 explicit failure).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns DepthExceeded when recursion passes kMaxUnificationDepth; propagates InvalidPointer and ArenaFull.
    // CEP:ASSUMES: the term store is the one that produced the input term; variable chains are acyclic in legitimate use (enforced by the guard, not assumed).
    // CEP:COST: O(term nodes) with one intern per changed non-variable node; measured in bench CEP-BENCH-0004.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::cyclic_binding_rejected.
    // CEP:SECURITY: recursion depth bounded; every child read is bounds-checked.
    fn apply_bounded(
        &self,
        terms: &TermStore,
        term: TermPtr,
        symbols: &crate::ir::symbol_table::SymbolTable,
        depth: u32,
    ) -> Result<TermPtr, SubstitutionError> {
        if depth > kMaxUnificationDepth {
            return Err(SubstitutionError::DepthExceeded);
        }
        let view = terms.term(term).map_err(map_term_error)?;
        match view.tag() {
            TermTag::Variable => {
                let bound = self.lookup(view.symbol())?;
                match bound {
                    Some(replacement) => self.apply_bounded(terms, replacement, symbols, depth + 1),
                    None => Ok(term),
                }
            }
            TermTag::Function | TermTag::Predicate => {
                let symbol = view.symbol();
                let count = view.child_count();
                let mut children: [TermPtr; kMaxSymbolArity as usize] =
                    [TermPtr::invalid(); kMaxSymbolArity as usize];
                if count as usize > children.len() {
                    return Err(SubstitutionError::InvalidPointer);
                }
                let mut changed = false;
                for index in 0..count {
                    let child = view.child(index).map_err(map_term_error)?;
                    let substituted = self.apply_bounded(terms, child, symbols, depth + 1)?;
                    if substituted != child {
                        changed = true;
                    }
                    children[index as usize] = substituted;
                }
                if !changed {
                    return Ok(term);
                }
                let result = if view.tag() == TermTag::Function {
                    terms.intern_fun(symbols, symbol, &children[..count as usize])
                } else {
                    terms.intern_pred(symbols, symbol, &children[..count as usize])
                };
                result.map_err(map_term_error)
            }
            TermTag::Equality => {
                let left = view.child(0).map_err(map_term_error)?;
                let right = view.child(1).map_err(map_term_error)?;
                let new_left = self.apply_bounded(terms, left, symbols, depth + 1)?;
                let new_right = self.apply_bounded(terms, right, symbols, depth + 1)?;
                if new_left == left && new_right == right {
                    return Ok(term);
                }
                terms
                    .intern_eq(symbols, new_left, new_right)
                    .map_err(map_term_error)
            }
            _ => Ok(term),
        }
    }

    // CEP:WHAT: Materializes the substitution into an arena record and returns its offset.
    // CEP:WHY: Design 5.4: derivation steps reference substitutions by offset; the record is the serialized form read by proof output.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull when the record does not fit; InvalidSubstitution never occurs at write time.
    // CEP:ASSUMES: the arena is the same one the term store uses.
    // CEP:COST: O(bound variables) plus one arena allocation.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::materialize_and_read_back.
    // CEP:SECURITY: binding count bounded by kMaxVariablesPerClause.
    pub fn materialize(&self) -> Result<u32, SubstitutionError> {
        let mut count: u32 = 0;
        for index in 0..kMaxVariablesPerClause {
            if self.bindings[index as usize].get() != kInvalidTermOffset {
                count += 1;
            }
        }
        let header_range = self
            .arena
            .alloc_array::<SubstitutionRecord>(1)
            .map_err(|_| SubstitutionError::ArenaFull)?;
        let pairs_range = self
            .arena
            .alloc_array::<SubstitutionBinding>(count)
            .map_err(|_| SubstitutionError::ArenaFull)?;
        let header = self
            .arena
            .array_mut::<SubstitutionRecord>(header_range)
            .map_err(|_| SubstitutionError::ArenaFull)?;
        header[0] = SubstitutionRecord {
            binding_count: count,
            reserved: 0,
        };
        if count > 0 {
            let pairs = self
                .arena
                .array_mut::<SubstitutionBinding>(pairs_range)
                .map_err(|_| SubstitutionError::ArenaFull)?;
            let mut cursor = 0;
            for index in 0..kMaxVariablesPerClause {
                let offset = self.bindings[index as usize].get();
                if offset != kInvalidTermOffset {
                    pairs[cursor] = SubstitutionBinding {
                        variable: index,
                        term_offset: offset,
                    };
                    cursor += 1;
                }
            }
        }
        Ok(header_range.start)
    }

    // CEP:WHAT: Reads back a materialized substitution record.
    // CEP:WHY: Cold proof output and the verifier must decode records; the hot crate owns the layout, so it owns the reader.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidSubstitution when the offset is unreadable or the pair array is truncated.
    // CEP:ASSUMES: offset came from materialize().
    // CEP:COST: bounds checks plus slice construction.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::materialize_and_read_back.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn read_record(
        &self,
        offset: u32,
    ) -> Result<(&'a SubstitutionRecord, &'a [SubstitutionBinding]), SubstitutionError> {
        if offset == kInvalidSubstitutionOffset {
            return Err(SubstitutionError::InvalidSubstitution);
        }
        let header_size = core::mem::size_of::<SubstitutionRecord>() as u32;
        let header_end = offset
            .checked_add(header_size)
            .ok_or(SubstitutionError::InvalidSubstitution)?;
        if header_end > self.arena.used_bytes() {
            return Err(SubstitutionError::InvalidSubstitution);
        }
        let header_range = ArenaRange::new(offset, header_end)
            .map_err(|_| SubstitutionError::InvalidSubstitution)?;
        let header_slice = self
            .arena
            .array::<SubstitutionRecord>(header_range)
            .map_err(|_| SubstitutionError::InvalidSubstitution)?;
        if header_slice.is_empty() {
            return Err(SubstitutionError::InvalidSubstitution);
        }
        let header = &header_slice[0];
        let pairs_bytes = header
            .binding_count
            .checked_mul(core::mem::size_of::<SubstitutionBinding>() as u32)
            .ok_or(SubstitutionError::InvalidSubstitution)?;
        let pairs_end = header_end
            .checked_add(pairs_bytes)
            .ok_or(SubstitutionError::InvalidSubstitution)?;
        if pairs_end > self.arena.used_bytes() {
            return Err(SubstitutionError::InvalidSubstitution);
        }
        let pairs_range = ArenaRange::new(header_end, pairs_end)
            .map_err(|_| SubstitutionError::InvalidSubstitution)?;
        let pairs = self
            .arena
            .array::<SubstitutionBinding>(pairs_range)
            .map_err(|_| SubstitutionError::InvalidSubstitution)?;
        Ok((header, pairs))
    }
}

// CEP:WHAT: Maps term-store errors onto substitution errors.
// CEP:WHY: CEP&CC 33.18: component-specific error types; a single mapping point keeps the translation auditable.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/substitution_test.rs::invalid_term_refused.
// CEP:SECURITY: none.
fn map_term_error(error: TermError) -> SubstitutionError {
    match error {
        TermError::ArenaFull | TermError::TableFull => SubstitutionError::ArenaFull,
        _ => SubstitutionError::InvalidPointer,
    }
}
