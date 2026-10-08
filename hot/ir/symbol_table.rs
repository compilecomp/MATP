// CEP:FILE: hot/ir/symbol_table.rs
// CEP:WHAT: Frozen read-only symbol table: dense u32 symbol IDs mapped to kind, arity, weight, flags, and sort signature.
// CEP:WHY: Design 5.6 requires the table to be built during parsing (CEP-1) and frozen before search, with all hot-path code using symbol IDs and never string names; the frozen layout is two plain arrays in the arena so lookups are one bounds check and one load with zero allocation.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SymbolError::UnknownSymbol for out-of-range IDs and SymbolError::InvalidSignature for corrupted sort-signature metadata; never panics.
// CEP:ASSUMES: The table is built exclusively by the CEP-1 builder (cold/symbol_table_builder.rs), frozen once, and never mutated afterwards; entry count and pool bounds are validated at freeze time and re-checked on every access.
// CEP:COST: info is 2.95 cycles median (bounds compare + load) on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0002, artifact benches/artifacts/term_symbol_lookup.json.
// CEP:EVIDENCE: bench CEP-BENCH-0002; unit/hot/symbol_table_test.rs; security/symbol_bounds_test.rs; cold builder test unit/cold/symbol_table_builder_test.rs.
// CEP:SECURITY: symbol IDs arriving from untrusted input are bounds-checked before any array access (CEP&CC 22.6); no strings exist in the hot table, so no unbounded name handling can occur here.
// CEP:HPC-DETERMINISM: deterministic; the table is immutable after freeze and contains no addresses, clocks, or iteration-order-dependent state.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: a lookup must bounds-check the ID and load one fixed-size entry; the bench-main disassembly (artifact disasm_term.txt) contains exactly that inlined sequence with no calls; measured 2.95 cycles median.

use crate::memory::arena::{Arena, ArenaRange};
use mapt_config::limits::{kDefaultSymbolWeight, kMaxSymbolArity, kMaxSymbolCount};

/// CEP:WHAT: Sort identifier: a dense u32 index into the sort universe.
/// CEP:WHY: Design 5.6 references SortId throughout symbol signatures; a newtype keeps sort IDs distinct from symbol IDs at zero cost.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; the type is a transparent u32.
/// CEP:ASSUMES: values are assigned by the CEP-1 builder and are dense.
/// CEP:COST: 4-byte copy type.
/// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs.
/// CEP:SECURITY: validated by consumers through bounds checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SortId(pub u32);

/// CEP:WHAT: Symbol kinds recognized by the IR (design 5.6).
/// CEP:WHY: Term construction legality depends on the kind (functions take arguments, sorts do not); an explicit enum with a fixed representation replaces tag integers (CEP&CC 33.12).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; closed vocabulary.
/// CEP:ASSUMES: u8 representation is sufficient and stable for FFI.
/// CEP:COST: 1-byte field.
/// CEP:EVIDENCE: unit/hot/symbol_table_test.rs::kind_roundtrip.
/// CEP:SECURITY: out-of-range values cannot be constructed through the safe API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SymbolKind {
    /// CEP:WHAT: Function symbol (maps terms to terms).
    /// CEP:WHY: Design 5.6 symbol kind.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: arity >= 1 in practice, arity 0 means constant.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    Function = 0,
    /// CEP:WHAT: Predicate symbol (maps terms to propositions).
    /// CEP:WHY: Design 5.6 symbol kind.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: arity 0 means propositional atom.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    Predicate = 1,
    /// CEP:WHAT: Sort symbol (type constructor).
    /// CEP:WHY: Design 5.6 symbol kind; TFF/THF support.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    Sort = 2,
    /// CEP:WHAT: Variable symbol (reserved for the variable environment).
    /// CEP:WHY: Design 5.6 lists Variable as a kind; first-order variables are represented as Var terms, this kind marks variable symbols in mixed tables.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: none.
    Variable = 3,
}

/// CEP:WHAT: Symbol flag bits (bit positions in SymbolInfo::flags).
/// CEP:WHY: Design 5.6 has a flags byte (built-in, theory-specific); named bit constants replace magic masks (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bit 0 is built-in, bit 1 is theory-tagged; further bits are Phase 5 theory work.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/symbol_table_test.rs::flag_masks.
/// CEP:SECURITY: none.
pub const kSymbolFlagBuiltin: u16 = 1;
/// CEP:WHAT: Bit marking a symbol as carrying theory-specific semantics.
/// CEP:WHY: Design 5.6 theory flags; used by Phase 5 theory reasoning.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 5.
/// CEP:SECURITY: none.
pub const kSymbolFlagTheory: u16 = 2;

/// CEP:WHAT: One frozen symbol-table entry.
/// CEP:WHY: Design 5.6 field list as a fixed-layout struct; storing entries in one array keeps the table traversable and cache-friendly (CEP&CC 23.6.2).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; validated by freeze().
/// CEP:ASSUMES: sort signatures live in the shared sort pool; names live in CEP-1 cold storage, never here.
/// CEP:COST: 16 bytes per symbol.
/// CEP:EVIDENCE: layout checked by static assertions below and unit/hot/symbol_table_test.rs::lookups.
/// CEP:SECURITY: fixed layout, no pointers, no strings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct SymbolInfo {
    /// CEP:WHAT: Symbol kind.
    /// CEP:WHY: Drives construction legality checks.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: set by the builder.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: closed enum.
    pub kind: SymbolKind,
    /// CEP:WHAT: Symbol arity.
    /// CEP:WHY: Term construction validates child counts against it.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxSymbolArity, enforced by the builder.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: security/symbol_bounds_test.rs.
    /// CEP:SECURITY: bounds term fan-out.
    pub arity: u16,
    /// CEP:WHAT: Symbol flag bits.
    /// CEP:WHY: Built-in and theory markers (design 5.6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: masks defined above.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/symbol_table_test.rs::flag_masks.
    /// CEP:SECURITY: none.
    pub flags: u16,
    /// CEP:WHAT: Clause-weight contribution of the symbol (design 15.3).
    /// CEP:WHY: Named per-symbol weight lets strategies tune weighting without code changes; default kDefaultSymbolWeight.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 for KBO admissibility when used as KBO weight.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
    /// CEP:SECURITY: none.
    pub weight: u32,
    /// CEP:WHAT: Offset of the sort signature inside the sort pool.
    /// CEP:WHY: Argument sorts plus return sort are stored contiguously in a shared pool to keep entries fixed-size (design 5.6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: validated by freeze().
    /// CEP:ASSUMES: signature length entries exist in the pool.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs.
    /// CEP:SECURITY: validated by signature access bounds checks.
    pub sort_signature: u32,
    /// CEP:WHAT: Number of sort-pool entries in the signature (argument sorts + return sort).
    /// CEP:WHY: arity + 1 entries expected; length stored explicitly so signatures can be validated without the table.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: validated by freeze().
    /// CEP:ASSUMES: equals arity + 1 for Function/Predicate/Variable kinds, 1 for Sort.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs.
    /// CEP:SECURITY: bounds-checked at every access.
    pub sort_signature_len: u16,
    /// CEP:WHAT: Reserved padding to a 16-byte entry.
    /// CEP:WHY: Explicit padding keeps the layout fixed and the struct size a power of two; reserved fields must be zero (CEP&CC 38.17 stable IR).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: freeze() rejects nonzero reserved bytes.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/symbol_table_test.rs::lookups.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u16,
}

// CEP:WHAT: Layout checks for SymbolInfo.
// CEP:WHY: The entry is written by CEP-1 and read by CEP-0 in the same process and across the FFI later; the layout must be pinned (CEP&CC 22.8, 38.17). The natural repr(C) layout of the field list is 20 bytes (u8 kind, u16 arity, u16 flags, u32 weight, u32 sort offset, u16 sig len, u16 reserved).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on layout drift.
// CEP:ASSUMES: u8/u16/u32 sizes from the target ABI.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/symbol_table_test.rs::lookups.
// CEP:SECURITY: layout drift is an ABI break.
const _: () = assert!(core::mem::size_of::<SymbolInfo>() == 20);

/// CEP:WHAT: Error cases of the frozen symbol table.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the table never panics.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/symbol_table_test.rs covers every variant.
/// CEP:SECURITY: unknown-symbol errors are the untrusted-ID boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolError {
    /// CEP:WHAT: The symbol ID is outside the frozen table.
    UnknownSymbol,
    /// CEP:WHAT: The sort-signification metadata is inconsistent (out-of-pool offset or length).
    InvalidSignature,
    /// CEP:WHAT: Freeze-time validation failed.
    InvalidTable,
}

/// CEP:WHAT: Frozen symbol table view over arena arrays.
/// CEP:WHY: Design 5.6: built in CEP-1, frozen, then read by CEP-0; the view borrows immutable slices from the arena so no copy and no lock is needed and mutation is impossible by construction.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SymbolError.
/// CEP:ASSUMES: the backing arena outlives this view; the arrays were written by the CEP-1 builder.
/// CEP:COST: see info(); O(1) per lookup.
/// CEP:EVIDENCE: unit/hot/symbol_table_test.rs; security/symbol_bounds_test.rs.
/// CEP:SECURITY: every ID is bounds-checked before array access.
pub struct SymbolTable<'a> {
    /// CEP:WHAT: Frozen entry array.
    /// CEP:WHY: Dense ID -> entry mapping.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length == symbol count, <= kMaxSymbolCount.
    /// CEP:COST: one slice access per lookup.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: bounds-checked.
    entries: &'a [SymbolInfo],
    /// CEP:WHAT: Shared sort-signature pool.
    /// CEP:WHY: Variable-length signatures are stored out-of-line to keep entries fixed-size.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: offsets and lengths in entries are in-pool; validated at freeze.
    /// CEP:COST: slice access per signature read.
    /// CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::declare_predicate.
    /// CEP:SECURITY: bounds-checked.
    sort_pool: &'a [SortId],
}

impl<'a> SymbolTable<'a> {
    // CEP:WHAT: Freezes a symbol table view over arena ranges written by the CEP-1 builder.
    // CEP:WHY: Freeze is the trust boundary: every invariant that CEP-0 relies on is validated once here (CEP&CC 22.3, Law 3) so the hot path never re-validates structure, only IDs.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns SymbolError::InvalidTable when the entry count exceeds kMaxSymbolCount, the sort pool is misaligned or oversized, an entry's signature is out of pool, a signature length disagrees with the kind, the arity exceeds kMaxSymbolArity, the weight is zero for KBO use, or reserved bytes are nonzero.
    // CEP:ASSUMES: the builder wrote SymbolInfo entries and a SortId pool into the given ranges of the given arena.
    // CEP:COST: O(n) one-time validation at freeze; no allocation.
    // CEP:EVIDENCE: unit/cold/symbol_table_builder_test.rs::freeze_rejects_bad_tables; unit/hot/symbol_table_test.rs.
    // CEP:SECURITY: full structural validation of builder output before hot use.
    pub fn freeze(
        arena: &'a Arena,
        entries_range: ArenaRange,
        sort_pool_range: ArenaRange,
    ) -> Result<SymbolTable<'a>, SymbolError> {
        let entries = arena
            .array::<SymbolInfo>(entries_range)
            .map_err(|_| SymbolError::InvalidTable)?;
        if entries.len() > kMaxSymbolCount as usize {
            return Err(SymbolError::InvalidTable);
        }
        let sort_pool = arena
            .array::<SortId>(sort_pool_range)
            .map_err(|_| SymbolError::InvalidTable)?;
        for entry in entries.iter() {
            if entry.arity > kMaxSymbolArity {
                return Err(SymbolError::InvalidTable);
            }
            if entry.weight == 0 || entry.reserved != 0 {
                return Err(SymbolError::InvalidTable);
            }
            let expected_len = match entry.kind {
                SymbolKind::Sort => 1,
                _ => {
                    // CEP:WHAT: Signature length for non-sort kinds is arity plus one.
                    // CEP:WHY: Function and predicate signatures append the return sort.
                    // CEP:STATUS: complete
                    // CEP:FAILURE: none.
                    // CEP:ASSUMES: none.
                    // CEP:COST: constant.
                    // CEP:EVIDENCE: unit/hot/symbol_table_test.rs::signature_slice.
                    // CEP:SECURITY: none.
                    entry.arity + 1
                }
            };
            if entry.sort_signature_len != expected_len {
                return Err(SymbolError::InvalidTable);
            }
            let start = entry.sort_signature as usize;
            let len = entry.sort_signature_len as usize;
            if start > sort_pool.len() || len > sort_pool.len() - start {
                return Err(SymbolError::InvalidTable);
            }
        }
        Ok(SymbolTable { entries, sort_pool })
    }

    // CEP:WHAT: Returns the number of frozen symbols.
    // CEP:WHY: Bounds for ID validation and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/symbol_table_test.rs.
    // CEP:SECURITY: none.
    pub fn symbol_count(&self) -> u32 {
        self.entries.len() as u32
    }

    // CEP:WHAT: Returns the frozen entry for a symbol ID.
    // CEP:WHY: The single hot-path lookup every term-construction site uses; one bounds check plus one load.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns SymbolError::UnknownSymbol when symbol_id >= symbol_count.
    // CEP:ASSUMES: table was validated at freeze.
    // CEP:COST: 2.95 cycles median on x86-64 (Intel Xeon, virtualized), bench CEP-BENCH-0002.
    // CEP:EVIDENCE: bench CEP-BENCH-0002; security/symbol_bounds_test.rs::unknown_id_rejected.
    // CEP:SECURITY: bounds check retained in release for untrusted IDs (CEP&CC 23.7).
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: a dense-array lookup with a bounds check is the minimum work for safe indexed access; measured 2.95 cycles median (bench CEP-BENCH-0002); the inlined sequence appears in artifact disasm_term.txt.
    pub fn info(&self, symbol_id: u32) -> Result<&SymbolInfo, SymbolError> {
        if symbol_id as usize >= self.entries.len() {
            return Err(SymbolError::UnknownSymbol);
        }
        Ok(&self.entries[symbol_id as usize])
    }

    // CEP:WHAT: Returns the sort signature (argument sorts then return sort) of a symbol.
    // CEP:WHY: Sort-correctness checks in term construction read signatures; out-of-line storage keeps them cheap.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns SymbolError::UnknownSymbol for bad IDs and SymbolError::InvalidSignature for pool inconsistencies (impossible after freeze; retained as defense in depth).
    // CEP:ASSUMES: freeze validated the pool.
    // CEP:COST: bounds check plus slice construction.
    // CEP:EVIDENCE: unit/hot/symbol_table_test.rs::signature_slice.
    // CEP:SECURITY: bounds check retained in release.
    pub fn sort_signature(&self, symbol_id: u32) -> Result<&[SortId], SymbolError> {
        let entry = self.info(symbol_id)?;
        let start = entry.sort_signature as usize;
        let len = entry.sort_signature_len as usize;
        if start > self.sort_pool.len() || len > self.sort_pool.len() - start {
            return Err(SymbolError::InvalidSignature);
        }
        Ok(&self.sort_pool[start..start + len])
    }

    // CEP:WHAT: Returns the default weight contributed by this symbol to clause weight.
    // CEP:WHY: Term weight accumulation (design 15.3) reads per-symbol weights; the helper centralizes the fallback rule.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates UnknownSymbol.
    // CEP:ASSUMES: entry weights are >= 1 (validated at freeze).
    // CEP:COST: same as info().
    // CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
    // CEP:SECURITY: none.
    pub fn symbol_weight(&self, symbol_id: u32) -> Result<u32, SymbolError> {
        let entry = self.info(symbol_id)?;
        if entry.weight == 0 {
            return Ok(kDefaultSymbolWeight);
        }
        Ok(entry.weight)
    }
}
