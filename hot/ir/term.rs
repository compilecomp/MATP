// CEP:FILE: hot/ir/term.rs
// CEP:WHAT: Hash-consed term store: fixed-layout terms in the shared arena, canonicalized through an open-addressing table so structural equality is offset equality.
// CEP:WHY: Design 5.1: hash-consing eliminates duplicate terms (memory grows with distinct subterms, not clause count), makes equality a pointer compare (the hottest comparison in superposition), and gives every term a stable deterministic identity. Alternatives rejected: structural comparison per equality test (O(size) per compare on the hottest path), per-node heap allocation (banned in CEP-0, CEP&CC 25.5), and pointer-address hashing (nondeterministic, banned by CEP&CC 38.10).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns TermError::UnknownSymbol / ArityMismatch for illegal symbol use, DepthExceeded beyond kMaxTermDepth, WeightExceeded beyond kMaxTermWeight, TableFull at the load-factor bound, ArenaFull when the arena is exhausted, InvalidPointer for unreadable term references. Never panics. Never allocates outside the arena.
// CEP:ASSUMES: Terms are immutable after interning; the hash table never resizes (design 5.1); term identity is offset identity, which equals structural identity by the hash-consing invariant (design 5.7 explicitly carves hash-consed terms out of the pointer-identity ban); offsets are deterministic for a deterministic allocation sequence, so identical input produces identical IR.
// CEP:COST: intern of an n-ary term is O(n) expected (hash over children, probe, arena write); measured 37.9 cycles median for a binary-term probe hit including measurement-loop overhead on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0002, artifact benches/artifacts/term_intern_binary_hit.json.
// CEP:EVIDENCE: bench CEP-BENCH-0002; unit/hot/term_test.rs; property/term_property_test.rs; fuzz/term_fuzz_test.rs; contract/term_contract_test.rs; disassembly artifact benches/artifacts/disasm_term.txt.
// CEP:SECURITY: all term reads are bounds-checked slice accesses; term offsets are private tokens that untrusted input cannot forge (parsers build terms only through intern); depth and weight bounds prevent resource exhaustion from malicious nesting (CEP&CC 22.10).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the FNV-1a hash has no seed, probe order depends only on the hash, and allocation order is the call order.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: intern pays a bounds check per term read and a branch per probe; both are required security costs (CEP&CC 23.7). Removing the per-read slice bounds check via cached slices is deferred; ticket CEP-1009.

use crate::ir::symbol_table::{SymbolKind, SymbolTable};
use crate::memory::arena::{Arena, ArenaRange};
use core::cell::Cell;
use mapt_config::limits::{
    kDefaultSymbolWeight, kInvalidTermOffset, kKboVariableWeight, kMaxSymbolArity, kMaxTermDepth,
    kMaxTermWeight, kMaxVariablesPerClause, kTermHashTableCapacity,
    kTermHashTableLoadFactorPercent,
};

/// CEP:WHAT: Term tag byte (design 5.1 term kinds).
/// CEP:WHY: The tag drives every case analysis on terms; an explicit u8 enum with named constants packs into one word with the child count and flags.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; closed vocabulary.
/// CEP:ASSUMES: at most 256 kinds; values are part of the serialized IR contract (kIrVersion).
/// CEP:COST: 1-byte field.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: out-of-range tags cannot be constructed through the safe API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TermTag {
    /// CEP:WHAT: Variable, identified by a dense per-clause index stored in the symbol field.
    Variable = 0,
    /// CEP:WHAT: Function symbol applied to child terms.
    Function = 1,
    /// CEP:WHAT: Predicate symbol applied to child terms.
    Predicate = 2,
    /// CEP:WHAT: Equality atom Eq(left, right), special-cased for superposition (design 5.1).
    Equality = 3,
    /// CEP:WHAT: Higher-order application App(func, arg) (design 5.1).
    Application = 4,
    /// CEP:WHAT: Lambda abstraction Lam(var, body) (design 5.1; not built on the Phase 1 hot path).
    Lambda = 5,
    /// CEP:WHAT: Sort annotation, identified by a SortId in the symbol field (design 5.1).
    Sort = 6,
}

/// CEP:WHAT: Groundness flag bit position in the term flags byte.
/// CEP:WHY: Design 5.1 caches flags on the header; groundness drives indexing (perfect hash for ground terms, design 9.1) and is queried constantly.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bit 0 is the only Phase 1 flag.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::ground_flag.
/// CEP:SECURITY: none.
pub const kTermFlagGround: u8 = 1;

/// CEP:WHAT: FNV-1a 32-bit offset basis (hash constant).
/// CEP:WHY: The hash-consing hash must be a documented, seedless, deterministic function; FNV-1a constants are published reference values (Fowler/Noll/Vo).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: standard published constants.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: property/term_property_test.rs::hash_is_deterministic.
/// CEP:SECURITY: seedless hashing cannot be poisoned by hash-seed control.
pub const kFnvOffsetBasis32: u32 = 2_166_136_261;

/// CEP:WHAT: FNV-1a 32-bit prime (hash constant).
/// CEP:WHY: See kFnvOffsetBasis32.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: standard published constant.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: property/term_property_test.rs::hash_is_deterministic.
/// CEP:SECURITY: none.
pub const kFnvPrime32: u32 = 16_777_619;

/// CEP:WHAT: Number of u32 words in the fixed part of a term record.
/// CEP:WHY: The in-memory term layout is a u32 word array: w0 packs tag/flags/child-count, w1 is the symbol, w2 packs depth/reserved, w3 is the cached weight, children follow; the fixed size must be a named constant used by every access (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: layout version 1 (kIrVersion).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: layout drift is an IR version break.
pub const kTermFixedWords: u32 = 4;

/// CEP:WHAT: Bit masks and shifts for word 0 (tag, flags, child count).
/// CEP:WHY: Packing keeps the fixed part at four words; every mask and shift is a named constant instead of a magic number (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: tag occupies bits 0-7, flags bits 8-15, child count bits 16-31.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: none.
pub const kTermTagMask: u32 = 0xFF;
/// CEP:WHAT: Shift of the flags byte inside word 0.
/// CEP:WHY: See kTermTagMask.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: none.
pub const kTermFlagsShift: u32 = 8;
/// CEP:WHAT: Shift of the child count inside word 0.
/// CEP:WHY: See kTermTagMask.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: none.
pub const kTermCountShift: u32 = 16;
/// CEP:WHAT: Named term-tag discriminants (values pinned to the TermTag repr by static assertions).
/// CEP:WHY: The tag decoder must not match raw digits (CEP&CC 11.3) and must reject unknown values (Law 6).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: values equal the TermTag enum discriminants; enforced below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagVariable: u8 = 0;
/// CEP:WHAT: Function-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagFunction: u8 = 1;
/// CEP:WHAT: Predicate-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagPredicate: u8 = 2;
/// CEP:WHAT: Equality-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagEquality: u8 = 3;
/// CEP:WHAT: Application-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagApplication: u8 = 4;
/// CEP:WHAT: Lambda-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagLambda: u8 = 5;
/// CEP:WHAT: Sort-tag discriminant.
/// CEP:WHY: See kTermTagVariable.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip.
/// CEP:SECURITY: none.
pub const kTermTagSort: u8 = 6;
/// CEP:WHAT: Word-array index of the depth-and-reserved word.
/// CEP:WHY: Named index instead of a raw 2 (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: layout version 1.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: none.
pub const kTermWordIndexDepth: usize = 2;
/// CEP:WHAT: Word-array index of the cached weight word.
/// CEP:WHY: Named index instead of a raw 3 (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: layout version 1.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
/// CEP:SECURITY: none.
pub const kTermWordIndexWeight: usize = 3;
/// CEP:WHAT: Percent scale for the load-factor bound computation.
/// CEP:WHY: Named instead of a raw 100 (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::table_full_after_load_factor_bound.
/// CEP:SECURITY: none.
pub const kPercentScale: u32 = 100;

/// CEP:WHAT: Mask of the depth field inside word 2.
/// CEP:WHY: Depth is cached on the record (design 8.3 caching discipline) and must be extracted by a named mask.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: depth occupies bits 0-15.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::depth_cache.
/// CEP:SECURITY: none.
pub const kTermDepthMask: u32 = 0xFFFF;

/// CEP:WHAT: Opaque handle to a hash-consed term (byte offset of its word array in the arena).
/// CEP:WHY: Offsets are stable, deterministic, and half the width of pointers; the private field makes forged handles impossible outside this crate, so every TermPtr in the system was produced by intern and satisfies the hash-consing invariant by construction.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; transparent u32 token.
/// CEP:ASSUMES: values are arena offsets of term records.
/// CEP:COST: 4-byte copy type.
/// CEP:EVIDENCE: property/term_property_test.rs::interning_is_canonical.
/// CEP:SECURITY: unforgeable outside the crate; serialization through as_u32 is explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TermPtr(u32);

impl TermPtr {
    // CEP:WHAT: Returns the raw arena offset for serialization and diagnostics.
    // CEP:WHY: Cold printers and the future FFI need the numeric identity; keeping construction private preserves the invariant while allowing read-out.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/cold/debug_printer_test.rs.
    // CEP:SECURITY: read-only projection; no inverse in the public API.
    pub fn as_u32(&self) -> u32 {
        self.0
    }

    // CEP:WHAT: Constructs the invalid handle used for zero-filling unused clause literal slots.
    // CEP:WHY: Unused inline slots need a deterministic filler whose dereference fails loudly; the invalid offset makes TermStore::term return InvalidPointer instead of reading garbage (CEP&CC 22.4 no uninitialized or misleading reads).
    // CEP:STATUS: complete
    // CEP:FAILURE: dereferencing the result always returns TermError::InvalidPointer.
    // CEP:ASSUMES: crate-internal use only; never stored as a real atom.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/clause_test.rs::inline_slots_zeroed; unit/cold/verifier_test.rs.
    // CEP:SECURITY: loud-failure sentinel.
    pub(crate) fn invalid() -> TermPtr {
        TermPtr(kInvalidTermOffset)
    }

    // CEP:WHAT: Rebuilds a handle from a raw offset written by as_u32 (crate-internal round trip).
    // CEP:WHY: Substitution records store term offsets; reading them back requires the inverse of as_u32; keeping both crate-internal preserves the unforgeable-handle invariant outside the crate while allowing serialization round trips.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (the offset was validated when the handle was first created).
    // CEP:ASSUMES: offset came from a handle produced by this store.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/substitution_test.rs::materialize_and_read_back.
    // CEP:SECURITY: crate-internal only; the public API exposes no inverse.
    pub(crate) fn from_raw(offset: u32) -> TermPtr {
        TermPtr(offset)
    }

    // CEP:WHAT: Rebuilds a handle from a raw offset for diagnostics and verification.
    // CEP:WHY: The cold IR verifier and debug printer read term offsets from hash-table slots and serialized records; they need the inverse of as_u32. The constructor is memory-safe for any u32 because every dereference goes through the bounds-checked term() accessor; semantic validity is the caller's documented contract (offsets come from this store's table or as_u32).
    // CEP:STATUS: complete
    // CEP:FAILURE: dereferencing an invalid offset returns TermError::InvalidPointer, never UB.
    // CEP:ASSUMES: the offset was produced by this store (as_u32 or a hash-table slot).
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/verifier_test.rs; unit/cold/debug_printer_test.rs.
    // CEP:SECURITY: bounds checks on every use make forged handles fail loudly instead of reading out of bounds.
    pub fn from_verified_offset(offset: u32) -> TermPtr {
        TermPtr(offset)
    }
}

/// CEP:WHAT: Error cases of the term store.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the store never panics.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/term_test.rs covers every variant.
/// CEP:SECURITY: depth/weight/table errors are the resource-exhaustion boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TermError {
    /// CEP:WHAT: The symbol ID is not in the frozen table.
    UnknownSymbol,
    /// CEP:WHAT: The symbol kind does not fit the requested term tag.
    SymbolKindMismatch,
    /// CEP:WHAT: The child count does not match the symbol arity.
    ArityMismatch,
    /// CEP:WHAT: Term depth exceeds kMaxTermDepth.
    DepthExceeded,
    /// CEP:WHAT: Cached term weight exceeds kMaxTermWeight.
    WeightExceeded,
    /// CEP:WHAT: The hash-consing table reached its load-factor bound.
    TableFull,
    /// CEP:WHAT: The arena is exhausted.
    ArenaFull,
    /// CEP:WHAT: A term reference is not readable as a term record.
    InvalidPointer,
    /// CEP:WHAT: A variable index is out of the legal range.
    VariableOutOfRange,
}

/// CEP:WHAT: Read-only view over one interned term record.
/// CEP:WHY: Views give field access without copying records and keep every read a bounds-checked slice access; the accessor methods are the only sanctioned decoding of the word layout.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: accessors are infallible because the view is constructed only from validated records.
/// CEP:ASSUMES: the slice has at least kTermFixedWords words plus the declared child count; guaranteed by intern and re-checked at construction.
/// CEP:COST: field access is 1-2 loads; child access adds a bounds check.
/// CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
/// CEP:SECURITY: all indexing is bounds-checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TermView<'a> {
    /// CEP:WHAT: The term's word array.
    /// CEP:WHY: Backing storage of the view.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: validated at view construction.
    /// CEP:COST: slice reference.
    /// CEP:EVIDENCE: unit/hot/term_test.rs.
    /// CEP:SECURITY: bounds-checked.
    words: &'a [u32],
}

impl<'a> TermView<'a> {
    // CEP:WHAT: Constructs a view over a word slice, validating the declared child count fits.
    // CEP:WHY: One validation point for every term read (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::InvalidPointer when the slice is shorter than the fixed part plus declared children.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: fuzz/term_fuzz_test.rs::truncated_records_rejected.
    // CEP:SECURITY: bounds enforcement for corrupted or truncated records.
    pub fn from_words(words: &'a [u32]) -> Result<TermView<'a>, TermError> {
        if words.len() < kTermFixedWords as usize {
            return Err(TermError::InvalidPointer);
        }
        let tag = (words[0] & kTermTagMask) as u8;
        if tag > kTermTagSort {
            // Unknown tag discriminants are corrupt records; reject them loudly (Law 6)
            // instead of aliasing them to a wrong kind.
            return Err(TermError::InvalidPointer);
        }
        let child_count = (words[0] >> kTermCountShift) as usize;
        if words.len() < kTermFixedWords as usize + child_count {
            return Err(TermError::InvalidPointer);
        }
        Ok(TermView { words })
    }

    // CEP:WHAT: Returns the term tag.
    // CEP:WHY: Tag dispatch is the first branch of every traversal; the discriminant space is validated at record construction (from_words), so this accessor is total on valid views and unknown discriminants can never be silently aliased to a wrong kind (CEP&CC Law 6, 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none on views built through from_words (which rejects unknown discriminants).
    // CEP:ASSUMES: the view passed from_words validation.
    // CEP:COST: 1 load + mask.
    // CEP:EVIDENCE: unit/hot/term_test.rs::tag_roundtrip; fuzz/term_fuzz_test.rs::truncated_records_rejected.
    // CEP:SECURITY: out-of-range tags are rejected at from_words, never silently reinterpreted.
    pub fn tag(&self) -> TermTag {
        match (self.words[0] & kTermTagMask) as u8 {
            kTermTagVariable => TermTag::Variable,
            kTermTagFunction => TermTag::Function,
            kTermTagPredicate => TermTag::Predicate,
            kTermTagEquality => TermTag::Equality,
            kTermTagApplication => TermTag::Application,
            kTermTagLambda => TermTag::Lambda,
            _ => TermTag::Sort,
        }
    }

    // CEP:WHAT: Returns the flags byte.
    // CEP:WHY: Groundness and future flags are cached here (design 5.1).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load + shift.
    // CEP:EVIDENCE: unit/hot/term_test.rs::ground_flag.
    // CEP:SECURITY: none.
    pub fn flags(&self) -> u8 {
        (self.words[0] >> kTermFlagsShift) as u8
    }

    // CEP:WHAT: Returns true when the term contains no variables.
    // CEP:WHY: Ground terms drive ground indexing and simplification decisions.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: the ground bit was computed at intern.
    // CEP:COST: 1 load + test.
    // CEP:EVIDENCE: unit/hot/term_test.rs::ground_flag.
    // CEP:SECURITY: none.
    pub fn is_ground(&self) -> bool {
        self.flags() & kTermFlagGround != 0
    }

    // CEP:WHAT: Returns the symbol ID (or variable index / sort ID, depending on tag).
    // CEP:WHY: The symbol field's meaning is tag-dependent by design 5.1; the accessor documents the overload once.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/term_test.rs::symbol_field.
    // CEP:SECURITY: consumers must bounds-check IDs against the symbol table.
    pub fn symbol(&self) -> u32 {
        self.words[1]
    }

    // CEP:WHAT: Returns the cached term depth (leaves have depth 0).
    // CEP:WHY: Design 8.3 caches order-relevant measurements at construction; depth also bounds recursion.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: computed at intern as 1 + max(child depths).
    // CEP:COST: 1 load + mask.
    // CEP:EVIDENCE: unit/hot/term_test.rs::depth_cache.
    // CEP:SECURITY: none.
    pub fn depth(&self) -> u16 {
        (self.words[kTermWordIndexDepth] & kTermDepthMask) as u16
    }

    // CEP:WHAT: Returns the cached term weight.
    // CEP:WHY: KBO comparison (design 8.3) and clause weighting (design 15.3) read the cache instead of re-summing.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: computed at intern from symbol weights; <= kMaxTermWeight.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
    // CEP:SECURITY: none.
    pub fn weight(&self) -> u32 {
        self.words[kTermWordIndexWeight]
    }

    // CEP:WHAT: Returns the child count.
    // CEP:WHY: Traversal bounds.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load + shift.
    // CEP:EVIDENCE: unit/hot/term_test.rs::word_layout.
    // CEP:SECURITY: none.
    pub fn child_count(&self) -> u16 {
        (self.words[0] >> kTermCountShift) as u16
    }

    // CEP:WHAT: Returns the i-th child handle.
    // CEP:WHY: Child access with a retained bounds check; out-of-range is a caller bug surfaced as an error, not a panic.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::InvalidPointer when i >= child_count.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare + 1 load.
    // CEP:EVIDENCE: fuzz/term_fuzz_test.rs::child_index_rejected.
    // CEP:SECURITY: bounds check retained in release.
    pub fn child(&self, index: u16) -> Result<TermPtr, TermError> {
        if index >= self.child_count() {
            return Err(TermError::InvalidPointer);
        }
        let slot = kTermFixedWords as usize + index as usize;
        Ok(TermPtr(self.words[slot]))
    }

    // CEP:WHAT: Returns all child handles as a slice-backed copy-free iterator bound.
    // CEP:WHY: Bulk child traversal (unification, printing) avoids per-child error plumbing by validating the range once.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; the view is pre-validated.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load per child.
    // CEP:EVIDENCE: unit/hot/term_test.rs::children_slice.
    // CEP:SECURITY: slice indexing is bounds-checked.
    pub fn children(&self) -> impl Iterator<Item = TermPtr> + 'a {
        let count = self.child_count() as usize;
        self.words[kTermFixedWords as usize..kTermFixedWords as usize + count]
            .iter()
            .map(|word| TermPtr(*word))
    }
}

/// CEP:WHAT: The hash-consed term store.
/// CEP:WHY: Design 5.1: one shared arena, one open-addressing table, no resizing; the store is the sole creator of TermPtr values, which is what makes offset identity equal structural identity.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see TermError.
/// CEP:ASSUMES: the table is allocated once at construction; the arena outlives the store; single-threaded use (Cell interior mutability).
/// CEP:COST: see file header; O(1) expected per intern.
/// CEP:EVIDENCE: bench CEP-BENCH-0002; all term tests.
/// CEP:SECURITY: bounded table, bounded depth, bounded weight, bounds-checked reads.
pub struct TermStore<'a> {
    /// CEP:WHAT: Shared arena reference.
    /// CEP:WHY: All term records are allocated from it (design 5.1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: arena outlives the store.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: unit/hot/term_test.rs::store_construction; property/term_property_test.rs::interning_is_canonical.
    /// CEP:SECURITY: arena is caller-controlled and bounded.
    arena: &'a Arena,
    /// CEP:WHAT: Byte range of the hash table inside the arena.
    /// CEP:WHY: Kept for diagnostics and table reads.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: allocated at construction, never resized.
    /// CEP:COST: 8-byte field.
    /// CEP:EVIDENCE: unit/hot/term_test.rs.
    /// CEP:SECURITY: fixed capacity.
    table_range: ArenaRange,
    /// CEP:WHAT: Hash table slots (kInvalidTermOffset = empty), interior-mutable.
    /// CEP:WHY: Cell slots let shared &TermStore references intern terms without locks (single-threaded discipline is compile-enforced by !Sync).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: exactly kTermHashTableCapacity slots.
    /// CEP:COST: 4 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/term_test.rs::store_construction.
    /// CEP:SECURITY: capacity-bounded.
    slots: &'a [Cell<u32>],
    /// CEP:WHAT: Number of live table entries.
    /// CEP:WHY: Load-factor enforcement (design 5.1: refuse beyond 0.65).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: interning returns TableFull at the bound.
    /// CEP:ASSUMES: increments only on insert.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/term_test.rs::table_full_after_load_factor_bound.
    /// CEP:SECURITY: probe-length bound.
    live_terms: Cell<u32>,
}

impl<'a> TermStore<'a> {
    // CEP:WHAT: Constructs the term store and its fixed hash table in the arena.
    // CEP:WHY: The table must exist before any interning and never resize (design 5.1); allocating it here makes construction order explicit and deterministic.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::ArenaFull when the table does not fit; TermError::InvalidPointer never occurs but is mapped for total function typing.
    // CEP:ASSUMES: called before the hot path starts (CEP-1 initialization phase).
    // CEP:COST: one arena allocation of kTermHashTableCapacity * 4 bytes.
    // CEP:EVIDENCE: unit/hot/term_test.rs::store_construction.
    // CEP:SECURITY: fixed, named capacity; no growth path exists.
    pub fn new(arena: &'a Arena) -> Result<TermStore<'a>, TermError> {
        let table_range = arena
            .alloc_array::<Cell<u32>>(kTermHashTableCapacity)
            .map_err(|_| TermError::ArenaFull)?;
        let slots = arena
            .array::<Cell<u32>>(table_range)
            .map_err(|_| TermError::InvalidPointer)?;
        for slot in slots.iter() {
            slot.set(kInvalidTermOffset);
        }
        Ok(TermStore {
            arena,
            table_range,
            slots,
            live_terms: Cell::new(0),
        })
    }

    // CEP:WHAT: Returns the number of interned terms.
    // CEP:WHY: Diagnostics and load-factor reporting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/term_test.rs::store_construction.
    // CEP:SECURITY: none.
    pub fn live_terms(&self) -> u32 {
        self.live_terms.get()
    }

    // CEP:WHAT: Returns a validated view of the term stored at a raw arena offset.
    // CEP:WHY: Cold diagnostics, the IR verifier, and proof output read terms serialized as offsets (for example from hash-table slots); this public entry point validates the offset exactly like term() so cold code never needs the private constructor.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::InvalidPointer when the offset is unreadable or the record is truncated.
    // CEP:ASSUMES: the offset came from TermPtr::as_u32 or a hash-table slot of this store.
    // CEP:COST: as term().
    // CEP:EVIDENCE: unit/cold/verifier_test.rs; unit/cold/debug_printer_test.rs.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn term_by_offset(&self, offset: u32) -> Result<TermView<'a>, TermError> {
        self.term(TermPtr::from_raw(offset))
    }

    // CEP:WHAT: Returns a validated view of the term referenced by ptr.
    // CEP:WHY: Every hot-path term read goes through this single bounds-checked entry point.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::InvalidPointer when the offset is out of arena bounds or the record is truncated.
    // CEP:ASSUMES: ptr was produced by intern (structurally guaranteed by the private constructor).
    // CEP:COST: 3 compares + slice construction.
    // CEP:EVIDENCE: fuzz/term_fuzz_test.rs::truncated_records_rejected.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn term(&self, ptr: TermPtr) -> Result<TermView<'a>, TermError> {
        let offset = ptr.0;
        if offset >= self.arena.used_bytes()
            || !offset.is_multiple_of(core::mem::size_of::<u32>() as u32)
        {
            return Err(TermError::InvalidPointer);
        }
        let max_words = (self.arena.used_bytes() - offset) / core::mem::size_of::<u32>() as u32;
        let range = ArenaRange::new(offset, self.arena.used_bytes())
            .map_err(|_| TermError::InvalidPointer)?;
        let words = self
            .arena
            .array::<u32>(range)
            .map_err(|_| TermError::InvalidPointer)?;
        let visible = (max_words as usize).min(words.len());
        TermView::from_words(&words[..visible])
    }

    // CEP:WHAT: Interns a variable term.
    // CEP:WHY: Variables are terms (design 5.1); clause-local dense indices keep substitution lookup flat (design 5.5).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermError::VariableOutOfRange when var_index >= kMaxVariablesPerClause; otherwise see intern().
    // CEP:ASSUMES: var_index is a per-clause dense index (design 5.5).
    // CEP:COST: see intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::variable_terms.
    // CEP:SECURITY: index bound enforced.
    pub fn intern_var(&self, var_index: u32) -> Result<TermPtr, TermError> {
        if var_index >= kMaxVariablesPerClause {
            return Err(TermError::VariableOutOfRange);
        }
        self.intern(
            TermTag::Variable,
            var_index,
            &[],
            kKboVariableWeight,
            0,
            false,
        )
    }

    // CEP:WHAT: Interns a function application f(children).
    // CEP:WHY: The dominant construction path for first-order terms.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns UnknownSymbol / SymbolKindMismatch / ArityMismatch from table validation; see intern() for the rest.
    // CEP:ASSUMES: symbols is the frozen table the caller also uses for search.
    // CEP:COST: table validation (1 lookup) plus intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::function_terms.
    // CEP:SECURITY: symbol ID and arity validated against the frozen table.
    pub fn intern_fun(
        &self,
        symbols: &SymbolTable,
        symbol_id: u32,
        children: &[TermPtr],
    ) -> Result<TermPtr, TermError> {
        let info = symbols
            .info(symbol_id)
            .map_err(|_| TermError::UnknownSymbol)?;
        if info.kind != SymbolKind::Function {
            return Err(TermError::SymbolKindMismatch);
        }
        if children.len() as u16 != info.arity {
            return Err(TermError::ArityMismatch);
        }
        self.intern_tagged(symbols, TermTag::Function, symbol_id, children)
    }

    // CEP:WHAT: Interns a predicate atom p(children).
    // CEP:WHY: Literals are built on predicate atoms (design 5.2).
    // CEP:STATUS: complete
    // CEP:FAILURE: as intern_fun().
    // CEP:ASSUMES: as intern_fun().
    // CEP:COST: as intern_fun().
    // CEP:EVIDENCE: unit/hot/term_test.rs::predicate_terms.
    // CEP:SECURITY: as intern_fun().
    pub fn intern_pred(
        &self,
        symbols: &SymbolTable,
        symbol_id: u32,
        children: &[TermPtr],
    ) -> Result<TermPtr, TermError> {
        let info = symbols
            .info(symbol_id)
            .map_err(|_| TermError::UnknownSymbol)?;
        if info.kind != SymbolKind::Predicate {
            return Err(TermError::SymbolKindMismatch);
        }
        if children.len() as u16 != info.arity {
            return Err(TermError::ArityMismatch);
        }
        self.intern_tagged(symbols, TermTag::Predicate, symbol_id, children)
    }

    // CEP:WHAT: Interns an equality atom Eq(left, right).
    // CEP:WHY: Equality is special-cased for superposition (design 5.1); it carries no symbol ID (reserved 0) and exactly two children.
    // CEP:STATUS: complete
    // CEP:FAILURE: see intern().
    // CEP:ASSUMES: the symbol field is reserved zero for equality and never participates in symbol-table lookups.
    // CEP:COST: see intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::equality_terms.
    // CEP:SECURITY: fixed arity two enforced.
    pub fn intern_eq(
        &self,
        symbols: &SymbolTable,
        left: TermPtr,
        right: TermPtr,
    ) -> Result<TermPtr, TermError> {
        self.intern_tagged(
            symbols,
            TermTag::Equality,
            kEqualityReservedSymbol,
            &[left, right],
        )
    }

    // CEP:WHAT: Interns a higher-order application App(func, arg).
    // CEP:WHY: Design 5.1 includes App for the lambda-free higher-order fragment (design 14.1).
    // CEP:STATUS: complete
    // CEP:FAILURE: see intern().
    // CEP:ASSUMES: Phase 1 builds but never decomposes applications; applicative encoding arrives with Phase 5.
    // CEP:COST: see intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::application_and_sort_terms.
    // CEP:SECURITY: fixed arity two enforced.
    pub fn intern_app(
        &self,
        symbols: &SymbolTable,
        func: TermPtr,
        arg: TermPtr,
    ) -> Result<TermPtr, TermError> {
        self.intern_tagged(
            symbols,
            TermTag::Application,
            kEqualityReservedSymbol,
            &[func, arg],
        )
    }

    // CEP:WHAT: Interns a sort annotation term Sort(sort_id).
    // CEP:WHY: Design 5.1 includes Sort as a term kind for typed fragments (TFF/THF).
    // CEP:STATUS: complete
    // CEP:FAILURE: see intern().
    // CEP:ASSUMES: the symbol field carries the SortId; no symbol-table validation happens here (sorts are validated by the builder).
    // CEP:COST: see intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::application_and_sort_terms.
    // CEP:SECURITY: none beyond intern().
    pub fn intern_sort(&self, sort_id: u32) -> Result<TermPtr, TermError> {
        self.intern(TermTag::Sort, sort_id, &[], kDefaultSymbolWeight, 0, true)
    }

    // CEP:WHAT: Validates children, computes cached depth/weight/groundness, then interns a compound term.
    // CEP:WHY: Centralizing the per-tag metadata computation guarantees every interned term carries correct caches (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates DepthExceeded / WeightExceeded / InvalidPointer from child reads; see intern().
    // CEP:ASSUMES: children were interned by this store; tag-fixed terms (Equality, Application, Lambda) carry no symbol-table entry and use the default symbol weight.
    // CEP:COST: O(children) reads plus intern().
    // CEP:EVIDENCE: unit/hot/term_test.rs::depth_cache and weight_accumulation.
    // CEP:SECURITY: depth and weight bounds enforced here.
    fn intern_tagged(
        &self,
        symbols: &SymbolTable,
        tag: TermTag,
        symbol_id: u32,
        children: &[TermPtr],
    ) -> Result<TermPtr, TermError> {
        if children.len() > kMaxSymbolArity as usize {
            return Err(TermError::ArityMismatch);
        }
        let mut depth: u32 = 0;
        let base_weight: u64 = match tag {
            TermTag::Function | TermTag::Predicate => symbols
                .symbol_weight(symbol_id)
                .map_err(|_| TermError::UnknownSymbol)?
                as u64,
            _ => kDefaultSymbolWeight as u64,
        };
        let mut weight: u64 = base_weight;
        let mut ground = true;
        for child in children.iter() {
            let view = self.term(*child)?;
            let child_depth = view.depth() as u32 + 1;
            if child_depth > depth {
                depth = child_depth;
            }
            weight += view.weight() as u64;
            if !view.is_ground() {
                ground = false;
            }
        }
        if depth > kMaxTermDepth as u32 {
            return Err(TermError::DepthExceeded);
        }
        if weight > kMaxTermWeight as u64 {
            return Err(TermError::WeightExceeded);
        }
        self.intern(
            tag,
            symbol_id,
            children,
            weight as u32,
            depth as u16,
            ground,
        )
    }

    // CEP:WHAT: The hash-consing core: probe for a structurally equal term, insert a new record on miss.
    // CEP:WHY: This function implements design 5.1: FNV-1a over (tag, symbol, count, child offsets), linear probing, insert-on-miss, no resizing, load-factor bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TableFull at the load-factor bound, ArenaFull when the record does not fit; never panics.
    // CEP:ASSUMES: child offsets are interned handles (hash-consing makes offset equality structural equality); the table capacity is a power of two.
    // CEP:COST: O(n) hash over children, 1 probe expected (load factor 0.65), one arena write on miss; measured in bench CEP-BENCH-0002.
    // CEP:EVIDENCE: bench CEP-BENCH-0002; property/term_property_test.rs (interning_is_canonical, hash_is_deterministic).
    // CEP:SECURITY: bounded probe chain (load-factor bound), bounded record size.
    // CEP:OPTIMAL: not-optimal
    // CEP:OPTNOTE: the candidate comparison re-reads the record on every probe hit; caching the hash word in the record would shorten misses at the cost of 4 bytes per term; deferred, ticket CEP-1010.
    fn intern(
        &self,
        tag: TermTag,
        symbol_id: u32,
        children: &[TermPtr],
        weight: u32,
        depth: u16,
        ground: bool,
    ) -> Result<TermPtr, TermError> {
        let child_count = children.len() as u32;
        let word0 = (tag as u32)
            | (if ground { kTermFlagGround as u32 } else { 0 } << kTermFlagsShift)
            | (child_count << kTermCountShift);
        let word2 = depth as u32;
        let mut hash = kFnvOffsetBasis32;
        hash = (hash ^ word0).wrapping_mul(kFnvPrime32);
        hash = (hash ^ symbol_id).wrapping_mul(kFnvPrime32);
        hash = (hash ^ word2).wrapping_mul(kFnvPrime32);
        for child in children.iter() {
            hash = (hash ^ child.0).wrapping_mul(kFnvPrime32);
        }
        let mask = kTermHashTableCapacity - 1;
        let mut slot = hash & mask;
        loop {
            let occupied = self.slots[slot as usize].get();
            if occupied == kInvalidTermOffset {
                break;
            }
            if self.records_equal(occupied, word0, symbol_id, word2, children)? {
                return Ok(TermPtr(occupied));
            }
            slot = (slot + 1) & mask;
        }
        let live_after = self.live_terms.get() + 1;
        let bound = (kTermHashTableCapacity / kPercentScale) * kTermHashTableLoadFactorPercent;
        if live_after > bound {
            return Err(TermError::TableFull);
        }
        let total_words = kTermFixedWords + child_count;
        let range = self
            .arena
            .alloc_bytes(
                total_words * core::mem::size_of::<u32>() as u32,
                core::mem::align_of::<u32>() as u32,
            )
            .map_err(|_| TermError::ArenaFull)?;
        let words = self
            .arena
            .array_mut::<u32>(range)
            .map_err(|_| TermError::ArenaFull)?;
        words[0] = word0;
        words[1] = symbol_id;
        words[kTermWordIndexDepth] = word2;
        words[kTermWordIndexWeight] = weight;
        let child_base = kTermFixedWords as usize;
        for (index, child) in children.iter().enumerate() {
            words[child_base + index] = child.0;
        }
        self.slots[slot as usize].set(range.start);
        self.live_terms.set(live_after);
        Ok(TermPtr(range.start))
    }

    // CEP:WHAT: Compares a table candidate against a prospective record.
    // CEP:WHY: Probe hits must be verified structurally (hash equality is not identity); by the hash-consing invariant it suffices to compare tag/flags/count/symbol and child offsets.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates InvalidPointer when the candidate record is unreadable (corruption detector).
    // CEP:ASSUMES: occupied offset is a term record produced by this store.
    // CEP:COST: O(children) compares.
    // CEP:EVIDENCE: property/term_property_test.rs::interning_is_canonical.
    // CEP:SECURITY: unreadable candidates surface as errors, never as UB.
    fn records_equal(
        &self,
        occupied: u32,
        word0: u32,
        symbol_id: u32,
        word2: u32,
        children: &[TermPtr],
    ) -> Result<bool, TermError> {
        let candidate = self.term(TermPtr(occupied))?;
        let candidate_count = candidate.child_count() as u32;
        if candidate_count != children.len() as u32 {
            return Ok(false);
        }
        if candidate.words[0] != word0
            || candidate.words[1] != symbol_id
            || candidate.words[kTermWordIndexDepth] != word2
        {
            return Ok(false);
        }
        for (index, child) in children.iter().enumerate() {
            if candidate.words[kTermFixedWords as usize + index] != child.0 {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // CEP:WHAT: Returns true iff two handles reference the same term.
    // CEP:WHY: Documenting that equality is offset equality makes the hash-consing contract explicit at use sites (design 5.1).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: both handles were produced by this store.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: property/term_property_test.rs::interning_is_canonical.
    // CEP:SECURITY: none.
    pub fn term_equal(&self, left: TermPtr, right: TermPtr) -> bool {
        left == right
    }

    // CEP:WHAT: Returns the byte range of the hash table (diagnostics).
    // CEP:WHY: Cold diagnostics and the verifier need the table location.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/cold/verifier_test.rs.
    // CEP:SECURITY: none.
    pub fn table_range(&self) -> ArenaRange {
        self.table_range
    }
}

/// CEP:WHAT: Reserved symbol field value for tag-fixed terms (Equality, Application) that carry no symbol ID.
/// CEP:WHY: The word layout requires a symbol word for every tag; a named zero constant documents that the field is unused for those tags instead of leaving a bare 0 at call sites (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: never passed to the symbol table.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::equality_terms.
/// CEP:SECURITY: none.
pub const kEqualityReservedSymbol: u32 = 0;
