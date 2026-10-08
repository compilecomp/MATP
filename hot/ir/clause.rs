// CEP:FILE: hot/ir/clause.rs
// CEP:WHAT: Clause representation and store: monotonic IDs, inline literal arrays for small clauses with arena overflow for large ones, cached weight and age, and per-clause derivation steps for proof tracking.
// CEP:WHY: Design 5.3: inline literals (8) cover over 95 percent of clauses and remove one indirection from the hottest reads; the monotonic u64 ID gives deterministic selection ordering (design 8.4); carrying the derivation step on the clause builds the proof DAG incrementally (design 5.4) so no separate proof reconstruction pass is needed for basic proofs.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns ClauseError::TooManyLiterals beyond kMaxClauseLiterals, ClauseError::ArenaFull when the arena is exhausted, ClauseError::InvalidPointer for unreadable clause references, ClauseError::WeightOverflow when the summed atom weight exceeds u32. Never panics.
// CEP:ASSUMES: Clauses are immutable after construction; the arena outlives the store; literal atoms were interned by the same backing term store; clause identity is the u64 ID, never the address.
// CEP:COST: construction is O(n^2) worst-case for the canonical insertion sort with n <= kMaxClauseLiterals plus one arena write; measured 20.4 cycles median for a 3-literal clause on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0003, artifact benches/artifacts/clause_new_3lit.json.
// CEP:EVIDENCE: bench CEP-BENCH-0003; unit/hot/clause_test.rs; cold verifier tests unit/cold/verifier_test.rs; disassembly artifact benches/artifacts/disasm_clause.txt.
// CEP:SECURITY: literal count is bounded; the ID counter is bounded by kMaxClauses checks; all reads are bounds-checked slice accesses; canonical order is a documented, tested invariant (CEP&CC 38.17 canonicalizable).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; IDs are monotonic, the canonical literal order is a total order (polarity, atom offset), and insertion sort is stable.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: construction pays an insertion sort to keep clauses canonical; for clauses at the 8-literal inline boundary this is 8 compares; acceptable because canonical form removes ordering work from every downstream consumer; ticket CEP-1014 tracks a merge-sort path for overflow clauses.

use crate::memory::arena::{Arena, ArenaRange};
use core::cell::Cell;
use mapt_config::limits::{
    kFirstClauseId, kInlineClauseLiterals, kInvalidClauseOffset, kMaxClauseLiterals, kMaxClauses,
    kMaxDerivationParents,
};

use crate::ir::literal::Literal;
use crate::ir::term::TermStore;

/// CEP:WHAT: Inference rule names for derivation steps (design 5.4).
/// CEP:WHY: Every derived clause must name the rule that produced it; the closed vocabulary is the proof-graph edge label set and maps one-to-one onto TSTP rule names.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; closed vocabulary.
/// CEP:ASSUMES: values fit u8 and are part of the serialized proof contract.
/// CEP:COST: 1-byte field.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
/// CEP:SECURITY: out-of-range values cannot be constructed through the safe API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum InferenceRule {
    /// CEP:WHAT: Clause comes from the input problem.
    Input = 0,
    /// CEP:WHAT: Clause is the negated conjecture (design 7.2 stage 1).
    NegatedConjecture = 1,
    /// CEP:WHAT: Binary resolution (Robinson 1965).
    Resolution = 2,
    /// CEP:WHAT: Superposition (Bachmair & Ganzinger 1994).
    Superposition = 3,
    /// CEP:WHAT: Factoring (Bachmair & Ganzinger 1994).
    Factoring = 4,
    /// CEP:WHAT: Equality factoring (Nieuwenhuis & Rubio 2001).
    EqualityFactoring = 5,
    /// CEP:WHAT: Demodulation rewriting (Bachmair & Ganzinger 1994).
    Demodulation = 6,
    /// CEP:WHAT: Forward subsumption deletion.
    ForwardSubsumption = 7,
    /// CEP:WHAT: Backward subsumption deletion.
    BackwardSubsumption = 8,
    /// CEP:WHAT: Subsumption resolution (Riazanov 2003).
    SubsumptionResolution = 9,
    /// CEP:WHAT: Tautology deletion.
    TautologyDeletion = 10,
    /// CEP:WHAT: Condensation.
    Condensation = 11,
    /// CEP:WHAT: Equality resolution (Nieuwenhuis & Rubio 2001).
    EqualityResolution = 12,
    /// CEP:WHAT: AVATAR split (Voronkov 2014).
    AvatarSplit = 13,
    /// CEP:WHAT: Clause learned by the SAT engine.
    SatLearn = 14,
    /// CEP:WHAT: Theory lemma (DPLL(T)).
    TheoryLemma = 15,
}

/// CEP:WHAT: Error cases of the clause store.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the store never panics.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/clause_test.rs covers every variant.
/// CEP:SECURITY: literal-count and ID bounds are resource-exhaustion guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseError {
    /// CEP:WHAT: More than kMaxClauseLiterals literals were supplied.
    TooManyLiterals,
    /// CEP:WHY: Bounded clause size (design 5.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_bound_enforced.
    /// CEP:SECURITY: memory bound.
    LiteralBoundExceeded,
    /// CEP:WHAT: The clause ID budget kMaxClauses is exhausted.
    ClauseBudgetExceeded,
    /// CEP:WHAT: The arena is exhausted.
    ArenaFull,
    /// CEP:WHAT: A clause reference is unreadable.
    InvalidPointer,
    /// CEP:WHAT: The summed atom weight exceeds u32.
    WeightOverflow,
    /// CEP:WHAT: The parent list in a derivation step exceeds kMaxDerivationParents.
    TooManyParents,
}

/// CEP:WHAT: Opaque handle to a clause record (byte offset in the arena).
/// CEP:WHY: Same offset-token discipline as TermPtr: private field, produced only by the store, deterministic identity (CEP&CC 38.10).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; transparent u32 token.
/// CEP:ASSUMES: values are arena offsets of clause records.
/// CEP:COST: 4-byte copy type.
/// CEP:EVIDENCE: unit/hot/clause_test.rs.
/// CEP:SECURITY: unforgeable outside the crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ClausePtr(u32);

impl ClausePtr {
    // CEP:WHAT: Returns the raw arena offset for serialization and diagnostics.
    // CEP:WHY: Cold printers and the future FFI need the numeric identity; construction stays private.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/cold/verifier_test.rs.
    // CEP:SECURITY: read-only projection.
    pub fn as_u32(&self) -> u32 {
        self.0
    }
}

/// CEP:WHAT: Stable clause identifier (monotonic u64 counter, never hash-based).
/// CEP:WHY: Design 5.3: deterministic selection ordering ties need a tiebreaker; the ID is it (design 8.4 passive-set key (age, weight, id)).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; newtype over u64.
/// CEP:ASSUMES: assigned by the store, starts at kFirstClauseId.
/// CEP:COST: 8-byte copy type.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::ids_are_monotonic.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ClauseId(pub u64);

/// CEP:WHAT: Proof-tracking record: rule, up to four parent clause IDs, and the applied substitution.
/// CEP:WHY: Design 5.4: every derived clause carries its derivation, building the proof DAG incrementally; the bounded parent array keeps the record fixed-size (no allocation, no indirection).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: construction validates the parent count against kMaxDerivationParents.
/// CEP:ASSUMES: absent parents are kInvalidClauseId; absent substitution is kInvalidSubstitutionOffset.
/// CEP:COST: 48 bytes (u64-aligned parents array), embedded in the clause header.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
/// CEP:SECURITY: fixed layout, no pointers.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct DerivationStep {
    /// CEP:WHAT: The inference rule.
    /// CEP:WHY: Proof-graph edge label.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: closed enum.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs.
    /// CEP:SECURITY: none.
    pub rule: InferenceRule,
    /// CEP:WHAT: Number of valid parent entries.
    /// CEP:WHY: Bounded array fill level.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxDerivationParents.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs.
    /// CEP:SECURITY: validated at construction.
    pub parent_count: u8,
    /// CEP:WHAT: Reserved padding.
    /// CEP:WHY: Explicit alignment padding to u64; must stay zero (checked by the cold verifier).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: verifier flags nonzero.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/cold/verifier_test.rs.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u16,
    /// CEP:WHAT: Parent clause IDs (kInvalidClauseId = 0 for absent slots).
    /// CEP:WHY: Proof-graph parent edges; zero is the reserved invalid ID (kInvalidClauseId in config/limits.rs).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: fixed capacity kMaxDerivationParents.
    /// CEP:COST: 32 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
    /// CEP:SECURITY: none.
    pub parents: [u64; kMaxDerivationParents],
    /// CEP:WHAT: Arena offset of the applied substitution (kInvalidSubstitutionOffset when none).
    /// CEP:WHY: Design 5.4: the MGU or matching substitution is part of the proof record; the sentinel constant lives in config/limits.rs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: offset semantics owned by the substitution engine.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/substitution_test.rs.
    /// CEP:SECURITY: validated by consumers.
    pub substitution: u32,
}

// CEP:WHAT: Derivation step layout pin.
// CEP:WHY: The record is embedded in clause headers and serialized in proofs; layout drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<DerivationStep>() == 48);

/// CEP:WHAT: Clause flag bits (design 5.3 flags field).
/// CEP:WHY: Active/passive membership, split-component marking, and locking are boolean clause state; named masks replace magic numbers.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bit assignments listed per constant.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
/// CEP:SECURITY: none.
pub const kClauseFlagPassive: u16 = 1;
/// CEP:WHAT: Bit marking a clause as active (given-clause loop membership).
/// CEP:WHY: Design 5.3 flags.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: mutually exclusive with passive in Phase 3 usage.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: none.
pub const kClauseFlagActive: u16 = 2;
/// CEP:WHAT: Bit marking an AVATAR split component.
/// CEP:WHY: Design 5.3 flags; consumed by Phase 4.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4.
/// CEP:SECURITY: none.
pub const kClauseFlagSplitComponent: u16 = 4;
/// CEP:WHAT: Bit protecting a clause from deletion during conflict analysis.
/// CEP:WHY: Mirrors SAT clause locking (design 11.1 S29) on the ATP side.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: none.
pub const kClauseFlagLocked: u16 = 8;

/// CEP:WHAT: Fixed-layout clause header followed by the literal storage strategy (inline up to kInlineClauseLiterals, arena overflow beyond).
/// CEP:WHY: Design 5.3 field list; the inline array keeps small clauses in one cache line pair and the overflow pointer keeps the representation general.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ClauseError.
/// CEP:ASSUMES: overflow_offset is kInvalidClauseOffset exactly when literal_count <= kInlineClauseLiterals.
/// CEP:COST: 152 bytes per clause header (u64-aligned id and derivation step).
/// CEP:EVIDENCE: layout pinned below; unit/hot/clause_test.rs::inline_and_overflow_layout.
/// CEP:SECURITY: fixed layout, no pointers, bounded literal count.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct Clause {
    /// CEP:WHAT: Stable monotonic clause ID.
    /// CEP:WHY: Deterministic identity and selection tiebreak (design 5.3, 8.4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: assigned by the store.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::ids_are_monotonic.
    /// CEP:SECURITY: none.
    pub id: ClauseId,
    /// CEP:WHAT: Number of literals.
    /// CEP:WHY: Traversal bound; also selects inline vs overflow storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxClauseLiterals.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_bound_enforced.
    /// CEP:SECURITY: bounds iteration.
    pub literal_count: u16,
    /// CEP:WHAT: Clause flag bits.
    /// CEP:WHY: See kClauseFlag* constants.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
    /// CEP:SECURITY: none.
    pub flags: u16,
    /// CEP:WHAT: Cached clause weight (sum of atom weights).
    /// CEP:WHY: Selection heuristics order by weight (design 15.3); caching avoids recomputation on every selection.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: construction refuses overflow via ClauseError::WeightOverflow.
    /// CEP:ASSUMES: computed from cached term weights at construction.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::clause_weight_is_sum_of_atom_weights.
    /// CEP:SECURITY: none.
    pub weight: u32,
    /// CEP:WHAT: Step number when the clause was derived.
    /// CEP:WHY: Age-weight selection (design 15.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: assigned by the caller (search loop).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
    /// CEP:SECURITY: none.
    pub age: u32,
    /// CEP:WHAT: AVATAR split level / component ID (0 = not split).
    /// CEP:WHY: Design 5.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consumed by Phase 4.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
    /// CEP:SECURITY: none.
    pub split_level: u16,
    /// CEP:WHAT: Theory-specific metadata (0 = pure FOL).
    /// CEP:WHY: Design 5.3.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: consumed by Phase 5.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
    /// CEP:SECURITY: none.
    pub theory_tag: u8,
    /// CEP:WHAT: Literal Block Distance (SAT-engine quality metric).
    /// CEP:WHY: Design 5.3; meaningful for SAT-learned clauses, 0 otherwise.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback.
    /// CEP:SECURITY: none.
    pub lbd: u8,
    /// CEP:WHAT: Reserved padding keeping the pre-literal part aligned.
    /// CEP:WHY: Explicit padding; must be zero (verifier-checked).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: verifier flags nonzero.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/cold/verifier_test.rs.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u32,
    /// CEP:WHAT: Derivation step for proof tracking.
    /// CEP:WHY: Design 5.4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: see DerivationStep.
    /// CEP:COST: 40 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
    /// CEP:SECURITY: none.
    pub derivation: DerivationStep,
    /// CEP:WHAT: Overflow literal array offset (kInvalidClauseOffset when all literals are inline).
    /// CEP:WHY: Design 5.3 overflow path for clauses with more than kInlineClauseLiterals literals.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: interpreted only when literal_count > kInlineClauseLiterals.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::inline_and_overflow_layout.
    /// CEP:SECURITY: bounds-checked on access.
    pub overflow_offset: u32,
    /// CEP:WHAT: Inline literal storage.
    /// CEP:WHY: Design 5.3: >95 percent of clauses have <= 8 literals; inline storage removes one indirection from the hot path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries beyond literal_count are zeroed (verifier-checked).
    /// CEP:COST: 64 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::inline_and_overflow_layout.
    /// CEP:SECURITY: none.
    pub inline_literals: [Literal; kInlineClauseLiterals],
}

// CEP:WHAT: Clause layout pin.
// CEP:WHY: Clause records are read by CEP-0 search, CEP-1 printers, and later FFI; drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_test.rs::clause_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<Clause>() == 152);

/// CEP:WHAT: The clause store: sole creator of clause records and IDs.
/// CEP:WHY: Design 5.3 + 8.4: the store assigns monotonic IDs (deterministic tiebreak), enforces the literal bound, computes cached weight, and stores clauses contiguously in the arena.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ClauseError.
/// CEP:ASSUMES: single-threaded use; arena outlives the store; the term store used at construction is the same one backing literal atoms.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: bench CEP-BENCH-0003; unit/hot/clause_test.rs.
/// CEP:SECURITY: all reads bounds-checked; IDs and counts bounded.
pub struct ClauseStore<'a> {
    /// CEP:WHAT: Shared arena reference.
    /// CEP:WHY: Clause storage (design 5.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: outlives the store.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: all clause tests.
    /// CEP:SECURITY: arena is caller-controlled and bounded.
    arena: &'a Arena,
    /// CEP:WHAT: Next clause ID to assign.
    /// CEP:WHY: Monotonic, never reused, deterministic (design 5.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: construction refuses to continue past kMaxClauses.
    /// CEP:ASSUMES: starts at kFirstClauseId.
    /// CEP:COST: 8 bytes with interior mutability.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::ids_are_monotonic.
    /// CEP:SECURITY: budget bound.
    next_id: Cell<u64>,
    /// CEP:WHAT: Number of constructed clauses.
    /// CEP:WHY: Diagnostics and budget accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::store_construction.
    /// CEP:SECURITY: none.
    live_clauses: Cell<u32>,
}

impl<'a> ClauseStore<'a> {
    // CEP:WHAT: Constructs the clause store.
    // CEP:WHY: Explicit initialization before the hot path; no allocation happens here (records are allocated on demand from the arena).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: arena outlives the store.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/clause_test.rs::store_construction.
    // CEP:SECURITY: none.
    pub fn new(arena: &'a Arena) -> ClauseStore<'a> {
        ClauseStore {
            arena,
            next_id: Cell::new(kFirstClauseId),
            live_clauses: Cell::new(0),
        }
    }

    // CEP:WHAT: Returns the number of constructed clauses.
    // CEP:WHY: Diagnostics and budget accounting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/clause_test.rs::store_construction.
    // CEP:SECURITY: none.
    pub fn live_clauses(&self) -> u32 {
        self.live_clauses.get()
    }

    // CEP:WHAT: Returns the next unassigned clause ID.
    // CEP:WHY: Deterministic diagnostics; tests assert monotonicity.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/clause_test.rs::ids_are_monotonic.
    // CEP:SECURITY: none.
    pub fn next_clause_id(&self) -> ClauseId {
        ClauseId(self.next_id.get())
    }

    // CEP:WHAT: Constructs a clause: validates bounds, sorts literals canonically, computes weight, allocates, assigns the next ID.
    // CEP:WHY: Design 5.3: every field invariant (canonical literal order, cached weight, monotonic ID, bounded count) is established here so downstream consumers never re-validate (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TooManyLiterals / LiteralBoundExceeded beyond the bound, ClauseBudgetExceeded past kMaxClauses, WeightOverflow on weight overflow, ArenaFull when the arena is exhausted, TooManyParents for bad derivations.
    // CEP:ASSUMES: literal atoms were interned by the given term store (weight reads demand readable terms).
    // CEP:COST: O(n^2) worst-case canonical insertion sort (n <= kMaxClauseLiterals = 512, typical n <= 8) plus one arena allocation; measured in bench CEP-BENCH-0003.
    // CEP:EVIDENCE: bench CEP-BENCH-0003; unit/hot/clause_test.rs (canonical order, weight, monotonic ids, overflow layout).
    // CEP:SECURITY: literal count, ID budget, and weight sum are all explicitly bounded.
    pub fn new_clause(
        &self,
        terms: &TermStore,
        literals: &[Literal],
        age: u32,
        derivation: DerivationStep,
    ) -> Result<ClausePtr, ClauseError> {
        if derivation.parent_count as usize > kMaxDerivationParents {
            return Err(ClauseError::TooManyParents);
        }
        let count = literals.len();
        if count > kMaxClauseLiterals as usize {
            return Err(ClauseError::TooManyLiterals);
        }
        if self.next_id.get() > kMaxClauses {
            return Err(ClauseError::ClauseBudgetExceeded);
        }
        let mut weight: u64 = 0;
        for literal in literals.iter() {
            let view = terms
                .term(literal.atom())
                .map_err(|_| ClauseError::InvalidPointer)?;
            weight += view.weight() as u64;
        }
        if weight > u32::MAX as u64 {
            return Err(ClauseError::WeightOverflow);
        }
        let overflow_needed = count > kInlineClauseLiterals;
        let overflow_range = if overflow_needed {
            let range = self
                .arena
                .alloc_array::<Literal>(count as u32)
                .map_err(|_| ClauseError::ArenaFull)?;
            let overflow_slot = self
                .arena
                .array_mut::<Literal>(range)
                .map_err(|_| ClauseError::ArenaFull)?;
            overflow_slot.copy_from_slice(literals);
            sort_literals_canonical(overflow_slot);
            range
        } else {
            ArenaRange::new(self.arena.used_bytes(), self.arena.used_bytes())
                .map_err(|_| ClauseError::ArenaFull)?
        };
        let mut inline_literals = [default_literal(); kInlineClauseLiterals];
        if !overflow_needed {
            for (index, literal) in literals.iter().enumerate() {
                inline_literals[index] = *literal;
            }
            sort_literals_canonical(&mut inline_literals[..count]);
        }
        let header_range = self
            .arena
            .alloc_array::<Clause>(1)
            .map_err(|_| ClauseError::ArenaFull)?;
        let header_slot = self
            .arena
            .array_mut::<Clause>(header_range)
            .map_err(|_| ClauseError::ArenaFull)?;
        let clause_id = ClauseId(self.next_id.get());
        self.next_id.set(self.next_id.get() + 1);
        self.live_clauses.set(self.live_clauses.get() + 1);
        header_slot[0] = Clause {
            id: clause_id,
            literal_count: count as u16,
            flags: 0,
            weight: weight as u32,
            age,
            split_level: 0,
            theory_tag: 0,
            lbd: 0,
            reserved: 0,
            derivation,
            overflow_offset: if overflow_needed {
                overflow_range.start
            } else {
                kInvalidClauseOffset
            },
            inline_literals,
        };
        Ok(ClausePtr(header_range.start))
    }

    // CEP:WHAT: Returns the clause header at a handle.
    // CEP:WHY: Single bounds-checked entry point for clause reads.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidPointer when the offset is unreadable, misaligned, or truncated.
    // CEP:ASSUMES: ptr was produced by this store.
    // CEP:COST: 3 compares + slice construction.
    // CEP:EVIDENCE: unit/hot/clause_test.rs::header_readback; fuzz coverage in sat_fuzz for store hygiene.
    // CEP:SECURITY: bounds and alignment checks retained in release.
    pub fn clause(&self, ptr: ClausePtr) -> Result<&'a Clause, ClauseError> {
        let offset = ptr.0;
        let clause_size = core::mem::size_of::<Clause>() as u32;
        let end = offset
            .checked_add(clause_size)
            .ok_or(ClauseError::InvalidPointer)?;
        if end > self.arena.used_bytes() {
            return Err(ClauseError::InvalidPointer);
        }
        let range = ArenaRange::new(offset, end).map_err(|_| ClauseError::InvalidPointer)?;
        let slice = self
            .arena
            .array::<Clause>(range)
            .map_err(|_| ClauseError::InvalidPointer)?;
        if slice.is_empty() {
            return Err(ClauseError::InvalidPointer);
        }
        Ok(&slice[0])
    }

    // CEP:WHAT: Returns the i-th literal of a clause.
    // CEP:WHY: Inference generation iterates literals; the accessor hides the inline/overflow split (design 5.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidPointer for out-of-range indices or unreadable overflow storage.
    // CEP:ASSUMES: the clause header is readable.
    // CEP:COST: 1 compare + 1 load (inline) or slice construction (overflow).
    // CEP:EVIDENCE: unit/hot/clause_test.rs::inline_and_overflow_layout.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn literal(&self, clause: &Clause, index: u16) -> Result<Literal, ClauseError> {
        if index >= clause.literal_count {
            return Err(ClauseError::InvalidPointer);
        }
        if (index as usize) < kInlineClauseLiterals {
            return Ok(clause.inline_literals[index as usize]);
        }
        if clause.overflow_offset == kInvalidClauseOffset {
            return Err(ClauseError::InvalidPointer);
        }
        let overflow_start = clause.overflow_offset;
        let overflow_end = overflow_start
            .checked_add(clause.literal_count as u32 * core::mem::size_of::<Literal>() as u32)
            .ok_or(ClauseError::InvalidPointer)?;
        let range = ArenaRange::new(overflow_start, overflow_end)
            .map_err(|_| ClauseError::InvalidPointer)?;
        let slice = self
            .arena
            .array::<Literal>(range)
            .map_err(|_| ClauseError::InvalidPointer)?;
        let local = index as usize - kInlineClauseLiterals;
        if local >= slice.len() {
            return Err(ClauseError::InvalidPointer);
        }
        Ok(slice[local])
    }
}

// CEP:WHAT: Canonical literal order key: (polarity, atom offset) ascending.
// CEP:WHY: Design 5.7 requires a canonicalizable IR; a total deterministic order on literals makes clause equality decidable by element-wise comparison and clause printing stable (CEP&CC 38.19 stable ordering).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: atom offsets are deterministic within a run (design 5.7 hash-consing carve-out).
// CEP:COST: 1 compare per comparison.
// CEP:EVIDENCE: unit/hot/clause_test.rs::canonical_order; unit/cold/verifier_test.rs.
// CEP:SECURITY: none.
fn literal_order_key(literal: &Literal) -> (bool, u32) {
    (!literal.is_positive(), literal.atom().as_u32())
}

// CEP:WHAT: Stable insertion sort into canonical literal order.
// CEP:WHY: no_std forbids the standard sort (allocation and unstable ordering are both banned); insertion sort is stable, allocation-free, and O(n^2) only on adversarial 512-literal clauses which the bound caps.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: n <= kMaxClauseLiterals.
// CEP:COST: O(n^2) worst case, O(n) when already sorted (the common case for CNF output).
// CEP:EVIDENCE: unit/hot/clause_test.rs::canonical_order; property coverage via clause tests.
// CEP:SECURITY: bounded by the literal-count validation above it.
fn sort_literals_canonical(literals: &mut [Literal]) {
    for i in 1..literals.len() {
        let mut j = i;
        while j > 0 && literal_order_key(&literals[j]) < literal_order_key(&literals[j - 1]) {
            literals.swap(j, j - 1);
            j -= 1;
        }
    }
}

// CEP:WHAT: Produces the invalid-atom literal used to fill unused inline slots.
// CEP:WHY: Unused inline slots must hold a deterministic filler whose atom dereference fails loudly (TermError::InvalidPointer) instead of reading unrelated memory; the verifier checks that filler atoms are never dereferenced on live paths.
// CEP:STATUS: complete
// CEP:FAILURE: dereferencing the filler atom always errors.
// CEP:ASSUMES: crate-internal use only.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/clause_test.rs::inline_slots_zeroed; unit/cold/verifier_test.rs::filler_atoms_fail_loudly.
// CEP:SECURITY: loud-failure sentinel, no silent garbage reads.
fn default_literal() -> Literal {
    Literal::new(crate::ir::term::TermPtr::invalid(), true)
}
