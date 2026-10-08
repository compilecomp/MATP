// CEP:FILE: hot/sat/clause.rs
// CEP:WHAT: SAT clause storage: length-prefixed clause records in the arena with two watched literals at positions 0 and 1 and intrusive watch-list links embedded in each record.
// CEP:WHY: Design 11.1 S3/S4 and 11.3: clauses are arena-backed and generation-tagged; the watched-literal scheme (Chaff, Moskewicz et al. DAC 2001; CaDiCaL, Biere SAT 2020) gives O(1) amortized propagation cost only if watch traversal touches no separately allocated nodes, so each clause carries its own two next-pointers; keeping the watched literals at positions 0 and 1 makes the "which slot watches this literal" test a single compare pair.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SatClauseError::TooManyLiterals beyond the bound, EmptyClause for zero-length clauses, VariableOutOfRange for out-of-declared-range variables, LearntBudgetExceeded past kSatMaxLearntClauses, ArenaFull on exhaustion, InvalidClauseOffset for unreadable records. Never panics.
// CEP:ASSUMES: Clause records are immutable except for literal swaps at positions 0/1 and the two next_in_watch links; watched literals are always positions 0 and 1; learnt counting covers all learnt clauses ever attached (deletion policy is Phase 2).
// CEP:COST: creation is O(length) validation plus one arena allocation; literal reads are 1 compare + 1 load; measured within bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: unit/hot/sat_watch_test.rs; unit/hot/sat_bcp_test.rs; fuzz/sat_fuzz_test.rs; bench CEP-BENCH-0005.
// CEP:SECURITY: every offset and index is bounds-checked before access; variable range validated against the declared count.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; offsets are monotonic arena positions and literal order is caller-defined.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: literal access pays one bounds check per read; a raw pointer scheme would save the compare but violate the bounds-proof rule (CEP&CC 22.4); the check is required cost; ticket CEP-1015 tracks a batched read API for BCP.

use crate::memory::arena::{Arena, ArenaRange};
use crate::sat::literal::SatLiteral;
use core::cell::Cell;
use mapt_config::limits::{
    kInvalidClauseOffset, kMaxSatClauseLiterals, kMaxSatVariables, kSatMaxLearntClauses,
};

/// CEP:WHAT: Watch slots per SAT clause (one per watched literal).
/// CEP:WHY: Named array size instead of a raw 2 (CEP&CC 11.3); matches the two watched literals of design 11.3.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: exactly two watched literals per clause of length >= 2.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
/// CEP:SECURITY: none.
pub const kSatWatchSlotsPerClause: usize = 2;

/// CEP:WHAT: Error cases of SAT clause storage.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs covers every variant.
/// CEP:SECURITY: bounds are denial-of-service guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatClauseError {
    /// CEP:WHAT: Clause has zero literals (input contradiction).
    EmptyClause,
    /// CEP:WHAT: Clause exceeds kMaxSatClauseLiterals literals.
    TooManyLiterals,
    /// CEP:WHAT: A literal's variable exceeds the declared variable count.
    VariableOutOfRange,
    /// CEP:WHAT: Learnt-clause budget kSatMaxLearntClauses exhausted (deletion policy is Phase 2).
    LearntBudgetExceeded,
    /// CEP:WHAT: Arena exhausted.
    ArenaFull,
    /// CEP:WHAT: Clause offset unreadable or malformed.
    InvalidClauseOffset,
}

/// CEP:WHAT: Clause flag bits.
/// CEP:WHY: Learnt status and locking (design 11.1 S29) are per-clause booleans; named masks replace magic numbers.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bit assignments below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::learnt_budget_enforced.
/// CEP:SECURITY: none.
pub const kSatClauseFlagLearnt: u16 = 1;
/// CEP:WHAT: Lock bit protecting a clause from deletion during conflict analysis.
/// CEP:WHY: Design 11.1 S29; consumed by Phase 2.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 2.
/// CEP:SECURITY: none.
pub const kSatClauseFlagLocked: u16 = 2;

/// CEP:WHAT: Fixed clause header stored immediately before the literal array.
/// CEP:WHY: Length, flags, LBD, and the two intrusive watch links must be readable without touching the literals; a 16-byte header keeps the record aligned and self-describing.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: literals follow contiguously as u32 encodings.
/// CEP:COST: 16 bytes per clause.
/// CEP:EVIDENCE: layout pinned by static assertion; unit/hot/sat_watch_test.rs::record_layout.
/// CEP:SECURITY: fixed layout, no pointers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct SatClauseHeader {
    /// CEP:WHAT: Number of literals.
    /// CEP:WHY: Traversal bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1, <= kMaxSatClauseLiterals.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    /// CEP:SECURITY: bounds iteration.
    pub length: u32,
    /// CEP:WHAT: Flag bits.
    /// CEP:WHY: See kSatClauseFlag* constants.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::learnt_budget_enforced.
    /// CEP:SECURITY: none.
    pub flags: u16,
    /// CEP:WHAT: Literal Block Distance (design 11.1 S23).
    /// CEP:WHY: Deletion policy input (Phase 2); recorded at creation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: 0 for problem clauses.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: reserved for Phase 2.
    /// CEP:SECURITY: none.
    pub lbd: u8,
    /// CEP:WHAT: Reserved padding.
    /// CEP:WHY: Fixed 16-byte header; must be zero.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: verifier flags nonzero.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/cold/verifier_test.rs.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u8,
    /// CEP:WHAT: Intrusive next-clause links for the two watch lists this clause belongs to.
    /// CEP:WHY: Design 11.3: the watch list is threaded through the clause structures themselves; slot i corresponds to watched literal position i.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kInvalidClauseOffset terminates each list.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    /// CEP:SECURITY: none.
    pub next_in_watch: [u32; kSatWatchSlotsPerClause],
}

// CEP:WHAT: Clause header layout pin.
// CEP:WHY: The record layout is the watch-scheme memory contract; drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::record_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<SatClauseHeader>() == 16);

/// CEP:WHAT: Arena-backed SAT clause storage.
/// CEP:WHY: Design 11.1 S3/S4: clauses are arena-allocated with two watched literals; this store owns record creation, validation, and access.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see SatClauseError.
/// CEP:ASSUMES: the arena outlives the store; the declared variable count bounds all literal variables.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: bench CEP-BENCH-0005; all SAT unit tests.
/// CEP:SECURITY: bounds-checked accessors.
pub struct ClauseStorage<'a> {
    /// CEP:WHAT: Shared arena.
    /// CEP:WHY: Record allocation (design 11.1 S4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: outlives the store.
    /// CEP:COST: 8-byte reference.
    /// CEP:EVIDENCE: all SAT tests.
    /// CEP:SECURITY: bounded arena.
    arena: &'a Arena,
    /// CEP:WHAT: Declared variable count for validation.
    /// CEP:WHY: Literals whose variable exceeds it would index watch heads out of range.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: creation rejects such literals.
    /// CEP:ASSUMES: fixed at initialization.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/literal_encoding_test.rs.
    /// CEP:SECURITY: validation bound.
    variable_count: u32,
    /// CEP:WHAT: Number of clauses created.
    /// CEP:WHY: Diagnostics.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    /// CEP:SECURITY: none.
    clause_count: Cell<u32>,
    /// CEP:WHAT: Number of learnt clauses created.
    /// CEP:WHY: Design 11.6 deletion threshold input (Phase 2); the budget is enforced at creation even though deletion is not yet implemented.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: creation refuses past kSatMaxLearntClauses.
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::learnt_budget_enforced.
    /// CEP:SECURITY: memory bound.
    learnt_count: Cell<u32>,
}

impl<'a> ClauseStorage<'a> {
    // CEP:WHAT: Initializes clause storage over the arena.
    // CEP:WHY: Explicit variable-count validation before any record exists.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (variable-count validation happens in SatCore).
    // CEP:ASSUMES: variable_count <= kMaxSatVariables.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    // CEP:SECURITY: none.
    pub fn new(arena: &'a Arena, variable_count: u32) -> ClauseStorage<'a> {
        ClauseStorage {
            arena,
            variable_count,
            clause_count: Cell::new(0),
            learnt_count: Cell::new(0),
        }
    }

    // CEP:WHAT: Returns the number of clauses created.
    // CEP:WHY: Diagnostics and budget accounting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    // CEP:SECURITY: none.
    pub fn clause_count(&self) -> u32 {
        self.clause_count.get()
    }

    // CEP:WHAT: Returns the number of learnt clauses created.
    // CEP:WHY: Deletion-threshold accounting (design 11.6).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::learnt_budget_enforced.
    // CEP:SECURITY: none.
    pub fn learnt_count(&self) -> u32 {
        self.learnt_count.get()
    }

    // CEP:WHAT: Creates a clause record: validates, allocates header plus literals, returns the offset.
    // CEP:WHY: Design 11.1 S3: arena-backed records; validation happens exactly once at creation so propagation can trust the record (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns EmptyClause for zero literals, TooManyLiterals past the bound, VariableOutOfRange for bad variables, LearntBudgetExceeded for learnt clauses past the budget, ArenaFull on exhaustion.
    // CEP:ASSUMES: literals is non-empty; duplicate literals and tautologies are stored verbatim (sanitization is Phase 3 preprocessing, design 11.1 S30-S37).
    // CEP:COST: O(length) validation plus one allocation.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::{creation_validates_bounds, learnt_budget_enforced}; fuzz/sat_fuzz_test.rs.
    // CEP:SECURITY: length and variable bounds enforced before any write.
    pub fn new_clause(
        &self,
        literals: &[SatLiteral],
        learnt: bool,
        lbd: u8,
    ) -> Result<u32, SatClauseError> {
        if literals.is_empty() {
            return Err(SatClauseError::EmptyClause);
        }
        if literals.len() as u32 > kMaxSatClauseLiterals {
            return Err(SatClauseError::TooManyLiterals);
        }
        for literal in literals.iter() {
            if literal.variable().0 >= self.variable_count
                || literal.variable().0 >= kMaxSatVariables
            {
                return Err(SatClauseError::VariableOutOfRange);
            }
        }
        if learnt {
            let next = self.learnt_count.get() + 1;
            if next > kSatMaxLearntClauses {
                return Err(SatClauseError::LearntBudgetExceeded);
            }
            self.learnt_count.set(next);
        }
        let header_range = self
            .arena
            .alloc_array::<SatClauseHeader>(1)
            .map_err(|_| SatClauseError::ArenaFull)?;
        let literal_range = self
            .arena
            .alloc_array::<u32>(literals.len() as u32)
            .map_err(|_| SatClauseError::ArenaFull)?;
        let header = self
            .arena
            .array_mut::<SatClauseHeader>(header_range)
            .map_err(|_| SatClauseError::ArenaFull)?;
        header[0] = SatClauseHeader {
            length: literals.len() as u32,
            flags: if learnt { kSatClauseFlagLearnt } else { 0 },
            lbd,
            reserved: 0,
            next_in_watch: [kInvalidClauseOffset, kInvalidClauseOffset],
        };
        let words = self
            .arena
            .array_mut::<u32>(literal_range)
            .map_err(|_| SatClauseError::ArenaFull)?;
        for (index, literal) in literals.iter().enumerate() {
            words[index] = literal.encoding();
        }
        self.clause_count.set(self.clause_count.get() + 1);
        Ok(header_range.start)
    }

    // CEP:WHAT: Reads the clause header at an offset.
    // CEP:WHY: Single validated entry point for header reads.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidClauseOffset when unreadable.
    // CEP:ASSUMES: offset came from new_clause.
    // CEP:COST: 2 compares + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::record_layout.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn header(&self, offset: u32) -> Result<SatClauseHeader, SatClauseError> {
        if offset == kInvalidClauseOffset {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let end = offset
            .checked_add(core::mem::size_of::<SatClauseHeader>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        if end > self.arena.used_bytes() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let range =
            ArenaRange::new(offset, end).map_err(|_| SatClauseError::InvalidClauseOffset)?;
        let slice = self
            .arena
            .array::<SatClauseHeader>(range)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        if slice.is_empty() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        Ok(slice[0])
    }

    // CEP:WHAT: Reads the i-th literal of a clause.
    // CEP:WHY: BCP and attach read literals; positions 0 and 1 are the watched literals.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidClauseOffset for out-of-range indices or unreadable storage.
    // CEP:ASSUMES: the header is readable.
    // CEP:COST: 2 compares + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn literal(&self, offset: u32, index: u32) -> Result<SatLiteral, SatClauseError> {
        let header = self.header(offset)?;
        if index >= header.length {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let literal_base = offset
            .checked_add(core::mem::size_of::<SatClauseHeader>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        let literal_address = literal_base
            .checked_add(index * core::mem::size_of::<u32>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        let literal_end = literal_address
            .checked_add(core::mem::size_of::<u32>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        if literal_end > self.arena.used_bytes() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let range = ArenaRange::new(literal_address, literal_end)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        let words = self
            .arena
            .array::<u32>(range)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        if words.is_empty() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        Ok(SatLiteral::from_encoding(words[0]))
    }

    // CEP:WHAT: Writes the i-th literal of a clause (watch swap primitive).
    // CEP:WHY: BCP swaps a candidate literal into the watched position when moving the watch; only positions 0 and 1 and interior positions of the same clause are ever written.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidClauseOffset for out-of-range indices or unreadable storage.
    // CEP:ASSUMES: the record was created by this store.
    // CEP:COST: 3 compares + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents.
    // CEP:SECURITY: bounds checks retained in release.
    pub fn set_literal(
        &self,
        offset: u32,
        index: u32,
        literal: SatLiteral,
    ) -> Result<(), SatClauseError> {
        let header = self.header(offset)?;
        if index >= header.length {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let literal_base = offset
            .checked_add(core::mem::size_of::<SatClauseHeader>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        let literal_address = literal_base
            .checked_add(index * core::mem::size_of::<u32>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        let literal_end = literal_address
            .checked_add(core::mem::size_of::<u32>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        if literal_end > self.arena.used_bytes() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let range = ArenaRange::new(literal_address, literal_end)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        let words = self
            .arena
            .array_mut::<u32>(range)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        if words.is_empty() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        words[0] = literal.encoding();
        Ok(())
    }

    // CEP:WHAT: Reads one next_in_watch link of a clause.
    // CEP:WHY: Watch-list traversal (design 11.3 intrusive links).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates InvalidClauseOffset.
    // CEP:ASSUMES: slot is 0 or 1.
    // CEP:COST: as header().
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: none.
    pub fn next_in_watch(&self, offset: u32, slot: u32) -> Result<u32, SatClauseError> {
        let header = self.header(offset)?;
        if slot > 1 {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        Ok(header.next_in_watch[slot as usize])
    }

    // CEP:WHAT: Writes one next_in_watch link of a clause.
    // CEP:WHY: Attach, unlink, and relink during BCP watch moves.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates InvalidClauseOffset.
    // CEP:ASSUMES: slot is 0 or 1.
    // CEP:COST: as header() plus 1 store.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: none.
    pub fn set_next_in_watch(
        &self,
        offset: u32,
        slot: u32,
        next: u32,
    ) -> Result<(), SatClauseError> {
        let end = offset
            .checked_add(core::mem::size_of::<SatClauseHeader>() as u32)
            .ok_or(SatClauseError::InvalidClauseOffset)?;
        if end > self.arena.used_bytes() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        if slot > 1 {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        let range =
            ArenaRange::new(offset, end).map_err(|_| SatClauseError::InvalidClauseOffset)?;
        let headers = self
            .arena
            .array_mut::<SatClauseHeader>(range)
            .map_err(|_| SatClauseError::InvalidClauseOffset)?;
        if headers.is_empty() {
            return Err(SatClauseError::InvalidClauseOffset);
        }
        headers[0].next_in_watch[slot as usize] = next;
        Ok(())
    }
}
