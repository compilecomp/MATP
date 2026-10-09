// CEP:FILE: hot/ordering/precedence.rs
// CEP:WHAT: Frozen symbol precedence table: an arena-backed u32 rank array over all symbol IDs plus one pseudo-entry for the equality head, giving a strict total order on term heads.
// CEP:WHY: Design 8.3: KBO and LPO are both parameterized by a strict total precedence on function symbols; the design bans hard-coded weights and precedences (11.3) and defers strategy-file loading to config, so Phase 2 ships the frozen arena view plus two deterministic construction policies (identifier order as the default, explicit ranks for strategies), built once before the hot path and then only read (design 19.4).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns PrecedenceError::UnknownSymbol for out-of-range symbol IDs and PrecedenceError::InvalidRanks when explicit ranks are not a permutation; never panics.
// CEP:ASSUMES: The table is built once and frozen; the arena outlives the view; the equality pseudo-entry occupies the slot after the last real symbol ID, so Application and Lambda heads (reserved symbol field) are rejected explicitly as unsupported (Phase 5 higher-order scope) rather than aliased onto a real symbol.
// CEP:COST: rank is 1 bounds check + 1 load (same shape as the symbol-table lookup measured at 2.95 cycles in bench CEP-BENCH-0002); construction is O(n) once.
// CEP:EVIDENCE: unit/hot/ordering_test.rs::{id_order_is_default, explicit_ranks_validated, unknown_symbol_rejected, equality_pseudo_entry}.
// CEP:SECURITY: symbol IDs are bounds-checked on every rank read; rank arrays are bounded by kMaxSymbolCount plus one.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the default policy is a pure function of symbol IDs, validation order is index-ordered, and the frozen view contains no mutable state.

use crate::memory::arena::Arena;
use mapt_config::limits::kMaxSymbolCount;

/// CEP:WHAT: Error cases of the precedence table.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary for the ordering component.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs::{explicit_ranks_validated, unknown_symbol_rejected}.
/// CEP:SECURITY: bounds errors are the validation boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrecedenceError {
    /// CEP:WHAT: The symbol ID is outside the frozen table.
    UnknownSymbol,
    /// CEP:WHAT: Explicit ranks are not a permutation of 0..n over symbols plus the equality entry.
    InvalidRanks,
    /// CEP:WHAT: The arena is exhausted during construction.
    ArenaFull,
}

/// CEP:WHAT: Frozen precedence view: rank per symbol ID, one extra slot for the equality head.
/// CEP:WHY: Design 8.3: the ordering needs a strict total order on heads; a flat u32 array indexed by dense symbol ID is one bounds check and one load per comparison (the same access shape the symbol table already measured as target-optimal).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see PrecedenceError.
/// CEP:ASSUMES: frozen after construction; arena outlives the view.
/// CEP:COST: 4 bytes per symbol plus 4 for the equality entry.
/// CEP:EVIDENCE: unit/hot/ordering_test.rs.
/// CEP:SECURITY: bounds-checked reads.
#[derive(Debug)]
pub struct PrecedenceTable<'a> {
    /// CEP:WHAT: Rank array; index i < symbol_count is symbol i, index symbol_count is the equality head.
    /// CEP:WHY: One array keeps the hot read a single load; the trailing pseudo-slot avoids a second table for the equality head.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length equals symbol_count + 1; ranks form a permutation of 0..symbol_count.
    /// CEP:COST: 4 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/ordering_test.rs::{id_order_is_default, equality_pseudo_entry}.
    /// CEP:SECURITY: bounds-checked.
    ranks: &'a [u32],
}

impl<'a> PrecedenceTable<'a> {
    // CEP:WHAT: Builds the default precedence: rank(symbol i) = i, equality head maximal.
    // CEP:WHY: A deterministic default policy is required so that ordering behavior is reproducible without a strategy file (CEP&CC 38.10); identifier order is the least arbitrary total order available, and giving the equality head the top rank keeps equality atoms comparable with every predicate atom in literal-ordering use (design 8.3 configuration note).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull when the array does not fit and InvalidRanks when the symbol count is zero or exceeds kMaxSymbolCount.
    // CEP:ASSUMES: symbol_count matches the frozen symbol table.
    // CEP:COST: O(symbol_count) writes once.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::id_order_is_default.
    // CEP:SECURITY: count validated against kMaxSymbolCount.
    pub fn from_id_order(
        arena: &'a Arena,
        symbol_count: u32,
    ) -> Result<PrecedenceTable<'a>, PrecedenceError> {
        let ranks = Self::allocate(arena, symbol_count)?;
        for index in 0..symbol_count {
            ranks[index as usize] = index;
        }
        ranks[symbol_count as usize] = symbol_count;
        Ok(PrecedenceTable { ranks })
    }

    // CEP:WHAT: Builds a precedence from explicit ranks: entries 0..n-1 are symbol ranks, entry n is the equality head rank.
    // CEP:WHY: Design 8.3: "precedence ... loaded from a strategy file"; the strategy layer (config, Phase 3) supplies the rank vector and this constructor validates it is a strict total order before the hot path can depend on it (CEP&CC Law 3: validate once at the trust boundary).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidRanks when the vector is empty, contains a rank at or above its own length, or two symbols share a rank; ArenaFull when allocation fails.
    // CEP:ASSUMES: the caller supplies exactly symbol_count + 1 entries.
    // CEP:COST: O(n) validation with an arena scratch array (one-time, init phase).
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::{explicit_ranks_validated, duplicate_ranks_rejected}.
    // CEP:SECURITY: permutation validation prevents smuggled partial orders from reaching the hot path.
    pub fn from_ranks(
        arena: &'a Arena,
        ranks: &[u32],
    ) -> Result<PrecedenceTable<'a>, PrecedenceError> {
        // The input carries one entry per real symbol plus the trailing equality-head rank.
        let entry_count = ranks.len() as u32;
        if entry_count == 0 {
            return Err(PrecedenceError::InvalidRanks);
        }
        let total = entry_count as u64;
        if total > kMaxSymbolCount as u64 + 1 {
            return Err(PrecedenceError::InvalidRanks);
        }
        for rank in ranks.iter() {
            if *rank as u64 >= total {
                return Err(PrecedenceError::InvalidRanks);
            }
        }
        // Permutation validation with an init-phase scratch array; the scratch stays in the
        // arena as bounded initialization garbage (design 8.1 bump discipline).
        let scratch_range = arena
            .alloc_array::<u32>(entry_count)
            .map_err(|_| PrecedenceError::ArenaFull)?;
        let scratch = arena
            .array_mut::<u32>(scratch_range)
            .map_err(|_| PrecedenceError::ArenaFull)?;
        for slot in scratch.iter_mut() {
            *slot = 0;
        }
        for rank in ranks.iter() {
            let slot = &mut scratch[*rank as usize];
            if *slot != 0 {
                return Err(PrecedenceError::InvalidRanks);
            }
            *slot = 1;
        }
        let destination_range = arena
            .alloc_array::<u32>(entry_count)
            .map_err(|_| PrecedenceError::ArenaFull)?;
        let destination = arena
            .array_mut::<u32>(destination_range)
            .map_err(|_| PrecedenceError::ArenaFull)?;
        for (index, rank) in ranks.iter().enumerate() {
            destination[index] = *rank;
        }
        Ok(PrecedenceTable { ranks: destination })
    }

    // CEP:WHAT: Allocates the frozen rank array of symbol_count + 1 entries.
    // CEP:WHY: Shared sizing point for both construction policies (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull on exhaustion and InvalidRanks when the count is zero or exceeds kMaxSymbolCount.
    // CEP:ASSUMES: none.
    // CEP:COST: one arena allocation.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::id_order_is_default.
    // CEP:SECURITY: count bound validated.
    fn allocate(arena: &'a Arena, symbol_count: u32) -> Result<&'a mut [u32], PrecedenceError> {
        if symbol_count == 0 || symbol_count > kMaxSymbolCount {
            return Err(PrecedenceError::InvalidRanks);
        }
        let total = symbol_count + 1;
        let range = arena
            .alloc_array::<u32>(total)
            .map_err(|_| PrecedenceError::ArenaFull)?;
        arena
            .array_mut::<u32>(range)
            .map_err(|_| PrecedenceError::ArenaFull)
    }

    // CEP:WHAT: Returns the number of real symbols covered by the table.
    // CEP:WHY: Bounds documentation and construction cross-checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::id_order_is_default.
    // CEP:SECURITY: none.
    pub fn symbol_count(&self) -> u32 {
        self.ranks.len() as u32 - 1
    }

    // CEP:WHAT: Returns the rank of a symbol (higher rank = higher precedence).
    // CEP:WHY: The single hot-path read of the precedence component; one bounds check plus one load.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns UnknownSymbol when the ID is at or above the covered symbol count.
    // CEP:ASSUMES: the ID came from a term head or the frozen symbol table.
    // CEP:COST: 1 bounds check + 1 load.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::{id_order_is_default, unknown_symbol_rejected}.
    // CEP:SECURITY: bounds check retained in release (CEP&CC 23.7).
    pub fn rank(&self, symbol_id: u32) -> Result<u32, PrecedenceError> {
        if symbol_id >= self.symbol_count() {
            return Err(PrecedenceError::UnknownSymbol);
        }
        Ok(self.ranks[symbol_id as usize])
    }

    // CEP:WHAT: Returns the rank of the equality pseudo-head.
    // CEP:WHY: Equality atoms carry no symbol ID (reserved zero, term.rs), so their precedence is the dedicated trailing slot; keeping the accessor explicit prevents accidentally ranking them as symbol zero.
    // CEP:STATUS: complete
    // CEP:FAILURE: none; the slot exists by construction.
    // CEP:ASSUMES: built by from_id_order or validated from_ranks.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::id_order_is_default.
    // CEP:SECURITY: none.
    pub fn equality_rank(&self) -> u32 {
        self.ranks[self.ranks.len() - 1]
    }

    // CEP:WHAT: Returns true when symbol a has strictly higher precedence than symbol b.
    // CEP:WHY: Direct expression of the ordering component's core question; used by KBO's head case and LPO's case (b).
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates UnknownSymbol.
    // CEP:ASSUMES: both IDs are covered.
    // CEP:COST: 2 bounds checks + 2 loads + 1 compare.
    // CEP:EVIDENCE: unit/hot/ordering_test.rs::{id_order_is_default, kbo_precedence_case}.
    // CEP:SECURITY: none.
    pub fn precedes(&self, a: u32, b: u32) -> Result<bool, PrecedenceError> {
        Ok(self.rank(a)? > self.rank(b)?)
    }
}
