// CEP:FILE: hot/sat/watch_lists.rs
// CEP:WHAT: Watch-list heads for the watched-literal scheme: one head cell per literal encoding, linking intrusive lists threaded through clause records.
// CEP:WHY: Design 11.3 (S6): watch lists must live contiguously in the arena and the list links must be threaded through the clause structures themselves with no separate allocation; only the head array lives here, the links are the clause's next_in_watch pair (see sat/clause.rs), which eliminates pointer chasing and keeps watch traversal cache-friendly (CEP&CC 23.6.2, 23.6.4).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: head access is bounds-checked and returns kInvalidClauseOffset for unwatched literals; set_head validates the literal encoding range. Never panics.
// CEP:ASSUMES: The head array has exactly two entries per declared variable (one per polarity); the invalid offset sentinel means "empty list".
// CEP:COST: head read/write is 1 compare + 1 load/store; exercised inside the propagation measurement (44.5 cycles median per step) in bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: unit/hot/sat_watch_test.rs; property/bcp_property_test.rs (list integrity after propagation); bench CEP-BENCH-0005.
// CEP:SECURITY: literal encodings are bounded by construction (SatLiteral::new) and re-checked here; no untrusted index reaches the array.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; push-front insertion order is the clause creation order.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: a head read is one bounds check and one u32 load from a dense array indexed by the packed literal encoding; the inlined sequence appears in the propagate disassembly (artifact disasm_sat.txt).

use crate::memory::arena::Arena;
use crate::sat::literal::SatLiteral;
use core::cell::Cell;
use mapt_config::limits::{kInvalidClauseOffset, kMaxSatVariables};

/// CEP:WHAT: Literals per Boolean variable (two polarities).
/// CEP:WHY: Named constant for head-array sizing (CEP&CC 11.3); matches kSatWatchListCount.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
/// CEP:SECURITY: none.
const kLiteralsPerVariable: u32 = 2;

/// CEP:WHAT: Watch-list head array (two heads per variable).
/// CEP:WHY: Design 11.1 S6 and 11.3: contiguous storage, indexed by literal encoding.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see file header.
/// CEP:ASSUMES: sized once for the declared variable count.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
/// CEP:SECURITY: bounds-checked.
pub enum WatchListError {
    /// CEP:WHAT: The declared variable count is zero or above the bound.
    VariableCountInvalid,
    /// CEP:WHAT: The arena is exhausted.
    ArenaFull,
}

/// CEP:WHAT: Watch-list head array (two heads per variable).
/// CEP:WHY: Design 11.1 S6 and 11.3: contiguous storage, indexed by literal encoding.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see file header.
/// CEP:ASSUMES: sized once for the declared variable count.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
/// CEP:SECURITY: bounds-checked.
pub struct WatchLists<'a> {
    /// CEP:WHAT: Head cells indexed by literal encoding.
    /// CEP:WHY: One array covers both polarities of every variable (encoding = var*2 + sign).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length = 2 * declared variable count.
    /// CEP:COST: 4 bytes per literal.
    /// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    /// CEP:SECURITY: bounds-checked.
    heads: &'a [Cell<u32>],
}

impl<'a> WatchLists<'a> {
    // CEP:WHAT: Allocates and clears the head array for the declared variable count.
    // CEP:WHY: Initialization before the hot path; clearing makes every list provably empty.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns WatchListError::VariableCountInvalid for bad counts and ArenaFull when the head array does not fit; SatCore maps both onto SatClauseError.
    // CEP:ASSUMES: variable_count > 0 and <= kMaxSatVariables.
    // CEP:COST: O(2 * variable_count) one-time clear.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::initial_state_empty.
    // CEP:SECURITY: cleared arrays.
    pub fn new(arena: &'a Arena, variable_count: u32) -> Result<WatchLists<'a>, WatchListError> {
        if variable_count == 0 || variable_count > kMaxSatVariables {
            return Err(WatchListError::VariableCountInvalid);
        }
        let head_count = variable_count
            .checked_mul(kLiteralsPerVariable)
            .ok_or(WatchListError::VariableCountInvalid)?;
        let range = arena
            .alloc_array::<Cell<u32>>(head_count)
            .map_err(|_| WatchListError::ArenaFull)?;
        let heads = arena
            .array::<Cell<u32>>(range)
            .map_err(|_| WatchListError::ArenaFull)?;
        for slot in heads.iter() {
            slot.set(kInvalidClauseOffset);
        }
        Ok(WatchLists { heads })
    }

    // CEP:WHAT: Returns the head clause offset of a literal's watch list.
    // CEP:WHY: BCP begins each scan here; kInvalidClauseOffset ends the list.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns kInvalidClauseOffset for out-of-range encodings (cannot happen through SatLiteral).
    // CEP:ASSUMES: literal encodings are in range (validated at literal construction).
    // CEP:COST: 1 compare + 1 load.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::{initial_state_empty, attach_and_traverse}.
    // CEP:SECURITY: bounds check retained in release.
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: one bounds check plus one u32 load; exercised within the measured 44.5-cycle propagation step (bench CEP-BENCH-0005).
    pub fn head(&self, literal: SatLiteral) -> u32 {
        let index = literal.encoding() as usize;
        if index >= self.heads.len() {
            return kInvalidClauseOffset;
        }
        self.heads[index].get()
    }

    // CEP:WHAT: Writes the head clause offset of a literal's watch list.
    // CEP:WHY: Attach (push-front) and detach (unlink) update heads.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns false for out-of-range encodings (cannot happen through SatLiteral).
    // CEP:ASSUMES: as head().
    // CEP:COST: 1 compare + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: bounds check retained in release.
    pub fn set_head(&self, literal: SatLiteral, offset: u32) -> bool {
        let index = literal.encoding() as usize;
        if index >= self.heads.len() {
            return false;
        }
        self.heads[index].set(offset);
        true
    }

    // CEP:WHAT: Pushes a clause offset onto a literal's list (push-front).
    // CEP:WHY: Attach primitive shared by clause registration and watch moves; the caller first stores the old head into the clause's next_in_watch slot, so this is exactly one store.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns false when the literal is out of range.
    // CEP:ASSUMES: the caller has already written clause.next_in_watch[slot] = old head.
    // CEP:COST: 1 compare + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
    // CEP:SECURITY: bounds check retained in release.
    pub fn push_front(&self, literal: SatLiteral, offset: u32) -> bool {
        let index = literal.encoding() as usize;
        if index >= self.heads.len() {
            return false;
        }
        self.heads[index].set(offset);
        true
    }
}
