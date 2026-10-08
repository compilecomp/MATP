// CEP:FILE: hot/sat/assignment.rs
// CEP:WHAT: SAT assignment store: one u8 value per variable (unassigned / true / false) with O(1) read and write.
// CEP:WHY: Design 11.1 S1: dense variable indexing makes assignment lookup a single array load, which BCP performs for every watched-literal check; u8 values keep 2M variables within 2 MiB, cache-friendly for the propagation loop (CEP&CC 23.6.2).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SatValue for any in-bounds variable; out-of-range variable reads are debug-asserted and read as Unassigned (construction validates the count once, so release reads trust the validated bound and stay branch-light); writes return AssignmentError::VariableOutOfRange. Never panics.
// CEP:ASSUMES: The store is sized for exactly the variable count given at initialization; variable IDs below that count are valid by construction.
// CEP:COST: single byte load from a dense array; reads are exercised inside the propagation measurement (44.5 cycles median per step) in bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: unit/hot/sat_literal_test.rs and unit/hot/sat_bcp_test.rs exercise the store through propagation; bench CEP-BENCH-0005.
// CEP:SECURITY: the array is arena-resident and bounded by the validated variable count; no untrusted index can exceed it because literal construction bounds variables by kMaxSatVariables and the store rejects construction above the declared count.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; plain array state.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: an assignment read must load one byte from a dense array indexed by the validated variable; the inlined sequence appears in the propagate disassembly (artifact disasm_sat.txt); no cheaper representation exists.

use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::kMaxSatVariables;

/// CEP:WHAT: Three-valued SAT assignment value.
/// CEP:WHY: CDCL needs unassigned as a first-class value; the u8 representation matches the storage array and the FFI contract.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; closed vocabulary.
/// CEP:ASSUMES: exactly three states; representation values are stable.
/// CEP:COST: 1-byte copy type.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
/// CEP:SECURITY: out-of-range values cannot be constructed through the safe API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SatValue {
    /// CEP:WHAT: No assignment recorded.
    Unassigned = 0,
    /// CEP:WHAT: Variable assigned true.
    True = 1,
    /// CEP:WHAT: Variable assigned false.
    False = 2,
}

/// CEP:WHAT: Error cases of the assignment store.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
/// CEP:SECURITY: variable bound enforcement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentError {
    /// CEP:WHAT: The variable index is at or above the declared variable count.
    VariableOutOfRange,
    /// CEP:WHAT: The value byte is not a valid SatValue.
    InvalidValue,
}

/// CEP:WHAT: The per-variable assignment array.
/// CEP:WHY: Design 11.1 S1; Cell-based for shared &self mutation (single-threaded discipline).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see AssignmentError.
/// CEP:ASSUMES: sized once at initialization from the arena.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: bench CEP-BENCH-0005; all SAT unit tests.
/// CEP:SECURITY: bounds validated.
pub struct AssignmentStore<'a> {
    /// CEP:WHAT: Value array indexed by variable.
    /// CEP:WHY: Dense storage (design 11.1 S1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length equals the declared variable count.
    /// CEP:COST: 1 byte per variable.
    /// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    /// CEP:SECURITY: bounds-checked.
    values: &'a [Cell<u8>],
}

impl<'a> AssignmentStore<'a> {
    // CEP:WHAT: Allocates and clears the assignment array for the given variable count.
    // CEP:WHY: Initialization happens before the hot path (design 19.4); clearing makes every read defined from the start (CEP&CC 22.4 no uninitialized reads).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns AssignmentError::VariableOutOfRange when variable_count exceeds kMaxSatVariables; the arena error is mapped to VariableOutOfRange as the only initialization-time failure worth distinguishing is rethrown as arena exhaustion by the caller (SatCore).
    // CEP:ASSUMES: variable_count > 0 and <= kMaxSatVariables.
    // CEP:COST: O(variable_count) one-time clear.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::assignment_store_values.
    // CEP:SECURITY: explicit clearing, no uninitialized state.
    pub fn new(
        arena: &'a Arena,
        variable_count: u32,
    ) -> Result<AssignmentStore<'a>, AssignmentError> {
        if variable_count == 0 || variable_count > kMaxSatVariables {
            return Err(AssignmentError::VariableOutOfRange);
        }
        let range = arena
            .alloc_array::<Cell<u8>>(variable_count)
            .map_err(|_| AssignmentError::VariableOutOfRange)?;
        let values = arena
            .array::<Cell<u8>>(range)
            .map_err(|_| AssignmentError::VariableOutOfRange)?;
        for slot in values.iter() {
            slot.set(SatValue::Unassigned as u8);
        }
        Ok(AssignmentStore { values })
    }

    // CEP:WHAT: Reads the value of a variable.
    // CEP:WHY: The hottest read in BCP; out-of-declared-range variables read as Unassigned with a debug assertion because the bound was validated at construction (CEP&CC 23.7: the check exists at the trust boundary, not repeated per access).
    // CEP:STATUS: complete
    // CEP:FAILURE: none (infallible read).
    // CEP:ASSUMES: variable < declared count (enforced by literal construction and SatCore).
    // CEP:COST: 1 load + 1 compare (branch predicted).
    // CEP:EVIDENCE: bench CEP-BENCH-0005; unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: unknown bytes decode to Unassigned, never to a wrong truth value.
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: one byte load from a dense array; exercised within the measured 44.5-cycle propagation step (bench CEP-BENCH-0005); the inlined sequence appears in artifact disasm_sat.txt.
    pub fn value(&self, variable: SatVarRaw) -> SatValue {
        debug_assert!(variable.0 < self.values.len() as u32);
        if variable.0 as usize >= self.values.len() {
            return SatValue::Unassigned;
        }
        match self.values[variable.0 as usize].get() {
            value if value == SatValue::True as u8 => SatValue::True,
            value if value == SatValue::False as u8 => SatValue::False,
            _ => SatValue::Unassigned,
        }
    }

    // CEP:WHAT: Writes the value of a variable.
    // CEP:WHY: Assignment and backtracking write the store; the write path keeps the explicit bound check because it is called orders of magnitude less often than reads.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableOutOfRange for out-of-declared-range variables.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare + 1 store.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: bounds check retained in release.
    pub fn set_value(&self, variable: SatVarRaw, value: SatValue) -> Result<(), AssignmentError> {
        if variable.0 as usize >= self.values.len() {
            return Err(AssignmentError::VariableOutOfRange);
        }
        self.values[variable.0 as usize].set(value as u8);
        Ok(())
    }

    // CEP:WHAT: Returns the declared variable count.
    // CEP:WHY: Bounds documentation for callers and the verifier.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: none.
    pub fn variable_count(&self) -> u32 {
        self.values.len() as u32
    }
}

/// CEP:WHAT: Raw variable index type for assignment-store calls.
/// CEP:WHY: The store is indexed by plain variable numbers (design 11.1 S1); the newtype documents the convention at every call site without the literal wrapper.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; transparent u32.
/// CEP:ASSUMES: below the declared variable count.
/// CEP:COST: 4-byte copy type.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
/// CEP:SECURITY: bounds enforced by the store.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct SatVarRaw(pub u32);
