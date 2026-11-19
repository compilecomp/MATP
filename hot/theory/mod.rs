// CEP:FILE: hot/theory/mod.rs
// CEP:WHAT: The theory-reasoning engine (design 13, Phase 5 of design 26): the hash-consed ground term graph, the congruence closure for EUF, the difference-logic fragment of linear arithmetic over Q, the Nelson-Oppen combination coordinator, and the DPLL(T) outer loop over the CDCL solver, with theory atoms registered once and addressed by the Boolean abstraction.
// CEP:WHY: Design 26 Phase 5 ("DPLL(T) integration", "Congruence closure", "Nelson-Oppen combination") and design 13.2's architecture: the SAT solver proposes a Boolean assignment over theory atoms, the theory coordinator checks consistency under that assignment, an inconsistent assignment produces a theory lemma (the negation of the full atom assignment, theory-valid because the assignment is theory-inconsistent), the solver adds it and continues, and the loop ends in Satisfiable (a theory-backed model), Unsatisfiable (the abstraction refuted), or Unknown (the conflict budget). The lemma clause enters the proof trace through the axiom path because a theory lemma is theory-valid but not RUP against the Boolean abstraction - the trust axiom is documented in Spec 21 section 5 and the proof-graph side carries the TheoryLemma derivation source (hot/ir/clause.rs) whose producer this module's conflict reports feed.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: every entry point returns Result with TheoryError on capacity, storage, arithmetic, or round-bound exhaustion; the DPLL(T) loop reports TheoryStatus::Unknown at the conflict budget instead of running unbounded; never panics.
// CEP:ASSUMES: single-threaded; one shared arena outlives all theory structures; the CDCL solver is constructed over kMaxTheoryAtoms variables and used by no other owner.
// CEP:COST: construction is O(capacities); one DPLL(T) iteration is one SAT solve plus one theory check (O(nodes x arity) closure rounds + O(vars x edges) Bellman-Ford + the pair tests bounded by vars squared x Bellman-Ford); measured in bench CEP-BENCH-0014, artifacts benches/artifacts/theory_*.json.
// CEP:EVIDENCE: unit/hot/theory_test.rs; property/theory_property_test.rs; bench CEP-BENCH-0014 (artifacts benches/artifacts/theory_*.json).
// CEP:SECURITY: every loop is bounded by named capacities in config/limits.rs; no unbounded loop exists in this module.
// CEP:UNSAFE: none; this module is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; atoms are asserted in id order, nodes in id order, edges in assertion order, and every budget is counted identically per run (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;
use crate::sat::database::SatCoreError;
use mapt_config::limits::{kMaxTheoryAtoms, kMaxTheoryVars};

/// CEP:WHAT: The congruence closure over the term graph (design 13.4).
pub mod congruence;
/// CEP:WHAT: The difference-logic fragment of linear arithmetic over Q (design 13.1).
pub mod difference;
/// CEP:WHAT: The DPLL(T) outer loop over the CDCL solver (design 13.2).
pub mod dpll_t;
/// CEP:WHAT: The Nelson-Oppen combination coordinator (design 13.3).
pub mod nelson_oppen;
/// CEP:WHAT: The hash-consed ground term graph (design 13.4).
pub mod term_graph;

pub use congruence::CongruenceClosure;
pub use difference::DifferenceLogic;
pub use dpll_t::{TheoryOutcome, TheorySatSolver, TheoryStatus};
pub use nelson_oppen::NelsonOppen;
pub use term_graph::{TermGraph, TermNode};

/// CEP:WHAT: The theory engine's failure vocabulary.
/// CEP:WHY: One error type for every theory entry point keeps the translation points named (CEP&CC 24.2); storage failures nest the SAT core's storage errors because the theory structures allocate through the same arena discipline.
/// CEP:STATUS: complete
/// CEP:FAILURE: each variant IS the failure report.
/// CEP:ASSUMES: none.
/// CEP:COST: enum value.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::{term_capacity_enforced, variable_capacity_enforced, atom_capacity_enforced}.
/// CEP:SECURITY: every variant is a loud, bounded failure.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TheoryError {
    /// CEP:WHAT: A storage or invariant failure underneath the theory structures.
    /// CEP:WHY: Arena exhaustion and internal invariant violations nest the SAT core's storage vocabulary (one arena discipline).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: loud failure.
    Storage(SatCoreError),
    /// CEP:WHAT: The term graph's node capacity kMaxTheoryTerms is exhausted.
    /// CEP:WHY: The memory-exhaustion bound on the term state.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: loud failure.
    TermCapacity,
    /// CEP:WHAT: A variable id is outside the shared variable space kMaxTheoryVars.
    /// CEP:WHY: Both theory solvers address one bounded variable space.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::variable_capacity_enforced.
    /// CEP:SECURITY: loud failure.
    VarCapacity,
    /// CEP:WHAT: The theory-atom capacity kMaxTheoryAtoms is exhausted.
    /// CEP:WHY: The memory-exhaustion bound on the atom state and the Boolean abstraction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: loud failure.
    AtomCapacity,
    /// CEP:WHAT: The hash-consing table has no free slot.
    /// CEP:WHY: The loud backstop of the bounded probe loops (unreachable while the node bound is half the table).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: loud failure.
    HashTableFull,
    /// CEP:WHAT: A fixpoint (congruence rounds or Nelson-Oppen propagation rounds) exceeded its named round bound.
    /// CEP:WHY: The loud backstop of the bounded propagation loops.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: loud failure.
    PropagationRounds,
    /// CEP:WHAT: Difference-logic arithmetic exceeded its range.
    /// CEP:WHY: Severity 0 prevention: wraparound arithmetic could make an inconsistent system look consistent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: loud failure.
    ArithmeticOverflow,
    /// CEP:WHAT: An application node's arity exceeds kMaxTheoryArity.
    /// CEP:WHY: The closure's fixed scratch buffer bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: loud failure.
    ArityExceeded,
    /// CEP:WHAT: A CDCL solver call failed underneath the DPLL(T) loop.
    /// CEP:WHY: The Boolean abstraction's errors must surface with their cause, not be swallowed.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: loud failure.
    Sat(crate::sat::cdcl::CdclError),
}

/// CEP:WHAT: One theory atom id.
/// CEP:WHY: A typed index keeps atoms distinct from variable ids and term nodes; atom i maps to SAT variable i in the Boolean abstraction.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: produced only by AtomTable.
/// CEP:COST: 4 bytes.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
/// CEP:SECURITY: none.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct TheoryAtomId(pub u32);

// CEP:WHAT: Theory-atom kind tags.
// CEP:WHY: The kind routes assertions to the right theory solver (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: distinct values.
// CEP:COST: compile-time constants.
// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
// CEP:SECURITY: none.
const kAtomKindEquality: u32 = 0;
const kAtomKindDifference: u32 = 1;

/// CEP:WHAT: The theory-atom registry: kind, payload, and fixed-point bound per atom in fixed-density arena arrays.
/// CEP:WHY: Design 13.2's Boolean abstraction needs a stable atom surface both theory solvers and the SAT encoding read; the table is the single registration point (atom i is SAT variable i).
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError.
/// CEP:ASSUMES: single-threaded; no atom is ever removed.
/// CEP:COST: 20 bytes of arena per atom.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
/// CEP:SECURITY: bounds-checked reads throughout.
pub struct AtomTable<'a> {
    /// CEP:WHAT: Kind per atom (0 = EUF equality, 1 = difference constraint).
    /// CEP:WHY: The assertion router and the lemma builder's atom reader.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: bounds-checked reads.
    kind: &'a [Cell<u32>],
    /// CEP:WHAT: Left payload per atom: the equality's left term node, or the difference constraint's left variable.
    /// CEP:WHY: One cell covers both kinds' left side.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: bounds-checked reads.
    left: &'a [Cell<u32>],
    /// CEP:WHAT: Right payload per atom: the equality's right term node, or the difference constraint's right variable.
    /// CEP:WHY: One cell covers both kinds' right side.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: bounds-checked reads.
    right: &'a [Cell<u32>],
    /// CEP:WHAT: The difference constraint's bound in fixed-point units (0 for equality atoms).
    /// CEP:WHY: The constraint's weight, bounded by kTheoryDlMaxWeight at registration.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 8 bytes per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: bounds-checked reads.
    bound: &'a [Cell<i64>],
    /// CEP:WHAT: Number of registered atoms.
    /// CEP:WHY: Extent of the per-atom arrays; also the Boolean abstraction's variable count.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxTheoryAtoms.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: none.
    count: Cell<u32>,
}

impl<'a> AtomTable<'a> {
    /// CEP:WHAT: Constructs the atom table over the arena.
    /// CEP:WHY: Design 4.1: every structure is fully built before use.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    /// CEP:ASSUMES: the arena has room for the four arrays.
    /// CEP:COST: O(kMaxTheoryAtoms) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<AtomTable<'a>, TheoryError> {
        let kind = Self::alloc_u32(arena, kMaxTheoryAtoms)?;
        let left = Self::alloc_u32(arena, kMaxTheoryAtoms)?;
        let right = Self::alloc_u32(arena, kMaxTheoryAtoms)?;
        let bound = Self::alloc_i64(arena, kMaxTheoryAtoms)?;
        Ok(AtomTable {
            kind,
            left,
            right,
            bound,
            count: Cell::new(0),
        })
    }

    // CEP:WHAT: Arena array constructors with the single error translation.
    // CEP:WHY: One translation point per element type (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation each.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    // CEP:SECURITY: none.
    fn alloc_u32(arena: &'a Arena, count: u32) -> Result<&'a [Cell<u32>], TheoryError> {
        let range = arena.alloc_array::<Cell<u32>>(count).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<u32>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    fn alloc_i64(arena: &'a Arena, count: u32) -> Result<&'a [Cell<i64>], TheoryError> {
        let range = arena.alloc_array::<Cell<i64>>(count).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<i64>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: Registers an EUF equality atom (t1 = t2).
    /// CEP:WHY: Design 13.1's uninterpreted-function theory surface.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::AtomCapacity past the bound.
    /// CEP:ASSUMES: the term nodes exist in the solver's term graph.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: bounded by the atom capacity.
    pub fn equality_atom(
        &self,
        left: TermNode,
        right: TermNode,
    ) -> Result<TheoryAtomId, TheoryError> {
        let index = self.count.get();
        if index >= kMaxTheoryAtoms {
            return Err(TheoryError::AtomCapacity);
        }
        self.kind[index as usize].set(kAtomKindEquality);
        self.left[index as usize].set(left.0);
        self.right[index as usize].set(right.0);
        self.bound[index as usize].set(0);
        self.count.set(index + 1);
        Ok(TheoryAtomId(index))
    }

    /// CEP:WHAT: Registers a difference constraint atom (x - y <= bound) with the bound in fixed-point units.
    /// CEP:WHY: Design 13.1's linear-arithmetic fragment surface; the negation semantics (x - y > bound as y - x <= -bound - 1) is exact over the fixed-point representation and handled at assertion time.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::AtomCapacity past the bound, VarCapacity for out-of-range variables, and ArithmeticOverflow for an out-of-range bound.
    /// CEP:ASSUMES: the bound satisfies |bound| <= kTheoryDlMaxWeight.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: bounded by the atom, variable, and weight capacities.
    pub fn difference_atom(
        &self,
        left: u32,
        right: u32,
        bound: i64,
    ) -> Result<TheoryAtomId, TheoryError> {
        if left >= kMaxTheoryVars || right >= kMaxTheoryVars {
            return Err(TheoryError::VarCapacity);
        }
        if bound.abs() > mapt_config::limits::kTheoryDlMaxWeight {
            return Err(TheoryError::ArithmeticOverflow);
        }
        let index = self.count.get();
        if index >= kMaxTheoryAtoms {
            return Err(TheoryError::AtomCapacity);
        }
        self.kind[index as usize].set(kAtomKindDifference);
        self.left[index as usize].set(left);
        self.right[index as usize].set(right);
        self.bound[index as usize].set(bound);
        self.count.set(index + 1);
        Ok(TheoryAtomId(index))
    }

    /// CEP:WHAT: Returns the number of registered atoms.
    /// CEP:WHY: The DPLL(T) loop and the lemma builder size their scans on the count.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: none.
    pub fn atom_count(&self) -> u32 {
        self.count.get()
    }

    /// CEP:WHAT: Reads one atom's payload: kind, left, right, and bound.
    /// CEP:WHY: One bounds-checked read path for the coordinator and the tests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on an out-of-range atom id.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn get_atom(&self, atom: TheoryAtomId) -> Result<(u32, u32, u32, i64), TheoryError> {
        if atom.0 >= self.count.get() {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        let index = atom.0 as usize;
        Ok((
            self.kind[index].get(),
            self.left[index].get(),
            self.right[index].get(),
            self.bound[index].get(),
        ))
    }
}
