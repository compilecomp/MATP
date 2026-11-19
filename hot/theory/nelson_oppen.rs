// CEP:FILE: hot/theory/nelson_oppen.rs
// CEP:WHAT: The Nelson-Oppen combination coordinator (design 13.3): one EUF theory (the congruence closure over the term graph) and one difference-logic theory over the shared variable space, with bidirectional equality propagation to a fixpoint and the agreement checks that make the combined assignment's consistency decidable for the fragment.
// CEP:WHY: Design 13.3: for stably infinite, signature-disjoint theories the combination propagates equalities over shared variables; EUF (Nelson & Oppen 1980) and difference logic over Q are stably infinite and signature-disjoint, so the fragment's consistency check is: each solver consistent, every EUF-merged shared pair made zero-equal in the difference logic (consistency re-checked), and every difference-logic-entailed shared equality merged into EUF (with its disequalities re-checked); the fixpoint terminates because each round either propagates at least one equality or stabilizes (bounded by kMaxTheoryPropagationRounds with a loud error past it). The no-orientation simplification (no arrangement search over u < v versus u > v) is sound and complete here because a shared pair that is neither merged nor entailment-equal can be separated in both theories (the difference-logic entailment test is exact for the fragment) - the reasoning is Spec 21 section 6.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns TheoryError on storage failures, arithmetic overflow, or past the propagation round bound; check returns false for an inconsistent assignment; never panics.
// CEP:ASSUMES: single-threaded; reset before each assertion batch; atom ids reference the coordinator's own AtomTable; the term graph's variables are the difference logic's variables.
// CEP:COST: one check is O(rounds x (nodes x arity closure + vars x edges Bellman-Ford + pair tests x Bellman-Ford)) under the named bounds.
// CEP:EVIDENCE: unit/hot/theory_test.rs::{nelson_oppen_combines_theories, nelson_oppen_conflict_across_theories}; property/theory_property_test.rs.
// CEP:SECURITY: every loop is bounded by named capacities; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; variables and atoms are scanned in id order per round (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;

use super::congruence::CongruenceClosure;
use super::difference::DifferenceLogic;
use super::term_graph::{TermGraph, TermNode};
use super::{AtomTable, TheoryAtomId, TheoryError};

/// CEP:WHAT: The Nelson-Oppen coordinator: the atom table, the term graph, the EUF closure, and the difference-logic solver composed into one consistency state machine.
/// CEP:WHY: Design 13.3's combination needs one owner for the shared-variable interface so the equality propagation cannot diverge between the theories.
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError.
/// CEP:ASSUMES: atom registration finishes before the first check of a cycle.
/// CEP:COST: one closure, one difference-logic state, and one atom table per coordinator.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
/// CEP:SECURITY: bounds-checked throughout.
pub struct NelsonOppen<'a> {
    /// CEP:WHAT: The theory-atom registry.
    /// CEP:WHY: The assertion surface the DPLL(T) loop drives.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by atom_count.
    /// CEP:COST: see AtomTable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::atom_capacity_enforced.
    /// CEP:SECURITY: bounds-checked reads.
    atoms: AtomTable<'a>,
    /// CEP:WHAT: The ground term graph.
    /// CEP:WHY: The EUF theory's terms; its variable nodes are the shared variable space.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: no node is created after the first check of a cycle.
    /// CEP:COST: see TermGraph.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    graph: TermGraph<'a>,
    /// CEP:WHAT: The congruence closure over the graph.
    /// CEP:WHY: The EUF consistency engine.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: reset before each check cycle.
    /// CEP:COST: see CongruenceClosure.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounds-checked reads.
    closure: CongruenceClosure<'a>,
    /// CEP:WHAT: The difference-logic solver.
    /// CEP:WHY: The arithmetic fragment of the combination.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: reset before each check cycle.
    /// CEP:COST: see DifferenceLogic.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: bounds-checked reads.
    difference: DifferenceLogic<'a>,
    /// CEP:WHAT: The asserted truth of each atom in the current batch (0 = unasserted, 1 = true, 2 = false).
    /// CEP:WHY: The disequality check needs the assertion record, not the class state: a false equality is violated only when the batch asserted it false AND the closure merged the classes.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryAtoms; reset before each batch.
    /// CEP:COST: 1 byte per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_conflict_across_theories.
    /// CEP:SECURITY: bounds-checked reads.
    asserted_truth: &'a [Cell<u8>],
}

impl<'a> NelsonOppen<'a> {
    /// CEP:WHAT: Constructs the coordinator over the arena.
    /// CEP:WHY: Design 4.1: every structure is fully built before use; the closure borrows the coordinator-owned graph.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError on arena exhaustion.
    /// CEP:ASSUMES: the arena has room for every substructure.
    /// CEP:COST: O(capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<NelsonOppen<'a>, TheoryError> {
        let graph = TermGraph::new(arena)?;
        let closure = CongruenceClosure::new(arena)?;
        let difference = DifferenceLogic::new(arena)?;
        let atoms = AtomTable::new(arena)?;
        let asserted_truth = Self::alloc_u8(arena)?;
        Ok(NelsonOppen {
            atoms,
            graph,
            closure,
            difference,
            asserted_truth,
        })
    }

    // CEP:WHAT: Allocates the asserted-truth array.
    // CEP:WHY: One translation point for the arena error (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_conflict_across_theories.
    // CEP:SECURITY: none.
    fn alloc_u8(arena: &'a Arena) -> Result<&'a [Cell<u8>], TheoryError> {
        let range = arena
            .alloc_array::<Cell<u8>>(mapt_config::limits::kMaxTheoryAtoms)
            .map_err(|_| {
                TheoryError::Storage(crate::sat::database::SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        arena.array::<Cell<u8>>(range).map_err(|_| {
            TheoryError::Storage(crate::sat::database::SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: The coordinator's term graph, for term construction by the caller.
    /// CEP:WHY: EUF equality atoms reference term nodes; the graph must be built before registration.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before registration.
    /// CEP:COST: one reference.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: none.
    pub fn graph(&self) -> &TermGraph<'a> {
        &self.graph
    }

    /// CEP:WHAT: The coordinator's atom table, for registration by the caller.
    /// CEP:WHY: The DPLL(T) loop registers atoms once and encodes them into the SAT solver.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before the first solve.
    /// CEP:COST: one reference.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: none.
    pub fn atoms(&self) -> &AtomTable<'a> {
        &self.atoms
    }

    /// CEP:WHAT: Resets both theory solvers and the closure for one assertion batch.
    /// CEP:WHY: The DPLL(T) loop re-asserts the full atom assignment per conflict cycle; one reset point keeps the two theories' states in lockstep.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before each batch.
    /// CEP:COST: O(term nodes + variables).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: none.
    pub fn reset(&self) {
        self.closure.reset();
        self.difference.reset();
        for slot in 0..mapt_config::limits::kMaxTheoryAtoms as usize {
            self.asserted_truth[slot].set(0);
        }
    }

    /// CEP:WHAT: Asserts one atom's truth value into its theory: an EUF equality merges or is left for the disequality check; a difference constraint adds its edge or the exact negation (y - x <= -bound - 1 over the fixed-point units).
    /// CEP:WHY: Design 13.2 step 2: the theory solvers receive the SAT solver's assignment; the negation semantics are exact over the discrete fixed-point representation (the one-unit epsilon is the smallest positive Q-element the representation can address).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError; never panics.
    /// CEP:ASSUMES: reset was called for this batch.
    /// CEP:COST: O(1) amortized per atom (the merge is lazy).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_conflict_across_theories.
    /// CEP:SECURITY: bounded by the capacities.
    pub fn assert_atom(&self, atom: TheoryAtomId, value: bool) -> Result<(), TheoryError> {
        self.asserted_truth[atom.0 as usize].set(if value { 1 } else { 2 });
        let (kind, left, right, bound) = self.atoms.get_atom(atom)?;
        match kind {
            super::kAtomKindEquality => {
                if value {
                    self.closure.assert_equal(TermNode(left), TermNode(right))?;
                }
                // A false equality is a disequality; it is checked against the
                // closure's classes after the fixpoint in check().
            }
            _ => {
                if value {
                    self.difference.add_constraint(left, right, bound)?;
                } else {
                    // The negation of x - y <= bound over the fixed-point Q is
                    // y - x <= -bound - 1: exact, one representation unit.
                    let negated = bound
                        .checked_neg()
                        .and_then(|value| value.checked_sub(1))
                        .ok_or(TheoryError::ArithmeticOverflow)?;
                    self.difference.add_constraint(right, left, negated)?;
                }
            }
        }
        Ok(())
    }

    /// CEP:WHAT: Runs the combination consistency check: per theory consistency, then the equality-propagation fixpoint (EUF merges to difference-logic zero pairs, difference-logic-entailed equalities to EUF merges), with disequality and negative-cycle violations re-checked every round.
    /// CEP:WHY: Design 13.3: each theory checks its own consistency and equalities over shared variables propagate; the fixpoint's agreement is the combined theory's consistency for the fragment (Spec 21 section 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Ok(true) when the assignment is combination-consistent, Ok(false) when a conflict was found, and TheoryError past the round bound or on storage failures.
    /// CEP:ASSUMES: the assertion batch completed before the call.
    /// CEP:COST: O(rounds x (closure + Bellman-Ford + pair tests)) under the named bounds.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::{nelson_oppen_combines_theories, nelson_oppen_conflict_across_theories}.
    /// CEP:SECURITY: bounded rounds.
    pub fn check(&self) -> Result<bool, TheoryError> {
        for _ in 0..mapt_config::limits::kMaxTheoryPropagationRounds {
            // 1. Per-theory consistency.
            self.closure.check(&self.graph)?;
            let variables = mapt_config::limits::kMaxTheoryVars;
            for atom_id in 0..self.atoms.atom_count() {
                let (kind, left, right, _) = self.atoms.get_atom(TheoryAtomId(atom_id))?;
                if kind == super::kAtomKindEquality
                    && self.asserted_truth[atom_id as usize].get() == 2
                {
                    // A false equality is a disequality: violated when the batch
                    // asserted it false AND the closure merged the two classes.
                    if self.closure.find(TermNode(left))? == self.closure.find(TermNode(right))? {
                        return Ok(false);
                    }
                }
            }
            if !self.difference.check()? {
                return Ok(false);
            }
            // 2. EUF to difference logic: every shared pair merged in EUF becomes
            //    a zero equality in the difference logic.
            let mut changed = false;
            for left in 0..variables {
                for right in (left + 1)..variables {
                    let left_node = self.graph.var_node(left)?;
                    let right_node = self.graph.var_node(right)?;
                    let merged = self.closure.find(left_node)? == self.closure.find(right_node)?;
                    let zero_merged = self.difference.zero_equal(left, right)?;
                    if merged && !zero_merged {
                        self.difference.add_zero_equality(left, right)?;
                        changed = true;
                    }
                }
            }
            // 3. Difference logic to EUF: a shared pair whose equality the
            //    difference logic entails must be merged in EUF (the model must
            //    identify the pair, so the closure is re-run with the merge).
            for left in 0..variables {
                if !self.difference.occurs_in(left)? {
                    continue;
                }
                for right in (left + 1)..variables {
                    if !self.difference.occurs_in(right)? {
                        continue;
                    }
                    if self.difference.zero_equal(left, right)? {
                        continue;
                    }
                    let left_node = self.graph.var_node(left)?;
                    let right_node = self.graph.var_node(right)?;
                    let merged = self.closure.find(left_node)? == self.closure.find(right_node)?;
                    if merged {
                        continue;
                    }
                    if self.difference.entailed_equal(left, right)? {
                        self.closure.assert_equal(left_node, right_node)?;
                        self.difference.add_zero_equality(left, right)?;
                        changed = true;
                    }
                }
            }
            if !changed {
                // 4. Final agreement: every EUF-merged pair is now zero-merged and
                //    every difference-logic entailment is EUF-merged; the fixpoint
                //    is the combination's consistency (Spec 21 section 6).
                return Ok(true);
            }
        }
        Err(TheoryError::PropagationRounds)
    }
}
