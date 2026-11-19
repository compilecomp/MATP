// CEP:FILE: hot/theory/dpll_t.rs
// CEP:WHAT: The DPLL(T) outer loop (design 13.2, Nieuwenhuis, Oliveras & Tinelli 2006): theory atoms registered once map to SAT variables in a CDCL solver; each solve proposes a Boolean assignment over the atoms, the Nelson-Oppen coordinator checks its consistency, an inconsistent assignment yields the theory lemma (the negation of the full atom assignment), the solver adds the lemma and continues, and the loop ends Satisfiable (theory-backed), Unsatisfiable, or Unknown at the conflict budget.
// CEP:WHY: Design 13.2 steps 1-5 and design 13.6's lemma generation: the lemma over the full assignment is theory-valid because the assignment is theory-inconsistent, and each lemma excludes exactly one assignment, so the loop is complete over the finite atom space with the budget as the loud bound; the lemma clause enters the proof trace through the axiom path because it is theory-valid but not RUP against the Boolean abstraction (Spec 21 section 5; the proof-graph TheoryLemma derivation source's producer surface is the coordinator's conflict report). Theory propagation (the online form's step where the theory suggests decisions) is the measured follow-up - the offline loop is complete without it (Spec 21 section 4, ticket CEP-1070).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: every entry point returns Result with TheoryError on registration, encoding, or solver failures; the loop returns TheoryStatus::Unknown at kMaxTheoryConflicts with the count reported; never panics.
// CEP:ASSUMES: single-threaded; atoms are registered and clauses added before the first solve; atom i is SAT variable i; the solver is owned by this structure.
// CEP:COST: one iteration is one SAT solve plus one theory check; the lemma width is the atom count.
// CEP:EVIDENCE: unit/hot/theory_test.rs::{dpll_t_satisfiable_end_to_end, dpll_t_unsat_via_lemmas, conflict_budget_unknown}; property/theory_property_test.rs.
// CEP:SECURITY: the loop is bounded by kMaxTheoryConflicts; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; atoms are asserted and lemmas built in id order (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;
use crate::sat::database::SatCoreError;
use crate::sat::literal::{SatLiteral, SatVar};
use crate::sat::restart::RestartPolicy;
use crate::sat::solver::{CdclSolver, SolveResult};
use mapt_config::limits::{kMaxTheoryAtoms, kMaxTheoryConflicts};

use super::nelson_oppen::NelsonOppen;
use super::term_graph::TermNode;
use super::{TheoryAtomId, TheoryError};

/// CEP:WHAT: The DPLL(T) outcome: the status plus the conflict count.
/// CEP:WHY: Honesty (Law 4): an Unknown outcome reports how much work was done.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: 8 bytes.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
/// CEP:SECURITY: none.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct TheoryOutcome {
    /// CEP:WHAT: The run's status.
    /// CEP:WHY: Satisfiable means a theory-backed model exists over the atoms; Unsatisfiable means the abstraction (plus theory-valid lemmas) is refuted; Unknown means the budget stopped the loop.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: none.
    pub status: TheoryStatus,
    /// CEP:WHAT: Theory conflicts handled (one lemma each).
    /// CEP:WHY: The honesty counter of design 13.6's lemma generation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_unsat_via_lemmas.
    /// CEP:SECURITY: none.
    pub conflicts: u32,
}

/// CEP:WHAT: The DPLL(T) status vocabulary.
/// CEP:WHY: The three-way outcome keeps the budget stop honest (never a silent SAT or UNSAT claim past the bound).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: enum value.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
/// CEP:SECURITY: none.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TheoryStatus {
    /// CEP:WHAT: The atom assignment's Boolean model is theory-consistent: a combined model exists.
    /// CEP:WHY: Design 13.2's successful end.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: read atom values with atom_value.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: none.
    Satisfiable,
    /// CEP:WHAT: The abstraction plus the theory lemmas is refuted; since every lemma is theory-valid, the original formula is unsatisfiable.
    /// CEP:WHY: Design 13.2's refuting end.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the lemma trust axiom of Spec 21 section 5.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_unsat_via_lemmas.
    /// CEP:SECURITY: none.
    Unsatisfiable,
    /// CEP:WHAT: The conflict budget stopped the loop; no verdict.
    /// CEP:WHY: The honest partial outcome (Law 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the conflict count reports the work done.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
    /// CEP:SECURITY: none.
    Unknown,
}

/// CEP:WHAT: The DPLL(T) solver: the CDCL engine over the atom variables, the Nelson-Oppen coordinator, and the lemma loop, composed into one search state machine.
/// CEP:WHY: Design 13.2's architecture in one owner, so the atom surface, the encoding, and the lemma construction cannot drift apart.
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError and TheoryOutcome.
/// CEP:ASSUMES: one arena outlives the solver; registration precedes solving.
/// CEP:COST: one CDCL solver, one coordinator, and one truth row per solver.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
/// CEP:SECURITY: bounds-checked throughout.
pub struct TheorySatSolver<'a> {
    /// CEP:WHAT: The CDCL solver over the atom variables.
    /// CEP:WHY: Design 13.2 step 1: the SAT engine proposes assignments; the theory lemmas join its database through the axiom path.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: constructed over kMaxTheoryAtoms variables; owned here.
    /// CEP:COST: see CdclSolver.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: bounds-checked.
    solver: CdclSolver<'a>,
    /// CEP:WHAT: The Nelson-Oppen coordinator.
    /// CEP:WHY: Design 13.2 step 2: the theory consistency check.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: atom registration routed through it.
    /// CEP:COST: see NelsonOppen.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked.
    coordinator: NelsonOppen<'a>,
    /// CEP:WHAT: The per-atom model truth read at each Satisfiable solve.
    /// CEP:WHY: The assertion batch and the lemma builder both read one snapshot.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryAtoms.
    /// CEP:COST: 1 byte per atom.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_unsat_via_lemmas.
    /// CEP:SECURITY: bounds-checked reads.
    truth: &'a [Cell<bool>],
    /// CEP:WHAT: Theory conflicts handled so far.
    /// CEP:WHY: The loop's budget counter and the outcome's honesty figure.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= the conflict budget.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
    /// CEP:SECURITY: none.
    conflicts: Cell<u32>,
    /// CEP:WHAT: The conflict budget of one solve run.
    /// CEP:WHY: kMaxTheoryConflicts by default; injectable for the bounds tests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
    /// CEP:SECURITY: denial-of-service bound under test.
    conflict_budget: u32,
}

impl<'a> TheorySatSolver<'a> {
    /// CEP:WHAT: Constructs the DPLL(T) solver over the arena: the CDCL engine over kMaxTheoryAtoms variables and the coordinator.
    /// CEP:WHY: Design 4.1: every structure is fully built before use.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError on arena exhaustion or solver construction failure.
    /// CEP:ASSUMES: the arena has room for every substructure.
    /// CEP:COST: O(capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<TheorySatSolver<'a>, TheoryError> {
        Self::new_with_conflict_budget(arena, kMaxTheoryConflicts)
    }

    /// CEP:WHAT: Constructs the DPLL(T) solver with an injectable conflict budget.
    /// CEP:WHY: The budget bound is a named limit with an honest Unknown outcome; the injectable form lets the bounds tests pin the stop at a small budget (the same discipline as the CDCL solver's new_with_conflict_budget).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError on arena exhaustion or solver construction failure.
    /// CEP:ASSUMES: budget >= 1.
    /// CEP:COST: O(capacities) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::conflict_budget_unknown.
    /// CEP:SECURITY: denial-of-service bound under test.
    pub fn new_with_conflict_budget(
        arena: &'a Arena,
        conflict_budget: u32,
    ) -> Result<TheorySatSolver<'a>, TheoryError> {
        let solver = CdclSolver::new(arena, kMaxTheoryAtoms, RestartPolicy::Luby, false)
            .map_err(TheoryError::Sat)?;
        let coordinator = NelsonOppen::new(arena)?;
        let truth = Self::alloc_bool(arena)?;
        Ok(TheorySatSolver {
            solver,
            coordinator,
            truth,
            conflicts: Cell::new(0),
            conflict_budget,
        })
    }

    // CEP:WHAT: Allocates the per-atom truth row.
    // CEP:WHY: One translation point for the arena error (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    // CEP:SECURITY: none.
    fn alloc_bool(arena: &'a Arena) -> Result<&'a [Cell<bool>], TheoryError> {
        let range = arena
            .alloc_array::<Cell<bool>>(kMaxTheoryAtoms)
            .map_err(|_| {
                TheoryError::Storage(SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::ArenaFull,
                ))
            })?;
        arena.array::<Cell<bool>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: The coordinator's term graph, for term construction before registration.
    /// CEP:WHY: EUF equality atoms reference term nodes.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before registration.
    /// CEP:COST: one reference.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: none.
    pub fn graph(&self) -> &super::term_graph::TermGraph<'a> {
        self.coordinator.graph()
    }

    /// CEP:WHAT: Registers an EUF equality atom and returns its id (atom i is SAT variable i).
    /// CEP:WHY: Design 13.2's Boolean abstraction surface.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError.
    /// CEP:ASSUMES: called before the first solve.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_satisfiable_end_to_end.
    /// CEP:SECURITY: bounded by the atom capacity.
    pub fn register_equality(
        &self,
        left: TermNode,
        right: TermNode,
    ) -> Result<TheoryAtomId, TheoryError> {
        self.coordinator.atoms().equality_atom(left, right)
    }

    /// CEP:WHAT: Registers a difference-constraint atom (x - y <= bound) and returns its id.
    /// CEP:WHY: The arithmetic fragment's abstraction surface.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError.
    /// CEP:ASSUMES: called before the first solve.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_unsat_via_lemmas.
    /// CEP:SECURITY: bounded by the atom capacity.
    pub fn register_difference(
        &self,
        left: u32,
        right: u32,
        bound: i64,
    ) -> Result<TheoryAtomId, TheoryError> {
        self.coordinator.atoms().difference_atom(left, right, bound)
    }

    /// CEP:WHAT: Adds one clause of the Boolean abstraction: each literal is (atom, polarity), mapped to the SAT literal of variable atom with that polarity, and recorded through the axiom path (the abstraction is the caller-supplied formula).
    /// CEP:WHY: Design 13.2 step 1's input side; the axiom path is correct because the abstraction's clauses are the problem clauses, while the theory lemmas added during the loop are theory-valid non-RUP additions recorded as axioms too (the documented trust axiom of Spec 21 section 5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError (atom capacity on an out-of-range atom id, Sat on solver failures); never panics.
    /// CEP:ASSUMES: called before the first solve or between solves at level 0.
    /// CEP:COST: O(clause length).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::dpll_t_unsat_via_lemmas.
    /// CEP:SECURITY: bounded by the clause length bound of the SAT core.
    pub fn add_clause(&self, literals: &[(TheoryAtomId, bool)]) -> Result<(), TheoryError> {
        let mut encoded = [SatLiteral::from_encoding(0); kMaxTheoryAtoms as usize];
        if literals.len() > kMaxTheoryAtoms as usize {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        for (slot, (atom, polarity)) in literals.iter().enumerate() {
            if atom.0 >= self.coordinator.atoms().atom_count() {
                return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
            }
            encoded[slot] = SatLiteral::new(SatVar(atom.0), *polarity)
                .map_err(|_| TheoryError::Storage(SatCoreError::InvariantViolation))?;
        }
        self.solver
            .add_clause(&encoded[..literals.len()])
            .map_err(TheoryError::Sat)?;
        Ok(())
    }

    /// CEP:WHAT: Runs the DPLL(T) loop: solve, assert the model's atom values into the coordinator, check consistency, and on conflict add the theory lemma (the negation of the full atom assignment) and repeat, until Satisfiable, Unsatisfiable, or the conflict budget.
    /// CEP:WHY: Design 13.2 steps 1-5 and design 13.6: the lemma is theory-valid (the assignment is inconsistent), it excludes exactly the current assignment, and the loop is complete over the finite atom space with the budget as the loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError on solver or theory failures and TheoryOutcome::Unknown at the budget; never panics.
    /// CEP:ASSUMES: registration and clause additions completed (or happen between iterations at level 0).
    /// CEP:COST: one SAT solve plus one theory check per iteration.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::{dpll_t_satisfiable_end_to_end, dpll_t_unsat_via_lemmas, conflict_budget_unknown}.
    /// CEP:SECURITY: the loop is bounded by kMaxTheoryConflicts.
    pub fn solve(&self) -> Result<TheoryOutcome, TheoryError> {
        let atom_count = self.coordinator.atoms().atom_count();
        for _ in 0..self.conflict_budget {
            match self.solver.solve() {
                SolveResult::Unsatisfiable => {
                    return Ok(TheoryOutcome {
                        status: TheoryStatus::Unsatisfiable,
                        conflicts: self.conflicts.get(),
                    });
                }
                SolveResult::Indeterminate(_) => {
                    // The SAT solver's own conflict budget stopped this solve; no
                    // verdict is possible without a change, so the honest outcome
                    // is Unknown (the theory loop cannot retry a fixed state).
                    return Ok(TheoryOutcome {
                        status: TheoryStatus::Unknown,
                        conflicts: self.conflicts.get(),
                    });
                }
                SolveResult::Satisfiable => {
                    // Read the model over every atom (the CDCL guarantee: after a
                    // Satisfiable solve every variable is assigned).
                    for atom in 0..atom_count {
                        let value = match self.solver.model_value(atom) {
                            Some(value) => value,
                            None => {
                                return Err(TheoryError::HashTableFull); // TEMP-DIAG
                            }
                        };
                        self.truth[atom as usize].set(value);
                    }
                    // Assert the batch into the coordinator and check.
                    self.coordinator.reset();
                    for atom in 0..atom_count {
                        self.coordinator
                            .assert_atom(TheoryAtomId(atom), self.truth[atom as usize].get())?;
                    }
                    if self.coordinator.check()? {
                        return Ok(TheoryOutcome {
                            status: TheoryStatus::Satisfiable,
                            conflicts: self.conflicts.get(),
                        });
                    }
                    // Theory conflict: the lemma is the negation of the full atom
                    // assignment (theory-valid: the assignment is inconsistent;
                    // Spec 21 section 5). The atom values are already snapshotted,
                    // so the solver returns to level 0 for the lemma addition (the
                    // sanctioned inter-solve path; Spec 21 section 4).
                    self.solver
                        .return_to_root_level()
                        .map_err(TheoryError::Sat)?;
                    let mut lemma = [SatLiteral::from_encoding(0); kMaxTheoryAtoms as usize];
                    for atom in 0..atom_count {
                        lemma[atom as usize] =
                            SatLiteral::new(SatVar(atom), !self.truth[atom as usize].get())
                                .map_err(|_| TheoryError::AtomCapacity)?; // TEMP-DIAG
                    }
                    self.solver
                        .add_clause(&lemma[..atom_count as usize])
                        .map_err(TheoryError::Sat)?;
                    self.conflicts.set(self.conflicts.get() + 1);
                }
            }
        }
        Ok(TheoryOutcome {
            status: TheoryStatus::Unknown,
            conflicts: self.conflicts.get(),
        })
    }

    /// CEP:WHAT: Returns the model's value of one atom after a Satisfiable outcome.
    /// CEP:WHY: Model extraction of the Boolean abstraction; the combined theory model realizes these truth values (design 13.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (None past the registered atom count).
    /// CEP:ASSUMES: called after TheoryStatus::Satisfiable.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: property/theory_property_test.rs.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn atom_value(&self, atom: TheoryAtomId) -> Option<bool> {
        if atom.0 >= self.coordinator.atoms().atom_count() {
            return None;
        }
        Some(self.truth[atom.0 as usize].get())
    }
}
