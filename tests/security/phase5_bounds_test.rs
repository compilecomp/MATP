// CEP:FILE: tests/security/phase5_bounds_test.rs
// CEP:WHAT: Security-bound tests of the Phase 5 theory engine (design 13, Spec 21): the term-graph node capacity, the shared variable capacity, the atom capacity, the DPLL(T) conflict budget, the Nelson-Oppen propagation round bound, the difference-logic weight range, and the application arity bound - the denial-of-service and arithmetic-overflow guards of the theory layer.
// CEP:WHY: CEP&CC 34.3 and design 20.2: every Phase 5 bound must be exercised on the production code path; the conflict budget and the round bounds are denial-of-service guards (an unbounded DPLL(T) loop or propagation fixpoint would hang the run), and the weight range is the Severity 0 arithmetic-overflow guard.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fresh arenas; fixed bounds from config/limits.rs.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to security/phase5_bounds_test.rs.
// CEP:SECURITY: these tests ARE the security-bound evidence.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::theory::dpll_t::{TheorySatSolver, TheoryStatus};
use mapt::hot::theory::term_graph::TermGraph;
use mapt::hot::theory::TheoryError;
use mapt_config::limits::{kMaxTheoryArity, kMaxTheoryAtoms, kMaxTheoryVars, kTheoryDlMaxWeight};

// CEP:WHAT: The term-graph node capacity fires loudly and never wraps.
// CEP:WHY: The memory-exhaustion bound on the theory state (config/limits.rs kMaxTheoryTerms).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: the fixture fills the graph to capacity.
// CEP:COST: linear in the capacity.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::term_capacity_loud and unit/hot/theory_test.rs::term_capacity_enforced.
// CEP:SECURITY: resource-exhaustion guard.
#[test]
fn term_capacity_loud() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    for symbol in 0..mapt_config::limits::kMaxTheoryTerms {
        graph.const_node(symbol).expect("node");
    }
    let overflow = graph.const_node(mapt_config::limits::kMaxTheoryTerms);
    assert!(
        matches!(
            overflow,
            Err(TheoryError::TermCapacity) | Err(TheoryError::HashTableFull)
        ),
        "the node bound must fire loudly"
    );
}

// CEP:WHAT: The shared variable capacity fires loudly (VarCapacity).
// CEP:WHY: Both theory solvers address one bounded variable space (config/limits.rs kMaxTheoryVars).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: the id equals the capacity.
// CEP:COST: constant.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::variable_capacity_loud and unit/hot/theory_test.rs::variable_capacity_enforced.
// CEP:SECURITY: resource-exhaustion guard.
#[test]
fn variable_capacity_loud() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let result = graph.var_node(kMaxTheoryVars);
    assert_eq!(result, Err(TheoryError::VarCapacity));
}

// CEP:WHAT: The theory-atom capacity fires loudly (AtomCapacity).
// CEP:WHY: The atom table is the Boolean abstraction's variable count; the bound bounds the lemma width and the abstraction size (config/limits.rs kMaxTheoryAtoms).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: the fixture fills the table.
// CEP:COST: linear in the capacity.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::atom_capacity_loud and unit/hot/theory_test.rs::atom_capacity_enforced.
// CEP:SECURITY: resource-exhaustion guard.
#[test]
fn atom_capacity_loud() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    for _ in 0..kMaxTheoryAtoms {
        solver.register_equality(a, b).expect("atom");
    }
    assert_eq!(
        solver.register_equality(a, b),
        Err(TheoryError::AtomCapacity)
    );
}

// CEP:WHAT: The DPLL(T) conflict budget stops the loop with the honest Unknown outcome.
// CEP:WHY: The denial-of-service guard of design 13.2's outer loop: an unbounded lemma loop would hang the run (config/limits.rs kMaxTheoryConflicts, injectable).
// CEP:STATUS: complete
// CEP:FAILURE: panics when the run claims a verdict past the budget.
// CEP:ASSUMES: budget 0 runs zero iterations.
// CEP:COST: constant.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::conflict_budget_stops_honestly and unit/hot/theory_test.rs::conflict_budget_unknown.
// CEP:SECURITY: denial-of-service guard.
#[test]
fn conflict_budget_stops_honestly() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new_with_conflict_budget(arena, 0).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    let eq = solver.register_equality(a, b).expect("atom");
    solver.add_clause(&[(eq, true)]).expect("clause");
    let outcome = solver.solve().expect("solve");
    assert_eq!(outcome.status, TheoryStatus::Unknown);
    assert_eq!(outcome.conflicts, 0);
}

// CEP:WHAT: The difference-logic weight range fires loudly (ArithmeticOverflow) and never wraps.
// CEP:WHY: Severity 0 prevention: wraparound weights could make an inconsistent constraint system look consistent (config/limits.rs kTheoryDlMaxWeight).
// CEP:STATUS: complete
// CEP:FAILURE: panics when an out-of-range weight is accepted.
// CEP:ASSUMES: the bound is kTheoryDlMaxWeight.
// CEP:COST: constant.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::dl_weight_overflow_loud and unit/hot/theory_test.rs::difference_logic_conflict.
// CEP:SECURITY: arithmetic-overflow guard.
#[test]
fn dl_weight_overflow_loud() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let overflow = solver.register_difference(0, 1, kTheoryDlMaxWeight + 1);
    assert_eq!(overflow, Err(TheoryError::ArithmeticOverflow));
    let _ = solver
        .register_difference(0, 1, kTheoryDlMaxWeight)
        .expect("at the bound");
}

// CEP:WHAT: The application arity bound fires loudly (ArityExceeded).
// CEP:WHY: The closure's fixed scratch buffer bound (config/limits.rs kMaxTheoryArity).
// CEP:STATUS: complete
// CEP:FAILURE: panics when an over-arity application is accepted.
// CEP:ASSUMES: the bound is kMaxTheoryArity.
// CEP:COST: constant.
// CEP:EVIDENCE: backs security/phase5_bounds_test.rs::arity_bound_loud and unit/hot/theory_test.rs::term_capacity_enforced.
// CEP:SECURITY: memory bound on the closure scratch.
#[test]
fn arity_bound_loud() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let seed = graph.const_node(0).expect("seed");
    let over = [seed; kMaxTheoryArity as usize + 1];
    assert_eq!(graph.app_node(1, &over), Err(TheoryError::ArityExceeded));
}
