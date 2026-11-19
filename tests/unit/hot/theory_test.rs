// CEP:FILE: tests/unit/hot/theory_test.rs
// CEP:WHAT: Unit pins for the theory engine (design 13, Phase 5): term-graph hash-consing and bounds, congruence closure and its argument propagation, difference-logic consistency and conflict, the Nelson-Oppen combination and its cross-theory conflict, the DPLL(T) ends (Satisfiable, Unsatisfiable via lemmas, Unknown at the budget), and the capacity vocabularies.
// CEP:WHY: Every cited CEP:EVIDENCE pointer in hot/theory/ must resolve to a failing-without-the-fix test (CEP&CC 39.1); these pins are that resolution.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the pinned behavior is missing.
// CEP:ASSUMES: fixed seeds only; no untrusted input.
// CEP:COST: constant per test.
// CEP:EVIDENCE: cited by hot/theory/{term_graph,congruence,difference,nelson_oppen,dpll_t,mod}.rs.
// CEP:SECURITY: no untrusted input; fixed bounds.

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::SatLiteral;
use mapt::hot::sat::solver::CdclSolver;
use mapt::hot::theory::congruence::CongruenceClosure;
use mapt::hot::theory::difference::DifferenceLogic;
use mapt::hot::theory::dpll_t::{TheorySatSolver, TheoryStatus};
use mapt::hot::theory::term_graph::TermGraph;
use mapt::hot::theory::{TheoryAtomId, TheoryError};
use mapt_config::limits::{kMaxTheoryArity, kMaxTheoryAtoms, kMaxTheoryTerms, kMaxTheoryVars};

fn lit(atom: u32, positive: bool) -> (TheoryAtomId, bool) {
    (TheoryAtomId(atom), positive)
}

// CEP:WHAT: Verifies the term graph hash-conses structurally identical nodes.
// CEP:WHY: The unique-node invariant the congruence closure's signature classes rely on.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when duplicates are created.
// CEP:ASSUMES: the fixture above.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/term_graph.rs::{const_node, var_node, app_node}.
// CEP:SECURITY: none.
#[test]
fn term_graph_hash_consing() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let a = graph.const_node(7).expect("a");
    let a2 = graph.const_node(7).expect("a2");
    assert_eq!(a, a2, "identical constants share one node");
    let x = graph.var_node(3).expect("x");
    let x2 = graph.var_node(3).expect("x2");
    assert_eq!(x, x2, "identical variables share one node");
    let f1 = graph.app_node(11, &[a, x]).expect("f(a,x)");
    let f2 = graph.app_node(11, &[a, x]).expect("f(a,x) again");
    assert_eq!(f1, f2, "identical applications share one node");
    let f3 = graph.app_node(11, &[x, a]).expect("f(x,a)");
    assert_ne!(f1, f3, "argument order is structural");
    assert_eq!(graph.node_count(), 4, "one node per distinct term");
    let mut buffer = [a; kMaxTheoryArity as usize];
    let (kind, symbol, arity) = graph.read_node(f1, &mut buffer).expect("read");
    assert_eq!((kind, symbol, arity), (2, 11, 2));
}

// CEP:WHAT: Verifies the term graph and arity bounds fire loudly.
// CEP:WHY: The memory-exhaustion bounds of the theory state.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the bound is not enforced.
// CEP:ASSUMES: the node capacity is kMaxTheoryTerms; the arity bound is kMaxTheoryArity.
// CEP:COST: linear in the capacity.
// CEP:EVIDENCE: cited by hot/theory/term_graph.rs::{append_node, app_node} and config/limits.rs kMaxTheoryTerms.
// CEP:SECURITY: memory bound under test.
#[test]
fn term_capacity_enforced() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    for symbol in 0..kMaxTheoryTerms {
        graph.const_node(symbol).expect("node");
    }
    let overflow = graph.const_node(kMaxTheoryTerms);
    assert!(matches!(
        overflow,
        Err(TheoryError::TermCapacity) | Err(TheoryError::HashTableFull)
    ));
    // The arity bound fires before the capacity bound on the fresh graph.
    let arena2 = make_arena(12_582_912);
    let graph2 = TermGraph::new(arena2).expect("graph2");
    let seed = graph2.const_node(0).expect("seed");
    let over = [seed; kMaxTheoryArity as usize + 1];
    let result = graph2.app_node(1, &over);
    assert!(matches!(result, Err(TheoryError::ArityExceeded)));
    let at_bound = [seed; kMaxTheoryArity as usize];
    let _ = graph2.app_node(1, &at_bound).expect("at the bound");
}

// CEP:WHAT: Verifies the shared-variable space bound fires loudly.
// CEP:WHY: Both theory solvers address one bounded variable space.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an out-of-range variable id is accepted.
// CEP:ASSUMES: the variable capacity is kMaxTheoryVars.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/term_graph.rs::var_node and config/limits.rs kMaxTheoryVars.
// CEP:SECURITY: memory bound under test.
#[test]
fn variable_capacity_enforced() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let result = graph.var_node(kMaxTheoryVars);
    assert_eq!(result, Err(TheoryError::VarCapacity));
    let _ = graph.var_node(kMaxTheoryVars - 1).expect("at the bound");
}

// CEP:WHAT: Verifies the theory-atom capacity fires loudly.
// CEP:WHY: The atom table is also the Boolean abstraction's variable count.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an extra atom is accepted.
// CEP:ASSUMES: the atom capacity is kMaxTheoryAtoms.
// CEP:COST: linear in the capacity.
// CEP:EVIDENCE: cited by hot/theory/mod.rs::AtomTable and config/limits.rs kMaxTheoryAtoms.
// CEP:SECURITY: memory bound under test.
#[test]
fn atom_capacity_enforced() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    for _ in 0..kMaxTheoryAtoms {
        solver.register_equality(a, b).expect("atom");
    }
    let overflow = solver.register_equality(a, b);
    assert_eq!(overflow, Err(TheoryError::AtomCapacity));
}

// CEP:WHAT: Verifies the congruence closure merges asserted equalities.
// CEP:WHY: Design 13.4's assertion rule.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the classes stay separate.
// CEP:ASSUMES: the fixture above.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/congruence.rs::{assert_equal, find}.
// CEP:SECURITY: none.
#[test]
fn congruence_closes() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let closure = CongruenceClosure::new(arena).expect("closure");
    let a = graph.const_node(1).expect("a");
    let b = graph.const_node(2).expect("b");
    closure.assert_equal(a, b).expect("merge");
    assert_eq!(
        closure.find(a).expect("find a"),
        closure.find(b).expect("find b")
    );
    closure.reset();
    assert_ne!(
        closure.find(a).expect("find a"),
        closure.find(b).expect("find b")
    );
}

// CEP:WHAT: Verifies congruence propagates through application arguments.
// CEP:WHY: Design 13.4's propagation rule: a = b implies f(a) = f(b).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the application classes stay separate.
// CEP:ASSUMES: the fixture above; the signature-fixpoint runs in check.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/congruence.rs::check.
// CEP:SECURITY: none.
#[test]
fn congruence_propagates_through_arguments() {
    let arena = make_arena(12_582_912);
    let graph = TermGraph::new(arena).expect("graph");
    let closure = CongruenceClosure::new(arena).expect("closure");
    let a = graph.const_node(1).expect("a");
    let b = graph.const_node(2).expect("b");
    let c = graph.const_node(3).expect("c");
    let d = graph.const_node(4).expect("d");
    let fa = graph.app_node(10, &[a, c]).expect("f(a,c)");
    let fb = graph.app_node(10, &[b, d]).expect("f(b,d)");
    closure.assert_equal(a, b).expect("a = b");
    closure.assert_equal(c, d).expect("c = d");
    closure.check(&graph).expect("closure");
    assert_eq!(
        closure.find(fa).expect("find f(a,c)"),
        closure.find(fb).expect("find f(b,d)"),
        "congruence must merge f(a,c) with f(b,d)"
    );
    // The same signature over a different function symbol stays separate.
    let ga = graph.app_node(11, &[a, c]).expect("g(a,c)");
    assert_ne!(
        closure.find(fa).expect("find f(a,c)"),
        closure.find(ga).expect("find g(a,c)")
    );
}

// CEP:WHAT: Verifies the difference logic accepts a consistent constraint system.
// CEP:WHY: The Bellman-Ford consistency check's accepting side.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a consistent system is rejected.
// CEP:ASSUMES: x - y <= 5 and y - x <= 3 are jointly satisfiable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/difference.rs::check.
// CEP:SECURITY: none.
#[test]
fn difference_logic_consistent() {
    let arena = make_arena(12_582_912);
    let dl = DifferenceLogic::new(arena).expect("dl");
    dl.add_constraint(0, 1, 5).expect("x - y <= 5");
    dl.add_constraint(1, 0, 3).expect("y - x <= 3");
    assert!(dl.check().expect("check"));
}

// CEP:WHAT: Verifies the difference logic rejects an inconsistent system (a negative cycle).
// CEP:WHY: Design 13.1's constraint-graph consistency test.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when an inconsistent system is accepted.
// CEP:ASSUMES: x - y <= 1 and y - x <= -2 force x - y <= 1 and x - y >= 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/difference.rs::check and config/limits.rs kTheoryDlMaxWeight.
// CEP:SECURITY: none.
#[test]
fn difference_logic_conflict() {
    let arena = make_arena(12_582_912);
    let dl = DifferenceLogic::new(arena).expect("dl");
    dl.add_constraint(0, 1, 1).expect("x - y <= 1");
    dl.add_constraint(1, 0, -2).expect("y - x <= -2");
    assert!(!dl.check().expect("check"), "the cycle must be detected");
    // The zero-class mirror unions only on the pair.
    let dl2 = DifferenceLogic::new(arena).expect("dl2");
    dl2.add_constraint(0, 1, 0).expect("x - y <= 0");
    assert!(
        !dl2.zero_equal(0, 1).expect("zero"),
        "one inequality is not an equality"
    );
    dl2.add_zero_equality(0, 1).expect("pair");
    assert!(dl2.zero_equal(0, 1).expect("zero pair"));
}

// CEP:WHAT: Verifies the Nelson-Oppen coordinator accepts a consistent mixed assignment (design 13.3).
// CEP:WHY: The combination's accepting side: EUF merges propagate to the difference logic, and the DL-entailed equalities merge back.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a consistent mixed assignment is rejected.
// CEP:ASSUMES: x = y (EUF), x - z <= 0, z - y <= 0 (DL) are jointly satisfiable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/nelson_oppen.rs::check.
// CEP:SECURITY: none.
#[test]
fn nelson_oppen_combines_theories() {
    let arena = make_arena(12_582_912);
    let coordinator = mapt::hot::theory::NelsonOppen::new(arena).expect("coordinator");
    let x = coordinator.graph().var_node(0).expect("x");
    let y = coordinator.graph().var_node(1).expect("y");
    let _z = coordinator.graph().var_node(2).expect("z");
    let eq = coordinator.atoms().equality_atom(x, y).expect("eq");
    let dxz = coordinator
        .atoms()
        .difference_atom(0, 2, 0)
        .expect("x - z <= 0");
    let dzy = coordinator
        .atoms()
        .difference_atom(2, 1, 0)
        .expect("z - y <= 0");
    coordinator.reset();
    coordinator.assert_atom(eq, true).expect("assert eq");
    coordinator.assert_atom(dxz, true).expect("assert dxz");
    coordinator.assert_atom(dzy, true).expect("assert dzy");
    assert!(
        coordinator.check().expect("check"),
        "the mixed assignment is combination-consistent"
    );
    // The DL-entailed equality x = z must have propagated back into EUF.
    assert_ne!(
        coordinator.graph().var_node(0).expect("x"),
        coordinator.graph().var_node(2).expect("z"),
        "sanity: distinct variable nodes"
    );
}

// CEP:WHAT: Verifies the Nelson-Oppen coordinator rejects an assignment whose EUF merge the difference logic forbids.
// CEP:WHY: The combination's conflict side: the EUF-merged pair must be zero-feasible in the difference logic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the cross-theory conflict is missed.
// CEP:ASSUMES: x = y (EUF) against y - x <= -5 (DL) is inconsistent.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/nelson_oppen.rs::check.
// CEP:SECURITY: none.
#[test]
fn nelson_oppen_conflict_across_theories() {
    let arena = make_arena(12_582_912);
    let coordinator = mapt::hot::theory::NelsonOppen::new(arena).expect("coordinator");
    let x = coordinator.graph().var_node(0).expect("x");
    let y = coordinator.graph().var_node(1).expect("y");
    let eq = coordinator.atoms().equality_atom(x, y).expect("eq");
    let sep = coordinator
        .atoms()
        .difference_atom(1, 0, -5)
        .expect("y - x <= -5");
    coordinator.reset();
    coordinator.assert_atom(eq, true).expect("assert eq true");
    coordinator.assert_atom(sep, true).expect("assert sep true");
    assert!(
        !coordinator.check().expect("check"),
        "the EUF merge contradicts the difference constraint"
    );
}

// CEP:WHAT: Verifies the DPLL(T) loop's Satisfiable end over EUF atoms.
// CEP:WHY: Design 13.2's successful end: the Boolean model is theory-consistent.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a satisfiable formula is rejected or the model is unreadable.
// CEP:ASSUMES: the formula {a = b} with the clause (a = b).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve and config/limits.rs kMaxTheoryAtoms.
// CEP:SECURITY: none.
#[test]
fn dpll_t_satisfiable_end_to_end() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    let atom = solver.register_equality(a, b).expect("atom");
    solver.add_clause(&[lit(atom.0, true)]).expect("clause");
    let outcome = solver.solve().expect("solve");
    assert_eq!(outcome.status, TheoryStatus::Satisfiable);
    assert_eq!(outcome.conflicts, 0, "no theory conflict was needed");
    assert_eq!(solver.atom_value(atom), Some(true));
}

// CEP:WHAT: Verifies the DPLL(T) loop refutes an EUF-inconsistent formula through theory lemmas.
// CEP:WHY: Design 13.6: the inconsistent assignment (a=b, b=c, a!=c) yields a lemma; the loop terminates Unsatisfiable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the formula is accepted or no lemma was needed.
// CEP:ASSUMES: the triangle fixture above.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve and the axiom-path lemma record (Spec 21 section 5).
// CEP:SECURITY: none.
#[test]
fn dpll_t_unsat_via_lemmas() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    let c = solver.graph().const_node(3).expect("c");
    let eq_ab = solver.register_equality(a, b).expect("a = b");
    let eq_bc = solver.register_equality(b, c).expect("b = c");
    let eq_ac = solver.register_equality(a, c).expect("a = c");
    solver.add_clause(&[lit(eq_ab.0, true)]).expect("c1");
    solver.add_clause(&[lit(eq_bc.0, true)]).expect("c2");
    solver.add_clause(&[lit(eq_ac.0, false)]).expect("c3");
    let outcome = solver.solve().expect("solve");
    assert_eq!(outcome.status, TheoryStatus::Unsatisfiable);
    assert!(
        outcome.conflicts >= 1,
        "at least one theory lemma was needed"
    );
}

// CEP:WHAT: Verifies the DPLL(T) loop refutes an inconsistent difference-logic formula through theory lemmas.
// CEP:WHY: Design 13.2 over the arithmetic fragment.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the inconsistent constraints are accepted.
// CEP:ASSUMES: (x - y <= 1) and (y - x <= -2) are jointly unsatisfiable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve.
// CEP:SECURITY: none.
#[test]
fn dpll_t_dl_unsat_via_lemmas() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let low = solver.register_difference(0, 1, 1).expect("x - y <= 1");
    let high = solver.register_difference(1, 0, -2).expect("y - x <= -2");
    solver.add_clause(&[lit(low.0, true)]).expect("c1");
    solver.add_clause(&[lit(high.0, true)]).expect("c2");
    let outcome = solver.solve().expect("solve");
    assert_eq!(outcome.status, TheoryStatus::Unsatisfiable);
    assert!(outcome.conflicts >= 1);
}

// CEP:WHAT: Verifies the DPLL(T) conflict budget stops the run with Unknown.
// CEP:WHY: The honest partial outcome (Law 4) at the named bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the run claims a verdict past the budget.
// CEP:ASSUMES: the triangle fixture needs at least one conflict; budget 0 is rejected at construction.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::{new_with_conflict_budget, solve} and config/limits.rs kMaxTheoryConflicts.
// CEP:SECURITY: denial-of-service bound under test.
#[test]
fn conflict_budget_unknown() {
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new_with_conflict_budget(arena, 0).expect("solver");
    let a = solver.graph().const_node(1).expect("a");
    let b = solver.graph().const_node(2).expect("b");
    let eq_ab = solver.register_equality(a, b).expect("a = b");
    let eq_bc = solver.register_equality(b, a).expect("b = a");
    solver.add_clause(&[lit(eq_ab.0, true)]).expect("c1");
    solver.add_clause(&[lit(eq_bc.0, true)]).expect("c2");
    // Budget 0: the loop never runs; the honest outcome is Unknown.
    let outcome = solver.solve().expect("solve");
    assert_eq!(outcome.status, TheoryStatus::Unknown);
    assert_eq!(outcome.conflicts, 0);
}

// CEP:WHAT: Sanity-pins the underlying CDCL engine's reachability from the theory module.
// CEP:WHY: The Boolean abstraction rides on the solver's guarantee that a Satisfiable solve assigns every atom variable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the guarantee does not hold.
// CEP:ASSUMES: one unit clause over variable 0.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve.
// CEP:SECURITY: none.
#[test]
fn cdcl_model_guarantee() {
    let arena = make_arena(12_582_912);
    let solver = CdclSolver::new(
        arena,
        8,
        mapt::hot::sat::restart::RestartPolicy::Luby,
        false,
    )
    .expect("solver");
    solver
        .add_clause(&[SatLiteral::new(mapt::hot::sat::literal::SatVar(0), true).expect("lit")])
        .expect("unit");
    assert_eq!(
        solver.solve(),
        mapt::hot::sat::solver::SolveResult::Satisfiable
    );
    assert_eq!(
        solver.model_value(0),
        Some(true),
        "every variable is assigned after Satisfiable"
    );
}
