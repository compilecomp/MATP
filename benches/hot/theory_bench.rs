// CEP:FILE: benches/hot/theory_bench.rs
// CEP:WHAT: Theory-reasoning benchmarks (bench CEP-BENCH-0014): cycles per congruence-closure check (assert batch plus signature fixpoint) on a fixed term graph, cycles per difference-logic consistency check (assert batch plus Bellman-Ford) on a fixed constraint set, cycles per full DPLL(T) SAT solve (SAT solve plus theory assertion batch plus Nelson-Oppen check) on a fixed combined formula, and cycles per full DPLL(T) UNSAT run through the theory-lemma path.
// CEP:WHY: Design 26 Phase 5 ("DPLL(T) integration", "Congruence closure", "Nelson-Oppen combination") and design 13: the closure check is the EUF theory's per-assignment cost inside the DPLL(T) loop, the Bellman-Ford check is the arithmetic theory's per-assignment cost, and the two full runs are the loop's steady-state iteration and its conflict path; one bench file covers the Phase 5 theory engine's four measured surfaces (CEP&CC Law 4).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly).
// CEP:ASSUMES: The cycle counter is accurate; measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/theory/mod.rs (CEP:COST), hot/theory/congruence.rs (CEP:COST), hot/theory/difference.rs (CEP:COST), and hot/theory/dpll_t.rs (CEP:COST); artifacts theory_congruence_check.json, theory_dl_check.json, theory_dpll_t_solve.json, theory_dpll_t_unsat.json; baselines in scripts/bench_gate.py.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::hot::memory::arena::Arena;
use mapt::hot::theory::congruence::CongruenceClosure;
use mapt::hot::theory::difference::DifferenceLogic;
use mapt::hot::theory::dpll_t::TheorySatSolver;
use mapt::hot::theory::term_graph::TermGraph;
use mapt::hot::theory::TermNode;

// CEP:WHAT: Arena bytes for the closure and difference-logic check benches.
// CEP:WHY: Named fixture size (CEP&CC 11.3); one megabyte covers the term graph, the closure, and the difference logic with headroom.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kTheoryBenchArenaBytes: u32 = 1_048_576;

// CEP:WHAT: Arena bytes for the DPLL(T) solve benches (the CDCL engine over kMaxTheoryAtoms variables rides in the same region), and the measured iterations per solve run.
// CEP:WHY: Named fixture size matching the unit-suite fixture class (12 MiB covers the abstraction's registry and arrays); the iteration count keeps the deliberately leaked fixture memory bounded: 15 repeats x 4 iterations x 12 MiB is under one GiB per measurement block, because every fixture is Box::leaked for 'static lifetimes and never freed (the harness discipline shared with the preprocessing bench).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: memory bound on the bench itself.
const kTheoryBenchSolverArenaBytes: u32 = 12_582_912;
const kTheoryBenchSolverIterations: u32 = 4;

// CEP:WHAT: The congruence fixture: four constants, four variables, one application layer f(c_i, x_i), and one wrapper layer h(f_i), so the asserted merges propagate through two signature rounds.
// CEP:WHY: The fixture exercises the fixpoint's real work: asserted merges collide the f signatures first, then the h signatures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one graph, one closure, twelve nodes.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_congruence_fixture(
    arena: &'static Arena,
) -> (
    &'static TermGraph<'static>,
    &'static CongruenceClosure<'static>,
    [TermNode; 4],
    [TermNode; 4],
) {
    let graph = Box::leak(Box::new(TermGraph::new(arena).expect("graph")));
    let closure = Box::leak(Box::new(CongruenceClosure::new(arena).expect("closure")));
    let mut constants = [TermNode(0); 4];
    let mut variables = [TermNode(0); 4];
    let mut applications = [TermNode(0); 4];
    for (index, slot) in applications.iter_mut().enumerate() {
        constants[index] = graph.const_node(100 + index as u32).expect("const");
        variables[index] = graph.var_node(index as u32).expect("var");
        *slot = graph
            .app_node(50, &[constants[index], variables[index]])
            .expect("app");
    }
    for application in applications.iter() {
        graph.app_node(60, &[*application]).expect("wrap");
    }
    (graph, closure, constants, variables)
}

// CEP:WHAT: The difference-logic fixture: thirty chain constraints u_i - u_{i+1} <= 2 plus two zero-equality pairs, a consistent system.
// CEP:WHY: The fixture exercises the assert batch plus the full Bellman-Ford over a realistic edge count without a negative cycle (the conflict side is the unit pins' territory).
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver, thirty-two constraints.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_difference_fixture(arena: &'static Arena) -> &'static DifferenceLogic<'static> {
    let logic = Box::leak(Box::new(DifferenceLogic::new(arena).expect("logic")));
    for variable in 0..30u32 {
        logic
            .add_constraint(variable, variable + 1, 2 * (1 << 16))
            .expect("constraint");
    }
    logic.add_zero_equality(0, 5).expect("pair");
    logic.add_zero_equality(10, 20).expect("pair");
    logic
}

// CEP:WHAT: The DPLL(T) SAT fixture: six EUF equality atoms, four difference atoms, and five clauses whose first model is theory-consistent on the first solve.
// CEP:WHY: The fixture measures the loop's steady-state iteration (SAT solve, the assertion batch, the Nelson-Oppen propagation and check); the lemma path is measured separately by the UNSAT fixture.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver, ten atoms, five clauses.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_dpll_t_fixture(arena: &'static Arena) -> &'static TheorySatSolver<'static> {
    let solver = Box::leak(Box::new(TheorySatSolver::new(arena).expect("solver")));
    let graph = solver.graph();
    let c0 = graph.const_node(1).expect("c0");
    let c1 = graph.const_node(2).expect("c1");
    let x0 = graph.var_node(0).expect("x0");
    let x1 = graph.var_node(1).expect("x1");
    let x2 = graph.var_node(2).expect("x2");
    let fx0 = graph.app_node(10, &[x0, c0]).expect("f(x0,c0)");
    let fx1 = graph.app_node(10, &[x1, c0]).expect("f(x1,c0)");
    let fx2 = graph.app_node(10, &[x2, c0]).expect("f(x2,c0)");
    let eq_c = solver.register_equality(c0, c1).expect("atom c0 = c1");
    let eq_fx01 = solver.register_equality(fx0, fx1).expect("atom f0 = f1");
    let eq_fx12 = solver.register_equality(fx1, fx2).expect("atom f1 = f2");
    let eq_xx = solver.register_equality(x0, x2).expect("atom x0 = x2");
    let d_0 = solver
        .register_difference(0, 1, 4 * (1 << 16))
        .expect("x0-x1<=4");
    let d_1 = solver
        .register_difference(1, 2, 4 * (1 << 16))
        .expect("x1-x2<=4");
    let d_2 = solver
        .register_difference(1, 0, -2 * (1 << 16))
        .expect("x1-x0<=-2");
    let d_3 = solver
        .register_difference(2, 1, -2 * (1 << 16))
        .expect("x2-x1<=-2");
    solver.add_clause(&[(eq_c, true)]).expect("clause");
    solver.add_clause(&[(eq_fx01, true)]).expect("clause");
    solver.add_clause(&[(eq_fx12, true)]).expect("clause");
    solver
        .add_clause(&[(d_0, true), (d_2, true), (eq_xx, true)])
        .expect("clause");
    solver
        .add_clause(&[(d_1, true), (d_3, true)])
        .expect("clause");
    solver
}

// CEP:WHAT: Validates the SAT fixture's documented contract: the run ends Satisfiable with zero theory conflicts.
// CEP:WHY: A drifted fixture would silently measure a different workload than the one the CEP:EVIDENCE citations describe; the validation runs once per bench invocation, outside the measured loop.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the fixture's outcome drifts.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solve.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn validate_dpll_t_sat_fixture() {
    let region = allocate_aligned_region(kTheoryBenchSolverArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let solver = make_dpll_t_fixture(arena);
    let outcome = solver.solve().expect("fixture solve");
    if outcome.status != mapt::hot::theory::TheoryStatus::Satisfiable || outcome.conflicts != 0 {
        panic!(
            "dpll_t SAT fixture drifted: status {:?}, conflicts {}",
            outcome.status, outcome.conflicts
        );
    }
}

// CEP:WHAT: Builds the DPLL(T) UNSAT fixture: three forced EUF atoms whose assignment merges all three constants while the third atom is asserted false (a disequality), so the first model is theory-inconsistent and the lemma path drives the run to Unsatisfiable.
// CEP:WHY: The lemma path (design 13.6) is the loop's conflict surface: one theory conflict, then the lemma clause is falsified by the forced units at the root, and the run ends Unsatisfiable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver, three atoms, three unit clauses.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_dpll_t_unsat_fixture(arena: &'static Arena) -> &'static TheorySatSolver<'static> {
    let solver = Box::leak(Box::new(TheorySatSolver::new(arena).expect("solver")));
    let graph = solver.graph();
    let a = graph.const_node(1).expect("a");
    let b = graph.const_node(2).expect("b");
    let c = graph.const_node(3).expect("c");
    let eq_ab = solver.register_equality(a, b).expect("a = b");
    let eq_bc = solver.register_equality(b, c).expect("b = c");
    let eq_ac = solver.register_equality(a, c).expect("a = c");
    solver.add_clause(&[(eq_ab, true)]).expect("clause");
    solver.add_clause(&[(eq_bc, true)]).expect("clause");
    solver.add_clause(&[(eq_ac, false)]).expect("clause");
    solver
}

// CEP:WHAT: Validates the UNSAT fixture's documented contract: Unsatisfiable after exactly one theory conflict.
// CEP:WHY: Same drift guard as the SAT fixture; the deterministic search makes the conflict count a stable contract.
// CEP:STATUS: complete
// CEP:FAILURE: panics when the fixture's outcome drifts.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solve.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn validate_dpll_t_unsat_fixture() {
    let region = allocate_aligned_region(kTheoryBenchSolverArenaBytes).expect("region");
    let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let solver = make_dpll_t_unsat_fixture(arena);
    let outcome = solver.solve().expect("fixture solve");
    if outcome.status != mapt::hot::theory::TheoryStatus::Unsatisfiable || outcome.conflicts != 1 {
        panic!(
            "dpll_t UNSAT fixture drifted: status {:?}, conflicts {}",
            outcome.status, outcome.conflicts
        );
    }
}

// CEP:WHAT: Bench entry: measures the four theory surfaces.
// CEP:WHY: See the file header.
// CEP:STATUS: complete
// CEP:FAILURE: panics on fixture failure.
// CEP:ASSUMES: fresh fixtures.
// CEP:COST: see the measurements.
// CEP:EVIDENCE: the artifacts cited in the file header.
// CEP:SECURITY: none.
fn main() {
    // Congruence-closure check: reset, the asserted merges, and the signature
    // fixpoint over the fixed graph (the merges propagate through two
    // application layers, so the fixpoint runs its real rounds).
    {
        let region = allocate_aligned_region(kTheoryBenchArenaBytes).expect("region");
        let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
        let (graph, closure, constants, variables) = make_congruence_fixture(arena);
        let (check_median, check_min) = measure_cycles(500, |_| {
            // The measured op is the per-assignment theory batch of the DPLL(T)
            // loop: reset, the asserted merges, and the signature fixpoint.
            closure.reset();
            closure
                .assert_equal(constants[0], constants[1])
                .expect("merge");
            closure
                .assert_equal(variables[0], variables[1])
                .expect("merge");
            closure
                .assert_equal(constants[2], constants[3])
                .expect("merge");
            closure
                .assert_equal(variables[2], variables[3])
                .expect("merge");
            match closure.check(graph) {
                Ok(()) => 1u64,
                Err(_) => 0,
            }
        });
        write_artifact(&Measurement {
            bench_id: "CEP-BENCH-0014",
            name: "theory_congruence_check",
            iterations: 500,
            cycles_median: check_median,
            cycles_min: check_min,
        });
        println!(
            "theory_congruence_check: median {:.2} cycles/op, min {:.2} cycles/op",
            check_median, check_min
        );
    }

    // Difference-logic check: reset, the assert batch, and the Bellman-Ford.
    {
        let region = allocate_aligned_region(kTheoryBenchArenaBytes).expect("region");
        let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
        let logic = make_difference_fixture(arena);
        let (dl_median, dl_min) = measure_cycles(500, |_| {
            logic.reset();
            for variable in 0..30u32 {
                let _ = logic.add_constraint(variable, variable + 1, 2 * (1 << 16));
            }
            let _ = logic.add_zero_equality(0, 5);
            let _ = logic.add_zero_equality(10, 20);
            match logic.check() {
                Ok(true) => 1u64,
                _ => 0,
            }
        });
        write_artifact(&Measurement {
            bench_id: "CEP-BENCH-0014",
            name: "theory_dl_check",
            iterations: 500,
            cycles_median: dl_median,
            cycles_min: dl_min,
        });
        println!(
            "theory_dl_check: median {:.2} cycles/op, min {:.2} cycles/op",
            dl_median, dl_min
        );
    }

    // Full DPLL(T) SAT solve on the fixed combined formula (fresh solver per
    // iteration: the fixture's allocation is part of the per-run cost the
    // caller sees, matching the preprocessing round's discipline).
    {
        validate_dpll_t_sat_fixture();
        let (solve_median, solve_min) = measure_cycles(kTheoryBenchSolverIterations, |_| {
            let region = allocate_aligned_region(kTheoryBenchSolverArenaBytes).expect("region");
            let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
            let solver = make_dpll_t_fixture(arena);
            match solver.solve() {
                Ok(outcome) => u64::from(outcome.conflicts),
                Err(_) => 0,
            }
        });
        write_artifact(&Measurement {
            bench_id: "CEP-BENCH-0014",
            name: "theory_dpll_t_solve",
            iterations: kTheoryBenchSolverIterations,
            cycles_median: solve_median,
            cycles_min: solve_min,
        });
        println!(
            "theory_dpll_t_solve: median {:.2} cycles/op, min {:.2} cycles/op",
            solve_median, solve_min
        );
    }

    // Full DPLL(T) UNSAT run on the lemma-path fixture: one theory conflict,
    // then the lemma clause is falsified by the forced units at the root.
    {
        validate_dpll_t_unsat_fixture();
        let (unsat_median, unsat_min) = measure_cycles(kTheoryBenchSolverIterations, |_| {
            let region = allocate_aligned_region(kTheoryBenchSolverArenaBytes).expect("region");
            let arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
            let solver = make_dpll_t_unsat_fixture(arena);
            match solver.solve() {
                Ok(outcome) => u64::from(outcome.conflicts),
                Err(_) => 0,
            }
        });
        write_artifact(&Measurement {
            bench_id: "CEP-BENCH-0014",
            name: "theory_dpll_t_unsat",
            iterations: kTheoryBenchSolverIterations,
            cycles_median: unsat_median,
            cycles_min: unsat_min,
        });
        println!(
            "theory_dpll_t_unsat: median {:.2} cycles/op, min {:.2} cycles/op",
            unsat_median, unsat_min
        );
    }
}
