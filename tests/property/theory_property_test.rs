// CEP:FILE: tests/property/theory_property_test.rs
// CEP:WHAT: Property tests for the theory engine (design 13, Phase 5): random small EUF, difference-logic, and combined instances decided by TheorySatSolver and checked against independent brute-force oracles (naive union-find with a fixpoint congruence closure, and an independent Bellman-Ford over the constraint graph, both implemented test-side).
// CEP:WHY: The theory engine's soundness claims (Spec 21 sections 3, 6, 7) are theorem-level statements over unbounded inputs; the property form exercises random instances where every atom assignment is enumerable, so Satisfiable and Unsatisfiable are both decided exactly and a wrong conflict set, a missed congruence, or an unsound combination would flip a verdict.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the solver's verdict disagrees with the oracle.
// CEP:ASSUMES: fixed seeds only; the oracles are independently implemented from the hot-path code (no shared closure or Bellman-Ford code).
// CEP:COST: linear in seeds x assignments.
// CEP:EVIDENCE: cited by hot/theory/nelson_oppen.rs::check and hot/theory/dpll_t.rs::solve; Spec 21 section 8.
// CEP:SECURITY: no untrusted input; fixed seeds and bounds.

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, DeterministicRng};
use mapt::hot::theory::dpll_t::{TheorySatSolver, TheoryStatus};
use mapt::hot::theory::TheoryAtomId;

// CEP:WHAT: The fixed-point scale the DL tests use to express integer weights, derived from the named shift constant.
// CEP:WHY: Law 7: the tests must not hard-code the representation's shift; deriving it from kTheoryDlScaleShift keeps the oracle and the engine on one named source.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn scale() -> i64 {
    1 << mapt_config::limits::kTheoryDlScaleShift
}

// CEP:WHAT: The EUF oracle: builds the partition from the true equalities, closes it under congruence (a naive fixpoint over the term list), and checks the false equalities against it.
// CEP:WHY: Independently implemented from hot/theory/congruence.rs (no shared code).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: terms are indices into the caller's term list with (kind, symbol, args) triples.
// CEP:COST: O(terms squared x rounds) worst case over tiny instances.
// CEP:EVIDENCE: property/theory_property_test.rs::euf_instances_agree_with_oracle.
// CEP:SECURITY: none.
fn euf_consistent(
    terms: &[(u32, u32, Vec<usize>)],
    equalities: &[(usize, usize)],
    assignment: &[bool],
) -> bool {
    let count = terms.len();
    let mut parent: Vec<usize> = (0..count).collect();
    let find = |parent: &mut Vec<usize>, mut node: usize| -> usize {
        while parent[node] != node {
            parent[node] = parent[parent[node]];
            node = parent[node];
        }
        node
    };
    for (index, &(left, right)) in equalities.iter().enumerate() {
        if assignment[index] {
            let a = find(&mut parent, left);
            let b = find(&mut parent, right);
            parent[a] = b;
        }
    }
    // Congruence fixpoint: merge application nodes with equal signatures.
    loop {
        let mut merged = false;
        for i in 0..count {
            for j in 0..count {
                let (ki, si, ai) = &terms[i];
                let (kj, sj, aj) = &terms[j];
                if *ki != 2 || *kj != 2 || si != sj || ai.len() != aj.len() {
                    continue;
                }
                let same_args = ai
                    .iter()
                    .zip(aj.iter())
                    .all(|(&x, &y)| find(&mut parent, x) == find(&mut parent, y));
                if same_args {
                    let a = find(&mut parent, i);
                    let b = find(&mut parent, j);
                    if a != b {
                        parent[a] = b;
                        merged = true;
                    }
                }
            }
        }
        if !merged {
            break;
        }
    }
    for (index, &(left, right)) in equalities.iter().enumerate() {
        if !assignment[index] && find(&mut parent, left) == find(&mut parent, right) {
            return false;
        }
    }
    true
}

// CEP:WHAT: The difference-logic oracle: an independent Bellman-Ford over the constraint graph with the true constraints as edges and the false constraints as their exact negations.
// CEP:WHY: Independently implemented from hot/theory/difference.rs::check.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: constraints are (left, right, integer weight) triples; weights are already scaled.
// CEP:COST: O(vars x edges) per assignment.
// CEP:EVIDENCE: property/theory_property_test.rs::{dl_instances_agree_with_oracle, combined_instances_agree_with_oracle}.
// CEP:SECURITY: none.
fn dl_consistent(vars: usize, constraints: &[(usize, usize, i64)], assignment: &[bool]) -> bool {
    let mut edges: Vec<(usize, usize, i64)> = Vec::new();
    for (index, &(left, right, weight)) in constraints.iter().enumerate() {
        if assignment[index] {
            edges.push((left, right, weight));
        } else {
            edges.push((right, left, -weight - 1));
        }
    }
    let mut dist = vec![0i64; vars];
    for _ in 0..=vars {
        let mut changed = false;
        for &(l, r, w) in edges.iter() {
            if dist[r]
                .checked_add(w)
                .map(|value| value < dist[l])
                .unwrap_or(false)
            {
                dist[l] = dist[r] + w;
                changed = true;
            }
        }
        if !changed {
            return true;
        }
    }
    false
}

// CEP:WHAT: The clause-satisfaction half of the oracles.
// CEP:WHY: The abstraction's clauses must hold under the atom assignment.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(clauses).
// CEP:EVIDENCE: property/theory_property_test.rs.
// CEP:SECURITY: none.
fn clauses_satisfied(clauses: &[(usize, bool)], assignment: &[bool]) -> bool {
    // A clause is a DISJUNCTION: satisfied when some literal matches.
    clauses
        .iter()
        .any(|&(atom, positive)| assignment[atom] == positive)
}

// CEP:WHAT: The combined oracle: EUF partition plus congruence, difference-logic check, EUF merges propagated to the difference logic, and difference-logic-entailed equalities merged back into the partition, to a fixpoint (the test-side mirror of Spec 21 section 6, with independently implemented primitives).
// CEP:WHY: The combination's verdict must match an enumerable model search: a combined model exists iff the fixpoint stabilizes without a conflict and the shared pairs can be arranged.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: equality atoms come first in the atom order, difference atoms after.
// CEP:COST: O(assignments x fixpoint) over tiny instances.
// CEP:EVIDENCE: property/theory_property_test.rs::combined_instances_agree_with_oracle.
// CEP:SECURITY: none.
fn combined_consistent(
    vars: usize,
    terms: &[(u32, u32, Vec<usize>)],
    equalities: &[(usize, usize)],
    constraints: &[(usize, usize, i64)],
    assignment: &[bool],
) -> bool {
    let eq_count = equalities.len();
    let dl_count = constraints.len();
    let count = terms.len();
    let mut parent: Vec<usize> = (0..count).collect();
    let find = |parent: &mut Vec<usize>, mut node: usize| -> usize {
        while parent[node] != node {
            parent[node] = parent[parent[node]];
            node = parent[node];
        }
        node
    };
    let close_euf = |parent: &mut Vec<usize>| loop {
        let mut merged = false;
        for i in 0..count {
            for j in 0..count {
                let (ki, si, ai) = &terms[i];
                let (kj, sj, aj) = &terms[j];
                if *ki != 2 || *kj != 2 || si != sj || ai.len() != aj.len() {
                    continue;
                }
                let same_args = ai
                    .iter()
                    .zip(aj.iter())
                    .all(|(&x, &y)| find(parent, x) == find(parent, y));
                if same_args {
                    let a = find(parent, i);
                    let b = find(parent, j);
                    if a != b {
                        parent[a] = b;
                        merged = true;
                    }
                }
            }
        }
        if !merged {
            break;
        }
    };
    let dl_edges = |constraints: &[(usize, usize, i64)],
                    assignment: &[bool],
                    extra: &[(usize, usize, i64)]|
     -> Vec<(usize, usize, i64)> {
        let mut edges: Vec<(usize, usize, i64)> = Vec::new();
        for (index, &(left, right, weight)) in constraints.iter().enumerate() {
            if assignment[eq_count + index] {
                edges.push((left, right, weight));
            } else {
                edges.push((right, left, -weight - 1));
            }
        }
        edges.extend_from_slice(extra);
        edges
    };
    let bf = |vars: usize, edges: &[(usize, usize, i64)]| -> bool {
        let mut dist = vec![0i64; vars];
        for _ in 0..=vars {
            let mut changed = false;
            for &(l, r, w) in edges.iter() {
                if dist[r]
                    .checked_add(w)
                    .map(|value| value < dist[l])
                    .unwrap_or(false)
                {
                    dist[l] = dist[r] + w;
                    changed = true;
                }
            }
            if !changed {
                return true;
            }
        }
        false
    };
    let mut extra: Vec<(usize, usize, i64)> = Vec::new();
    for _ in 0..8 {
        // EUF side: merge the true equalities, close under congruence, check the false ones.
        for (index, &(left, right)) in equalities.iter().enumerate() {
            if assignment[index] {
                let a = find(&mut parent, left);
                let b = find(&mut parent, right);
                parent[a] = b;
            }
        }
        close_euf(&mut parent);
        for (index, &(left, right)) in equalities.iter().enumerate() {
            if !assignment[index] && find(&mut parent, left) == find(&mut parent, right) {
                return false;
            }
        }
        // Difference-logic side, including the propagated zero pairs.
        if !bf(vars, &dl_edges(constraints, assignment, &extra)) {
            return false;
        }
        // EUF merges to DL zero pairs.
        let mut changed = false;
        for u in 0..vars {
            for v in 0..vars {
                if u == v {
                    continue;
                }
                // The generated term list places the variable nodes at 1..=vars.
                let u_node = 1 + u;
                let v_node = 1 + v;
                if find(&mut parent, u_node) == find(&mut parent, v_node)
                    && !extra.iter().any(|&(a, b, w)| {
                        (a == u && b == v && w == 0) || (a == v && b == u && w == 0)
                    })
                {
                    extra.push((u, v, 0));
                    extra.push((v, u, 0));
                    changed = true;
                }
            }
        }
        // DL-entailed equalities merge back into the partition.
        for u in 0..vars {
            for v in 0..vars {
                if u == v {
                    continue;
                }
                let u_node = 1 + u;
                let v_node = 1 + v;
                if find(&mut parent, u_node) == find(&mut parent, v_node) {
                    continue;
                }
                // Entailment: both strict separations must be inconsistent
                // (the two-orientation test of Spec 21 section 6).
                let mut left_sep = dl_edges(constraints, assignment, &extra);
                left_sep.push((u, v, -1));
                let mut right_sep = dl_edges(constraints, assignment, &extra);
                right_sep.push((v, u, -1));
                if !bf(vars, &left_sep) && !bf(vars, &right_sep) {
                    let a = find(&mut parent, u_node);
                    let b = find(&mut parent, v_node);
                    parent[a] = b;
                    extra.push((u, v, 0));
                    extra.push((v, u, 0));
                    changed = true;
                }
            }
        }
        let _ = dl_count;
        if !changed {
            return true;
        }
    }
    false
}

// CEP:WHAT: Drives one EUF instance through the solver and the oracle and compares the verdicts.
// CEP:WHY: The property body for the EUF family.
// CEP:STATUS: complete
// CEP:FAILURE: panics the test on a verdict mismatch.
// CEP:ASSUMES: the solver result is never Unknown at these sizes.
// CEP:COST: constant per instance.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve.
// CEP:SECURITY: none.
fn check_euf_instance(seed: u64) {
    let mut rng = DeterministicRng::new(seed);
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let graph = solver.graph();
    // Terms: two constants, two variables, and four applications.
    let c0 = graph.const_node(1).expect("c0");
    let c1 = graph.const_node(2).expect("c1");
    let x0 = graph.var_node(0).expect("x0");
    let x1 = graph.var_node(1).expect("x1");
    let _fa0 = graph.app_node(10, &[c0, x0]).expect("f(c0,x0)");
    let _fa1 = graph.app_node(10, &[c1, x1]).expect("f(c1,x1)");
    let _fb0 = graph.app_node(11, &[x0]).expect("g(x0)");
    let _fb1 = graph.app_node(11, &[x1]).expect("g(x1)");
    let terms = vec![
        (0u32, 1u32, Vec::new()),
        (0, 2, Vec::new()),
        (1, 0, Vec::new()),
        (1, 1, Vec::new()),
        (2, 10, vec![0, 2]),
        (2, 10, vec![1, 3]),
        (2, 11, vec![2]),
        (2, 11, vec![3]),
    ];
    // Atoms: four random equalities over the eight terms.
    let mut equalities: Vec<(usize, usize)> = Vec::new();
    let mut atoms: Vec<(TheoryAtomId, usize, usize)> = Vec::new();
    for _ in 0..4 {
        let left = (rng.next_u64() as usize) % terms.len();
        let right = (rng.next_u64() as usize) % terms.len();
        let node_left = mapt::hot::theory::TermNode(left as u32);
        let node_right = mapt::hot::theory::TermNode(right as u32);
        let atom = solver
            .register_equality(node_left, node_right)
            .expect("atom");
        equalities.push((left, right));
        atoms.push((atom, left, right));
    }
    // Clauses: two random clauses over the four atoms.
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
    for _ in 0..2 {
        let mut clause = Vec::new();
        for _ in 0..2 {
            let atom = (rng.next_u64() as usize) % 4;
            let positive = rng.next_u64().is_multiple_of(2);
            clause.push((atom, positive));
        }
        clauses.push(clause.clone());
        let encoded: Vec<(TheoryAtomId, bool)> = clause
            .iter()
            .map(|&(atom, positive)| (atoms[atom].0, positive))
            .collect();
        solver.add_clause(&encoded).expect("clause");
    }
    let outcome = solver.solve().expect("solve");
    // Oracle: enumerate all assignments.
    let mut expected_sat = false;
    for mask in 0u32..16 {
        let assignment: Vec<bool> = (0..4).map(|i| (mask >> i) & 1 == 1).collect();
        if !clauses_satisfied(&clauses[0], &assignment)
            || !clauses_satisfied(&clauses[1], &assignment)
        {
            continue;
        }
        if euf_consistent(&terms, &equalities, &assignment) {
            expected_sat = true;
            break;
        }
    }
    let expected = if expected_sat {
        TheoryStatus::Satisfiable
    } else {
        TheoryStatus::Unsatisfiable
    };
    assert!(
        outcome.status != TheoryStatus::Unknown,
        "seed {}: the run must converge at these sizes",
        seed
    );
    assert_eq!(
        outcome.status, expected,
        "seed {}: the solver and the oracle disagree",
        seed
    );
}

// CEP:WHAT: Drives one difference-logic instance through the solver and the oracle.
// CEP:WHY: The property body for the arithmetic family.
// CEP:STATUS: complete
// CEP:FAILURE: panics the test on a verdict mismatch.
// CEP:ASSUMES: integer weights scaled by the scale() helper (2^kTheoryDlScaleShift).
// CEP:COST: constant per instance.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve.
// CEP:SECURITY: none.
fn check_dl_instance(seed: u64) {
    let mut rng = DeterministicRng::new(seed);
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let mut constraints: Vec<(usize, usize, i64)> = Vec::new();
    let mut atoms: Vec<TheoryAtomId> = Vec::new();
    for _ in 0..4 {
        let left = (rng.next_u64() as usize) % 3;
        let right = (rng.next_u64() as usize) % 3;
        let raw = (rng.next_u64() as i64 % 6) - 2;
        let atom = solver
            .register_difference(left as u32, right as u32, raw * scale())
            .expect("atom");
        constraints.push((left, right, raw * scale()));
        atoms.push(atom);
    }
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
    for _ in 0..2 {
        let mut clause = Vec::new();
        for _ in 0..2 {
            let atom = (rng.next_u64() as usize) % 4;
            let positive = rng.next_u64().is_multiple_of(2);
            clause.push((atom, positive));
        }
        clauses.push(clause.clone());
        let encoded: Vec<(TheoryAtomId, bool)> = clause
            .iter()
            .map(|&(atom, positive)| (atoms[atom], positive))
            .collect();
        solver.add_clause(&encoded).expect("clause");
    }
    let outcome = match solver.solve() {
        Ok(value) => value,
        Err(error) => panic!("seed {}: solve error {:?}", seed, error),
    };
    let mut expected_sat = false;
    for mask in 0u32..16 {
        let assignment: Vec<bool> = (0..4).map(|i| (mask >> i) & 1 == 1).collect();
        if !clauses_satisfied(&clauses[0], &assignment)
            || !clauses_satisfied(&clauses[1], &assignment)
        {
            continue;
        }
        if dl_consistent(3, &constraints, &assignment) {
            expected_sat = true;
            break;
        }
    }
    let expected = if expected_sat {
        TheoryStatus::Satisfiable
    } else {
        TheoryStatus::Unsatisfiable
    };
    assert!(
        outcome.status != TheoryStatus::Unknown,
        "seed {}: the run must converge at these sizes",
        seed
    );
    assert_eq!(
        outcome.status, expected,
        "seed {}: the solver and the oracle disagree",
        seed
    );
}

// CEP:WHAT: Drives one combined EUF+DL instance through the solver and the oracle.
// CEP:WHY: The property body for the Nelson-Oppen combination.
// CEP:STATUS: complete
// CEP:FAILURE: panics the test on a verdict mismatch.
// CEP:ASSUMES: equality atoms first, difference atoms after; the variable nodes sit at the end of the term list.
// CEP:COST: constant per instance.
// CEP:EVIDENCE: cited by hot/theory/nelson_oppen.rs::check; Spec 21 section 8.
// CEP:SECURITY: none.
fn check_combined_instance(seed: u64) {
    let mut rng = DeterministicRng::new(seed);
    let arena = make_arena(12_582_912);
    let solver = TheorySatSolver::new(arena).expect("solver");
    let graph = solver.graph();
    let c0 = graph.const_node(1).expect("c0");
    let x0 = graph.var_node(0).expect("x0");
    let x1 = graph.var_node(1).expect("x1");
    let x2 = graph.var_node(2).expect("x2");
    let _fx0 = graph.app_node(10, &[x0, c0]).expect("f(x0,c0)");
    let _fx1 = graph.app_node(10, &[x1, c0]).expect("f(x1,c0)");
    let _fx2 = graph.app_node(10, &[x2, c0]).expect("f(x2,c0)");
    // Term list for the oracle: constants, variables at the end, applications.
    let terms = vec![
        (0u32, 1u32, Vec::new()),
        (1, 0, Vec::new()),
        (1, 1, Vec::new()),
        (1, 2, Vec::new()),
        (2, 10, vec![1, 0]),
        (2, 10, vec![2, 0]),
        (2, 10, vec![3, 0]),
    ];
    // Two EUF equalities over the application nodes, two DL constraints.
    let mut equalities: Vec<(usize, usize)> = Vec::new();
    let mut eq_atoms: Vec<TheoryAtomId> = Vec::new();
    for _ in 0..2 {
        let pick = (rng.next_u64() as usize) % 3;
        let (left, right) = match pick {
            0 => (4usize, 5usize),
            1 => (4, 6),
            _ => (0, 1),
        };
        let atom = solver
            .register_equality(
                mapt::hot::theory::TermNode(left as u32),
                mapt::hot::theory::TermNode(right as u32),
            )
            .expect("eq atom");
        equalities.push((left, right));
        eq_atoms.push(atom);
    }
    let mut constraints: Vec<(usize, usize, i64)> = Vec::new();
    let mut dl_atoms: Vec<TheoryAtomId> = Vec::new();
    for _ in 0..2 {
        let left = (rng.next_u64() as usize) % 3;
        let right = (rng.next_u64() as usize) % 3;
        let raw = (rng.next_u64() as i64 % 5) - 2;
        let atom = solver
            .register_difference(left as u32, right as u32, raw * scale())
            .expect("dl atom");
        constraints.push((left, right, raw * scale()));
        dl_atoms.push(atom);
    }
    let mut clauses: Vec<Vec<(usize, bool)>> = Vec::new();
    for _ in 0..2 {
        let mut clause = Vec::new();
        for _ in 0..2 {
            let atom = (rng.next_u64() as usize) % 4;
            let positive = rng.next_u64().is_multiple_of(2);
            clause.push((atom, positive));
        }
        clauses.push(clause.clone());
        let encoded: Vec<(TheoryAtomId, bool)> = clause
            .iter()
            .map(|&(atom, positive)| {
                if atom < 2 {
                    (eq_atoms[atom], positive)
                } else {
                    (dl_atoms[atom - 2], positive)
                }
            })
            .collect();
        solver.add_clause(&encoded).expect("clause");
    }
    let outcome = solver.solve().expect("solve");
    let mut expected_sat = false;
    for mask in 0u32..16 {
        let assignment: Vec<bool> = (0..4).map(|i| (mask >> i) & 1 == 1).collect();
        if !clauses_satisfied(&clauses[0], &assignment)
            || !clauses_satisfied(&clauses[1], &assignment)
        {
            continue;
        }
        let consistent = combined_consistent(3, &terms, &equalities, &constraints, &assignment);
        if consistent {
            expected_sat = true;
            break;
        }
    }
    let expected = if expected_sat {
        TheoryStatus::Satisfiable
    } else {
        TheoryStatus::Unsatisfiable
    };
    assert!(
        outcome.status != TheoryStatus::Unknown,
        "seed {}: the run must converge at these sizes",
        seed
    );
    assert_eq!(
        outcome.status, expected,
        "seed {}: the solver and the oracle disagree",
        seed
    );
}

// CEP:WHAT: Property: random EUF instances agree with the brute-force oracle.
// CEP:WHY: The EUF verdicts' soundness and completeness over enumerable assignments.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any verdict mismatch.
// CEP:ASSUMES: 48 fixed seeds; four atoms per instance.
// CEP:COST: linear in seeds.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve; Spec 21 section 8.
// CEP:SECURITY: no untrusted input; fixed seeds.
#[test]
fn euf_instances_agree_with_oracle() {
    for seed in 1..=48u64 {
        check_euf_instance(seed);
    }
}

// CEP:WHAT: Property: random difference-logic instances agree with the brute-force oracle.
// CEP:WHY: The arithmetic verdicts' soundness and completeness over enumerable assignments.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any verdict mismatch.
// CEP:ASSUMES: 48 fixed seeds; four atoms per instance.
// CEP:COST: linear in seeds.
// CEP:EVIDENCE: cited by hot/theory/dpll_t.rs::solve; Spec 21 section 8.
// CEP:SECURITY: no untrusted input; fixed seeds.
#[test]
fn dl_instances_agree_with_oracle() {
    for seed in 1..=48u64 {
        check_dl_instance(seed);
    }
}

// CEP:WHAT: Property: random combined EUF+DL instances agree with the brute-force oracle.
// CEP:WHY: The Nelson-Oppen combination's soundness and completeness over enumerable assignments (design 13.3).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any verdict mismatch.
// CEP:ASSUMES: 48 fixed seeds; two equality and two difference atoms per instance.
// CEP:COST: linear in seeds.
// CEP:EVIDENCE: cited by hot/theory/nelson_oppen.rs::check; Spec 21 section 8.
// CEP:SECURITY: no untrusted input; fixed seeds.
#[test]
fn combined_instances_agree_with_oracle() {
    for seed in 1..=48u64 {
        check_combined_instance(seed);
    }
}
