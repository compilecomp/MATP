// CEP:FILE: tests/security/phase2_bounds_test.rs
// CEP:WHAT: Security tests for the Phase 2 bounds: unification depth guard on cyclic chains, discrimination-tree node and entry caps at small injected scales, the ordering step budget at an injected scale, the index flat-capacity bound, and the SAT conflict budget constant sanity.
// CEP:WHY: CEP&CC 22.10 and design 25.1: every bound is a denial-of-service mitigation; the injected-scale constructors (new_with_caps, compare_*_with_budget) let the enforcement paths run in milliseconds while sharing the exact production code (CEP&CC 34.3: test the mechanism, not a copy).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any bound that does not fire.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by config/limits.rs Phase 2 bound constants.
// CEP:SECURITY: this file IS the security boundary evidence.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::index::discrimination_tree::{DiscriminationTree, IndexError};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::ordering::{compare_kbo_with_budget, compare_lpo_with_budget, OrderingError};
use mapt::hot::unification::substitution::{Substitution, SubstitutionError};
use mapt::hot::unification::unify::unify;
use mapt_config::limits::{kIndexTermCapacity, kSatMaxConflicts};

// CEP:WHAT: Verifies the unification depth guard fires on a cyclic binding chain (caller misuse).
// CEP:WHY: CEP&CC 22.10: the dereference chain must be bounded; a caller-built cycle x0 -> x1 -> ... -> xN must produce DepthExceeded, never a loop.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the chain loops, panics, or returns silently.
// CEP:ASSUMES: a substitution pre-loaded with a chain longer than kMaxUnificationDepth.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kMaxUnificationDepth.
// CEP:SECURITY: cyclic-state containment.
#[test]
fn unification_depth_bound_enforced() {
    let (arena, symbols, builder, terms, _clauses) = common::make_term_fixture();
    let substitution = Substitution::new(arena);
    // Build the cycle x0 -> x1 -> ... -> x63 -> x0: only kMaxVariablesPerClause (64)
    // variables exist and bind refuses double binds, so the longest acyclic chain is
    // 63 links -- below the guard -- and only the closing edge x63 -> x0 makes the
    // dereference chain infinite, which the depth guard must stop.
    for variable in 0..64u32 {
        let next = terms.intern_var((variable + 1) % 64).expect("next");
        substitution.bind(variable, next).expect("bind");
    }
    // The chain x0 -> x1 -> ... -> x63 -> x0 is cyclic: dereferencing must hit the guard.
    let start = terms.intern_var(0).expect("start");
    let target = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let outcome = unify(&terms, &substitution, start, target);
    assert_eq!(
        outcome,
        Err(SubstitutionError::DepthExceeded),
        "the cyclic chain must be stopped by the depth guard"
    );
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable fixture setup.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Verifies the discrimination-tree node cap fires at an injected small scale.
// CEP:WHY: CEP&CC 22.10 and design 25.1: an unbounded insert flood must exhaust the tree loudly; the injected cap makes the flood four inserts long.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if inserts continue past the cap.
// CEP:ASSUMES: a tree with a four-node cap.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kDiscriminationTreeNodes.
// CEP:SECURITY: memory bound under insert floods.
#[test]
fn discrimination_tree_node_cap_enforced() {
    let arena = make_arena(16_777_216);
    let terms = TermStore::new(arena).expect("terms");
    let tree = DiscriminationTree::new_with_caps(arena, 4, 4).expect("tree");
    let symbols = common::standard_symbols();
    let table = symbols.finalize(arena).expect("freeze");
    let f = symbol_id(&symbols, "f");
    let a = terms
        .intern_fun(&table, symbol_id(&symbols, "a"), &[])
        .expect("a");
    // Flood the tree with ever-deeper chains f^k(a); each new depth adds two nodes
    // (the fresh f level and the fresh a leaf), so a four-node cap fills quickly.
    let mut term = a;
    let mut inserted = 0u32;
    loop {
        term = terms.intern_fun(&table, f, &[term]).expect("chain");
        match tree.insert(&terms, term, u64::from(inserted)) {
            Ok(()) => inserted += 1,
            Err(IndexError::TreeFull) => break,
            Err(other) => panic!("unexpected error: {:?}", other),
        }
    }
    assert!(
        inserted >= 1,
        "the flood must succeed at least once before the cap"
    );
    assert!(
        tree.node_count() <= 4,
        "the node count must never exceed the cap"
    );
    // Every further insert must keep failing loudly.
    let b = terms
        .intern_fun(&table, symbol_id(&symbols, "b"), &[])
        .expect("b");
    assert_eq!(
        tree.insert(&terms, b, 99),
        Err(IndexError::TreeFull),
        "the node cap must stop the insert flood"
    );
}

// CEP:WHAT: Verifies the discrimination-tree entry cap fires at an injected small scale.
// CEP:WHY: CEP&CC 22.10 and design 25.1: payload floods must exhaust the entry budget loudly; the injected cap makes the flood three inserts long.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if payload inserts continue past the cap.
// CEP:ASSUMES: a tree with a two-entry cap.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kDiscriminationTreeEntries.
// CEP:SECURITY: memory bound under payload floods.
#[test]
fn discrimination_tree_entry_budget_enforced() {
    let arena = make_arena(16_777_216);
    let terms = TermStore::new(arena).expect("terms");
    let tree = DiscriminationTree::new_with_caps(arena, 8, 2).expect("tree");
    let symbols = common::standard_symbols();
    let table = symbols.finalize(arena).expect("freeze");
    let a = terms
        .intern_fun(&table, symbol_id(&symbols, "a"), &[])
        .expect("a");
    tree.insert(&terms, a, 1).expect("first payload");
    tree.insert(&terms, a, 2).expect("second payload");
    assert_eq!(
        tree.insert(&terms, a, 3),
        Err(IndexError::EntryBudgetExceeded),
        "the entry cap must stop the payload flood"
    );
}

// CEP:WHAT: Verifies the ordering step budget fires at an injected small scale.
// CEP:WHY: CEP&CC 22.10: pathological LPO/KBO comparisons must fail loudly; the injected budget of one step makes any structural comparison exceed it.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a one-step budget completes a multi-step comparison.
// CEP:ASSUMES: distinct terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kMaxOrderingSteps.
// CEP:SECURITY: denial-of-service bound on adversarial pairs.
#[test]
fn ordering_step_budget_enforced() {
    let (arena, symbols, builder, terms, _clauses) = common::make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let fb = terms.intern_fun(&symbols, f, &[b]).expect("f(b)");
    // Both orderings compare f(a) and f(b) by recursing into the children; a one-step
    // budget exhausts on the first recursive call.
    assert_eq!(
        compare_kbo_with_budget(&terms, &precedence, fa, fb, 1),
        Err(OrderingError::StepBudgetExceeded),
        "a one-step budget cannot complete a parent-plus-child KBO comparison"
    );
    assert_eq!(
        compare_lpo_with_budget(&terms, &precedence, fa, fb, 1),
        Err(OrderingError::StepBudgetExceeded),
        "a one-step budget cannot complete a parent-plus-child LPO comparison"
    );
    // Sanity: the same comparison succeeds with the production-scale budget.
    assert!(compare_kbo_with_budget(&terms, &precedence, fa, fb, 1_000).is_ok());
    assert!(compare_lpo_with_budget(&terms, &precedence, fa, fb, 1_000).is_ok());
}

// CEP:WHAT: Verifies the index flat-capacity bound is enforced on terms with more symbols than kIndexTermCapacity.
// CEP:WHY: CEP&CC 22.10: the flat walk buffer must never overflow; wide terms beyond the capacity are rejected loudly.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an oversized term is accepted.
// CEP:ASSUMES: a wide binary tree with more leaves than the capacity.
// CEP:COST: linear in the term.
// CEP:EVIDENCE: cited by config/limits.rs kIndexTermCapacity.
// CEP:SECURITY: denial-of-service bound on index work per term.
#[test]
fn index_capacity_enforced() {
    let arena = make_arena(16_777_216);
    let terms = TermStore::new(arena).expect("terms");
    let tree = DiscriminationTree::new_with_caps(arena, 64, 64).expect("tree");
    let symbols = common::standard_symbols();
    let table = symbols.finalize(arena).expect("freeze");
    let a = terms
        .intern_fun(&table, symbol_id(&symbols, "a"), &[])
        .expect("a");
    let h = symbol_id(&symbols, "h");
    let mut level: Vec<TermPtr> = (0..kIndexTermCapacity).map(|_| a).collect();
    while level.len() > 1 {
        let mut next: Vec<TermPtr> = Vec::new();
        for pair in level.chunks(2) {
            next.push(
                terms
                    .intern_fun(&table, h, &[pair[0], pair[1]])
                    .expect("node"),
            );
        }
        level = next;
    }
    assert_eq!(
        tree.insert(&terms, level[0], 1),
        Err(IndexError::TermTooLarge),
        "wide terms beyond the flat capacity must be rejected"
    );
}

// CEP:WHAT: Verifies the SAT conflict budget constant is positive and above realistic workloads.
// CEP:WHY: Design 20.1/20.2: the budget is the explicit denial-of-service bound; the test pins its order of magnitude against the ATP inference budget it mirrors.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the constant drops to a trivially reachable value.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kSatMaxConflicts.
// CEP:SECURITY: budget sanity.
#[test]
fn solver_budget_sanity() {
    let opaque_budget = std::hint::black_box(kSatMaxConflicts);
    assert!(
        opaque_budget >= 1_000_000,
        "the budget must stay in the million range"
    );
    // A concrete solve must finish far below the budget.
    let arena = make_arena(8_388_608);
    let solver = mapt::hot::sat::solver::CdclSolver::new(
        arena,
        6,
        mapt::hot::sat::restart::RestartPolicy::Luby,
        false,
    )
    .expect("solver");
    let lit = |variable: u32, positive: bool| {
        mapt::hot::sat::literal::SatLiteral::new(
            mapt::hot::sat::literal::SatVar(variable),
            positive,
        )
        .expect("literal")
    };
    for pigeon in 0..3u32 {
        solver
            .add_clause(&[lit(pigeon * 2, true), lit(pigeon * 2 + 1, true)])
            .expect("pigeon clause");
    }
    for hole in 0..2u32 {
        for first in 0..3u32 {
            for second in (first + 1)..3u32 {
                solver
                    .add_clause(&[lit(first * 2 + hole, false), lit(second * 2 + hole, false)])
                    .expect("hole clause");
            }
        }
    }
    let outcome = solver.solve();
    assert_eq!(outcome, mapt::hot::sat::solver::SolveResult::Unsatisfiable);
    assert!(solver.conflicts() < kSatMaxConflicts);
}
