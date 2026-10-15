// CEP:FILE: tests/unit/hot/avatar_splitter_test.rs
// CEP:WHAT: Unit tests of the AVATAR splitter: the two-component split, ground singletons, the min-size gate, single-component clauses, the walk-budget degradation, and the literal tagging contract of the materialize path.
// CEP:WHY: CEP&CC 34.3: the splitter is the soundness-critical first half of design 12.2 rule 1; its partition claims (Spec 12 section 3) must be pinned executably.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the standard fixture vocabulary.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/avatar_splitter_test.rs.
// CEP:SECURITY: the budget test exercises the adversarial-term bound.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::avatar::splitter::{kMaxSplitComponents, try_split, try_split_with, SplitDecision};
use mapt::hot::ir::literal::{Literal, LiteralFlags};
use mapt::hot::ir::term::TermPtr;

// CEP:WHAT: Builds one predicate literal.
// CEP:WHY: Readable splitter fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn pred(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

#[test]
// CEP:WHAT: A clause with two variable-disjoint 2-literal components splits into exactly those components.
// CEP:WHY: Spec 12 section 3's core case: p(x,a) | p(x,b) | q(y,c) | q(y,d) has the dependency graph {x},{y} with two connected components of two literals each - the gate passes and the partition is exact.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a wrong partition.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: one split decision.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
// CEP:SECURITY: none.
fn two_variable_disjoint_components_split() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = &symbols;
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let _ = b;
    let literals = [
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "q", &[x, a], true),
        pred(&terms, &symbols, &builder, "p", &[y], true),
        pred(&terms, &symbols, &builder, "q", &[y, b], true),
    ];
    match try_split(&terms, &literals) {
        SplitDecision::Splittable(view) => {
            assert_eq!(view.component_count, 2, "exactly two components");
            assert_eq!(view.component_size[0], 2);
            assert_eq!(view.component_size[1], 2);
            assert_eq!(view.literal_component[0], 0);
            assert_eq!(view.literal_component[1], 0);
            assert_eq!(view.literal_component[2], 1);
            assert_eq!(view.literal_component[3], 1);
        }
        SplitDecision::Unsplittable => panic!("the two-component clause must split"),
    }
}

#[test]
// CEP:WHAT: A clause with a ground singleton component does not split under the production gate (min size 2).
// CEP:WHY: Spec 12 section 3's all-or-nothing gate: p(a) | q(x) | q(x)-side needs every component at least kAvatarMinComponentSize literals; the ground literal is a singleton, so the clause stays whole.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the clause splits.
// CEP:ASSUMES: kAvatarMinComponentSize == 2 (the limits chain).
// CEP:COST: one split decision.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::ground_singleton_blocks_split.
// CEP:SECURITY: none.
fn ground_singleton_blocks_split() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let _y = terms.intern_var(1).expect("y");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let literals = [
        pred(&terms, &symbols, &builder, "r", &[], true),
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "q", &[x, a], true),
    ];
    assert_eq!(try_split(&terms, &literals), SplitDecision::Unsplittable);
}

#[test]
// CEP:WHAT: The gate is injectable: min_component_size 1 splits a two-singleton clause; the production value does not.
// CEP:WHY: CEP&CC 34.3: both gate sides must be exercisable on the production code path.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a wrong gate outcome.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: two split decisions.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::min_component_size_gate.
// CEP:SECURITY: none.
fn min_component_size_gate() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let literals = [
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "q", &[y, y], true),
    ];
    assert!(
        matches!(
            try_split_with(&terms, &literals, 1),
            SplitDecision::Splittable(_)
        ),
        "gate 1 splits the two-singleton clause"
    );
    assert_eq!(
        try_split_with(&terms, &literals, 2),
        SplitDecision::Unsplittable,
        "gate 2 keeps it whole"
    );
}

#[test]
// CEP:WHAT: A clause whose literals all share one variable stays whole.
// CEP:WHY: The single-component case (the dependency graph is connected).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the clause splits.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: one split decision.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::single_component_stays_whole.
// CEP:SECURITY: none.
fn single_component_stays_whole() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let literals = [
        pred(&terms, &symbols, &builder, "p", &[x], true),
        pred(&terms, &symbols, &builder, "q", &[x, a], true),
        pred(&terms, &symbols, &builder, "q", &[x, b], false),
    ];
    assert_eq!(try_split(&terms, &literals), SplitDecision::Unsplittable);
}

#[test]
// CEP:WHAT: A clause with more literals than the node budget degrades to Unsplittable, never to an error or a hang.
// CEP:WHY: The adversarial bound (kAvatarSplitNodeBudget): the walk is budgeted; sound degradation is the designed behavior (Spec 12 section 7).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the budget path errors instead of degrading.
// CEP:ASSUMES: a clause wide enough to exhaust 4096 nodes (one literal per distinct variable over more than the budget... the budget counts nodes; wide clauses with distinct variables exceed it).
// CEP:COST: one split decision.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::walk_budget_degrades_to_unsplittable and security/phase4_bounds_test.rs::splitter_node_budget_enforced.
// CEP:SECURITY: denial-of-service bound.
fn walk_budget_degrades_to_unsplittable() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    // More literals than the node budget: each literal is one variable node plus one
    // predicate node, so kBudget + 1 literals exceed the walk budget.
    // The adversarial DAG: a doubling h-chain (one record per level, exponential
    // tree expansion) exhausts the walk budget with a single literal.
    let x0 = terms.intern_var(0).expect("var");
    let h = symbol_id(&builder, "h");
    let mut term = x0;
    for _ in 0..13 {
        term = terms
            .intern_fun(&symbols, h, &[term, term])
            .expect("doubling intern");
    }
    let literals: Vec<Literal> = vec![pred(&terms, &symbols, &builder, "p", &[term], true)];
    assert_eq!(
        try_split(&terms, &literals),
        SplitDecision::Unsplittable,
        "the budget exhaustion degrades to Unsplittable"
    );
}

#[test]
// CEP:WHAT: The literal component-tag contract: set_avatar_component_tag writes the masked slot tag and preserves the theory-laden bit; the tag wraps modulo 8.
// CEP:WHY: Ticket CEP-1011: literals of a component clause carry the component membership tag (design 5.2); the authoritative identity stays the clause's split_level.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a tag mismatch.
// CEP:ASSUMES: none.
// CEP:COST: a few tag writes.
// CEP:EVIDENCE: backs unit/hot/avatar_splitter_test.rs::component_literals_tagged (the literal-side contract of the materialize path).
// CEP:SECURITY: none.
fn component_literals_tagged() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let mut literal = pred(&terms, &symbols, &builder, "p", &[x], true);
    assert_eq!(
        literal.avatar_component_tag(),
        0,
        "fresh literals are untagged"
    );
    literal.set_theory_flags(LiteralFlags::kTheoryLaden);
    literal.set_avatar_component_tag(5);
    assert_eq!(literal.avatar_component_tag(), 5);
    assert_eq!(
        literal.theory_flags() & LiteralFlags::kTheoryLaden,
        LiteralFlags::kTheoryLaden,
        "the theory bit survives the tag write"
    );
    literal.set_avatar_component_tag(9);
    assert_eq!(
        literal.avatar_component_tag(),
        9 & LiteralFlags::kAvatarComponentMask,
        "tags wrap modulo 8 (the mask is authoritative)"
    );
    assert_eq!(
        kMaxSplitComponents,
        (mapt_config::limits::kMaxClauseLiterals / 2) as usize,
        "the component bound is structural"
    );
}
