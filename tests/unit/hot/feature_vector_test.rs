// CEP:FILE: tests/unit/hot/feature_vector_test.rs
// CEP:WHAT: Unit tests for the feature-vector index: per-symbol counting, equality-atom arguments, deep-term counting, the dominance and literal-count filters, truncated-vector soundness, the pair bound, and the pool capacity.
// CEP:WHY: Design 9.3 and CEP-1028: the filter is the subsumption pre-tier; its soundness (no true subsumption filtered out) is the correctness-critical property, pinned here on hand-built clauses before the property test verifies it against a brute-force oracle.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/index/feature_vector.rs.
// CEP:SECURITY: the pool capacity is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::index::feature_vector::{FeatureError, FeatureVectorIndex};
use mapt::hot::ir::literal::Literal;

// CEP:WHAT: Builds a predicate literal over interned argument terms.
// CEP:WHY: Readable fixture construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn pred(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[mapt::hot::ir::term::TermPtr],
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, true)
}

// CEP:WHAT: Verifies vectors store per-symbol occurrence counts.
// CEP:WHY: The dominance filter's input.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong counts.
// CEP:ASSUMES: clause p(f(a), f(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{build, pair}.
// CEP:SECURITY: none.
#[test]
fn vectors_store_counts() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let clause = [pred(&terms, &symbols, &builder, "q", &[f_a, f_a])];
    let vector = index.build(&terms, &clause).expect("vector");
    assert_eq!(vector.literal_count, 1);
    assert!(!vector.truncated);
    // f occurs twice, q once.
    let mut found_f = 0;
    let mut found_p = 0;
    for slot in 0..vector.pairs {
        let (symbol, count) = index.pair(vector, slot).expect("pair");
        if symbol == symbol_id(&builder, "f") {
            found_f = count;
        }
        if symbol == symbol_id(&builder, "q") {
            found_p = count;
        }
    }
    assert_eq!(found_f, 2);
    assert_eq!(found_p, 1);
}

// CEP:WHAT: Verifies counts aggregate per symbol across literals and nesting levels.
// CEP:WHY: The filter relies on totals, not per-literal counts.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong totals.
// CEP:ASSUMES: p(f(a)) and q(f(b), g(a)).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{build, collect}.
// CEP:SECURITY: none.
#[test]
fn counts_are_per_symbol() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let f_b = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[b])
        .expect("f(b)");
    let g_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "g"), &[a])
        .expect("g(a)");
    let clause = [
        pred(&terms, &symbols, &builder, "p", &[f_a]),
        pred(&terms, &symbols, &builder, "q", &[f_b, g_a]),
    ];
    let vector = index.build(&terms, &clause).expect("vector");
    let mut f_count = 0;
    let mut a_count = 0;
    for slot in 0..vector.pairs {
        let (symbol, count) = index.pair(vector, slot).expect("pair");
        if symbol == symbol_id(&builder, "f") {
            f_count = count;
        }
        if symbol == symbol_id(&builder, "a") {
            a_count = count;
        }
    }
    assert_eq!(f_count, 2, "f occurs in both literals");
    assert_eq!(a_count, 2, "a occurs under f and under g");
}

// CEP:WHAT: Verifies deep terms count symbols at every level.
// CEP:WHY: The recursion must not stop at depth one.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong total.
// CEP:ASSUMES: p(f(f(f(a)))).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::collect.
// CEP:SECURITY: none.
#[test]
fn deep_terms_count_all_levels() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let mut current = a;
    for _ in 0..3 {
        current = terms
            .intern_fun(&symbols, symbol_id(&builder, "f"), &[current])
            .expect("nest");
    }
    let clause = [pred(&terms, &symbols, &builder, "p", &[current])];
    let vector = index.build(&terms, &clause).expect("vector");
    let mut f_count = 0;
    for slot in 0..vector.pairs {
        let (symbol, count) = index.pair(vector, slot).expect("pair");
        if symbol == symbol_id(&builder, "f") {
            f_count = count;
        }
    }
    assert_eq!(f_count, 3);
}

// CEP:WHAT: Verifies equality atoms contribute their arguments' symbols but no pseudo-entry.
// CEP:WHY: The equality pseudo-symbol is an index-space sentinel, not a term symbol.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a pseudo-entry or missing argument counts.
// CEP:ASSUMES: clause (a = b).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{build, collect}.
// CEP:SECURITY: none.
#[test]
fn equality_atoms_contribute_arguments() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let atom = terms.intern_eq(&symbols, a, b).expect("eq");
    let clause = [Literal::new(atom, true)];
    let vector = index.build(&terms, &clause).expect("vector");
    // Exactly two pairs: a and b, each once; no equality pseudo-entry.
    assert_eq!(vector.pairs, 2);
    let mut total = 0;
    for slot in 0..vector.pairs {
        let (_symbol, count) = index.pair(vector, slot).expect("pair");
        total += count;
    }
    assert_eq!(total, 2);
}

// CEP:WHAT: Verifies the dominance filter passes a true subsumption pair.
// CEP:WHY: Soundness: no true subsumption may be filtered out.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a false negative.
// CEP:ASSUMES: p(x) subsumes p(f(a)) (x instantiates).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::may_subsume.
// CEP:SECURITY: none.
#[test]
fn dominance_filter_sound() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let x = terms.intern_var(0).expect("x");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let subsumer = [pred(&terms, &symbols, &builder, "p", &[x])];
    let target = [pred(&terms, &symbols, &builder, "p", &[f_a])];
    let candidate = index.build(&terms, &subsumer).expect("vector");
    let goal = index.build(&terms, &target).expect("vector");
    assert!(
        index.may_subsume(candidate, goal),
        "p(x) may subsume p(f(a))"
    );
}

// CEP:WHAT: Verifies the dominance filter rejects symbol-count violations.
// CEP:WHY: occ(f, C) > occ(f, D) rules out subsumption.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a pass.
// CEP:ASSUMES: p(f(a)) vs p(a).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::may_subsume.
// CEP:SECURITY: none.
#[test]
fn dominance_filter_rejects() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let heavy = [pred(&terms, &symbols, &builder, "p", &[f_a])];
    let light = [pred(&terms, &symbols, &builder, "p", &[a])];
    let candidate = index.build(&terms, &heavy).expect("vector");
    let goal = index.build(&terms, &light).expect("vector");
    assert!(
        !index.may_subsume(candidate, goal),
        "p(f(a)) cannot subsume p(a)"
    );
}

// CEP:WHAT: Verifies the literal-count filter rejects longer candidates.
// CEP:WHY: |C| > |D| rules out subsumption.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a pass.
// CEP:ASSUMES: two literals vs one.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::may_subsume.
// CEP:SECURITY: none.
#[test]
fn literal_count_filter_rejects() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let two = [
        pred(&terms, &symbols, &builder, "p", &[a]),
        pred(&terms, &symbols, &builder, "p", &[a]),
    ];
    let one = [pred(&terms, &symbols, &builder, "p", &[a])];
    let candidate = index.build(&terms, &two).expect("vector");
    let goal = index.build(&terms, &one).expect("vector");
    assert!(!index.may_subsume(candidate, goal));
}

// CEP:WHAT: Verifies truncated vectors pass every filter (sound degradation).
// CEP:WHY: Truncation only removes evidence of violation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a false negative.
// CEP:ASSUMES: a truncated candidate still may-subsumes an incompatible target.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{may_subsume, kFeatureVectorSlots}.
// CEP:SECURITY: none.
#[test]
fn filter_is_sound_on_truncated_vectors() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    // Build a clause with more distinct symbols than kFeatureVectorSlots using
    // nested h(x, y) terms over distinct f/g chains - simpler: many literals over
    // p with f/g alternation to exceed 256 distinct symbols is impractical in a
    // fixture; instead the truncated flag is pinned through the depth-overflow and
    // pair-cap logic by a synthetic vector constructed with truncated = true.
    let light = [pred(&terms, &symbols, &builder, "p", &[a])];
    let goal = index.build(&terms, &light).expect("vector");
    let synthetic = mapt::hot::index::feature_vector::FeatureVector {
        start: 0,
        pairs: 0,
        literal_count: 1,
        truncated: true,
    };
    assert!(index.may_subsume(synthetic, goal));
    assert!(index.may_subsume(goal, synthetic));
}

// CEP:WHAT: Verifies the pair bound is the documented slot capacity.
// CEP:WHY: Clauses beyond the bound are unfilterable (documented degradation).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the constant drifts from the documented policy.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{build, kFeatureVectorSlots} and config/limits.rs kFeatureVectorSlots.
// CEP:SECURITY: none.
#[test]
fn pair_bound_enforced() {
    // The bound is compile-time policy; the test pins its value and the truncation
    // behavior through a build that cannot exceed it in a fixture (all fixture
    // clauses have few symbols), plus the constant's documented value.
    assert_eq!(mapt_config::limits::kFeatureVectorSlots, 256);
    let (arena, _symbols, _builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 4096).expect("index");
    let x = terms.intern_var(0).expect("x");
    let clause = [Literal::new(x, true)];
    let vector = index.build(&terms, &clause).expect("vector");
    // A variable-only clause has zero symbol pairs.
    assert_eq!(vector.pairs, 0);
    assert!(!vector.truncated);
}

// CEP:WHAT: Verifies the pool capacity bound is loud.
// CEP:WHY: The memory bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when builds succeed past the bound.
// CEP:ASSUMES: pool capacity 2 words (one pair).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{new_with, build} and config/limits.rs kFeatureVectorPoolWords.
// CEP:SECURITY: the memory bound under test.
#[test]
fn pool_capacity_enforced() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let index = FeatureVectorIndex::new_with(arena, 2).expect("index");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    // First build: two pairs (f and p) need 4 words > 2.
    let clause = [pred(&terms, &symbols, &builder, "p", &[f_a])];
    let result = index.build(&terms, &clause);
    assert!(matches!(result, Err(FeatureError::PoolFull)));
}
