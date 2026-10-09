// CEP:FILE: tests/unit/hot/discrimination_tree_test.rs
// CEP:WHAT: Unit tests for the discrimination tree: exact retrieval, query-variable and stored-variable matching, the length rule, shared prefixes, payload lists, deletion, equality atoms, and capacity bounds.
// CEP:WHY: CEP&CC 32.8 and Formal Spec 04: the index is the retrieval filter of subsumption and rewriting; a wrong retrieval set silently breaks both, so every matching rule is pinned here.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; index arenas sized above the tree's fixed arrays.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/index/discrimination_tree.rs.
// CEP:SECURITY: capacity bounds are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use mapt::hot::index::discrimination_tree::{DiscriminationTree, IndexError};
use mapt_config::limits::kIndexTermCapacity;

// CEP:WHAT: Node and entry caps for the index unit-test fixture (small scale; production uses the named constants).
// CEP:WHY: The unit tests exercise behavior, not the production memory bound; the explicit-cap constructor keeps the enforcement code identical for both paths (CEP&CC 34.3); the security tests exercise the caps themselves.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: caps above every unit-test insert volume.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFixtureNodeCap: u32 = 4_096;
const kFixtureEntryCap: u32 = 4_096;

// CEP:WHAT: Arena capacity for one discrimination tree fixture.
// CEP:WHY: Sized for the small fixture caps plus term data; named instead of a magic number (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture caps x record sizes plus fixture data.
// CEP:COST: one allocation per fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kIndexFixtureArenaBytes: u32 = 16_777_216;

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
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

// CEP:WHAT: Builds an index fixture: term fixture plus a discrimination tree in a dedicated arena.
// CEP:WHY: The tree arrays need a larger arena than the standard term fixture provides; one call keeps the sizing single-sourced.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one arena plus the tree arrays.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_index_fixture() -> (
    &'static mapt::hot::memory::arena::Arena,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    mapt::hot::ir::term::TermStore<'static>,
    DiscriminationTree<'static>,
) {
    let arena = common::make_arena(kIndexFixtureArenaBytes);
    let builder = common::standard_symbols();
    let symbols = builder.finalize(arena).expect("freeze failed");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("term store failed");
    let tree = DiscriminationTree::new_with_caps(arena, kFixtureNodeCap, kFixtureEntryCap)
        .expect("tree failed");
    (arena, symbols, builder, terms, tree)
}

// CEP:WHAT: Verifies an exact query retrieves exactly the payloads stored at that path.
// CEP:WHY: The base retrieval contract (design 9.2).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong payload set.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs retrieve.
// CEP:SECURITY: none.
#[test]
fn exact_retrieval() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let h = symbol_id(&builder, "h");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let hba = terms.intern_fun(&symbols, h, &[b, a]).expect("h(b, a)");
    tree.insert(&terms, hab, 1).expect("insert hab");
    tree.insert(&terms, hba, 2).expect("insert hba");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, hab, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 1);
    let count = tree.retrieve(&terms, hba, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 2);
    // A different ground term retrieves nothing.
    let haa = terms.intern_fun(&symbols, h, &[a, a]).expect("h(a, a)");
    let count = tree.retrieve(&terms, haa, &mut buffer).expect("retrieve");
    assert_eq!(count, 0);
}

// CEP:WHAT: Verifies query variables match any stored symbol (design 9.2 rule).
// CEP:WHY: "Variables in the query match any symbol"; h(x, b) must retrieve h(a, b) but not h(g(a), b) (one symbol per variable, length rule).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong retrieval set.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs walk.
// CEP:SECURITY: none.
#[test]
fn query_variables_match_any_symbol() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let g = symbol_id(&builder, "g");
    let h = symbol_id(&builder, "h");
    let ga = terms.intern_fun(&symbols, g, &[a]).expect("g(a)");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let hgb = terms.intern_fun(&symbols, h, &[ga, b]).expect("h(g(a), b)");
    tree.insert(&terms, hab, 10).expect("insert hab");
    tree.insert(&terms, hgb, 20).expect("insert hgb");
    let x = terms.intern_var(0).expect("x");
    let query = terms.intern_fun(&symbols, h, &[x, b]).expect("h(x, b)");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, query, &mut buffer).expect("retrieve");
    // h(x, b) has three flat symbols; h(a, b) has three (match), h(g(a), b) has four (no).
    assert_eq!(count, 1, "only the length-matching instance is retrieved");
    assert_eq!(buffer[0], 10);
}

// CEP:WHAT: Verifies stored variable edges match any query symbol.
// CEP:WHY: The instance-retrieval direction rewriting needs: an indexed left-hand side f(x) is retrieved by the concrete query f(a).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missing payload.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs edge_matches.
// CEP:SECURITY: none.
#[test]
fn variable_edges_match_any_query_symbol() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f = symbol_id(&builder, "f");
    let x = terms.intern_var(0).expect("x");
    let fx = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");
    tree.insert(&terms, fx, 7).expect("insert f(x)");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, fa, &mut buffer).expect("retrieve");
    assert_eq!(
        count, 1,
        "the stored variable edge must match the query constant"
    );
    assert_eq!(buffer[0], 7);
    // A stored variable also matches a query variable.
    let y = terms.intern_var(1).expect("y");
    let fy = terms.intern_fun(&symbols, f, &[y]).expect("f(y)");
    let count = tree.retrieve(&terms, fy, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 7);
}

// CEP:WHAT: Verifies the length rule: stored paths longer than the query are not retrieved.
// CEP:WHY: Spec 04: paths must end together; f(x) (two symbols) must not retrieve f(g(a)) (three symbols).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if longer paths leak.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs walk.
// CEP:SECURITY: none.
#[test]
fn length_rule_enforced() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f = symbol_id(&builder, "f");
    let g = symbol_id(&builder, "g");
    let ga = terms.intern_fun(&symbols, g, &[a]).expect("g(a)");
    let fga = terms.intern_fun(&symbols, f, &[ga]).expect("f(g(a))");
    tree.insert(&terms, fga, 3).expect("insert f(g(a))");
    let x = terms.intern_var(0).expect("x");
    let fx = terms.intern_fun(&symbols, f, &[x]).expect("f(x)");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, fx, &mut buffer).expect("retrieve");
    assert_eq!(count, 0, "f(x) must not retrieve the longer stored path");
    // The exact longer query retrieves it.
    let count = tree.retrieve(&terms, fga, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 3);
}

// CEP:WHAT: Verifies shared prefixes share tree nodes.
// CEP:WHY: Design 9.2: "Nodes are allocated contiguously"; sharing is the memory win of the trie.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if nodes are duplicated per insert.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs find_or_create_child.
// CEP:SECURITY: none.
#[test]
fn shared_prefixes_share_nodes() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let fb = terms.intern_fun(&symbols, f, &[b]).expect("f(b)");
    let before = tree.node_count();
    tree.insert(&terms, fa, 1).expect("insert fa");
    let after_first = tree.node_count();
    tree.insert(&terms, fb, 2).expect("insert fb");
    let after_second = tree.node_count();
    // f(a) allocates two nodes (f, a); f(b) shares the f node and adds one (b).
    assert_eq!(after_first - before, 2);
    assert_eq!(after_second - after_first, 1);
}

// CEP:WHAT: Verifies multiple payloads at one leaf and their deterministic order.
// CEP:WHY: Design 9.2: leaves store clause references; the prepend order makes retrieval deterministic (most recent first).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong order or count.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs insert/collect_payloads.
// CEP:SECURITY: none.
#[test]
fn multiple_payloads_at_one_leaf() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    tree.insert(&terms, a, 1).expect("insert 1");
    tree.insert(&terms, a, 2).expect("insert 2");
    tree.insert(&terms, a, 3).expect("insert 3");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, a, &mut buffer).expect("retrieve");
    assert_eq!(count, 3);
    // Prepend order: the most recently inserted payload is first.
    assert_eq!(buffer[0], 3);
    assert_eq!(buffer[1], 2);
    assert_eq!(buffer[2], 1);
}

// CEP:WHAT: Verifies deletion removes exactly the named payload and keeps others.
// CEP:WHY: Design 9.2 delete and index maintenance (design 9.5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong remaining set.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs delete.
// CEP:SECURITY: none.
#[test]
fn delete_removes_payload() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    tree.insert(&terms, a, 1).expect("insert a/1");
    tree.insert(&terms, a, 2).expect("insert a/2");
    tree.insert(&terms, b, 3).expect("insert b/3");
    tree.delete(&terms, a, 2).expect("delete a/2");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, a, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 1);
    let count = tree.retrieve(&terms, b, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 3);
}

// CEP:WHAT: Verifies deleting an absent payload fails loudly.
// CEP:WHY: Law 6: no silent no-ops on maintenance operations.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a missing delete succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs delete.
// CEP:SECURITY: none.
#[test]
fn payload_missing_rejected() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    tree.insert(&terms, a, 1).expect("insert a/1");
    assert_eq!(
        tree.delete(&terms, a, 99),
        Err(IndexError::PayloadMissing),
        "deleting an absent payload must fail"
    );
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    assert_eq!(
        tree.delete(&terms, b, 1),
        Err(IndexError::PayloadMissing),
        "deleting along an absent path must fail"
    );
}

// CEP:WHAT: Verifies equality atoms are indexed and retrieved with the reserved pseudo-symbol.
// CEP:WHY: Equality atoms carry no symbol-table ID; the reserved encoding must distinguish them from symbol zero (design 5.1, limits kIndexEqualitySymbol).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on cross-contamination with a real symbol edge.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs flatten.
// CEP:SECURITY: none.
#[test]
fn equality_terms_indexed() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let eq_ab = terms.intern_eq(&symbols, a, b).expect("eq(a, b)");
    tree.insert(&terms, eq_ab, 5).expect("insert eq(a, b)");
    let mut buffer = [0u64; 8];
    let count = tree.retrieve(&terms, eq_ab, &mut buffer).expect("retrieve");
    assert_eq!(count, 1);
    assert_eq!(buffer[0], 5);
    // A binary function term with the same children must not retrieve the equality payload.
    let h = symbol_id(&builder, "h");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let count = tree.retrieve(&terms, hab, &mut buffer).expect("retrieve");
    assert_eq!(count, 0);
}

// CEP:WHAT: Verifies the result buffer bound is enforced.
// CEP:WHY: Law 6: overflow is a loud error, not a silent truncation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if overflow is silent.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs collect_payloads.
// CEP:SECURITY: output bound.
#[test]
fn buffer_bound_enforced() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    tree.insert(&terms, a, 1).expect("insert 1");
    tree.insert(&terms, a, 2).expect("insert 2");
    let mut buffer = [0u64; 1];
    assert_eq!(
        tree.retrieve(&terms, a, &mut buffer),
        Err(IndexError::BufferTooSmall)
    );
}

// CEP:WHAT: Verifies the flat-sequence capacity bound is enforced.
// CEP:WHY: CEP&CC 22.10: bounded buffers error loudly.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an oversized term is accepted.
// CEP:ASSUMES: a term with more than kIndexTermCapacity symbols.
// CEP:COST: linear in the term.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs flatten.
// CEP:SECURITY: capacity bound.
#[test]
fn term_capacity_enforced() {
    let (_arena, symbols, builder, terms, tree) = make_index_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let h = symbol_id(&builder, "h");
    // A complete binary tree with kIndexTermCapacity leaves: its flat preorder sequence
    // (2 x capacity - 1 symbols) exceeds the capacity while staying far below the depth cap.
    let mut level: Vec<mapt::hot::ir::term::TermPtr> = (0..kIndexTermCapacity).map(|_| a).collect();
    while level.len() > 1 {
        let mut next: Vec<mapt::hot::ir::term::TermPtr> = Vec::new();
        for pair in level.chunks(2) {
            let node = terms
                .intern_fun(&symbols, h, &[pair[0], pair[1]])
                .expect("tree node");
            next.push(node);
        }
        level = next;
    }
    let term = level[0];
    assert_eq!(
        tree.insert(&terms, term, 1),
        Err(IndexError::TermTooLarge),
        "terms beyond the flat capacity must be rejected"
    );
    let mut buffer = [0u64; 1];
    assert_eq!(
        tree.retrieve(&terms, term, &mut buffer),
        Err(IndexError::TermTooLarge)
    );
}

// CEP:WHAT: Verifies the node layout pins hold.
// CEP:WHY: CEP&CC 38.17: the record layouts are the index memory contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on layout drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs static assertions.
// CEP:SECURITY: none.
#[test]
fn node_layout() {
    assert_eq!(
        core::mem::size_of::<mapt::hot::index::discrimination_tree::IndexNode>(),
        20
    );
    assert_eq!(
        core::mem::size_of::<mapt::hot::index::discrimination_tree::IndexEntry>(),
        16
    );
}
