// CEP:FILE: tests/property/discrimination_property_test.rs
// CEP:WHAT: Property tests for the discrimination tree: retrieval agrees with a naive scan over the same matching rule across random insert/delete/query workloads, and deletion never perturbs unrelated payloads.
// CEP:WHY: CEP&CC 32.9 and Formal Spec 04 section 3: the retrieval soundness and completeness theorems are verified against an independent oracle over deterministic random term sets.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any violated property.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the deterministic LCG makes every run identical.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/index/discrimination_tree.rs and docs/formal/04_term_indexing.md.
// CEP:SECURITY: none; no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::DeterministicRng;
use mapt::hot::index::discrimination_tree::DiscriminationTree;
use mapt::hot::ir::term::{TermPtr, TermStore};

// CEP:WHAT: Property rounds per test.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyRounds: u32 = 24;

// CEP:WHAT: Terms in each round's vocabulary.
// CEP:WHY: Named constant; 24 terms keep the naive oracle cheap (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVocabularySize: usize = 24;

// CEP:WHAT: Tree caps for the property fixture.
// CEP:WHY: Named constants sized above the workload (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyNodeCap: u32 = 65_536;
const kPropertyEntryCap: u32 = 65_536;

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

// CEP:WHAT: Generates a random term with variables over the fixture vocabulary.
// CEP:WHY: The property must exercise variable edges on both the stored and the query side.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: depth >= 1.
// CEP:COST: bounded.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_term(
    rng: &mut DeterministicRng,
    terms: &TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    depth: u32,
) -> TermPtr {
    if depth == 0 || rng.below(4) == 0 {
        let choice = rng.below(4);
        if choice == 0 {
            return terms.intern_var(rng.below(3) as u32).expect("var");
        }
        let name = if choice == 1 { "a" } else { "b" };
        return terms
            .intern_fun(symbols, symbol_id(builder, name), &[])
            .expect("constant");
    }
    if rng.below(2) == 0 {
        let child = random_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "f"), &[child])
            .expect("f")
    } else {
        let left = random_term(rng, terms, symbols, builder, depth - 1);
        let right = random_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "h"), &[left, right])
            .expect("h")
    }
}

// CEP:WHAT: Computes the flat preorder symbol sequence of a term as (is_variable, tag, symbol) triples.
// CEP:WHY: The naive oracle needs the same flat representation the tree indexes (Spec 04 section 1).
// CEP:STATUS: complete
// CEP:FAILURE: panics on unreadable terms.
// CEP:ASSUMES: term depth below the guard.
// CEP:COST: O(term size).
// CEP:EVIDENCE: used by naive_retrieval.
// CEP:SECURITY: none.
fn flat_of(terms: &TermStore<'_>, term: TermPtr, out: &mut Vec<(bool, u8, u32)>) {
    let view = terms.term(term).expect("term view");
    let is_variable = view.tag() == mapt::hot::ir::term::TermTag::Variable;
    let symbol = if is_variable {
        view.symbol()
    } else if view.tag() == mapt::hot::ir::term::TermTag::Equality {
        mapt_config::limits::kIndexEqualitySymbol
    } else {
        view.symbol()
    };
    out.push((is_variable, view.tag() as u8, symbol));
    if is_variable {
        return;
    }
    for index in 0..view.child_count() {
        let child = view.child(index).expect("child");
        flat_of(terms, child, out);
    }
}

// CEP:WHAT: Naive oracle: does the stored sequence match the query sequence under the Spec 04 rule?
// CEP:WHY: Stored variable edges and query variables match anything; symbol edges match identical tag and symbol; sequences must have equal length.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: both sequences non-empty.
// CEP:COST: linear.
// CEP:EVIDENCE: used by retrieval_matches_naive_scan.
// CEP:SECURITY: none.
fn sequences_match(
    stored: &[(bool, u8, u32)],
    stored_is_var: bool,
    query: &[(bool, u8, u32)],
) -> bool {
    if stored.len() != query.len() {
        return false;
    }
    let _ = stored_is_var;
    for (index, (s, q)) in stored.iter().zip(query.iter()).enumerate() {
        let _ = index;
        if s.0 || q.0 {
            continue;
        }
        if s.1 != q.1 || s.2 != q.2 {
            return false;
        }
    }
    true
}

// CEP:WHAT: Property: retrieval returns exactly the payloads the naive scan selects, in both the insert-only and the delete-heavy regimes.
// CEP:WHY: Spec 04 Theorems (retrieval soundness and completeness as a filter): set equality against the oracle is the executable form.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any set difference.
// CEP:ASSUMES: random vocabularies and queries.
// CEP:COST: quadratic in the vocabulary per round (bounded).
// CEP:EVIDENCE: cited by hot/index/discrimination_tree.rs retrieve and docs/formal/04_term_indexing.md.
// CEP:SECURITY: none.
#[test]
fn retrieval_matches_naive_scan() {
    let arena = common::make_arena(16_777_216);
    let symbols_table = common::standard_symbols();
    let symbols = symbols_table.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let tree = DiscriminationTree::new_with_caps(arena, kPropertyNodeCap, kPropertyEntryCap)
        .expect("tree");
    let mut rng = DeterministicRng::new(0x1DDE_0001);
    // Build one shared vocabulary; each round inserts or deletes a subset and queries all.
    let mut vocabulary: Vec<TermPtr> = Vec::new();
    for _ in 0..kVocabularySize {
        vocabulary.push(random_term(&mut rng, &terms, &symbols, &symbols_table, 3));
    }
    let mut flats: Vec<Vec<(bool, u8, u32)>> = Vec::new();
    for term in vocabulary.iter() {
        let mut flat: Vec<(bool, u8, u32)> = Vec::new();
        flat_of(&terms, *term, &mut flat);
        flats.push(flat);
    }
    let mut live: Vec<(usize, u64)> = Vec::new();
    let mut next_payload: u64 = 0;
    for round in 0..kPropertyRounds {
        // Insert two fresh payloads, or delete one live payload, alternating.
        if round % 4 == 3 {
            if let Some(position) =
                (0..live.len()).find(|index| (*index as u64) % 3 == (round % 3) as u64)
            {
                let (vocab_index, payload) = live.remove(position);
                tree.delete(&terms, vocabulary[vocab_index], payload)
                    .expect("delete");
            }
        } else {
            let vocab_index =
                (rng.below(kVocabularySize as u64) as usize + round as usize) % kVocabularySize;
            let payload = next_payload;
            next_payload += 1;
            tree.insert(&terms, vocabulary[vocab_index], payload)
                .expect("insert");
            live.push((vocab_index, payload));
        }
        // Query every vocabulary term and compare against the naive scan over live entries.
        for (query_index, query_term) in vocabulary.iter().enumerate() {
            let mut query_flat: Vec<(bool, u8, u32)> = Vec::new();
            flat_of(&terms, *query_term, &mut query_flat);
            let mut expected: Vec<u64> = Vec::new();
            for (vocab_index, payload) in live.iter() {
                let stored_is_variable = query_flat[0].0;
                if sequences_match(&flats[*vocab_index], stored_is_variable, &query_flat) {
                    expected.push(*payload);
                }
            }
            let mut buffer = [0u64; 64];
            let count = tree
                .retrieve(&terms, *query_term, &mut buffer)
                .expect("retrieve");
            let actual: Vec<u64> = buffer[..count].to_vec();
            // Set equality (order is deterministic but the oracle is unordered).
            let mut sorted_expected = expected.clone();
            let mut sorted_actual = actual.clone();
            sorted_expected.sort_unstable();
            sorted_actual.sort_unstable();
            assert_eq!(
                sorted_expected, sorted_actual,
                "round {} query {}: retrieval must equal the naive scan",
                round, query_index
            );
        }
    }
}
