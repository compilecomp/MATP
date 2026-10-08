// CEP:FILE: tests/property/term_property_test.rs
// CEP:WHAT: Property tests for the term store: interning is canonical (structure identity equals handle identity), hashes are deterministic across stores, and random DAG construction preserves invariants.
// CEP:WHY: CEP&CC 38.43: the hash-consing invariant is the IR identity contract (design 5.1, 5.7); random term DAGs stress probe collisions and structural sharing.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/term.rs interning_is_canonical and hash_is_deterministic.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::{make_term_fixture, DeterministicRng};
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::SymbolTable;
use mapt::hot::ir::term::{TermStore, TermTag};

// CEP:WHAT: Number of random terms per property round.
// CEP:WHY: Fixed named iteration count (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyTerms: u32 = 2_048;

// CEP:WHAT: Builds a random term DAG from a seed and returns the interned handles in construction order.
// CEP:WHY: Shared generator so two stores receive identical sequences.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: O(kPropertyTerms) interns.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn build_random_terms(
    terms: &TermStore,
    symbols: &SymbolTable,
    builder: &SymbolTableBuilder,
    seed: u64,
) -> Vec<mapt::hot::ir::term::TermPtr> {
    let f_id = fixture_id(builder, "f");
    let g_id = fixture_id(builder, "g");
    let h_id = fixture_id(builder, "h");
    let a = terms
        .intern_fun(symbols, fixture_id(builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(symbols, fixture_id(builder, "b"), &[])
        .expect("b");
    let mut pool = vec![a, b];
    let mut rng = DeterministicRng::new(seed);
    for _ in 0..kPropertyTerms {
        let choice = rng.below(6);
        let handle = match choice {
            0 => terms.intern_var(rng.below(8) as u32).expect("var"),
            1 => {
                let child = pool[rng.below(pool.len() as u64) as usize];
                terms.intern_fun(symbols, f_id, &[child]).expect("f")
            }
            2 => {
                let child = pool[rng.below(pool.len() as u64) as usize];
                terms.intern_fun(symbols, g_id, &[child]).expect("g")
            }
            3 => {
                let left = pool[rng.below(pool.len() as u64) as usize];
                let right = pool[rng.below(pool.len() as u64) as usize];
                terms.intern_fun(symbols, h_id, &[left, right]).expect("h")
            }
            4 => {
                let left = pool[rng.below(pool.len() as u64) as usize];
                let right = pool[rng.below(pool.len() as u64) as usize];
                terms.intern_eq(symbols, left, right).expect("eq")
            }
            _ => pool[rng.below(pool.len() as u64) as usize],
        };
        pool.push(handle);
    }
    pool
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fixture_id(builder: &SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Verifies interning is canonical: equal structures yield equal handles.
// CEP:WHY: The hash-consing theorem (design 5.1) is the semantic-equality shortcut every engine relies on.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any duplicate structure.
// CEP:ASSUMES: none.
// CEP:COST: rebuilds every random term and compares handles.
// CEP:EVIDENCE: cited by hot/ir/term.rs interning_is_canonical.
// CEP:SECURITY: none.
#[test]
fn interning_is_canonical() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let handles = build_random_terms(&terms, &symbols, &builder, 0x43414E4F);
    for handle in handles.iter() {
        let view = terms.term(*handle).expect("read");
        let rebuilt = match view.tag() {
            TermTag::Variable => terms.intern_var(view.symbol()).expect("rebuild"),
            TermTag::Function | TermTag::Predicate => {
                let children: Vec<_> = view.children().collect();
                if view.tag() == TermTag::Function {
                    terms
                        .intern_fun(&symbols, view.symbol(), &children)
                        .expect("rebuild")
                } else {
                    terms
                        .intern_pred(&symbols, view.symbol(), &children)
                        .expect("rebuild")
                }
            }
            TermTag::Equality => {
                let children: Vec<_> = view.children().collect();
                terms
                    .intern_eq(&symbols, children[0], children[1])
                    .expect("rebuild")
            }
            TermTag::Application => {
                let children: Vec<_> = view.children().collect();
                terms
                    .intern_app(&symbols, children[0], children[1])
                    .expect("rebuild")
            }
            TermTag::Sort => terms.intern_sort(view.symbol()).expect("rebuild"),
            TermTag::Lambda => *handle,
        };
        assert_eq!(
            rebuilt, *handle,
            "rebuilding a term must return the identical handle"
        );
    }
}

// CEP:WHAT: Verifies identical construction sequences produce identical offsets across stores.
// CEP:WHY: CEP&CC 38.10: deterministic translation; term identity must not depend on addresses or allocation luck.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any offset divergence.
// CEP:ASSUMES: two independent arenas and stores.
// CEP:COST: two full random builds.
// CEP:EVIDENCE: cited by hot/ir/term.rs hash_is_deterministic.
// CEP:SECURITY: none.
#[test]
fn hash_is_deterministic() {
    let (arena_a, symbols_a, builder_a, _terms_a, _clauses_a) = make_term_fixture();
    let (arena_b, symbols_b, builder_b, _terms_b, _clauses_b) = make_term_fixture();
    let store_a = TermStore::new(arena_a).expect("store a");
    let store_b = TermStore::new(arena_b).expect("store b");
    let handles_a = build_random_terms(&store_a, &symbols_a, &builder_a, 0x53454544);
    let handles_b = build_random_terms(&store_b, &symbols_b, &builder_b, 0x53454544);
    assert_eq!(handles_a.len(), handles_b.len());
    for (left, right) in handles_a.iter().zip(handles_b.iter()) {
        assert_eq!(
            left.as_u32(),
            right.as_u32(),
            "identical sequences must produce identical offsets"
        );
    }
}

// CEP:WHAT: Verifies structural equality of shared subterms.
// CEP:WHY: Hash-consing must deduplicate across the whole DAG, not just siblings.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missed sharing.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs term_equal.
// CEP:SECURITY: none.
#[test]
fn structural_sharing() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, fixture_id(&builder, "a"), &[])
        .expect("a");
    let f_id = fixture_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let h_id = fixture_id(&builder, "h");
    let left = terms
        .intern_fun(&symbols, h_id, &[fa, a])
        .expect("h(f(a),a)");
    let right = terms
        .intern_fun(&symbols, h_id, &[fa, a])
        .expect("h(f(a),a) again");
    assert!(terms.term_equal(left, right));
    let other = terms
        .intern_fun(&symbols, h_id, &[a, fa])
        .expect("h(a,f(a))");
    assert!(!terms.term_equal(left, other));
}

// CEP:WHAT: Verifies the random-build fixture uses a valid sort universe.
// CEP:WHY: Guards the fixture itself against signature drift.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the fixture symbols are malformed.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
#[test]
fn fixture_sort_universe_valid() {
    let (_arena, symbols, _builder, _terms, _clauses) = make_term_fixture();
    for id in 0..symbols.symbol_count() {
        let info = symbols.info(id).expect("info");
        let signature = symbols.sort_signature(id).expect("signature");
        match info.kind {
            mapt::hot::ir::symbol_table::SymbolKind::Sort => {
                assert_eq!(signature.len(), 1, "sorts have themselves as signature");
            }
            _ => {
                assert_eq!(
                    signature.len(),
                    info.arity as usize + 1,
                    "functions and predicates have arity plus one signature entries"
                );
            }
        }
    }
}
