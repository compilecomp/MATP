// CEP:FILE: tests/unit/hot/avatar_component_test.rs
// CEP:WHAT: Unit tests of the AVATAR component table: interning identity, distinct slots, canonical word order, capacity and word-budget bounds, and dense assertion variables.
// CEP:WHY: CEP&CC 34.3: the table is the interning backbone of design 12.2 rule 1; its identity and bound claims (Spec 12 section 4) must be pinned executably.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fresh arena per test.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/avatar_component_test.rs.
// CEP:SECURITY: the bound tests exercise the resource-exhaustion guards.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{kAtpFixtureArenaBytes, make_arena, symbol_id};
use mapt::hot::avatar::component::{canonical_component_words, AvatarError, ComponentTable};
use mapt::hot::ir::literal::Literal;

// CEP:WHAT: Arena bytes for the component-table fixtures (small tables).
// CEP:WHY: Named fixture bound (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: covers the small tables plus slack.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kComponentArenaBytes: u32 = kAtpFixtureArenaBytes;

// CEP:WHAT: Two literals built over distinct ground atoms (distinct canonical words).
// CEP:WHY: The interning fixtures need distinct, deterministic word sequences.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: two interns.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn ground_literals(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
) -> Vec<Literal> {
    let a = terms
        .intern_fun(symbols, symbol_id(builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(symbols, symbol_id(builder, "b"), &[])
        .expect("b");
    vec![
        Literal::new(
            terms
                .intern_pred(symbols, symbol_id(builder, "p"), &[a])
                .expect("p(a)"),
            true,
        ),
        Literal::new(
            terms
                .intern_pred(symbols, symbol_id(builder, "q"), &[b])
                .expect("q(b)"),
            false,
        ),
    ]
}

// CEP:WHAT: Builds the full fixture (arena, symbols, builder, terms) for the table tests.
// CEP:WHY: One constructor.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn table_fixture(
    record_capacity: u32,
    word_capacity: u32,
) -> (
    ComponentTable<'static>,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    mapt::hot::ir::term::TermStore<'static>,
) {
    let arena = make_arena(kComponentArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _ = builder.declare_function("b", 0, 1, &[], sort_s).expect("b");
    let _ = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let _ = builder.declare_predicate("q", 1, 1, &[sort_s]).expect("q");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let table = ComponentTable::new_with(arena, record_capacity, word_capacity).expect("table");
    (table, symbols, builder, terms)
}

#[test]
// CEP:WHAT: Interning the same canonical words twice returns the same slot, fresh only the first time.
// CEP:WHY: Spec 12 section 4's identity contract (component sharing across splits, Voronkov 2014).
// CEP:STATUS: complete
// CEP:FAILURE: panics on a fresh second interning.
// CEP:ASSUMES: none.
// CEP:COST: two interns.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::components_interned_once.
// CEP:SECURITY: none.
fn components_interned_once() {
    let (table, symbols, builder, terms) = table_fixture(64, 256);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let count = canonical_component_words(&literals, &mut words);
    let first = table.intern(&words[..count], 1).expect("first intern");
    let second = table.intern(&words[..count], 2).expect("second intern");
    assert!(first.fresh, "the first interning creates the record");
    assert!(!second.fresh, "the second interning shares the record");
    assert_eq!(first.slot, second.slot);
    assert_eq!(table.component_count(), 1);
    // The first source sticks (the second interning's source is not read).
    assert_eq!(table.source_clause(first.slot), Some(1));
}

#[test]
// CEP:WHAT: Distinct word sequences occupy distinct slots.
// CEP:WHY: The injectivity direction of the identity contract.
// CEP:STATUS: complete
// CEP:FAILURE: panics if distinct components collide.
// CEP:ASSUMES: none.
// CEP:COST: two interns.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::distinct_components_get_distinct_slots.
// CEP:SECURITY: none.
fn distinct_components_get_distinct_slots() {
    let (table, symbols, builder, terms) = table_fixture(64, 256);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let first_count = canonical_component_words(&literals, &mut words);
    let first = table.intern(&words[..first_count], 1).expect("first");
    // The second sequence: only one literal (a sub-multiset).
    let second = table.intern(&words[..1], 1).expect("second");
    assert_ne!(first.slot, second.slot);
    assert_eq!(table.component_count(), 2);
}

#[test]
// CEP:WHAT: canonical_component_words sorts the words ascending and packs (atom << 1 | polarity).
// CEP:WHY: Spec 12 section 4's canonical form (sorted words make the sequence order-independent).
// CEP:STATUS: complete
// CEP:FAILURE: panics on unsorted words or wrong packing.
// CEP:ASSUMES: the fixture literals.
// CEP:COST: one canonicalization.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::canonical_words_sorted.
// CEP:SECURITY: none.
fn canonical_words_sorted() {
    let (_table, symbols, builder, terms) = table_fixture(64, 256);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let count = canonical_component_words(&literals, &mut words);
    assert_eq!(count, 2);
    assert!(
        words[0] <= words[1],
        "the word sequence is sorted ascending"
    );
    for (index, literal) in literals.iter().enumerate() {
        let expected = (literal.atom().as_u32() << 1) | if literal.is_positive() { 1 } else { 0 };
        assert!(
            words[..count].contains(&expected),
            "word {} must appear",
            index
        );
    }
}

#[test]
// CEP:WHAT: Interning past the record capacity returns ComponentTableFull.
// CEP:WHY: The assertion-variable space bound (kAvatarComponentCapacity; injectable for tests).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: capacity 2.
// CEP:COST: three interns.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::capacity_enforced and security/phase4_bounds_test.rs::component_table_capacity_enforced.
// CEP:SECURITY: resource bound.
fn capacity_enforced() {
    let (table, symbols, builder, terms) = table_fixture(1, 8);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let count = canonical_component_words(&literals, &mut words);
    assert!(table.intern(&words[..1], 1).is_ok());
    assert_eq!(
        table.intern(&words[..count], 1),
        Err(AvatarError::ComponentTableFull),
        "the second distinct component exceeds capacity 1"
    );
}

#[test]
// CEP:WHAT: Interning past the word-blob budget returns WordBudgetExceeded.
// CEP:WHY: The blob is the fixed shared storage; exhaustion is loud, never truncating.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: word capacity 2 (one 2-word component fits, a second does not).
// CEP:COST: two interns.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::word_budget_enforced and security/phase4_bounds_test.rs::component_word_budget_enforced.
// CEP:SECURITY: resource bound.
fn word_budget_enforced() {
    let (table, symbols, builder, terms) = table_fixture(2, 2);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let count = canonical_component_words(&literals, &mut words);
    assert_eq!(count, 2);
    assert!(table.intern(&words[..2], 1).is_ok(), "exactly fits");
    assert_eq!(
        table.intern(&words[..1], 1),
        Err(AvatarError::WordBudgetExceeded),
        "the blob is full"
    );
}

#[test]
// CEP:WHAT: Assertion variables are dense: SatVar(slot) for every slot, and the record capacity equals the variable space.
// CEP:WHY: Spec 12 section 4: the slot index doubles as the assertion variable (the abstraction solver's variable space is exactly the record capacity).
// CEP:STATUS: complete
// CEP:FAILURE: panics on a sparse mapping.
// CEP:ASSUMES: none.
// CEP:COST: a few interns.
// CEP:EVIDENCE: backs unit/hot/avatar_component_test.rs::assertion_variables_dense.
// CEP:SECURITY: none.
fn assertion_variables_dense() {
    let (table, symbols, builder, terms) = table_fixture(8, 64);
    let literals = ground_literals(&terms, &symbols, &builder);
    let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
        [0; mapt_config::limits::kMaxClauseLiterals as usize];
    let count = canonical_component_words(&literals, &mut words);
    let first = table.intern(&words[..count], 1).expect("first");
    let second = table.intern(&words[..1], 1).expect("second");
    let variables: Vec<u32> = [first.slot, second.slot]
        .iter()
        .map(|slot| table.assertion_variable(*slot).0)
        .collect();
    assert!(variables.contains(&first.slot), "variable == slot (dense)");
    assert!(variables.contains(&second.slot));
    assert_eq!(table.record_capacity(), 8);
    assert_eq!(table.component_count(), 2);
}
