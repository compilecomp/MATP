// CEP:FILE: tests/security/phase4_bounds_test.rs
// CEP:WHAT: Security-bound tests of the Phase 4 components: the component-table record capacity, the canonical-word blob budget, and the splitter node budget (the denial-of-service guards of the AVATAR layer).
// CEP:WHY: CEP&CC 34.3 and design 20.2: every Phase 4 bound must be exercised on the production code path at small scales.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fresh arenas.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to security/phase4_bounds_test.rs.
// CEP:SECURITY: these tests ARE the security-bound evidence.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{kAtpFixtureArenaBytes, make_arena, symbol_id};
use mapt::hot::avatar::component::{canonical_component_words, AvatarError, ComponentTable};
use mapt::hot::avatar::splitter::{try_split, SplitDecision};
use mapt::hot::ir::literal::Literal;

#[test]
// CEP:WHAT: The component-table record capacity bound fires loudly (ComponentTableFull) and never wraps.
// CEP:WHY: The record capacity is the assertion-variable space (kAvatarComponentCapacity production; injected small here).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: capacity 2 with enough words.
// CEP:COST: three interns.
// CEP:EVIDENCE: backs security/phase4_bounds_test.rs::component_table_capacity_enforced and unit/hot/avatar_component_test.rs::capacity_enforced.
// CEP:SECURITY: resource-exhaustion guard.
fn component_table_capacity_enforced() {
    let arena = make_arena(kAtpFixtureArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _ = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let table = ComponentTable::new_with(arena, 2, 64).expect("table");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[a])
        .expect("p(a)");
    let words_of = |literals: &[Literal]| -> Vec<u32> {
        let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
            [0; mapt_config::limits::kMaxClauseLiterals as usize];
        let count = canonical_component_words(literals, &mut words);
        words[..count].to_vec()
    };
    let positive = words_of(&[Literal::new(atom, true)]);
    let negative = words_of(&[Literal::new(atom, false)]);
    assert!(table.intern(&positive, 1).is_ok());
    assert!(table.intern(&negative, 1).is_ok());
    // A third DISTINCT component (the two-literal sequence) exceeds capacity 2 -
    // loudly, without wrapping.
    let both = words_of(&[Literal::new(atom, true), Literal::new(atom, false)]);
    assert_eq!(table.intern(&both, 1), Err(AvatarError::ComponentTableFull));
    assert_eq!(table.component_count(), 2, "no wrap past the bound");
}

#[test]
// CEP:WHAT: The canonical-word blob budget fires loudly (WordBudgetExceeded) and never truncates a component.
// CEP:WHY: Truncation would corrupt component identity (Spec 12 section 4); the bound must be an error.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: word capacity 1.
// CEP:COST: two interns.
// CEP:EVIDENCE: backs security/phase4_bounds_test.rs::component_word_budget_enforced and unit/hot/avatar_component_test.rs::word_budget_enforced.
// CEP:SECURITY: resource-exhaustion guard.
fn component_word_budget_enforced() {
    let arena = make_arena(kAtpFixtureArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _ = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let table = ComponentTable::new_with(arena, 2, 1).expect("table");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[a])
        .expect("p(a)");
    let single = {
        let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
            [0; mapt_config::limits::kMaxClauseLiterals as usize];
        let count = canonical_component_words(&[Literal::new(atom, true)], &mut words);
        words[..count].to_vec()
    };
    assert_eq!(single.len(), 1);
    assert!(table.intern(&single, 1).is_ok(), "the single word fits");
    let pair = {
        let mut words: [u32; mapt_config::limits::kMaxClauseLiterals as usize] =
            [0; mapt_config::limits::kMaxClauseLiterals as usize];
        let count = canonical_component_words(
            &[Literal::new(atom, true), Literal::new(atom, false)],
            &mut words,
        );
        words[..count].to_vec()
    };
    assert_eq!(
        table.intern(&pair, 1),
        Err(AvatarError::WordBudgetExceeded),
        "the two-word component exceeds the 1-word blob"
    );
}

#[test]
// CEP:WHAT: The splitter node budget (kAvatarSplitNodeBudget) degrades adversarially deep clauses to Unsplittable without unbounded work.
// CEP:WHY: The walk budget is the denial-of-service guard of design 12.3 (CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the budget path errors or hangs.
// CEP:ASSUMES: a clause with more literals than the node budget.
// CEP:COST: one split decision.
// CEP:EVIDENCE: backs security/phase4_bounds_test.rs::splitter_node_budget_enforced and unit/hot/avatar_splitter_test.rs::walk_budget_degrades_to_unsplittable.
// CEP:SECURITY: denial-of-service guard.
fn splitter_node_budget_enforced() {
    let (arena, symbols, builder, terms, _precedence, _substitution) =
        common::make_inference_fixture();
    let _ = arena;
    // The adversarial DAG: a doubling chain over one variable - each record is one
    // intern (depth grows linearly, well below kMaxTermDepth) but the tree expansion
    // doubles per level, so the walk exceeds kAvatarSplitNodeBudget geometrically.
    let x = terms.intern_var(0).expect("var");
    let h = symbol_id(&builder, "h");
    let mut term = x;
    for _ in 0..13 {
        term = terms
            .intern_fun(&symbols, h, &[term, term])
            .expect("doubling intern");
    }
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[term])
        .expect("atom");
    let literals = [Literal::new(atom, true)];
    assert_eq!(
        try_split(&terms, &literals),
        SplitDecision::Unsplittable,
        "the budget exhaustion degrades to the unsplit path (the doubling DAG is the adversarial case)"
    );
}
