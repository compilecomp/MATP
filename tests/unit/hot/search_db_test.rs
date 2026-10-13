// CEP:FILE: tests/unit/hot/search_db_test.rs
// CEP:WHAT: Unit tests for the search database: passive-heap ordering under all three strategies with clause-id tiebreaks, capacity bounds, active-set insertion and deletion with tree updates, the unit rule-tree flag, the forward-subsumption filter path, and the selection weight function.
// CEP:WHY: Design 8.4/15.2/15.3 and Spec 08 sections 4-5: the database's ordering and index invariants are the determinism and fairness backbone of the loop; they are pinned here at component scale.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; small injected capacities.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/search/passive.rs, hot/search/active.rs, and hot/search/given_clause.rs (SelectionWeight).
// CEP:SECURITY: the capacity bounds are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, make_inference_fixture, symbol_id};
use mapt::hot::ir::literal::Literal;
use mapt::hot::search::given_clause::{SearchOptions, SearchSpace, SelectionWeight};
use mapt::hot::search::passive::{PassiveHeap, SelectionStrategy};

// CEP:WHAT: Verifies the age/weight ratio ordering (small ratio pops first).
// CEP:WHY: Design 15.2's default strategy.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong pop order.
// CEP:ASSUMES: clauses with distinct ages and weights.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::{priority_of, push} and config/limits.rs kSelectionRatioScale.
// CEP:SECURITY: none.
#[test]
fn heap_orders_by_ratio() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 16, SelectionStrategy::AgeWeightRatio).expect("heap");
    // Clause A: age 10, weight 10 -> ratio 10 * 65536 / 10 = 65536.
    // Clause B: age 2, weight 1 -> ratio 2 * 65536 / 1 = 131072.
    // Clause C: age 40, weight 10 -> ratio 40 * 65536 / 10 = 262144.
    heap.push(1, 10, 10, 10).expect("push A");
    heap.push(2, 20, 2, 1).expect("push B");
    heap.push(3, 30, 40, 10).expect("push C");
    let first = heap.pop().expect("pop");
    let second = heap.pop().expect("pop");
    let third = heap.pop().expect("pop");
    assert_eq!(first.clause_id, 1, "smallest ratio first");
    assert_eq!(second.clause_id, 2);
    assert_eq!(third.clause_id, 3);
}

// CEP:WHAT: Verifies the ratio priority computation directly.
// CEP:WHY: The fixed-point formula.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong value.
// CEP:ASSUMES: age 3, weight 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::priority_of.
// CEP:SECURITY: none.
#[test]
fn ratio_priority_order() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 4, SelectionStrategy::AgeWeightRatio).expect("heap");
    assert_eq!(
        heap.priority_of(3, 2),
        (3u64 * mapt_config::limits::kSelectionRatioScale) / 2
    );
}

// CEP:WHAT: Verifies the weight-only ordering.
// CEP:WHY: Design 15.2 row 3.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong pop order.
// CEP:ASSUMES: distinct weights.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::{priority_of, pop}.
// CEP:SECURITY: none.
#[test]
fn heap_orders_by_weight() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 8, SelectionStrategy::WeightOnly).expect("heap");
    heap.push(1, 10, 0, 7).expect("push");
    heap.push(2, 20, 0, 3).expect("push");
    heap.push(3, 30, 0, 5).expect("push");
    assert_eq!(heap.pop().expect("pop").clause_id, 2);
    assert_eq!(heap.pop().expect("pop").clause_id, 3);
    assert_eq!(heap.pop().expect("pop").clause_id, 1);
}

// CEP:WHAT: Verifies the age-only ordering (breadth-first).
// CEP:WHY: Design 15.2 row 4.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong pop order.
// CEP:ASSUMES: distinct ages.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::{priority_of, pop}.
// CEP:SECURITY: none.
#[test]
fn heap_orders_by_age() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 8, SelectionStrategy::AgeOnly).expect("heap");
    heap.push(1, 10, 5, 100).expect("push");
    heap.push(2, 20, 1, 100).expect("push");
    heap.push(3, 30, 3, 100).expect("push");
    assert_eq!(heap.pop().expect("pop").clause_id, 2);
    assert_eq!(heap.pop().expect("pop").clause_id, 3);
    assert_eq!(heap.pop().expect("pop").clause_id, 1);
}

// CEP:WHAT: Verifies priority ties break by clause id (older first).
// CEP:WHY: Design 8.4's total key.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong order.
// CEP:ASSUMES: two clauses with equal priority.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::{push, sift_up}.
// CEP:SECURITY: none.
#[test]
fn tie_breaks_by_clause_id() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 8, SelectionStrategy::WeightOnly).expect("heap");
    heap.push(7, 70, 0, 5).expect("push");
    heap.push(2, 20, 0, 5).expect("push");
    heap.push(4, 40, 0, 5).expect("push");
    assert_eq!(heap.pop().expect("pop").clause_id, 2);
    assert_eq!(heap.pop().expect("pop").clause_id, 4);
    assert_eq!(heap.pop().expect("pop").clause_id, 7);
}

// CEP:WHAT: Verifies the heap key ordering through a mixed workload (the aggregate alias of the strategy tests).
// CEP:WHY: The limits-file evidence cites this name for the capacity constant's behavior.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong order.
// CEP:ASSUMES: interleaved pushes and pops.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs kPassiveHeapCapacity.
// CEP:SECURITY: none.
#[test]
fn heap_orders_by_key() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 8, SelectionStrategy::AgeWeightRatio).expect("heap");
    heap.push(1, 10, 1, 1).expect("push");
    heap.push(2, 20, 1, 1).expect("push");
    assert_eq!(heap.pop().expect("pop").clause_id, 1);
    heap.push(3, 30, 0, 1).expect("push");
    assert_eq!(heap.pop().expect("pop").clause_id, 3);
    assert_eq!(heap.pop().expect("pop").clause_id, 2);
    assert!(heap.pop().is_none());
}

// CEP:WHAT: Verifies the passive capacity bound.
// CEP:WHY: The loud memory bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a push past the bound succeeds.
// CEP:ASSUMES: capacity 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::{push, PassiveError::Full} and config/limits.rs kPassiveHeapCapacity.
// CEP:SECURITY: the memory bound under test.
#[test]
fn capacity_enforced() {
    let arena = make_arena(1_048_576);
    let heap = PassiveHeap::new_with(arena, 2, SelectionStrategy::AgeOnly).expect("heap");
    assert!(heap.push(1, 10, 0, 1).is_ok());
    assert!(heap.push(2, 20, 0, 1).is_ok());
    assert!(heap.push(3, 30, 0, 1).is_err());
}

// CEP:WHAT: Builds a small search space for the active-set tests.
// CEP:WHY: One constructor for this file's active tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh fixture.
// CEP:COST: one space.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn small_space() -> (
    SearchSpace<'static>,
    mapt::hot::ir::symbol_table::SymbolTable<'static>,
    mapt::cold::symbol_table_builder::SymbolTableBuilder,
    mapt::hot::ir::term::TermStore<'static>,
) {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    // The fixture arena also hosts the term table; build the space with small caps
    // against the remaining room.
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &options, 64, 32, 2048, 2048, 8192).expect("space");
    (space, symbols, builder, terms)
}

// CEP:WHAT: Builds a predicate literal.
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
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Verifies active-set insertion, slot reads, and removal with swap-remove.
// CEP:WHY: Spec 08 section 5.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong slot state.
// CEP:ASSUMES: three clauses inserted, the middle removed.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/active.rs::{insert, remove, slot}.
// CEP:SECURITY: none.
#[test]
fn active_insert_delete() {
    let (space, symbols, builder, terms) = small_space();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let clause_a = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let clause_b = [pred(&terms, &symbols, &builder, "p", &[b], true)];
    let clause_c = [pred(&terms, &symbols, &builder, "r", &[], true)];
    let store = &space.store;
    let ptr_a = store
        .new_clause(&terms, &clause_a, 0, input_derivation())
        .expect("c");
    let ptr_b = store
        .new_clause(&terms, &clause_b, 1, input_derivation())
        .expect("c");
    let ptr_c = store
        .new_clause(&terms, &clause_c, 2, input_derivation())
        .expect("c");
    space
        .active
        .insert(&terms, ptr_a.as_u32(), &clause_a)
        .expect("ins");
    space
        .active
        .insert(&terms, ptr_b.as_u32(), &clause_b)
        .expect("ins");
    space
        .active
        .insert(&terms, ptr_c.as_u32(), &clause_c)
        .expect("ins");
    assert_eq!(space.active.len(), 3);
    // Remove the middle: the last slot swaps into index 1.
    space.active.remove(&terms, store, 1).expect("remove");
    assert_eq!(space.active.len(), 2);
    assert_eq!(space.active.slot(0).expect("slot").offset, ptr_a.as_u32());
    assert_eq!(space.active.slot(1).expect("slot").offset, ptr_c.as_u32());
}

// CEP:WHAT: Verifies the atom tree tracks insertions and deletions.
// CEP:WHY: Spec 08 section 5's index invariant.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a stale payload.
// CEP:ASSUMES: one clause with one literal, removed after retrieval.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/active.rs::{insert, remove, atom_tree}.
// CEP:SECURITY: none.
#[test]
fn active_trees_updated() {
    let (space, symbols, builder, terms) = small_space();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let clause = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let ptr = space
        .store
        .new_clause(&terms, &clause, 0, input_derivation())
        .expect("c");
    space
        .active
        .insert(&terms, ptr.as_u32(), &clause)
        .expect("ins");
    let mut payloads: [u64; 8] = [0; 8];
    let count = space
        .active
        .atom_tree()
        .retrieve(&terms, clause[0].atom(), &mut payloads)
        .expect("retrieve");
    assert_eq!(count, 1);
    space
        .active
        .remove(&terms, &space.store, 0)
        .expect("remove");
    let count_after = space
        .active
        .atom_tree()
        .retrieve(&terms, clause[0].atom(), &mut payloads)
        .expect("retrieve");
    assert_eq!(count_after, 0, "the payload must be gone");
}

// CEP:WHAT: Verifies unit equations carry the unit flag in the rule tree.
// CEP:WHY: Demodulation uses unit rules only.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a missing flag.
// CEP:ASSUMES: a unit equation f(x) = x.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/active.rs::{insert, pack_payload, rule_tree}.
// CEP:SECURITY: none.
#[test]
fn rule_tree_indexes_units() {
    let (space, symbols, builder, terms) = small_space();
    let x = terms.intern_var(0).expect("x");
    let f_x = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    let atom = terms.intern_eq(&symbols, f_x, x).expect("eq");
    let clause = [Literal::new(atom, true)];
    let ptr = space
        .store
        .new_clause(&terms, &clause, 0, input_derivation())
        .expect("c");
    space
        .active
        .insert(&terms, ptr.as_u32(), &clause)
        .expect("ins");
    let mut payloads: [u64; 8] = [0; 8];
    let count = space
        .active
        .rule_tree()
        .retrieve(&terms, f_x, &mut payloads)
        .expect("retrieve");
    assert_eq!(count, 1);
    let (_offset, _index, unit) = mapt::hot::search::active::unpack_payload(payloads[0]);
    assert!(unit, "the unit equation must carry the unit flag");
}

// CEP:WHAT: Verifies the forward-subsumption path consults the feature filter.
// CEP:WHY: Design 9.3's two-tier flow (the filter runs before the matching check).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the filter is skipped (observable through a heavier subsumer being rejected without a match attempt - pinned by the dominance filter unit test and the loop-level test together).
// CEP:ASSUMES: an active p(a) and a given p(a) or r.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::forward_subsumed and hot/index/feature_vector.rs::may_subsume.
// CEP:SECURITY: none.
#[test]
fn forward_subsumption_uses_filter() {
    let (space, symbols, builder, terms) = small_space();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let small = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let ptr = space
        .store
        .new_clause(&terms, &small, 0, input_derivation())
        .expect("c");
    space
        .active
        .insert(&terms, ptr.as_u32(), &small)
        .expect("ins");
    // The filter must pass the (unit, binary) pair on to the matcher, which accepts.
    let context = mapt::hot::inference::InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &make_precedence(),
        ordering: mapt::hot::inference::OrderingKind::Kbo,
    };
    let larger = [
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "r", &[], true),
    ];
    let outcome =
        mapt::hot::search::given_clause::saturate_probe_forward(&space, &context, &larger);
    assert!(outcome, "p(a) subsumes p(a) or r through the filtered path");
}

// CEP:WHAT: Verifies the active slot capacity bound.
// CEP:WHY: The loud memory bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when insertion past the bound succeeds.
// CEP:ASSUMES: slot capacity 2 (through a fresh space).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/active.rs::{insert, ActiveError::SlotsFull} and config/limits.rs kActiveSetCapacity.
// CEP:SECURITY: the memory bound under test.
#[test]
fn active_capacity_enforced() {
    let (arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &options, 8, 2, 1024, 1024, 4096).expect("space");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let clause_a = [pred(&terms, &symbols, &builder, "p", &[a], true)];
    let clause_b = [pred(&terms, &symbols, &builder, "p", &[b], true)];
    let clause_c = [pred(&terms, &symbols, &builder, "r", &[], true)];
    let ptr_a = space
        .store
        .new_clause(&terms, &clause_a, 0, input_derivation())
        .expect("c");
    let ptr_b = space
        .store
        .new_clause(&terms, &clause_b, 1, input_derivation())
        .expect("c");
    let ptr_c = space
        .store
        .new_clause(&terms, &clause_c, 2, input_derivation())
        .expect("c");
    assert!(space
        .active
        .insert(&terms, ptr_a.as_u32(), &clause_a)
        .is_ok());
    assert!(space
        .active
        .insert(&terms, ptr_b.as_u32(), &clause_b)
        .is_ok());
    assert!(space
        .active
        .insert(&terms, ptr_c.as_u32(), &clause_c)
        .is_err());
}

// CEP:WHAT: Verifies the selection weight counts symbols per design 15.3.
// CEP:WHY: weight = sum of symbol weights x occurrences.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong weight.
// CEP:ASSUMES: p(f(a)): p + f + a = 3 with default weights.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{SelectionWeight, of}.
// CEP:SECURITY: none.
#[test]
fn selection_weight_counts_symbols() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_a = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let clause = [pred(&terms, &symbols, &builder, "p", &[f_a], true)];
    assert_eq!(SelectionWeight::of(&terms, &symbols, &clause), 3);
}

// CEP:WHAT: Verifies variables contribute the selection variable weight (zero).
// CEP:WHY: Design 15.3's variable default.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong weight.
// CEP:ASSUMES: p(x): weight 1 (p only).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::SelectionWeight and config/limits.rs kSelectionVariableWeight.
// CEP:SECURITY: none.
#[test]
fn selection_weight_ignores_variables() {
    let (_arena, symbols, builder, terms, _p, _s) = make_inference_fixture();
    let x = terms.intern_var(0).expect("x");
    let clause = [pred(&terms, &symbols, &builder, "p", &[x], true)];
    assert_eq!(SelectionWeight::of(&terms, &symbols, &clause), 1);
}

// CEP:WHAT: Builds an id-order precedence over the fixture vocabulary.
// CEP:WHY: The context needs one; the fixture bundle does not carry it into the space.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: fixture arena with room.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_precedence() -> mapt::hot::ordering::precedence::PrecedenceTable<'static> {
    let arena = make_arena(1_048_576);
    mapt::hot::ordering::precedence::PrecedenceTable::from_id_order(arena, 8).expect("prec")
}

// CEP:WHAT: Builds an Input derivation step.
// CEP:WHY: Store fixtures need one.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn input_derivation() -> mapt::hot::ir::clause::DerivationStep {
    mapt::hot::ir::clause::DerivationStep {
        rule: mapt::hot::ir::clause::InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [0; 4],
        substitution: mapt_config::limits::kInvalidSubstitutionOffset,
    }
}
