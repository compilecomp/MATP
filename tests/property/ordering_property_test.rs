// CEP:FILE: tests/property/ordering_property_test.rs
// CEP:WHAT: Property tests for KBO and LPO: irreflexivity, transitivity on ground terms, totality on ground terms, the subterm property, antisymmetry of the outcomes, and stability of KBO under substitution.
// CEP:WHY: CEP&CC 32.9 and Formal Spec 03: the orderings are simplification orders; the definitional theorems (sections 2-4) are verified over deterministic random ground terms for both orderings in one harness.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any violated property.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the deterministic LCG makes every run identical.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ordering/* property pointers.
// CEP:SECURITY: none; no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_term_fixture, DeterministicRng};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::ordering::{compare_kbo, compare_lpo, OrderingComparison};

// CEP:WHAT: Property iterations per test.
// CEP:WHY: Named constant (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyIterations: u32 = 48;

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

// CEP:WHAT: Generates a random ground term of bounded depth.
// CEP:WHY: Ground totality and transitivity are ground-term properties; the generator picks constants and unary/binary applications.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: depth >= 1.
// CEP:COST: exponential in depth (bounded).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn ground_term(
    rng: &mut DeterministicRng,
    terms: &TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    depth: u32,
) -> TermPtr {
    if depth == 0 || rng.below(4) == 0 {
        let name = if rng.below(2) == 0 { "a" } else { "b" };
        return terms
            .intern_fun(symbols, symbol_id(builder, name), &[])
            .expect("constant");
    }
    if rng.below(2) == 0 {
        let child = ground_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "f"), &[child])
            .expect("f")
    } else {
        let left = ground_term(rng, terms, symbols, builder, depth - 1);
        let right = ground_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "h"), &[left, right])
            .expect("h")
    }
}

// CEP:WHAT: Runs a comparison function generically over both orderings.
// CEP:WHY: One harness, two orderings: every property is checked for KBO and LPO identically.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: selector 0 = KBO, 1 = LPO.
// CEP:COST: as the selected comparison.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn compare(
    selector: u32,
    terms: &TermStore<'_>,
    precedence: &PrecedenceTable<'_>,
    left: TermPtr,
    right: TermPtr,
) -> Result<OrderingComparison, mapt::hot::ordering::OrderingError> {
    if selector == 0 {
        compare_kbo(terms, precedence, left, right)
    } else {
        compare_lpo(terms, precedence, left, right)
    }
}

// CEP:WHAT: Property: both orderings are irreflexive and antisymmetric on every generated term.
// CEP:WHY: Spec 03 Theorems 2.1 and 3.1: simplification orders are strict orders.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on compare(t, t) != Equal or flipped outcomes.
// CEP:ASSUMES: random ground terms.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs and lpo.rs.
// CEP:SECURITY: none.
#[test]
fn ordering_irreflexive() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let mut rng = DeterministicRng::new(0x0DDE_0001);
    for _ in 0..kPropertyIterations {
        let term = ground_term(&mut rng, &terms, &symbols, &builder, 3);
        for selector in 0..2u32 {
            assert_eq!(
                compare(selector, &terms, &precedence, term, term),
                Ok(OrderingComparison::Equal),
                "every term equals itself"
            );
        }
    }
}

// CEP:WHAT: Property: both orderings are total on generated ground terms.
// CEP:WHY: Spec 03 Theorems 2.4 and 3.4: with a total precedence, ground terms are always comparable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any Incomparable ground pair.
// CEP:ASSUMES: random ground terms.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo and lpo.rs compare_lpo.
// CEP:SECURITY: none.
#[test]
fn ordering_total_on_ground() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let mut rng = DeterministicRng::new(0x0DDE_0002);
    for _ in 0..kPropertyIterations {
        let left = ground_term(&mut rng, &terms, &symbols, &builder, 3);
        let right = ground_term(&mut rng, &terms, &symbols, &builder, 3);
        for selector in 0..2u32 {
            let forward = compare(selector, &terms, &precedence, left, right);
            assert_ne!(
                forward,
                Ok(OrderingComparison::Incomparable),
                "ground terms must be comparable"
            );
            let backward = compare(selector, &terms, &precedence, right, left);
            assert_ne!(
                backward,
                Ok(OrderingComparison::Incomparable),
                "ground terms must be comparable in both argument orders"
            );
            // Antisymmetry: exactly one of the two strict directions holds, or the terms are equal.
            match (forward, backward) {
                (Ok(OrderingComparison::Greater), Ok(OrderingComparison::Less)) => {}
                (Ok(OrderingComparison::Less), Ok(OrderingComparison::Greater)) => {}
                (Ok(OrderingComparison::Equal), Ok(OrderingComparison::Equal)) => {}
                other => panic!("outcomes must be antisymmetric, got {:?}", other),
            }
        }
    }
}

// CEP:WHAT: Property: both orderings are transitive on generated ground terms.
// CEP:WHY: Spec 03 Theorems 2.2 and 3.2.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any Greater chain with a non-Greater close.
// CEP:ASSUMES: random ground term triples.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo and lpo.rs compare_lpo.
// CEP:SECURITY: none.
#[test]
fn ordering_transitive_ground() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let mut rng = DeterministicRng::new(0x0DDE_0003);
    for _ in 0..kPropertyIterations {
        let first = ground_term(&mut rng, &terms, &symbols, &builder, 2);
        let second = ground_term(&mut rng, &terms, &symbols, &builder, 3);
        let third = ground_term(&mut rng, &terms, &symbols, &builder, 4);
        for selector in 0..2u32 {
            let ab = compare(selector, &terms, &precedence, first, second);
            let bc = compare(selector, &terms, &precedence, second, third);
            if ab == Ok(OrderingComparison::Greater) && bc == Ok(OrderingComparison::Greater) {
                assert_eq!(
                    compare(selector, &terms, &precedence, first, third),
                    Ok(OrderingComparison::Greater),
                    "Greater o Greater must be Greater"
                );
            }
        }
    }
}

// CEP:WHAT: Property: both orderings have the subterm property on generated ground terms.
// CEP:WHY: Spec 03 Theorems 2.3 and 3.3: a simplification order dominates its proper subterms.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any container not above its child.
// CEP:ASSUMES: random ground containers.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo and lpo.rs compare_lpo.
// CEP:SECURITY: none.
#[test]
fn subterm_property_both_orderings() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let mut rng = DeterministicRng::new(0x0DDE_0004);
    for _ in 0..kPropertyIterations {
        let child = ground_term(&mut rng, &terms, &symbols, &builder, 2);
        let container = if rng.below(2) == 0 {
            terms
                .intern_fun(&symbols, symbol_id(&builder, "f"), &[child])
                .expect("f")
        } else {
            let other = ground_term(&mut rng, &terms, &symbols, &builder, 2);
            terms
                .intern_fun(&symbols, symbol_id(&builder, "h"), &[child, other])
                .expect("h")
        };
        for selector in 0..2u32 {
            assert_eq!(
                compare(selector, &terms, &precedence, container, child),
                Ok(OrderingComparison::Greater),
                "containers must dominate their subterms"
            );
        }
    }
}

// CEP:WHAT: Property: KBO is stable under substitution on generated pairs where it is Greater.
// CEP:WHY: Spec 03 Theorem 2.5: s >_kbo t implies s*sigma >_kbo t*sigma for every sigma; the test applies a random ground binding to both sides.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any Greater pair losing its direction under substitution.
// CEP:ASSUMES: random pairs and a ground substitution.
// CEP:COST: constant per iteration.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo.
// CEP:SECURITY: none.
#[test]
fn kbo_stable_under_substitution() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence =
        PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence");
    let substitution = mapt::hot::unification::substitution::Substitution::new(arena);
    let mut rng = DeterministicRng::new(0x0DDE_0005);
    let binder = ground_term(&mut rng, &terms, &symbols, &builder, 2);
    let mut checked = 0;
    for _ in 0..kPropertyIterations {
        let left = random_shallow_term(&mut rng, &terms, &symbols, &builder, 2);
        let right = random_shallow_term(&mut rng, &terms, &symbols, &builder, 2);
        if compare_kbo(&terms, &precedence, left, right) != Ok(OrderingComparison::Greater) {
            continue;
        }
        // Bind every variable the terms share to the ground binder.
        let entry = substitution.trail_depth();
        for variable in 0..4u32 {
            let var_term = terms.intern_var(variable).expect("var");
            let occurs_left = naive_occurs(&terms, variable, left, 0);
            let occurs_right = naive_occurs(&terms, variable, right, 0);
            if occurs_left || occurs_right {
                substitution.bind(variable, binder).expect("bind");
            }
            let _ = var_term;
        }
        let applied_left = substitution.apply(&terms, left, &symbols).expect("apply");
        let applied_right = substitution.apply(&terms, right, &symbols).expect("apply");
        if applied_left != applied_right {
            assert_eq!(
                compare_kbo(&terms, &precedence, applied_left, applied_right),
                Ok(OrderingComparison::Greater),
                "KBO Greater must survive substitution"
            );
        }
        checked += 1;
        substitution.undo_to(entry);
    }
    assert!(checked > 0, "the generator must produce Greater pairs");
}

// CEP:WHAT: Generates a random shallow term with variables.
// CEP:WHY: Substitution stability needs terms with variables.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: depth >= 1.
// CEP:COST: bounded.
// CEP:EVIDENCE: used by kbo_stable_under_substitution.
// CEP:SECURITY: none.
fn random_shallow_term(
    rng: &mut DeterministicRng,
    terms: &TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    depth: u32,
) -> TermPtr {
    if depth == 0 || rng.below(3) == 0 {
        let choice = rng.below(3);
        if choice == 0 {
            return terms.intern_var(rng.below(4) as u32).expect("var");
        }
        let name = if choice == 1 { "a" } else { "b" };
        return terms
            .intern_fun(symbols, symbol_id(builder, name), &[])
            .expect("constant");
    }
    if rng.below(2) == 0 {
        let child = random_shallow_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "f"), &[child])
            .expect("f")
    } else {
        let left = random_shallow_term(rng, terms, symbols, builder, depth - 1);
        let right = random_shallow_term(rng, terms, symbols, builder, depth - 1);
        terms
            .intern_fun(symbols, symbol_id(builder, "h"), &[left, right])
            .expect("h")
    }
}

// CEP:WHAT: Naive reference: does the variable occur in the term?
// CEP:WHY: Independent oracle for binding decisions.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(term size).
// CEP:EVIDENCE: used by kbo_stable_under_substitution.
// CEP:SECURITY: none.
fn naive_occurs(terms: &TermStore<'_>, variable: u32, term: TermPtr, depth: u32) -> bool {
    if depth > 32 {
        return false;
    }
    let view = match terms.term(term) {
        Ok(view) => view,
        Err(_) => return false,
    };
    if view.tag() == mapt::hot::ir::term::TermTag::Variable {
        return view.symbol() == variable;
    }
    for index in 0..view.child_count() {
        if let Ok(child) = view.child(index) {
            if naive_occurs(terms, variable, child, depth + 1) {
                return true;
            }
        }
    }
    false
}
