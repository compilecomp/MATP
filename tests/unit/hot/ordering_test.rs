// CEP:FILE: tests/unit/hot/ordering_test.rs
// CEP:WHAT: Unit tests for the precedence table, KBO, and LPO: construction policies, weight dominance, precedence and lexicographic tie-breaks, the variable condition, ground totality, and the LPO cases.
// CEP:WHY: CEP&CC 32.8 and Formal Spec 03: the orderings are side conditions of every superposition and resolution inference; an unsound ordering silently produces unsound inferences, so the definitional cases are pinned here before Phase 3 consumes them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ordering/*.
// CEP:SECURITY: rank validation and unknown symbols are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::ordering::precedence::{PrecedenceError, PrecedenceTable};
use mapt::hot::ordering::{compare_kbo, compare_lpo, OrderingComparison, OrderingError};
use mapt_config::limits::kMaxSymbolCount;

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

// CEP:WHAT: Builds the default ID-order precedence for the fixture.
// CEP:WHY: Shared setup for the ordering tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn default_precedence<'a>(
    arena: &'a mapt::hot::memory::arena::Arena,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
) -> PrecedenceTable<'a> {
    PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("precedence")
}

// CEP:WHAT: Verifies the default policy ranks symbols by ID with the equality head maximal.
// CEP:WHY: Design 8.3 configuration note and the determinism requirement (CEP&CC 38.10).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong ranks.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/precedence.rs from_id_order.
// CEP:SECURITY: none.
#[test]
fn id_order_is_default() {
    let (arena, _symbols, builder, _terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    assert_eq!(precedence.symbol_count(), builder.symbol_count());
    for id in 0..builder.symbol_count() {
        assert_eq!(precedence.rank(id), Ok(id));
    }
    assert_eq!(precedence.equality_rank(), builder.symbol_count());
}

// CEP:WHAT: Verifies explicit ranks are validated as a permutation and rejected otherwise.
// CEP:WHY: CEP&CC Law 3: the trust boundary validates strategy input before the hot path depends on totality.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a non-permutation is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/precedence.rs from_ranks.
// CEP:SECURITY: smuggled partial orders must be rejected.
#[test]
fn explicit_ranks_validated() {
    let (arena, _symbols, _builder, _terms, _clauses) = make_term_fixture();
    // A valid permutation of three entries (two symbols plus the equality head).
    let valid = PrecedenceTable::from_ranks(arena, &[1, 2, 0]).expect("valid permutation");
    assert_eq!(valid.symbol_count(), 2);
    assert_eq!(valid.rank(0), Ok(1));
    assert_eq!(valid.equality_rank(), 0);
    let (arena2, _s2, _b2, _t2, _c2) = make_term_fixture();
    // Duplicated ranks are rejected.
    assert_eq!(
        PrecedenceTable::from_ranks(arena2, &[1, 1, 0]).err(),
        Some(PrecedenceError::InvalidRanks)
    );
    let (arena3, _s3, _b3, _t3, _c3) = make_term_fixture();
    // Out-of-range ranks are rejected.
    assert_eq!(
        PrecedenceTable::from_ranks(arena3, &[0, 1, 3]).err(),
        Some(PrecedenceError::InvalidRanks)
    );
}

// CEP:WHAT: Verifies unknown symbols are rejected on rank reads.
// CEP:WHY: Law 6: bounds violations are loud.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an out-of-range read succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/precedence.rs rank.
// CEP:SECURITY: bounds enforcement.
#[test]
fn unknown_symbol_rejected() {
    let (arena, _symbols, builder, _terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    assert_eq!(
        precedence.rank(builder.symbol_count()),
        Err(PrecedenceError::UnknownSymbol)
    );
    assert_eq!(
        precedence.rank(kMaxSymbolCount),
        Err(PrecedenceError::UnknownSymbol)
    );
}

// CEP:WHAT: Verifies KBO weight dominance: f(f(a)) is greater than f(a) by weight alone.
// CEP:WHY: Spec 03 section 2 case 1; the fast path must decide on cached header weights.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong direction.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_bounded.
// CEP:SECURITY: none.
#[test]
fn kbo_weight_dominates() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let ffa = terms.intern_fun(&symbols, f, &[fa]).expect("f(f(a))");
    assert_eq!(
        compare_kbo(&terms, &precedence, ffa, fa),
        Ok(OrderingComparison::Greater)
    );
    assert_eq!(
        compare_kbo(&terms, &precedence, fa, ffa),
        Ok(OrderingComparison::Less)
    );
    assert_eq!(
        compare_kbo(&terms, &precedence, fa, fa),
        Ok(OrderingComparison::Equal)
    );
}

// CEP:WHAT: Verifies the KBO precedence case on weight ties.
// CEP:WHY: Spec 03 section 2 case 2: equal weights fall to head precedence; with ID order, g > f when g's ID is larger.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong direction.
// CEP:ASSUMES: ground terms with equal weight.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_bounded.
// CEP:SECURITY: none.
#[test]
fn kbo_precedence_case() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let f_id = symbol_id(&builder, "f");
    let g_id = symbol_id(&builder, "g");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let ga = terms.intern_fun(&symbols, g_id, &[a]).expect("g(a)");
    let expected = if g_id > f_id {
        OrderingComparison::Greater
    } else {
        OrderingComparison::Less
    };
    assert_eq!(compare_kbo(&terms, &precedence, ga, fa), Ok(expected));
    assert_eq!(
        compare_kbo(&terms, &precedence, fa, ga),
        Ok(if expected == OrderingComparison::Greater {
            OrderingComparison::Less
        } else {
            OrderingComparison::Greater
        })
    );
}

// CEP:WHAT: Verifies the KBO lexicographic case on weight and head ties.
// CEP:WHY: Spec 03 section 2 case 3: same head, first differing child decides.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong direction.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_bounded.
// CEP:SECURITY: none.
#[test]
fn kbo_lexicographic_case() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a_id = symbol_id(&builder, "a");
    let b_id = symbol_id(&builder, "b");
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let b = terms.intern_fun(&symbols, b_id, &[]).expect("b");
    let h = symbol_id(&builder, "h");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let hba = terms.intern_fun(&symbols, h, &[b, a]).expect("h(b, a)");
    // First children a vs b decide; b has the larger ID so h(b, a) is greater.
    let expected = if b_id > a_id {
        OrderingComparison::Less
    } else {
        OrderingComparison::Greater
    };
    assert_eq!(compare_kbo(&terms, &precedence, hab, hba), Ok(expected));
}

// CEP:WHAT: Verifies the KBO variable condition gates weight dominance.
// CEP:WHY: Spec 03 section 2: f(x, x) must not dominate g(x) (equal weights) because the variable counts differ; the lazy check converts the structural answer to Incomparable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the variable condition is ignored.
// CEP:ASSUMES: weight-equal fixture symbols f/2 and g/1 both contribute weight 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs variable_counts_dominate.
// CEP:SECURITY: none.
#[test]
fn kbo_variable_condition_gates() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let x = terms.intern_var(0).expect("x");
    let g_id = symbol_id(&builder, "g");
    let h = symbol_id(&builder, "h");
    let hxx = terms.intern_fun(&symbols, h, &[x, x]).expect("h(x, x)");
    let gx = terms.intern_fun(&symbols, g_id, &[x]).expect("g(x)");
    // w(h(x,x)) = w(h) + 2 > w(g(x)) = w(g) + 1 with unit weights, so weight dominance
    // applies and the variable condition holds (x occurs at least as often): Greater.
    assert_eq!(
        compare_kbo(&terms, &precedence, hxx, gx),
        Ok(OrderingComparison::Greater)
    );
    // The real gate: h(x, y) vs h(y, x) have equal weight and the same head, the lex
    // comparison says Greater at the first child (if x's index < y's), but the variable
    // counts are equal (one x and one y each side), so it stays comparable; instead the
    // canonical gating pair is h(x, x) vs h(y, x): counts differ, must be Incomparable
    // whenever the lex or precedence case would otherwise decide.
    let y = terms.intern_var(1).expect("y");
    let hyx = terms.intern_fun(&symbols, h, &[y, x]).expect("h(y, x)");
    // First differing child: x vs y. y is a variable, so the child comparison is
    // Incomparable, and so is the parent.
    assert_eq!(
        compare_kbo(&terms, &precedence, hxx, hyx),
        Ok(OrderingComparison::Incomparable)
    );
    // Weight-dominance gating: h(y, y) has larger weight than g(x) but contains y twice
    // while the smaller term contains no y; both directions must fail their counts.
    let hyy = terms.intern_fun(&symbols, h, &[y, y]).expect("h(y, y)");
    let gx2 = terms.intern_fun(&symbols, g_id, &[x]).expect("g(x)");
    assert_eq!(
        compare_kbo(&terms, &precedence, hyy, gx2),
        Ok(OrderingComparison::Incomparable),
        "weight dominance must be gated by the variable condition"
    );
}

// CEP:WHAT: Verifies KBO is total on ground terms of the fixture vocabulary.
// CEP:WHY: Spec 03 Theorem 2.4: with a total precedence and unit weights KBO is total on ground terms; totality is what literal selection needs.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any Incomparable ground pair.
// CEP:ASSUMES: ground terms.
// CEP:COST: quadratic in the term set.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo.
// CEP:SECURITY: none.
#[test]
fn kbo_ground_totality() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f = symbol_id(&builder, "f");
    let g = symbol_id(&builder, "g");
    let h = symbol_id(&builder, "h");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let fb = terms.intern_fun(&symbols, f, &[b]).expect("f(b)");
    let ga = terms.intern_fun(&symbols, g, &[a]).expect("g(a)");
    let gb = terms.intern_fun(&symbols, g, &[b]).expect("g(b)");
    let haa = terms.intern_fun(&symbols, h, &[a, a]).expect("h(a, a)");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let ground = [a, b, fa, fb, ga, gb, haa, hab];
    for left in ground.iter() {
        for right in ground.iter() {
            let outcome = compare_kbo(&terms, &precedence, *left, *right);
            assert_ne!(
                outcome,
                Ok(OrderingComparison::Incomparable),
                "KBO must be total on ground terms"
            );
        }
    }
}

// CEP:WHAT: Verifies the LPO subterm case: f(t) is greater than t.
// CEP:WHY: Spec 03 section 3 case (a): every simplification order has the subterm property.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong direction.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/lpo.rs lpo_greater.
// CEP:SECURITY: none.
#[test]
fn lpo_subterm_case() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let ffa = terms.intern_fun(&symbols, f, &[fa]).expect("f(f(a))");
    assert_eq!(
        compare_lpo(&terms, &precedence, fa, a),
        Ok(OrderingComparison::Greater)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, ffa, fa),
        Ok(OrderingComparison::Greater)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, a, fa),
        Ok(OrderingComparison::Less)
    );
}

// CEP:WHAT: Verifies the LPO variable case: f(x) is greater than x, x is incomparable with y.
// CEP:WHY: Spec 03 section 3 case 1: a compound term dominates the variables it contains.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong outcome.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/lpo.rs lpo_greater.
// CEP:SECURITY: none.
#[test]
fn lpo_variable_case() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let fx = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[x])
        .expect("f(x)");
    assert_eq!(
        compare_lpo(&terms, &precedence, fx, x),
        Ok(OrderingComparison::Greater)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, x, fx),
        Ok(OrderingComparison::Less)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, x, y),
        Ok(OrderingComparison::Incomparable),
        "distinct variables are unrelated"
    );
}

// CEP:WHAT: Verifies the LPO precedence and lexicographic cases on ground terms.
// CEP:WHY: Spec 03 section 3 cases (b) and (c).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong direction.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/lpo.rs lpo_greater.
// CEP:SECURITY: none.
#[test]
fn lpo_precedence_and_lex_cases() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a_id = symbol_id(&builder, "a");
    let b_id = symbol_id(&builder, "b");
    let a = terms.intern_fun(&symbols, a_id, &[]).expect("a");
    let b = terms.intern_fun(&symbols, b_id, &[]).expect("b");
    let f_id = symbol_id(&builder, "f");
    let g_id = symbol_id(&builder, "g");
    let h = symbol_id(&builder, "h");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let ga = terms.intern_fun(&symbols, g_id, &[a]).expect("g(a)");
    // Precedence case: equal weight, different heads.
    let expected = if g_id > f_id {
        OrderingComparison::Greater
    } else {
        OrderingComparison::Less
    };
    assert_eq!(compare_lpo(&terms, &precedence, ga, fa), Ok(expected));
    // Lexicographic case: same head, first child decides.
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let hba = terms.intern_fun(&symbols, h, &[b, a]).expect("h(b, a)");
    let lex_expected = if b_id > a_id {
        OrderingComparison::Less
    } else {
        OrderingComparison::Greater
    };
    assert_eq!(compare_lpo(&terms, &precedence, hab, hba), Ok(lex_expected));
}

// CEP:WHAT: Verifies LPO is total on ground terms under the total default precedence.
// CEP:WHY: Spec 03 Theorem 3.4.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any Incomparable ground pair.
// CEP:ASSUMES: ground terms.
// CEP:COST: quadratic in the term set.
// CEP:EVIDENCE: cited by hot/ordering/lpo.rs compare_lpo.
// CEP:SECURITY: none.
#[test]
fn lpo_ground_totality() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let f = symbol_id(&builder, "f");
    let g = symbol_id(&builder, "g");
    let h = symbol_id(&builder, "h");
    let fa = terms.intern_fun(&symbols, f, &[a]).expect("f(a)");
    let fb = terms.intern_fun(&symbols, f, &[b]).expect("f(b)");
    let ga = terms.intern_fun(&symbols, g, &[a]).expect("g(a)");
    let gb = terms.intern_fun(&symbols, g, &[b]).expect("g(b)");
    let haa = terms.intern_fun(&symbols, h, &[a, a]).expect("h(a, a)");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    let ground = [a, b, fa, fb, ga, gb, haa, hab];
    for left in ground.iter() {
        for right in ground.iter() {
            let outcome = compare_lpo(&terms, &precedence, *left, *right);
            assert_ne!(
                outcome,
                Ok(OrderingComparison::Incomparable),
                "LPO must be total on ground terms"
            );
        }
    }
}

// CEP:WHAT: Verifies the KBO subterm property on ground terms.
// CEP:WHY: Spec 03 Theorem 2.3: KBO with weights >= 1 is a simplification order.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a compound is not above its subterm.
// CEP:ASSUMES: ground terms.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs compare_kbo.
// CEP:SECURITY: none.
#[test]
fn kbo_subterm_property() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let h = symbol_id(&builder, "h");
    let hab = terms.intern_fun(&symbols, h, &[a, b]).expect("h(a, b)");
    assert_eq!(
        compare_kbo(&terms, &precedence, hab, a),
        Ok(OrderingComparison::Greater)
    );
    assert_eq!(
        compare_kbo(&terms, &precedence, hab, b),
        Ok(OrderingComparison::Greater)
    );
}

// CEP:WHAT: Verifies unreadable term handles surface as errors, not panics.
// CEP:WHY: Law 6: structural failures are loud.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a panic.
// CEP:ASSUMES: forged offsets.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/kbo.rs map_term_error.
// CEP:SECURITY: forged-handle rejection.
#[test]
fn invalid_terms_rejected() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let forged = mapt::hot::ir::term::TermPtr::from_verified_offset(u32::MAX - 4);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    assert_eq!(
        compare_kbo(&terms, &precedence, forged, a),
        Err(OrderingError::InvalidPointer)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, forged, a),
        Err(OrderingError::InvalidPointer)
    );
}

// CEP:WHAT: Verifies Application-headed terms are rejected as unsupported by both orderings.
// CEP:WHY: Higher-order heads are Phase 5 scope (ticket CEP-1033); comparing them must fail loudly (Law 6) instead of aliasing the reserved symbol field onto a real symbol.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an Application head is compared or panics.
// CEP:ASSUMES: intern_app constructs the higher-order application.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/mod.rs OrderingError.
// CEP:SECURITY: reserved-symbol aliasing prevention.
#[test]
fn unsupported_heads_rejected() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let app = terms.intern_app(&symbols, a, a).expect("App(a, a)");
    assert_eq!(
        compare_kbo(&terms, &precedence, app, a),
        Err(OrderingError::UnsupportedHead)
    );
    assert_eq!(
        compare_lpo(&terms, &precedence, app, a),
        Err(OrderingError::UnsupportedHead)
    );
    assert_eq!(
        compare_kbo(&terms, &precedence, a, app),
        Err(OrderingError::UnsupportedHead)
    );
}

// CEP:WHAT: Verifies the equality pseudo-entry is distinct from symbol zero and maximal in the default policy.
// CEP:WHY: Equality atoms carry reserved symbol zero; the dedicated trailing slot must never alias symbol zero's rank (design 5.1, hot/ordering/precedence.rs).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the pseudo-rank equals any symbol rank in the default policy.
// CEP:ASSUMES: ID-order default policy.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ordering/precedence.rs file header.
// CEP:SECURITY: pseudo-symbol aliasing prevention.
#[test]
fn equality_pseudo_entry() {
    let (arena, _symbols, builder, _terms, _clauses) = make_term_fixture();
    let precedence = default_precedence(arena, &builder);
    let equality_rank = precedence.equality_rank();
    for id in 0..builder.symbol_count() {
        assert_ne!(
            precedence.rank(id),
            Ok(equality_rank),
            "the equality pseudo-rank must not alias symbol {}",
            id
        );
    }
    assert_eq!(equality_rank, builder.symbol_count());
}
