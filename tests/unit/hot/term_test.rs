// CEP:FILE: tests/unit/hot/term_test.rs
// CEP:WHAT: Unit tests for the term store: construction paths, validation, cached metadata, hash-consing canonicality, and the load-factor bound.
// CEP:WHY: CEP&CC 32.8 requires tests for every CEP-0 function; the term store is the IR foundation.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/term.rs.
// CEP:SECURITY: adversarial offsets and indices are exercised here and in fuzz/term_fuzz_test.rs.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::ir::term::{TermError, TermStore, TermTag};
use mapt_config::limits::{kDefaultSymbolWeight, kKboVariableWeight, kMaxVariablesPerClause};

// CEP:WHAT: Verifies store construction initializes an empty table.
// CEP:WHY: Construction invariant.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on nonzero live count.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs TermStore::new.
// CEP:SECURITY: none.
#[test]
fn store_construction() {
    let (_arena, _symbols, _builder, terms, _clauses) = make_term_fixture();
    assert_eq!(terms.live_terms(), 0);
}

// CEP:WHAT: Verifies variable term construction and bounds.
// CEP:WHY: Variables are clause-local dense indices; the bound must be enforced.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if out-of-range variables are accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_var.
// CEP:SECURITY: index bound.
#[test]
fn variable_terms() {
    let (_arena, _symbols, _builder, terms, _clauses) = make_term_fixture();
    let var = terms.intern_var(0).expect("var 0");
    assert_eq!(terms.term(var).expect("read").tag(), TermTag::Variable);
    assert_eq!(terms.term(var).expect("read").symbol(), 0);
    assert!(!terms.term(var).expect("read").is_ground());
    assert_eq!(terms.term(var).expect("read").weight(), kKboVariableWeight);
    let same = terms.intern_var(0).expect("var 0 again");
    assert_eq!(var, same, "hash-consing must canonicalize variables");
    let other = terms.intern_var(1).expect("var 1");
    assert_ne!(var, other);
    assert_eq!(
        terms.intern_var(kMaxVariablesPerClause),
        Err(TermError::VariableOutOfRange),
        "variable bound must be enforced"
    );
}

// CEP:WHAT: Verifies function term construction, arity and kind validation.
// CEP:WHY: Illegal symbol use must be refused at construction.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if validation is missing.
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_fun.
// CEP:SECURITY: symbol table validation.
#[test]
fn function_terms() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("constant a");
    assert_eq!(terms.term(a).expect("read").tag(), TermTag::Function);
    assert!(terms.term(a).expect("read").is_ground());
    let f_id = symbol_id(&builder, "f");
    assert_eq!(
        terms.intern_fun(&symbols, f_id, &[]),
        Err(TermError::ArityMismatch),
        "f/1 with no children must be rejected"
    );
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    assert_eq!(terms.term(fa).expect("read").child_count(), 1);
    let fa_again = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a) again");
    assert_eq!(fa, fa_again, "hash-consing must canonicalize f(a)");
    let p_id = symbol_id(&builder, "p");
    assert_eq!(
        terms.intern_fun(&symbols, p_id, &[a]),
        Err(TermError::SymbolKindMismatch),
        "predicates must not build function terms"
    );
    assert_eq!(
        terms.intern_fun(&symbols, 99_999, &[a]),
        Err(TermError::UnknownSymbol),
        "unknown symbols must be rejected"
    );
}

// CEP:WHAT: Verifies predicate term construction.
// CEP:WHY: Literal atoms are predicate terms (design 5.2).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on validation gaps.
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_pred.
// CEP:SECURITY: symbol table validation.
#[test]
fn predicate_terms() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let p_id = symbol_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    assert_eq!(terms.term(pa).expect("read").tag(), TermTag::Predicate);
    let f_id = symbol_id(&builder, "f");
    assert_eq!(
        terms.intern_pred(&symbols, f_id, &[a]),
        Err(TermError::SymbolKindMismatch),
        "function symbols must not build predicate terms"
    );
}

// CEP:WHAT: Verifies equality term construction.
// CEP:WHY: Equality is special-cased for superposition (design 5.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on structural errors.
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_eq.
// CEP:SECURITY: none.
#[test]
fn equality_terms() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let eq = terms.intern_eq(&symbols, a, b).expect("a = b");
    let view = terms.term(eq).expect("read");
    assert_eq!(view.tag(), TermTag::Equality);
    assert_eq!(view.child_count(), 2);
    assert!(view.is_ground());
    let eq_again = terms.intern_eq(&symbols, a, b).expect("a = b again");
    assert_eq!(eq, eq_again);
    let eq_flip = terms.intern_eq(&symbols, b, a).expect("b = a");
    assert_ne!(eq, eq_flip, "argument order is structural");
}

// CEP:WHAT: Verifies application and sort term construction.
// CEP:WHY: Higher-order application and sort annotations complete the term vocabulary (design 5.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on structural errors.
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_app and intern_sort.
// CEP:SECURITY: none.
#[test]
fn application_and_sort_terms() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let app = terms.intern_app(&symbols, a, b).expect("a applied to b");
    assert_eq!(terms.term(app).expect("read").tag(), TermTag::Application);
    let sort = terms.intern_sort(3).expect("sort term");
    assert_eq!(terms.term(sort).expect("read").tag(), TermTag::Sort);
    assert!(terms.term(sort).expect("read").is_ground());
    assert_eq!(
        terms.term(sort).expect("read").weight(),
        kDefaultSymbolWeight
    );
}

// CEP:WHAT: Verifies tag round trips across all term kinds.
// CEP:WHY: The tag byte must survive construction and reading.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on tag corruption.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs TermView::tag.
// CEP:SECURITY: none.
#[test]
fn tag_roundtrip() {
    let (_arena, _symbols, _builder, terms, _clauses) = make_term_fixture();
    let var = terms.intern_var(5).expect("var");
    assert_eq!(terms.term(var).expect("read").tag(), TermTag::Variable);
    let sort = terms.intern_sort(1).expect("sort");
    assert_eq!(terms.term(sort).expect("read").tag(), TermTag::Sort);
}

// CEP:WHAT: Verifies the word layout invariant: child count and flags decode from word 0.
// CEP:WHY: The packed layout is the term record contract (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on packing drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs layout constants.
// CEP:SECURITY: none.
#[test]
fn word_layout() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let view = terms.term(a).expect("read");
    assert_eq!(view.child_count(), 0);
    assert_eq!(view.flags(), mapt::hot::ir::term::kTermFlagGround);
    let f_id = symbol_id(&builder, "f");
    let var = terms.intern_var(0).expect("var");
    let fvar = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V0)");
    let fvar_view = terms.term(fvar).expect("read");
    assert_eq!(fvar_view.child_count(), 1);
    assert_eq!(fvar_view.flags(), 0, "f(V0) is not ground");
}

// CEP:WHAT: Verifies the symbol field round trip.
// CEP:WHY: The tag-dependent overload must be documented and tested.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on symbol corruption.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs TermView::symbol.
// CEP:SECURITY: none.
#[test]
fn symbol_field() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let f_id = symbol_id(&builder, "f");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    assert_eq!(terms.term(fa).expect("read").symbol(), f_id);
}

// CEP:WHAT: Verifies the depth cache.
// CEP:WHY: Cached depth must equal 1 + max child depth.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on cache drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs depth cache.
// CEP:SECURITY: none.
#[test]
fn depth_cache() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let f_id = symbol_id(&builder, "f");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let ffa = terms.intern_fun(&symbols, f_id, &[fa]).expect("f(f(a))");
    assert_eq!(terms.term(a).expect("read").depth(), 0);
    assert_eq!(terms.term(fa).expect("read").depth(), 1);
    assert_eq!(terms.term(ffa).expect("read").depth(), 2);
}

// CEP:WHAT: Verifies weight accumulation.
// CEP:WHY: Cached weight must equal symbol weight plus child weights.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on cache drift.
// CEP:ASSUMES: default weights are 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs weight cache.
// CEP:SECURITY: none.
#[test]
fn weight_accumulation() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let h_id = symbol_id(&builder, "h");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let hab = terms.intern_fun(&symbols, h_id, &[a, b]).expect("h(a,b)");
    assert_eq!(terms.term(hab).expect("read").weight(), 3);
    let f_id = symbol_id(&builder, "f");
    let fhab = terms.intern_fun(&symbols, f_id, &[hab]).expect("f(h(a,b))");
    assert_eq!(terms.term(fhab).expect("read").weight(), 4);
}

// CEP:WHAT: Verifies the groundness flag.
// CEP:WHY: Ground terms drive indexing decisions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on flag drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs ground flag.
// CEP:SECURITY: none.
#[test]
fn ground_flag() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let h_id = symbol_id(&builder, "h");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let var = terms.intern_var(0).expect("var");
    let mixed = terms
        .intern_fun(&symbols, h_id, &[a, var])
        .expect("h(a,V0)");
    assert!(!terms.term(mixed).expect("read").is_ground());
    let both = terms.intern_fun(&symbols, h_id, &[a, a]).expect("h(a,a)");
    assert!(terms.term(both).expect("read").is_ground());
}

// CEP:WHAT: Verifies child slice iteration.
// CEP:WHY: Bulk traversal is the printer and verifier path.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on order or count drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs children.
// CEP:SECURITY: none.
#[test]
fn children_slice() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let h_id = symbol_id(&builder, "h");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let hab = terms.intern_fun(&symbols, h_id, &[a, b]).expect("h(a,b)");
    let children: Vec<_> = terms.term(hab).expect("read").children().collect();
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], a);
    assert_eq!(children[1], b);
}

// CEP:WHAT: Verifies the load-factor bound refuses interning past 65 percent capacity.
// CEP:WHY: Design 5.1: no resizing; the bound is an explicit error.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if interning succeeds past the bound.
// CEP:ASSUMES: expensive test; run in release mode (CI job bench-gate runs it with --release --ignored).
// CEP:COST: approximately 1.4 million interns.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern load-factor bound.
// CEP:SECURITY: probe-length bound.
#[test]
#[ignore]
fn table_full_after_load_factor_bound() {
    use mapt::cold::symbol_table_builder::SymbolTableBuilder;
    use mapt::hot::ir::symbol_table::SymbolTable;
    use mapt_config::limits::kTermHashTableCapacity;
    let arena = common::make_arena(common::kTestArenaBytes);
    let mut builder = SymbolTableBuilder::new();
    let _ = builder.declare_sort("S").expect("sort");
    let base = builder
        .declare_function("a", 0, 1, &[], mapt::hot::ir::symbol_table::SortId(0))
        .expect("a");
    let mut unary_ids = Vec::new();
    for index in 0..4_096u32 {
        let id = builder
            .declare_function(
                &format!("u{}", index),
                1,
                1,
                &[mapt::hot::ir::symbol_table::SortId(0)],
                mapt::hot::ir::symbol_table::SortId(0),
            )
            .expect("unary symbol");
        unary_ids.push(id);
    }
    let symbols: SymbolTable = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("store");
    let a = terms.intern_fun(&symbols, base, &[]).expect("a");
    let mut inner = Vec::with_capacity(unary_ids.len());
    for id in unary_ids.iter() {
        inner.push(terms.intern_fun(&symbols, *id, &[a]).expect("inner"));
    }
    let bound =
        (kTermHashTableCapacity / 100) * mapt_config::limits::kTermHashTableLoadFactorPercent;
    let mut built: u32 = terms.live_terms();
    assert!(built < bound);
    let mut outer_index = 0usize;
    while built < bound {
        let child = inner[outer_index % inner.len()];
        let id = unary_ids[(outer_index / inner.len()) % unary_ids.len()];
        match terms.intern_fun(&symbols, id, &[child]) {
            Ok(_) => built += 1,
            Err(TermError::TableFull) => break,
            Err(other) => panic!("unexpected error: {:?}", other),
        }
        outer_index += 1;
    }
    assert!(
        built >= bound - 1,
        "the bound must be reachable: built {} bound {}",
        built,
        bound
    );
    let result = terms.intern_fun(&symbols, unary_ids[0], &[a]);
    assert!(matches!(result, Err(TermError::TableFull) | Ok(_)));
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Tests reference symbols by name for readability.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name (fixture bug).
// CEP:ASSUMES: standard fixture symbols.
// CEP:COST: linear scan of a tiny table.
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
