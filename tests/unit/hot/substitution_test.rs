// CEP:FILE: tests/unit/hot/substitution_test.rs
// CEP:WHAT: Unit tests for the substitution engine: binding discipline, trail undo, application, cycle rejection, and record round trips.
// CEP:WHY: CEP&CC 32.8: the substitution engine is the OPT-0 storage Phase 2 unification drives.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/unification/substitution.rs.
// CEP:SECURITY: variable bounds and cyclic bindings are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::unification::substitution::{Substitution, SubstitutionError, SubstitutionRecord};
use mapt_config::limits::{kInvalidSubstitutionOffset, kMaxVariablesPerClause};

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

// CEP:WHAT: Verifies the initial state is fully unbound.
// CEP:WHY: No uninitialized reads (CEP&CC 22.4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any phantom binding.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs new.
// CEP:SECURITY: none.
#[test]
fn initial_state_is_unbound() {
    let (arena, _symbols, _builder, _terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    for variable in 0..kMaxVariablesPerClause {
        assert_eq!(substitution.lookup(variable), Ok(None));
    }
    assert_eq!(substitution.trail_depth(), 0);
}

// CEP:WHAT: Verifies bind and lookup.
// CEP:WHY: The hottest substitution operations.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on lookup mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs bind/lookup.
// CEP:SECURITY: none.
#[test]
fn lookup_after_bind() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    substitution.bind(0, a).expect("bind");
    assert_eq!(substitution.lookup(0), Ok(Some(a)));
    assert_eq!(substitution.is_bound(0), Ok(true));
    assert_eq!(substitution.lookup(1), Ok(None));
    assert_eq!(substitution.trail_depth(), 1);
    assert_eq!(
        substitution.bind(kMaxVariablesPerClause, a),
        Err(SubstitutionError::VariableOutOfRange),
        "variable bound must be enforced"
    );
}

// CEP:WHAT: Verifies double binding is refused.
// CEP:WHY: The bind/undo discipline must be explicit.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if rebinding succeeds.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs bind.
// CEP:SECURITY: none.
#[test]
fn double_bind_refused() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    substitution.bind(0, a).expect("first bind");
    assert_eq!(
        substitution.bind(0, b),
        Err(SubstitutionError::VariableOutOfRange),
        "rebinding without undo must be refused"
    );
}

// CEP:WHAT: Verifies trail undo restores state.
// CEP:WHY: Backtracking correctness (design 8.2).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on stale bindings after undo.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs undo_to.
// CEP:SECURITY: none.
#[test]
fn trail_undo_restores_state() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    substitution.bind(0, a).expect("bind 0");
    let save = substitution.trail_depth();
    substitution.bind(1, b).expect("bind 1");
    assert_eq!(substitution.lookup(1), Ok(Some(b)));
    substitution.undo_to(save);
    assert_eq!(
        substitution.lookup(1),
        Ok(None),
        "undo must clear the later binding"
    );
    assert_eq!(
        substitution.lookup(0),
        Ok(Some(a)),
        "undo must keep earlier bindings"
    );
    substitution.bind(1, a).expect("rebind after undo is legal");
    substitution.undo_to(0);
    assert_eq!(substitution.lookup(0), Ok(None));
}

// CEP:WHAT: Verifies application replaces variables and re-interns results.
// CEP:WHY: Application semantics (design 5.5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on wrong result structure.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs apply.
// CEP:SECURITY: none.
#[test]
fn apply_replaces_variables() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let var = terms.intern_var(0).expect("V0");
    let fvar = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V0)");
    substitution.bind(0, a).expect("bind V0 -> a");
    let applied = substitution.apply(&terms, fvar, &symbols).expect("apply");
    let expected = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    assert_eq!(applied, expected, "f(V0) under V0->a must be f(a)");
    let unbound = terms.intern_var(1).expect("V1");
    assert_eq!(
        substitution.apply(&terms, unbound, &symbols),
        Ok(unbound),
        "unbound variables map to themselves"
    );
}

// CEP:WHAT: Verifies application is the identity on ground terms.
// CEP:WHY: No spaneous re-interning of untouched terms.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on identity violation.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs apply.
// CEP:SECURITY: none.
#[test]
fn apply_idempotent_on_ground_terms() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    assert_eq!(substitution.apply(&terms, fa, &symbols), Ok(fa));
}

// CEP:WHAT: Verifies cyclic bindings are rejected by the depth guard.
// CEP:WHY: A cycle x -> f(y), y -> x would recurse without the guard (CEP&CC 22.10 unbounded recursion ban).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a cycle hangs or succeeds.
// CEP:ASSUMES: none.
// CEP:COST: bounded by kMaxUnificationDepth.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs apply_bounded.
// CEP:SECURITY: recursion bound.
#[test]
fn cyclic_binding_rejected() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let f_id = symbol_id(&builder, "f");
    let x = terms.intern_var(0).expect("V0");
    let y = terms.intern_var(1).expect("V1");
    let f_y = terms.intern_fun(&symbols, f_id, &[y]).expect("f(V1)");
    substitution.bind(0, f_y).expect("V0 -> f(V1)");
    substitution.bind(1, x).expect("V1 -> V0");
    let result = substitution.apply(&terms, x, &symbols);
    assert!(
        matches!(result, Err(SubstitutionError::DepthExceeded)),
        "cyclic bindings must fail with DepthExceeded, got {:?}",
        result
    );
}

// CEP:WHAT: Verifies materialize and read_record round trips.
// CEP:WHY: Proof records reference substitutions by offset (design 5.4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on round-trip mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs materialize/read_record.
// CEP:SECURITY: none.
#[test]
fn materialize_and_read_back() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    substitution.bind(1, a).expect("bind 1");
    substitution.bind(4, b).expect("bind 4");
    let offset = substitution.materialize().expect("materialize");
    let (header, pairs) = substitution.read_record(offset).expect("read back");
    assert_eq!(header.binding_count, 2);
    assert_eq!(pairs.len(), 2);
    assert_eq!(pairs[0].variable, 1);
    assert_eq!(pairs[0].term_offset, a.as_u32());
    assert_eq!(pairs[1].variable, 4);
    assert_eq!(pairs[1].term_offset, b.as_u32());
    assert!(
        matches!(
            substitution.read_record(kInvalidSubstitutionOffset),
            Err(SubstitutionError::InvalidSubstitution)
        ),
        "the sentinel offset must be rejected"
    );
}

// CEP:WHAT: Pins the record layout.
// CEP:WHY: Layout drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on drift.
// CEP:ASSUMES: target ABI.
// CEP:COST: compile-time.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs.
// CEP:SECURITY: none.
#[test]
fn record_layout() {
    assert_eq!(core::mem::size_of::<SubstitutionRecord>(), 8);
    assert_eq!(
        core::mem::size_of::<mapt::hot::unification::substitution::SubstitutionBinding>(),
        8
    );
}

// CEP:WHAT: Verifies invalid term references are refused.
// CEP:WHY: Defense in depth for corrupted handles.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if garbage offsets are accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/unification/substitution.rs map_term_error.
// CEP:SECURITY: invalid pointer handling.
#[test]
fn invalid_term_refused() {
    let (arena, symbols, _builder, terms, _clauses) = make_term_fixture();
    let substitution = Substitution::new(arena);
    let forged = mapt::hot::ir::term::TermPtr::from_verified_offset(u32::MAX - 4);
    let result = substitution.apply(&terms, forged, &symbols);
    assert!(matches!(result, Err(SubstitutionError::InvalidPointer)));
}
