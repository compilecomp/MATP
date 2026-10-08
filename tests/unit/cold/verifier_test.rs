// CEP:FILE: tests/unit/cold/verifier_test.rs
// CEP:WHAT: Unit tests for the full IR verifier: valid IR passes, and each corruption class is detected.
// CEP:WHY: CEP&CC 38.18: the verifier must run in CI and detect every structural violation; this file proves detection by corrupting bytes through the public arena API.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly when a violation is missed.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/verifier.rs.
// CEP:SECURITY: corruption detection is the integrity boundary.

#[path = "../../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::cold::verifier::{
    verify_clause, verify_symbol_table, verify_term_store, VerificationError,
};
use mapt::hot::ir::clause::DerivationStep;
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermStore;
use mapt_config::limits::{kInvalidClauseId, kInvalidSubstitutionOffset};

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

// CEP:WHAT: Verifies a well-formed term store passes with zero violations.
// CEP:WHY: The verifier must not report phantom violations.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any false positive.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_term_store.
// CEP:SECURITY: none.
#[test]
fn valid_term_store_passes() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let var = terms.intern_var(0).expect("var");
    let _ = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let _ = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V0)");
    let _ = terms.intern_eq(&symbols, a, var).expect("a = V0");
    let violations = verify_term_store(arena, &terms, &symbols);
    assert!(
        violations.is_empty(),
        "unexpected violations: {:?}",
        violations
    );
    let table_violations = verify_symbol_table(&symbols);
    assert!(table_violations.is_empty());
}

// CEP:WHAT: Verifies corrupted term metadata is detected.
// CEP:WHY: WrongWeight and NotCanonical must fire when a record is tampered with.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if corruption passes unnoticed.
// CEP:ASSUMES: arena write through the public API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_one_term.
// CEP:SECURITY: corruption detection.
#[test]
fn term_corruption_detected() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let clean = verify_term_store(arena, &terms, &symbols);
    assert!(clean.is_empty());
    // Corrupt the weight word (word 3) of the f(a) record through the public arena API.
    let corrupt_range =
        mapt::hot::memory::arena::ArenaRange::new(fa.as_u32(), fa.as_u32() + 16).expect("range");
    {
        let words = arena.array_mut::<u32>(corrupt_range).expect("mut");
        words[3] = 99;
    }
    let violations = verify_term_store(arena, &terms, &symbols);
    assert!(
        violations.contains(&VerificationError::WrongWeight(fa.as_u32())),
        "weight corruption must be detected, got {:?}",
        violations
    );
}

// CEP:WHAT: Verifies symbol corruption breaks canonicality detection.
// CEP:WHY: Rewriting the symbol word makes the record structurally different from anything the table holds, so the rebuild must land on a different handle.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the corruption passes unnoticed.
// CEP:ASSUMES: arena write through the public API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_one_term.
// CEP:SECURITY: corruption detection.
#[test]
fn symbol_corruption_breaks_canonicality() {
    let (arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let f_id = symbol_id(&builder, "f");
    let g_id = symbol_id(&builder, "g");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let clean = verify_term_store(arena, &terms, &symbols);
    assert!(clean.is_empty());
    // Rewrite the symbol word (word 1) from f to g: same kind, same arity, so the structural
    // checks pass but the rebuild interns g(a), a record at a different offset.
    let corrupt_range =
        mapt::hot::memory::arena::ArenaRange::new(fa.as_u32(), fa.as_u32() + 16).expect("range");
    {
        let words = arena.array_mut::<u32>(corrupt_range).expect("mut");
        words[1] = g_id;
    }
    let violations = verify_term_store(arena, &terms, &symbols);
    assert!(
        violations.contains(&VerificationError::NotCanonical(fa.as_u32())),
        "symbol corruption must break canonicality, got {:?}",
        violations
    );
}

// CEP:WHAT: Verifies valid clauses pass clause verification.
// CEP:WHY: No phantom violations on the clause path.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on false positives.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_clause.
// CEP:SECURITY: none.
#[test]
fn valid_clauses_pass() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let p_id = symbol_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(&symbols, p_id, &[b]).expect("p(b)");
    let ptr = clauses
        .new_clause(
            &terms,
            &[Literal::new(pa, true), Literal::new(pb, false)],
            3,
            input_derivation(),
        )
        .expect("clause");
    let clause = clauses.clause(ptr).expect("read");
    let violations = verify_clause(clause, &clauses, &terms);
    assert!(
        violations.is_empty(),
        "unexpected violations: {:?}",
        violations
    );
}

// CEP:WHAT: Verifies clause weight corruption is detected.
// CEP:WHY: ClauseWrongWeight must fire on tampered headers.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if corruption passes unnoticed.
// CEP:ASSUMES: arena write through the public API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_clause.
// CEP:SECURITY: corruption detection.
#[test]
fn clause_corruption_detected() {
    let (arena, symbols, builder, terms, clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let p_id = symbol_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let ptr = clauses
        .new_clause(&terms, &[Literal::new(pa, true)], 0, input_derivation())
        .expect("clause");
    let clause_id = clauses.clause(ptr).expect("read").id;
    // Corrupt the weight field (offset 12 in the Clause layout) through the public arena API.
    let corrupt_range =
        mapt::hot::memory::arena::ArenaRange::new(ptr.as_u32() + 12, ptr.as_u32() + 16)
            .expect("range");
    {
        let words = arena.array_mut::<u32>(corrupt_range).expect("mut");
        words[0] = 99_999;
    }
    let clause = clauses.clause(ptr).expect("read");
    let violations = verify_clause(clause, &clauses, &terms);
    assert!(
        violations.contains(&VerificationError::ClauseWrongWeight(clause_id.0)),
        "weight corruption must be detected, got {:?}",
        violations
    );
}

// CEP:WHAT: Verifies inline slot tampering is detected.
// CEP:WHY: ClauseInlineSlotDirty must fire when an unused slot holds a live atom.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if tampering passes unnoticed.
// CEP:ASSUMES: arena write through the public API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/verifier.rs verify_clause.
// CEP:SECURITY: corruption detection.
#[test]
fn inline_slot_tampering_detected() {
    let (arena, symbols, builder, terms, clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let p_id = symbol_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(&symbols, p_id, &[b]).expect("p(b)");
    let ptr = clauses
        .new_clause(&terms, &[Literal::new(pa, true)], 0, input_derivation())
        .expect("clause");
    let clause_id = clauses.clause(ptr).expect("read").id;
    // Write a live literal into unused inline slot 7 (offset 84 + 7*8 in the Clause layout).
    let slot_offset = ptr.as_u32() + 84 + 7 * 8;
    let corrupt_range =
        mapt::hot::memory::arena::ArenaRange::new(slot_offset, slot_offset + 8).expect("range");
    {
        let slots = arena.array_mut::<Literal>(corrupt_range).expect("mut");
        slots[0] = Literal::new(pb, true);
    }
    let clause = clauses.clause(ptr).expect("read");
    let violations = verify_clause(clause, &clauses, &terms);
    assert!(
        violations.contains(&VerificationError::ClauseInlineSlotDirty(clause_id.0)),
        "dirty inline slot must be detected, got {:?}",
        violations
    );
}

// CEP:WHAT: Verifies filler atoms fail loudly on dereference.
// CEP:WHY: The invalid-atom sentinel must error, not read garbage.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a filler dereference succeeds.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs default_literal.
// CEP:SECURITY: loud-failure sentinel.
#[test]
fn filler_atoms_fail_loudly() {
    let (_arena, _symbols, _builder, terms, _clauses) = make_term_fixture();
    let forged =
        mapt::hot::ir::term::TermPtr::from_verified_offset(mapt_config::limits::kInvalidTermOffset);
    assert_eq!(
        terms.term(forged),
        Err(mapt::hot::ir::term::TermError::InvalidPointer)
    );
    let _ = TermStore::new;
}

// CEP:WHAT: Builds an input derivation step.
// CEP:WHY: Shared fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: mapt::hot::ir::clause::InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; 4],
        substitution: kInvalidSubstitutionOffset,
    }
}
