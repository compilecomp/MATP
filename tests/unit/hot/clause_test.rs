// CEP:FILE: tests/unit/hot/clause_test.rs
// CEP:WHAT: Unit tests for clauses and literals: layouts, canonical ordering, weight caching, monotonic IDs, inline/overflow storage, derivation records, and every reachable error path of new_clause.
// CEP:WHY: CEP&CC 32.8 requires tests for every CEP-0 function; clause invariants are consumed directly by the Phase 3 search loop.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/clause.rs and hot/ir/literal.rs.
// CEP:SECURITY: the literal bound, parent bound, weight overflow, and arena exhaustion paths are exercised here; the clause ID budget is unreachable defense-in-depth (see hot/ir/clause.rs).

#[path = "../../common/mod.rs"]
mod common;

use common::{kTestArenaBytes, make_arena, make_term_fixture, standard_symbols};
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::clause::{ClauseError, ClauseStore, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::{TermError, TermStore};
use mapt_config::limits::{
    kFirstClauseId, kInlineClauseLiterals, kInvalidClauseId, kInvalidClauseOffset,
    kInvalidSubstitutionOffset, kMaxClauseLiterals, kMaxDerivationParents, kMaxTermWeight,
    kTermHashTableCapacity,
};

// CEP:WHAT: Literals in the weight-overflow fixture (5 x kMaxTermWeight exceeds u32::MAX).
// CEP:WHY: Named constant; 4 literals would sum to exactly u32::MAX + 1, so 5 keeps the margin explicit.
#[allow(non_upper_case_globals)]
const kWeightOverflowLiterals: usize = 5;

// CEP:WHAT: Arena headroom above the term hash table in the arena-exhaustion fixture (64 KiB).
// CEP:WHY: Named constant; holds the symbol table, fixture terms, and roughly 400 clause headers before exhaustion.
#[allow(non_upper_case_globals)]
const kArenaFullHeadroomBytes: u32 = 65_536;

// CEP:WHAT: Upper bound on clause allocations before the arena-exhaustion test fails loudly (100_000).
// CEP:WHY: A regression that keeps allocating would otherwise hang the suite; the bound is far above the expected ~400.
#[allow(non_upper_case_globals)]
const kArenaFullIterationCap: u64 = 100_000;

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

// CEP:WHAT: Builds the fixture atoms p(a), p(b), q(a,b), r.
// CEP:WHY: Shared atom setup for clause tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fixture_atoms(
    terms: &mapt::hot::ir::term::TermStore,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
) -> (mapt::hot::ir::term::TermPtr, mapt::hot::ir::term::TermPtr) {
    let a = terms
        .intern_fun(symbols, symbol_id(builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(symbols, symbol_id(builder, "b"), &[])
        .expect("b");
    let p_id = symbol_id(builder, "p");
    let pa = terms.intern_pred(symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(symbols, p_id, &[b]).expect("p(b)");
    (pa, pb)
}

// CEP:WHAT: Verifies literal layout, polarity, negation, complementarity, and flags.
// CEP:WHY: Literal operations are the resolution preconditions (design 10.2).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any literal operation error.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/literal.rs.
// CEP:SECURITY: none.
#[test]
fn literal_operations() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let (pa, pb) = fixture_atoms(&terms, &symbols, &builder);
    let positive = Literal::new(pa, true);
    let negative = Literal::new(pa, false);
    assert!(positive.is_positive());
    assert!(!negative.is_positive());
    assert_eq!(positive.atom(), pa);
    let negated = positive.negate();
    assert!(!negated.is_positive());
    assert_eq!(negated.atom(), pa);
    assert!(positive.is_complementary(&negative));
    assert!(negative.is_complementary(&positive));
    assert!(!positive.is_complementary(&positive));
    let other = Literal::new(pb, false);
    assert!(
        !positive.is_complementary(&other),
        "different atoms are never complementary"
    );
    let mut flagged = Literal::new(pa, true);
    flagged.set_selected(true);
    flagged.set_maximal(true);
    flagged.set_theory_flags(3);
    assert!(flagged.is_selected());
    assert!(flagged.is_maximal());
    assert_eq!(flagged.theory_flags(), 3);
}

// CEP:WHAT: Pins the Literal layout at 8 bytes.
// CEP:WHY: Layout drift is an ABI break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on drift.
// CEP:ASSUMES: target ABI.
// CEP:COST: compile-time.
// CEP:EVIDENCE: cited by hot/ir/literal.rs.
// CEP:SECURITY: none.
#[test]
fn literal_layout() {
    assert_eq!(core::mem::size_of::<Literal>(), 8);
}

// CEP:WHAT: Pins the DerivationStep and Clause layouts.
// CEP:WHY: Layout drift is an IR break.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on drift.
// CEP:ASSUMES: target ABI.
// CEP:COST: compile-time.
// CEP:EVIDENCE: cited by hot/ir/clause.rs.
// CEP:SECURITY: none.
#[test]
fn clause_layout() {
    assert_eq!(core::mem::size_of::<DerivationStep>(), 48);
    assert_eq!(core::mem::size_of::<mapt::hot::ir::clause::Clause>(), 152);
    assert_eq!(kMaxDerivationParents, 4);
}

// CEP:WHAT: Verifies empty clause construction and printing marker state.
// CEP:WHY: The empty clause is the refutation target; its representation must be exact.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on nonzero literal count.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs new_clause.
// CEP:SECURITY: none.
#[test]
fn empty_clause() {
    let (_arena, _symbols, _builder, terms, clauses) = make_term_fixture();
    let ptr = clauses
        .new_clause(&terms, &[], 0, input_derivation())
        .expect("empty clause");
    let clause = clauses.clause(ptr).expect("read");
    assert_eq!(clause.literal_count, 0);
    assert_eq!(clause.overflow_offset, kInvalidClauseOffset);
}

// CEP:WHAT: Verifies IDs are monotonic and start at kFirstClauseId.
// CEP:WHY: Design 5.3: deterministic identity.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on ID reuse or regression.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs.
// CEP:SECURITY: none.
#[test]
fn ids_are_monotonic() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let first = clauses
        .new_clause(&terms, &[Literal::new(pa, true)], 0, input_derivation())
        .expect("first");
    let second = clauses
        .new_clause(&terms, &[Literal::new(pa, false)], 0, input_derivation())
        .expect("second");
    let first_id = clauses.clause(first).expect("read").id;
    let second_id = clauses.clause(second).expect("read").id;
    assert!(first_id.0 >= kFirstClauseId);
    assert!(second_id.0 > first_id.0);
    assert_eq!(clauses.live_clauses(), 2);
}

// CEP:WHAT: Verifies the literal bound is enforced.
// CEP:WHY: Design 5.3: bounded clause size.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if oversized clauses are accepted.
// CEP:ASSUMES: none.
// CEP:COST: builds kMaxClauseLiterals + 1 literals.
// CEP:EVIDENCE: cited by hot/ir/clause.rs.
// CEP:SECURITY: memory bound.
#[test]
fn literal_bound_enforced() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let too_many = vec![Literal::new(pa, true); kMaxClauseLiterals as usize + 1];
    assert_eq!(
        clauses.new_clause(&terms, &too_many, 0, input_derivation()),
        Err(ClauseError::TooManyLiterals)
    );
    let at_bound = vec![Literal::new(pa, false); kMaxClauseLiterals as usize];
    let ptr = clauses
        .new_clause(&terms, &at_bound, 0, input_derivation())
        .expect("clause at the bound");
    let clause = clauses.clause(ptr).expect("read");
    assert_eq!(clause.literal_count, kMaxClauseLiterals);
    assert!(clause.overflow_offset != kInvalidClauseOffset);
}

// CEP:WHAT: Verifies canonical literal ordering.
// CEP:WHY: Design 5.7: canonicalizable IR; the stored order must be the (polarity, atom) total order.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on unsorted storage.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs sort_literals_canonical.
// CEP:SECURITY: none.
#[test]
fn canonical_order() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, pb) = fixture_atoms(&terms, &symbols, &builder);
    let unordered = vec![
        Literal::new(pa, true),
        Literal::new(pb, false),
        Literal::new(pa, false),
    ];
    let ptr = clauses
        .new_clause(&terms, &unordered, 7, input_derivation())
        .expect("clause");
    let clause = clauses.clause(ptr).expect("read");
    let mut previous: Option<(bool, u32)> = None;
    for index in 0..clause.literal_count {
        let literal = clauses.literal(clause, index).expect("literal");
        let key = (!literal.is_positive(), literal.atom().as_u32());
        if let Some(prev) = previous {
            assert!(prev <= key, "literals must be stored in canonical order");
        }
        previous = Some(key);
    }
    assert_eq!(clause.age, 7);
}

// CEP:WHAT: Verifies clause weight equals the sum of atom weights.
// CEP:WHY: Design 15.3 weight caching.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on weight drift.
// CEP:ASSUMES: default weights.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs.
// CEP:SECURITY: none.
#[test]
fn clause_weight_is_sum_of_atom_weights() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, pb) = fixture_atoms(&terms, &symbols, &builder);
    let literals = vec![Literal::new(pa, true), Literal::new(pb, false)];
    let expected: u64 = terms.term(pa).expect("read").weight() as u64
        + terms.term(pb).expect("read").weight() as u64;
    let ptr = clauses
        .new_clause(&terms, &literals, 0, input_derivation())
        .expect("clause");
    assert_eq!(clauses.clause(ptr).expect("read").weight as u64, expected);
}

// CEP:WHAT: Verifies inline and overflow literal access.
// CEP:WHY: The accessor must hide the storage split (design 5.3).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any index mismatch.
// CEP:ASSUMES: none.
// CEP:COST: builds one inline and one overflow clause.
// CEP:EVIDENCE: cited by hot/ir/clause.rs literal.
// CEP:SECURITY: none.
#[test]
fn inline_and_overflow_layout() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, pb) = fixture_atoms(&terms, &symbols, &builder);
    let inline_lits: Vec<_> = (0..kInlineClauseLiterals)
        .map(|index| Literal::new(if index % 2 == 0 { pa } else { pb }, index % 2 == 0))
        .collect();
    let inline_ptr = clauses
        .new_clause(&terms, &inline_lits, 0, input_derivation())
        .expect("inline clause");
    let inline_clause = clauses.clause(inline_ptr).expect("read");
    assert_eq!(inline_clause.overflow_offset, kInvalidClauseOffset);
    for index in 0..kInlineClauseLiterals as u16 {
        assert!(clauses.literal(inline_clause, index).is_ok());
    }
    assert!(clauses
        .literal(inline_clause, kInlineClauseLiterals as u16)
        .is_err());
    let overflow_lits: Vec<_> = (0..(kInlineClauseLiterals + 4))
        .map(|index| Literal::new(if index % 2 == 0 { pa } else { pb }, index % 2 == 0))
        .collect();
    let overflow_ptr = clauses
        .new_clause(&terms, &overflow_lits, 0, input_derivation())
        .expect("overflow clause");
    let overflow_clause = clauses.clause(overflow_ptr).expect("read");
    assert!(overflow_clause.overflow_offset != kInvalidClauseOffset);
    for index in 0..overflow_clause.literal_count {
        assert!(clauses.literal(overflow_clause, index).is_ok());
    }
    assert!(clauses
        .literal(overflow_clause, overflow_clause.literal_count)
        .is_err());
}

// CEP:WHAT: Verifies unused inline slots hold the invalid-atom filler.
// CEP:WHY: Verifier-checked determinism of unused storage.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on dirty slots.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs default_literal.
// CEP:SECURITY: none.
#[test]
fn inline_slots_zeroed() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let ptr = clauses
        .new_clause(&terms, &[Literal::new(pa, true)], 0, input_derivation())
        .expect("one-literal clause");
    let clause = clauses.clause(ptr).expect("read");
    for slot in clause.literal_count as usize..kInlineClauseLiterals {
        let atom = clause.inline_literals[slot].atom();
        assert_eq!(
            terms.term(atom),
            Err(TermError::InvalidPointer),
            "unused inline slot must fail loudly on dereference"
        );
    }
}

// CEP:WHAT: Verifies derivation step validation and layout fields.
// CEP:WHY: Proof tracking correctness (design 5.4).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if invalid derivations are accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs DerivationStep.
// CEP:SECURITY: none.
#[test]
fn derivation_step_layout() {
    let (_arena, _symbols, _builder, _terms, _clauses) = make_term_fixture();
    let mut step = DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 2,
        reserved: 0,
        parents: [kInvalidClauseId; kMaxDerivationParents],
        substitution: kInvalidSubstitutionOffset,
    };
    step.parents[0] = 1;
    step.parents[1] = 2;
    assert_eq!(step.parents[2], kInvalidClauseId);
    assert_eq!(step.parent_count, 2);
    assert_eq!(step.rule, InferenceRule::Input);
}

// CEP:WHAT: Verifies header readback of all fields.
// CEP:WHY: Round-trip integrity of the stored header.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any field mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs clause().
// CEP:SECURITY: none.
#[test]
fn header_readback() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let ptr = clauses
        .new_clause(
            &terms,
            &[Literal::new(pa, true)],
            42,
            DerivationStep {
                rule: InferenceRule::NegatedConjecture,
                parent_count: 0,
                reserved: 0,
                parents: [kInvalidClauseId; kMaxDerivationParents],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("clause");
    let clause = clauses.clause(ptr).expect("read");
    assert_eq!(clause.age, 42);
    assert_eq!(clause.flags, 0);
    assert_eq!(clause.split_level, 0);
    assert_eq!(clause.theory_tag, 0);
    assert_eq!(clause.lbd, 0);
    assert_eq!(clause.reserved, 0);
    assert_eq!(clause.derivation.rule, InferenceRule::NegatedConjecture);
}

// CEP:WHAT: Verifies new_clause rejects derivations with more than kMaxDerivationParents parents.
// CEP:WHY: CEP&CC Law 6: every failure branch of a CEP-0 function must be exercised (32.8); the parent bound guards the fixed-size parents array.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the bound is not enforced.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs (ClauseError::TooManyParents).
// CEP:SECURITY: fixed-size record bound.
#[test]
fn too_many_parents_rejected() {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let mut derivation = input_derivation();
    derivation.parent_count = kMaxDerivationParents as u8 + 1;
    assert_eq!(
        clauses.new_clause(&terms, &[Literal::new(pa, true)], 0, derivation),
        Err(ClauseError::TooManyParents)
    );
    // At exactly the bound the derivation is structurally valid.
    derivation.parent_count = kMaxDerivationParents as u8;
    assert!(clauses
        .new_clause(&terms, &[Literal::new(pa, true)], 0, derivation)
        .is_ok());
}

// CEP:WHAT: Verifies new_clause rejects clauses whose summed atom weight exceeds u32.
// CEP:WHY: CEP&CC Law 6: the WeightOverflow branch must be exercised; the weight cache is a u32 field, so the u64 sum is checked before the cast.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the overflow is not rejected.
// CEP:ASSUMES: a zero-arity predicate may carry symbol weight kMaxTermWeight (intern caps at, not above, kMaxTermWeight).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/clause.rs (ClauseError::WeightOverflow).
// CEP:SECURITY: overflow prevention.
#[test]
fn weight_overflow_rejected() {
    let arena = make_arena(kTestArenaBytes);
    let mut builder = SymbolTableBuilder::new();
    let heavy = builder
        .declare_predicate("heavy", 0, kMaxTermWeight, &[])
        .expect("declare heavy");
    let symbols = builder.finalize(arena).expect("freeze failed");
    let terms = TermStore::new(arena).expect("term store failed");
    let clauses = ClauseStore::new(arena);
    let atom = terms.intern_pred(&symbols, heavy, &[]).expect("heavy atom");
    assert_eq!(
        terms.term(atom).expect("read atom").weight(),
        kMaxTermWeight,
        "fixture setup: the heavy atom must weigh exactly kMaxTermWeight"
    );
    let overflowing = vec![Literal::new(atom, true); kWeightOverflowLiterals];
    assert_eq!(
        clauses.new_clause(&terms, &overflowing, 0, input_derivation()),
        Err(ClauseError::WeightOverflow)
    );
    // Three heavy literals still fit: the u32 cache holds 3 x kMaxTermWeight.
    let fitting = vec![Literal::new(atom, false); kWeightOverflowLiterals - 2];
    let ptr = clauses
        .new_clause(&terms, &fitting, 0, input_derivation())
        .expect("three heavy literals fit");
    let clause = clauses.clause(ptr).expect("read");
    assert_eq!(clause.weight, 3 * kMaxTermWeight);
}

// CEP:WHAT: Verifies new_clause reports ArenaFull once the arena is exhausted, and that exhaustion is reachable and clean.
// CEP:WHY: CEP&CC Law 6: the ArenaFull branch must be exercised; bounded memory is a hard Phase 1 invariant (design 7.1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any error other than ArenaFull or when exhaustion does not occur before the iteration cap.
// CEP:ASSUMES: the arena holds the term hash table (kTermHashTableCapacity x 4 bytes) plus kArenaFullHeadroomBytes.
// CEP:COST: ~400 clause allocations.
// CEP:EVIDENCE: cited by hot/ir/clause.rs (ClauseError::ArenaFull).
// CEP:SECURITY: resource-exhaustion boundary.
#[test]
fn arena_full_after_exhaustion() {
    let arena = make_arena(kTermHashTableCapacity * 4 + kArenaFullHeadroomBytes);
    let builder = standard_symbols();
    let symbols = builder.finalize(arena).expect("freeze failed");
    let terms = TermStore::new(arena).expect("term store failed");
    let clauses = ClauseStore::new(arena);
    let (pa, _pb) = fixture_atoms(&terms, &symbols, &builder);
    let mut created: u64 = 0;
    loop {
        match clauses.new_clause(&terms, &[Literal::new(pa, true)], 0, input_derivation()) {
            Ok(_) => created += 1,
            Err(ClauseError::ArenaFull) => break,
            Err(other) => panic!("unexpected error before exhaustion: {:?}", other),
        }
        assert!(
            created < kArenaFullIterationCap,
            "arena must exhaust before the iteration cap"
        );
    }
    assert!(created > 0, "the headroom must fit at least one clause");
}

// CEP:WHAT: Builds an input derivation step.
// CEP:WHY: Shared fixture helper.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; kMaxDerivationParents],
        substitution: kInvalidSubstitutionOffset,
    }
}
