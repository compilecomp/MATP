// CEP:FILE: tests/unit/hot/induction_test.rs
// CEP:WHAT: Unit tests of automated induction: declaration validation (kind and arity rejections, skolem-occurrence), the input-signature scan (node budget, unary-predicate collection, non-unary filtering), the exact clausal shapes of both schemes pinned against the hand clausification of Spec 15 sections 3-4, the attempts budget, the passive-set entry, and the flagship end-to-end refutation of an inductive theorem that the plain saturation cannot prove.
// CEP:WHY: CEP&CC 34.3 and design 26 (revised build order Phase 4): induction schemes are theory axioms - the highest-trust clauses the prover can add - so every shape, bound, and rejection path is pinned executably before the property tests generalize; the flagship test (p(zero), p(x) -> p(succ(x)) |= forall x. p(x)) is the minimal problem whose proof REQUIRES the induction scheme, which is the feature's reason to exist.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the Nat-shaped fixture vocabulary (zero/succ/sk constructors, p/q unary predicates, lt binary predicate, r propositional, a constant).
// CEP:COST: offline.
// CEP:EVIDENCE: this file is the evidence cited by hot/induction/mod.rs and hot/induction/scheme.rs.
// CEP:SECURITY: the validation and budget tests exercise the soundness boundary.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::induction::{
    add_induction_schemes, validate_declaration, InductionDeclaration, InductionError,
};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};
use mapt_config::limits::{kFirstClauseId, kInductionScanNodeBudget, kMaxInductionAttempts};

// CEP:WHAT: Arena bytes for the induction fixture (term table plus small search caps plus mini-space slack).
// CEP:WHY: Named fixture size (CEP&CC 11.3); larger than the standard inference fixture because the flagship test runs the full saturation.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kInductionFixtureArena: u32 = 25_165_824;

// CEP:WHAT: The induction test fixture: Nat-shaped vocabulary over a leaked arena with a small search space.
// CEP:WHY: One constructor builds every piece the module needs: sort N; constants zero, sk, a; unary succ; unary predicates p, q; binary predicate lt; propositional r (the non-unary filter probe).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena per test.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
struct InductionFixture {
    space: SearchSpace<'static>,
    symbols: SymbolTable<'static>,
    terms: TermStore<'static>,
    precedence: PrecedenceTable<'static>,
    options: SearchOptions,
    zero: u32,
    succ: u32,
    sk: u32,
    a: u32,
    p: u32,
    q: u32,
    lt: u32,
    r: u32,
}

// CEP:WHAT: Builds the induction fixture.
// CEP:WHY: The dedicated vocabulary keeps the scheme-shape assertions readable and independent of the standard fixture.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn make_induction_fixture_selected(
    selection: mapt::hot::inference::SelectionFunction,
) -> InductionFixture {
    let region = allocate_aligned_region(kInductionFixtureArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_n = SortId(builder.declare_sort("N").expect("sort N"));
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_n)
        .expect("zero");
    let sk = builder
        .declare_function("sk", 0, 1, &[], sort_n)
        .expect("sk");
    let a = builder.declare_function("a", 0, 1, &[], sort_n).expect("a");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_n], sort_n)
        .expect("succ");
    let p = builder.declare_predicate("p", 1, 1, &[sort_n]).expect("p");
    let q = builder.declare_predicate("q", 1, 1, &[sort_n]).expect("q");
    let lt = builder
        .declare_predicate("lt", 2, 1, &[sort_n, sort_n])
        .expect("lt");
    let r = builder.declare_predicate("r", 0, 1, &[]).expect("r");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let mut options = SearchOptions::new();
    options.selection = selection;
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    InductionFixture {
        space,
        symbols,
        terms,
        precedence,
        options,
        zero,
        succ,
        sk,
        a,
        p,
        q,
        lt,
        r,
    }
}

// CEP:WHAT: Builds the fixture with a precedence that ranks zero highest among the function symbols.
// CEP:WHY: The flagship's refutation path needs ~p(zero) maximal inside the scheme clauses (Spec 15 section 6's worked path); from_id_order ranks by declaration order (later ids rank higher), so the test supplies the explicit rank permutation (zero swaps to the top) through the validated from_ranks constructor - the same mechanism the strategy layer will use.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by induction_refutes_inductive_theorem.
// CEP:SECURITY: none.
fn make_induction_fixture_with_high_zero_precedence() -> InductionFixture {
    let region = allocate_aligned_region(kInductionFixtureArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_n = SortId(builder.declare_sort("N").expect("sort N"));
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_n)
        .expect("zero");
    let sk = builder
        .declare_function("sk", 0, 1, &[], sort_n)
        .expect("sk");
    let a = builder.declare_function("a", 0, 1, &[], sort_n).expect("a");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_n], sort_n)
        .expect("succ");
    let p = builder.declare_predicate("p", 1, 1, &[sort_n]).expect("p");
    let q = builder.declare_predicate("q", 1, 1, &[sort_n]).expect("q");
    let lt = builder
        .declare_predicate("lt", 2, 1, &[sort_n, sort_n])
        .expect("lt");
    let r = builder.declare_predicate("r", 0, 1, &[]).expect("r");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let count = builder.symbol_count();
    // Explicit ranks: identity permutation with zero swapped to the top
    // function rank; the equality head keeps the highest rank (the from_id_order
    // convention).
    let mut ranks: Vec<u32> = (0..=count).collect();
    let top = count - 1;
    let zero_rank_position = ranks[zero as usize];
    ranks[zero as usize] = top;
    ranks[top as usize] = zero_rank_position;
    let precedence = PrecedenceTable::from_ranks(arena, &ranks).expect("custom precedence");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    InductionFixture {
        space,
        symbols,
        terms,
        precedence,
        options,
        zero,
        succ,
        sk,
        a,
        p,
        q,
        lt,
        r,
    }
}

// CEP:WHAT: Builds the fixture with the default selection (None).
// CEP:WHY: The common case; the flagship test injects FirstNegative explicitly.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_induction_fixture() -> InductionFixture {
    make_induction_fixture_selected(mapt::hot::inference::SelectionFunction::None)
}

// CEP:WHAT: Builds the inference context over the fixture's space.
// CEP:WHY: The module's entry points take the context.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn context_of(fixture: &InductionFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Interns a constant term by symbol id.
// CEP:WHY: Readable scheme-shape assertions.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by the shape tests.
// CEP:SECURITY: none.
fn constant(fixture: &InductionFixture, symbol: u32) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol, &[])
        .expect("constant")
}

// CEP:WHAT: Interns succ(t).
// CEP:WHY: The step-constructor application.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by the shape tests.
// CEP:SECURITY: none.
fn succ_of(fixture: &InductionFixture, child: TermPtr) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.succ, &[child])
        .expect("succ")
}

// CEP:WHAT: Interns a p(t) atom.
// CEP:WHY: The goal-side atom of the shape assertions.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by the shape tests.
// CEP:SECURITY: none.
fn p_atom(fixture: &InductionFixture, arg: TermPtr) -> TermPtr {
    fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[arg])
        .expect("p atom")
}

// CEP:WHAT: Reads one stored clause's literals as a Vec of (atom, polarity).
// CEP:WHY: The shape assertions compare stored clauses against expected literal sets.
// CEP:STATUS: complete
// CEP:FAILURE: panics on read failure.
// CEP:ASSUMES: the id is live.
// CEP:COST: O(literals).
// CEP:EVIDENCE: used by the shape tests.
// CEP:SECURITY: none.
fn read_clause(fixture: &InductionFixture, id: u64) -> Vec<(TermPtr, bool)> {
    let record = fixture
        .space
        .store
        .clause_by_id(mapt::hot::ir::clause::ClauseId(id))
        .expect("clause");
    let mut out = Vec::new();
    for index in 0..record.literal_count {
        let literal = fixture.space.store.literal(record, index).expect("literal");
        out.push((literal.atom(), literal.is_positive()));
    }
    out
}

// CEP:WHAT: The standard declaration over the fixture (no well-order).
// CEP:WHY: One constructor for the common case.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture symbols.
// CEP:COST: constant.
// CEP:EVIDENCE: used by most tests.
// CEP:SECURITY: none.
fn declaration(fixture: &InductionFixture) -> InductionDeclaration {
    InductionDeclaration {
        zero: fixture.zero,
        succ: fixture.succ,
        skolem: fixture.sk,
        well_founded: None,
    }
}

// CEP:WHAT: Validation rejects malformed declarations: non-constant zero, non-unary succ, non-constant skolem, non-binary well-order.
// CEP:WHY: Spec 15 section 2: every shape claim is mechanical; the rejections are the soundness boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any malformed shape is accepted.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::{validate_declaration, is_constant_function, is_unary_function}.
// CEP:SECURITY: input validation.
#[test]
fn declaration_validation_rejects_bad_shapes() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let good = declaration(&fixture);
    assert_eq!(validate_declaration(&fixture.symbols, &good), Ok(()));
    // zero must be a constant: succ is unary.
    let bad = InductionDeclaration {
        zero: fixture.succ,
        succ: good.succ,
        skolem: good.skolem,
        well_founded: good.well_founded,
    };
    assert_eq!(
        validate_declaration(&fixture.symbols, &bad),
        Err(InductionError::ZeroNotConstant)
    );
    // succ must be unary: zero is 0-ary.
    let mut bad = declaration(&fixture);
    bad.succ = fixture.zero;
    assert_eq!(
        validate_declaration(&fixture.symbols, &bad),
        Err(InductionError::SuccNotUnary)
    );
    // skolem must be a constant: p is a predicate, succ is unary.
    let mut bad = declaration(&fixture);
    bad.skolem = fixture.succ;
    assert_eq!(
        validate_declaration(&fixture.symbols, &bad),
        Err(InductionError::SkolemNotConstant)
    );
    // well-founded must be a binary predicate: p is unary, zero is a function.
    let mut bad = declaration(&fixture);
    bad.well_founded = Some(fixture.p);
    assert_eq!(
        validate_declaration(&fixture.symbols, &bad),
        Err(InductionError::WellFoundedNotBinary)
    );
    let mut bad = declaration(&fixture);
    bad.well_founded = Some(fixture.zero);
    assert_eq!(
        validate_declaration(&fixture.symbols, &bad),
        Err(InductionError::WellFoundedNotBinary)
    );
    let mut good_wf = declaration(&fixture);
    good_wf.well_founded = Some(fixture.lt);
    assert_eq!(validate_declaration(&fixture.symbols, &good_wf), Ok(()));
    let _ = context;
}

// CEP:WHAT: A skolem occurring in an input clause is rejected with SkolemOccursInInput and no scheme is added.
// CEP:WHY: Spec 15 section 3: the schemes are valid only with a fresh witness; the scan proves freshness mechanically.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an occurring skolem is accepted.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::{scan_input_signature, walk_term} and config/limits.rs (kInductionScanNodeBudget's skolem-freshness role).
// CEP:SECURITY: soundness boundary.
#[test]
fn skolem_occurrence_rejected() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    // Input clause mentioning the skolem: p(sk).
    let atom = p_atom(&fixture, constant(&fixture, fixture.sk));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(atom, true)])
        .expect("input");
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    );
    assert_eq!(stats, Err(InductionError::SkolemOccursInInput));
    // No scheme was added: only the input clause exists.
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 1);
}

// CEP:WHAT: The structural scheme clauses equal the hand clausification {~p(zero), p(sk), p(X)} and {~p(zero), ~p(succ(sk)), p(X)}.
// CEP:WHY: Spec 15 section 3: the two-clause shape is the soundness-critical core; pinning it against the independent hand derivation catches any builder drift.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any literal mismatch.
// CEP:ASSUMES: one occurring unary predicate p.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/scheme.rs::{structural_scheme_literals, kStructuralClauseCount} and config/limits.rs (kInductionSchemeClauses).
// CEP:SECURITY: none.
#[test]
fn structural_scheme_clauses_match_clausification() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let atom = p_atom(&fixture, constant(&fixture, fixture.a));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(atom, true)])
        .expect("input");
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 2);
    assert_eq!(stats.unary_predicates, 1);
    // Expected atoms.
    let t_zero = constant(&fixture, fixture.zero);
    let t_sk = constant(&fixture, fixture.sk);
    let t_x = fixture.terms.intern_var(0).expect("var");
    let p_zero = p_atom(&fixture, t_zero);
    let p_sk = p_atom(&fixture, t_sk);
    let p_succ_sk = p_atom(&fixture, succ_of(&fixture, t_sk));
    let p_x = p_atom(&fixture, t_x);
    // Clause kFirstClauseId+1: {~p(zero), p(sk), p(X)} (stored canonically sorted).
    let first = read_clause(&fixture, kFirstClauseId + 1);
    let expected_first: Vec<(TermPtr, bool)> = vec![(p_zero, false), (p_sk, true), (p_x, true)];
    assert_eq!(first.len(), expected_first.len());
    for expected in expected_first.iter() {
        assert!(first.contains(expected), "clause 1 missing {:?}", expected);
    }
    // Clause kFirstClauseId+2: {~p(zero), ~p(succ(sk)), p(X)}.
    let second = read_clause(&fixture, kFirstClauseId + 2);
    let expected_second: Vec<(TermPtr, bool)> =
        vec![(p_zero, false), (p_succ_sk, false), (p_x, true)];
    assert_eq!(second.len(), expected_second.len());
    for expected in expected_second.iter() {
        assert!(second.contains(expected), "clause 2 missing {:?}", expected);
    }
    // The derivation rules.
    for id in [kFirstClauseId + 1, kFirstClauseId + 2] {
        let record = fixture
            .space
            .store
            .clause_by_id(mapt::hot::ir::clause::ClauseId(id))
            .expect("clause");
        assert_eq!(
            record.derivation.rule,
            mapt::hot::ir::clause::InferenceRule::StructuralInduction
        );
        assert_eq!(record.derivation.parent_count, 0);
    }
}

// CEP:WHAT: The well-founded scheme clauses equal {~lt(Y, sk), p(Y), p(X)} and {~p(sk), p(X)}; non-unary predicates (r/0, lt/2) receive no schemes.
// CEP:WHY: Spec 15 section 4 pins the strong scheme's shape; the arity filter keeps the domain unary-only.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any literal mismatch or an unexpected scheme.
// CEP:ASSUMES: one occurring unary predicate p; lt declared as the well-order.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/scheme.rs::{well_founded_scheme_literals, kWellFoundedClauseCount}.
// CEP:SECURITY: none.
#[test]
fn well_founded_scheme_clauses_match_clausification() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let atom = p_atom(&fixture, constant(&fixture, fixture.a));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(atom, true)])
        .expect("input");
    let declaration = InductionDeclaration {
        zero: fixture.zero,
        succ: fixture.succ,
        skolem: fixture.sk,
        well_founded: Some(fixture.lt),
    };
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration,
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 2);
    assert_eq!(stats.well_founded_schemes, 2);
    assert_eq!(stats.unary_predicates, 1);
    // Expected atoms for the strong scheme.
    let t_sk = constant(&fixture, fixture.sk);
    let t_y = fixture.terms.intern_var(0).expect("var y");
    let t_x = fixture.terms.intern_var(1).expect("var x");
    let lt_y_sk = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.lt, &[t_y, t_sk])
        .expect("lt atom");
    let p_y = p_atom(&fixture, t_y);
    let p_x1 = p_atom(&fixture, t_x);
    let p_sk = p_atom(&fixture, t_sk);
    let third = read_clause(&fixture, kFirstClauseId + 3);
    let expected_third: Vec<(TermPtr, bool)> = vec![(lt_y_sk, false), (p_y, true), (p_x1, true)];
    assert_eq!(third.len(), 3);
    for expected in expected_third.iter() {
        assert!(third.contains(expected), "clause 3 missing {:?}", expected);
    }
    let p_x0 = p_atom(&fixture, t_y);
    let fourth = read_clause(&fixture, kFirstClauseId + 4);
    let expected_fourth: Vec<(TermPtr, bool)> = vec![(p_sk, false), (p_x0, true)];
    assert_eq!(fourth.len(), 2);
    for expected in expected_fourth.iter() {
        assert!(fourth.contains(expected), "clause 4 missing {:?}", expected);
    }
    for id in [kFirstClauseId + 3, kFirstClauseId + 4] {
        let record = fixture
            .space
            .store
            .clause_by_id(mapt::hot::ir::clause::ClauseId(id))
            .expect("clause");
        assert_eq!(
            record.derivation.rule,
            mapt::hot::ir::clause::InferenceRule::WellFoundedInduction
        );
    }
}

// CEP:WHAT: Schemes enter the passive set (the store grows by the scheme count and saturate processes them).
// CEP:WHY: Design 15.1: theory axioms join the initial passive population; the observable is the id growth plus a saturation that terminates Saturated on a satisfiable scheme set.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if schemes bypass the passive set.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: one small saturation.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::add_induction_schemes and hot/search/given_clause.rs::add_theory_clause.
// CEP:SECURITY: none.
#[test]
fn schemes_enter_passive_set() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let atom = p_atom(&fixture, constant(&fixture, fixture.a));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(atom, true)])
        .expect("input");
    let before = fixture.space.store.next_clause_id().0;
    add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    let after = fixture.space.store.next_clause_id().0;
    assert_eq!(after - before, 2);
    // Saturate the scheme-augmented satisfiable set: terminates without a refutation.
    let mut stats = SearchStats::default();
    let outcome = saturate(
        &fixture.space,
        &context,
        &fixture.options,
        &|_| false,
        &mut stats,
    )
    .expect("saturate");
    assert!(
        matches!(outcome, SearchOutcome::Saturated),
        "expected Saturated, got {:?}",
        outcome
    );
}

// CEP:WHAT: The attempts budget cuts the scheme enumeration atomically per predicate pair: max_attempts 1 adds NOTHING (a lone clause of a pair is not the clausification and is never emitted), max_attempts 2 covers exactly one predicate, and the skips are counted.
// CEP:WHY: CEP&CC 22.10/39.1 and Law 4: the bound is enforced, the pair atomicity is the soundness rule (Spec 15 section 3: the two clauses jointly clausify one valid axiom), and the skips are visible in the stats.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if more than the budget is added, a partial pair is emitted, or the skip is not counted.
// CEP:ASSUMES: two occurring unary predicates (p, q) so the cut is observable.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::add_induction_schemes and config/limits.rs (kMaxInductionAttempts, kInductionSchemeClauses).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn attempts_budget_enforced() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let p_a = p_atom(&fixture, constant(&fixture, fixture.a));
    let q_a = fixture
        .terms
        .intern_pred(
            &fixture.symbols,
            fixture.q,
            &[constant(&fixture, fixture.a)],
        )
        .expect("q atom");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, true)])
        .expect("input p");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(q_a, true)])
        .expect("input q");
    // Budget 1: the pair does not fit; nothing is added, both predicates skipped.
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        1,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 0);
    assert_eq!(stats.predicates_skipped, 2);
    assert_eq!(stats.unary_predicates, 2);
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 2);
    // Budget 2: exactly one predicate's pair fits; the other is skipped.
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        2,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 2);
    assert_eq!(stats.predicates_skipped, 1);
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 4);
}

// CEP:WHAT: A scan budget of 1 rejects the input with ScanBudgetExceeded and adds nothing.
// CEP:WHY: CEP&CC 34.3: the node budget is injectable and its exhaustion path is pinned at small scale.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the budget is not enforced.
// CEP:ASSUMES: any input with more than one term node.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::{scan_input_signature, walk_term} and config/limits.rs (kInductionScanNodeBudget).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn scan_budget_rejects_runaway_input() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let atom = p_atom(&fixture, succ_of(&fixture, constant(&fixture, fixture.a)));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(atom, true)])
        .expect("input");
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        1,
    );
    assert_eq!(stats, Err(InductionError::ScanBudgetExceeded));
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 1);
}

// CEP:WHAT: Non-unary predicates (the propositional r and the binary lt) never receive schemes, and predicates that do not occur are not counted.
// CEP:WHY: The domain is occurring unary predicates only (E's induction.ax discipline); the filter is part of the spec's enumeration contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unexpected scheme.
// CEP:ASSUMES: p occurs; r occurs; q does not occur.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::{is_derived domain collection, walk_term}.
// CEP:SECURITY: none.
#[test]
fn non_unary_and_unoccurring_predicates_ignored() {
    let fixture = make_induction_fixture();
    let context = context_of(&fixture);
    let p_a = p_atom(&fixture, constant(&fixture, fixture.a));
    let r_atom = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.r, &[])
        .expect("r atom");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, true)])
        .expect("input p");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(r_atom, true)])
        .expect("input r");
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.unary_predicates, 1);
    assert_eq!(stats.structural_schemes, 2);
    assert_eq!(stats.predicates_skipped, 0);
}

// CEP:WHAT: The flagship: with the structural schemes, the saturation refutes the inductive theorem p(zero), p(x) -> p(succ(x)) |= forall x. p(x); without schemes the same problem saturates without a refutation.
// CEP:WHY: The feature's reason to exist: the negated conjecture ~p(a) with the base and step axioms has no first-order refutation (the induction axiom is second-order in p), so the plain loop saturates honestly, while the two scheme clauses close the proof through Spec 15 section 6's worked path: scheme 1's ~p(zero) resolves with p(zero) to p(sk) or p(X); factoring yields the unit p(sk); the step clause's p(succ(X)) resolves with scheme 2's ~p(succ(sk)) to {~p(sk), ~p(zero), p(X)}; ~p(zero) with p(zero) yields {~p(sk), p(X)}; ~p(sk) with the unit p(sk) yields p(X); p(X) with ~p(a) closes the empty clause; the custom precedence ranks zero highest so ~p(zero) is maximal in scheme 1 (the eligibility the ordered calculus needs), and the same ordered restriction blocks the unbounded ground chain p(succ^n(a)) (the step clause's ~p(X) is never maximal), which keeps the search shallow and fast.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the schemes do not produce the refutation or the plain run unexpectedly refutes.
// CEP:ASSUMES: the custom precedence (zero ranked highest); the default selection (None, pure maximality).
// CEP:COST: two small saturations.
// CEP:EVIDENCE: cited by hot/induction/mod.rs (file header) and docs/formal/15_structural_induction.md section 6.
// CEP:SECURITY: none.
#[test]
fn induction_refutes_inductive_theorem() {
    // Without schemes: the plain loop saturates without a refutation (the
    // ordered calculus fires no inference at all: the step clause's negative
    // literal is never maximal and the constants do not unify).
    let plain = make_induction_fixture_with_high_zero_precedence();
    let plain_context = context_of(&plain);
    let t_a = constant(&plain, plain.a);
    let t_zero = constant(&plain, plain.zero);
    let t_x = plain.terms.intern_var(0).expect("x");
    let p_a = p_atom(&plain, t_a);
    let p_zero = p_atom(&plain, t_zero);
    let p_x = p_atom(&plain, t_x);
    let p_succ_x = p_atom(&plain, succ_of(&plain, t_x));
    plain
        .space
        .add_input_clause(
            &plain_context,
            &plain.options,
            &[Literal::new(p_zero, true)],
        )
        .expect("base");
    plain
        .space
        .add_input_clause(
            &plain_context,
            &plain.options,
            &[Literal::new(p_x, false), Literal::new(p_succ_x, true)],
        )
        .expect("step");
    plain
        .space
        .add_input_clause(&plain_context, &plain.options, &[Literal::new(p_a, false)])
        .expect("negated conjecture");
    let mut plain_stats = SearchStats::default();
    let plain_outcome = saturate(
        &plain.space,
        &plain_context,
        &plain.options,
        &|_| false,
        &mut plain_stats,
    )
    .expect("plain saturate");
    assert!(
        matches!(plain_outcome, SearchOutcome::Saturated),
        "plain run should saturate without a refutation, got {:?}",
        plain_outcome
    );

    // With schemes: the same problem refutes.
    let fixture = make_induction_fixture_with_high_zero_precedence();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_zero = constant(&fixture, fixture.zero);
    let t_x = fixture.terms.intern_var(0).expect("x");
    let p_a = p_atom(&fixture, t_a);
    let p_zero = p_atom(&fixture, t_zero);
    let p_x = p_atom(&fixture, t_x);
    let p_succ_x = p_atom(&fixture, succ_of(&fixture, t_x));
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_zero, true)])
        .expect("base");
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(p_x, false), Literal::new(p_succ_x, true)],
        )
        .expect("step");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, false)])
        .expect("negated conjecture");
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &declaration(&fixture),
        kMaxInductionAttempts,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 2);
    let mut search_stats = SearchStats::default();
    let outcome = saturate(
        &fixture.space,
        &context,
        &fixture.options,
        &|_| false,
        &mut search_stats,
    )
    .expect("saturate");
    assert!(
        matches!(outcome, SearchOutcome::Theorem { .. }),
        "induction run should refute, got {:?} (stats: inferences {}, given {})",
        outcome,
        search_stats.inferences,
        search_stats.given_processed
    );
}
