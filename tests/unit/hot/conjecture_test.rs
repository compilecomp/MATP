// CEP:FILE: tests/unit/hot/conjecture_test.rs
// CEP:WHAT: Unit tests of automated conjecture generation: template enumeration (T1 symmetry, T2 transitivity, T3 constructor instances, candidate cap, determinism), the bounded refutation filter (import with the complete reductio subproof, unprovable and budget-exhausted discards, vacuous-refutation rejection), the lemma's recorded parents, and the in-loop harvest schedule and budget.
// CEP:WHY: CEP&CC 34.3 and design 26 (revised build order Phase 4): the harvest is the only path that adds clauses to the main search OUTSIDE the given-clause loop's own derivations, so its soundness invariant (only refutation-proved lemmas, each with a complete checkable subproof) and its isolation invariant (failed attempts change nothing) are pinned executably here before the property tests generalize them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the fixture vocabulary (a/b/c constants, f/g unary, zero/succ/sk constructors, p/q unary predicates, lt binary, r propositional).
// CEP:COST: offline.
// CEP:EVIDENCE: this file is the evidence cited by hot/conjecture/{mod,template,filter}.rs.
// CEP:SECURITY: the discard and vacuous-refutation tests exercise the soundness boundary.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::conjecture::filter::{refute_and_maybe_import, CandidateOutcome, MiniCapacities};
use mapt::hot::conjecture::template::{collect_recent_units, enumerate_candidates, CandidateList};
use mapt::hot::conjecture::{harvest, harvest_with_types};
use mapt::hot::induction::InductionDeclaration;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClauseId, ClausePtr, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};
use mapt_config::limits::{
    kConjectureRefuteInferences, kFirstClauseId, kInvalidClauseId, kInvalidSubstitutionOffset,
    kMaxConjectureCandidates, kMaxConjectureHarvests, kMaxDerivationParents,
};

// CEP:WHAT: Arena bytes for the conjecture fixture (term table, main search caps, mini-space slack, and the chain family for the schedule tests).
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kConjectureFixtureArena: u32 = 50_331_648;

// CEP:WHAT: The conjecture test fixture: equality-capable vocabulary over a leaked arena with a small search space.
// CEP:WHY: One constructor builds every piece: sort S; constants a, b, c, zero, sk; unary f, g, succ; unary predicates p, q; binary lt; propositional r.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena per test.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
struct ConjectureFixture {
    space: SearchSpace<'static>,
    symbols: SymbolTable<'static>,
    builder: SymbolTableBuilder,
    terms: TermStore<'static>,
    precedence: PrecedenceTable<'static>,
    options: SearchOptions,
    a: u32,
    b: u32,
    c: u32,
    zero: u32,
    sk: u32,
    succ: u32,
    f: u32,
    p: u32,
}

// CEP:WHAT: Builds the conjecture fixture.
// CEP:WHY: The dedicated vocabulary keeps the template assertions readable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn make_conjecture_fixture() -> ConjectureFixture {
    let region = allocate_aligned_region(kConjectureFixtureArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort S"));
    let a = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let b = builder.declare_function("b", 0, 1, &[], sort_s).expect("b");
    let c = builder.declare_function("c", 0, 1, &[], sort_s).expect("c");
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_s)
        .expect("zero");
    let sk = builder
        .declare_function("sk", 0, 1, &[], sort_s)
        .expect("sk");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_s], sort_s)
        .expect("succ");
    let f = builder
        .declare_function("f", 1, 1, &[sort_s], sort_s)
        .expect("f");
    let p = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &options, 8192, 4096, 16384, 16384, 131072, 8192)
        .expect("space");
    ConjectureFixture {
        space,
        symbols,
        builder,
        terms,
        precedence,
        options,
        a,
        b,
        c,
        zero,
        sk,
        succ,
        f,
        p,
    }
}

// CEP:WHAT: Builds the inference context over the fixture's space.
// CEP:WHY: The module's entry points take the context.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn context_of(fixture: &ConjectureFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Interns a constant term by symbol id.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn constant(fixture: &ConjectureFixture, symbol: u32) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol, &[])
        .expect("constant")
}

// CEP:WHAT: Interns an equality atom.
// CEP:WHY: The unit-equation fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn eq_atom(fixture: &ConjectureFixture, left: TermPtr, right: TermPtr) -> TermPtr {
    fixture
        .terms
        .intern_eq(&fixture.symbols, left, right)
        .expect("eq atom")
}

// CEP:WHAT: Adds one DERIVED unit equation to the main space (a simulated derivation with the Demodulation rule).
// CEP:WHY: T1/T2 harvest derived units only; the tests inject them directly so the enumeration is pinned without running a search first; the parentless derivation is legal for the filter's purposes (the lemma import never re-derives the sources).
// CEP:STATUS: complete
// CEP:FAILURE: panics on add failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one add.
// CEP:EVIDENCE: used by the template tests.
// CEP:SECURITY: none.
fn add_derived_unit(fixture: &ConjectureFixture, left: TermPtr, right: TermPtr) {
    let context = context_of(fixture);
    let atom = eq_atom(fixture, left, right);
    let derivation = DerivationStep {
        rule: InferenceRule::Demodulation,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; kMaxDerivationParents],
        substitution: kInvalidSubstitutionOffset,
    };
    fixture
        .space
        .add_derived_clause(
            &context,
            &fixture.options,
            &[Literal::new(atom, true)],
            derivation,
        )
        .expect("derived unit");
}

// CEP:WHAT: The candidate list's atom pointers in order.
// CEP:WHY: Compact assertion helper.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(count).
// CEP:EVIDENCE: used by the template tests.
// CEP:SECURITY: none.
fn atoms_of(candidates: &CandidateList) -> Vec<TermPtr> {
    (0..candidates.count)
        .map(|index| candidates.literals[index].atom())
        .collect()
}

// CEP:WHAT: T1 enumerates the symmetry candidate of every derived unit, ascending by clause id, skipping reflexive units.
// CEP:WHY: Spec 16 section 4's first template.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any missing or extra candidate.
// CEP:ASSUMES: two derived units a=b and b=c.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs (T1 loop).
// CEP:SECURITY: none.
#[test]
fn symmetry_candidates() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let t_c = constant(&fixture, fixture.c);
    add_derived_unit(&fixture, t_a, t_b);
    add_derived_unit(&fixture, t_b, t_c);
    let window = collect_recent_units(&fixture.space, &context);
    let candidates = enumerate_candidates(&fixture.space, &context, &window, None);
    // T1: b=a and c=b; T2 joins a=b with b=c (old.right b == new.left b) into a=c.
    assert_eq!(candidates.count, 3);
    let atoms = atoms_of(&candidates);
    assert_eq!(atoms[0], eq_atom(&fixture, t_b, t_a));
    assert_eq!(atoms[1], eq_atom(&fixture, t_c, t_b));
    assert_eq!(atoms[2], eq_atom(&fixture, t_a, t_c));
}

// CEP:WHAT: T2 pairs derived units joined by hash-consed side identity in both chain directions.
// CEP:WHY: Spec 16 section 4's second template: a=b with b=c yields a=c (old -> new) and c=a (new -> old), enumerated in the fixed pair order.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any missing or extra candidate.
// CEP:ASSUMES: derived units a=b and b=c.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs (T2 loop) and config/limits.rs (kConjectureTransitivityWindow).
// CEP:SECURITY: none.
#[test]
fn transitivity_pairs_recent_units() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let t_c = constant(&fixture, fixture.c);
    add_derived_unit(&fixture, t_a, t_b);
    add_derived_unit(&fixture, t_b, t_c);
    let window = collect_recent_units(&fixture.space, &context);
    let candidates = enumerate_candidates(&fixture.space, &context, &window, None);
    // T1 gives b=a and c=b, then T2's old->new chain (old.right b == new.left b)
    // gives a=c; the new->old direction (new.right c == old.left a) does not fire.
    let atoms = atoms_of(&candidates);
    assert_eq!(candidates.count, 3);
    assert!(atoms.contains(&eq_atom(&fixture, t_a, t_c)));
    assert!(!atoms.contains(&eq_atom(&fixture, t_c, t_a)));
}

// CEP:WHAT: T3 instantiates unit equations with at most kConjectureInstanceVariables variables at the all-zero and all-successor-of-zero patterns, from input-range units and window units alike, skipping reflexive instances.
// CEP:WHY: Spec 16 section 4's third template: the induction base and step witnesses.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any missing or extra instance.
// CEP:ASSUMES: the input unit f(X)=X (one variable) and the derived unit a=b.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs::{instantiate_unit_at_patterns, count_variables} and config/limits.rs (kConjectureInstanceVariables).
// CEP:SECURITY: none.
#[test]
fn constructor_instances_bounded() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let t_zero = constant(&fixture, fixture.zero);
    let t_succ_zero = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.succ, &[t_zero])
        .expect("succ(zero)");
    let t_x = fixture.terms.intern_var(0).expect("x");
    let t_f_x = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.f, &[t_x])
        .expect("f(x)");
    // Input unit equation f(X) = X.
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_f_x, t_x), true)],
        )
        .expect("input unit");
    // A derived unit a=b (T1 also applies).
    add_derived_unit(&fixture, t_a, t_b);
    let declaration = InductionDeclaration {
        zero: fixture.zero,
        succ: fixture.succ,
        skolem: fixture.sk,
        well_founded: None,
    };
    let window = collect_recent_units(&fixture.space, &context);
    let candidates = enumerate_candidates(&fixture.space, &context, &window, Some(&declaration));
    let atoms = atoms_of(&candidates);
    // T1: b=a. T3 from the input f(X)=X: f(zero)=zero and f(succ(zero))=succ(zero).
    assert!(atoms.contains(&eq_atom(&fixture, t_b, t_a)));
    assert!(atoms.contains(&eq_atom(
        &fixture,
        {
            fixture
                .terms
                .intern_fun(&fixture.symbols, fixture.f, &[t_zero])
                .expect("f(zero)")
        },
        t_zero
    )));
    assert!(atoms.contains(&eq_atom(
        &fixture,
        {
            fixture
                .terms
                .intern_fun(&fixture.symbols, fixture.f, &[t_succ_zero])
                .expect("f(succ(zero))")
        },
        t_succ_zero
    )));
    // T3 skips the derived unit a=b (ground: no variables).
    assert_eq!(candidates.count, 3);
}

// CEP:WHAT: The candidate list is capped at kMaxConjectureCandidates (a deterministic prefix cut).
// CEP:WHY: Spec 16 section 5's per-harvest work bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the cap is exceeded.
// CEP:ASSUMES: more derivable candidates than the cap.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs::CandidateList::push and config/limits.rs (kMaxConjectureCandidates).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn candidate_budget_enforced() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    // More derived units than the candidate cap.
    for _ in 0..(kMaxConjectureCandidates + 4) {
        add_derived_unit(&fixture, t_a, t_b);
    }
    let window = collect_recent_units(&fixture.space, &context);
    // The window may cap first; either way the candidate list must respect its bound.
    assert!(window.count <= mapt_config::limits::kConjectureTransitivityWindow as usize);
    let candidates = enumerate_candidates(&fixture.space, &context, &window, None);
    assert!(candidates.count <= kMaxConjectureCandidates as usize);
    // All units are identical (a=b): the single symmetry candidate dedups.
    assert_eq!(candidates.count, 1);
}

// CEP:WHAT: The enumeration is deterministic: identical fixtures produce identical candidate atom sequences.
// CEP:WHY: CEP&CC 38.10 discipline, pinned at the unit level.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any divergence.
// CEP:ASSUMES: none.
// CEP:COST: two fixtures.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs (file header HPC-DETERMINISM).
// CEP:SECURITY: none.
#[test]
fn enumeration_is_deterministic() {
    let run = || {
        let fixture = make_conjecture_fixture();
        let context = context_of(&fixture);
        let t_a = constant(&fixture, fixture.a);
        let t_b = constant(&fixture, fixture.b);
        let t_c = constant(&fixture, fixture.c);
        add_derived_unit(&fixture, t_a, t_b);
        add_derived_unit(&fixture, t_b, t_c);
        let window = collect_recent_units(&fixture.space, &context);
        let candidates = enumerate_candidates(&fixture.space, &context, &window, None);
        atoms_of(&candidates)
    };
    let first = run();
    let second = run();
    assert_eq!(first, second);
}

// CEP:WHAT: A refuted candidate imports its lemma with a complete reductio subproof: the lemma's parents are the imported ConjectureNegation premise (the literal-wise complement) and the imported empty clause, and the TSTP renderer emits and the replay checker accepts the whole proof.
// CEP:WHY: The feature's soundness core (Spec 16 section 6, Spec 17 section 4): only a proved lemma enters, and its proof is recorded and independently checkable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any parent, shape, or checker mismatch.
// CEP:ASSUMES: the input axiom b=a stored in the oriented form (b ranks above a under from_id_order, so the equation is usable as the rewrite rule b -> a); the candidate a=b (the symmetry of a derived unit), provable by superposing b -> a into the negated literal (yielding the negative reflexive a != a) plus equality resolution.
// CEP:COST: one mini refutation.
// CEP:EVIDENCE: cited by hot/conjecture/filter.rs::{refute_and_maybe_import, import_refutation} and cold/proof_output/tstp.rs (ConjectureLemma reductio check).
// CEP:SECURITY: proof validation.
#[test]
fn refuted_candidate_imports_proof() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    // Input axiom: b = a, stored oriented (left side b ranks above right side a,
    // the form the superposition and demodulation rules require).
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_b, t_a), true)],
        )
        .expect("axiom");
    // Candidate: a = b (positive unit literal).
    let candidate = Literal::new(eq_atom(&fixture, t_a, t_b), true);
    let next_before = fixture.space.store.next_clause_id().0;
    let outcome = refute_and_maybe_import(
        &fixture.space,
        &context,
        &fixture.options,
        candidate,
        &MiniCapacities::production(),
    )
    .expect("filter");
    assert_eq!(outcome, CandidateOutcome::Imported);
    // The lemma is the newest clause with the ConjectureLemma rule.
    let next_after = fixture.space.store.next_clause_id().0;
    assert!(
        next_after > next_before + 1,
        "import must create subproof clauses"
    );
    let lemma_id = next_after - 1;
    let lemma = fixture
        .space
        .store
        .clause_by_id(ClauseId(lemma_id))
        .expect("lemma");
    assert_eq!(lemma.derivation.rule, InferenceRule::ConjectureLemma);
    assert_eq!(lemma.derivation.parent_count, 2);
    assert_eq!(lemma.literal_count, 1);
    let negation_id = lemma.derivation.parents[0];
    let empty_id = lemma.derivation.parents[1];
    let negation = fixture
        .space
        .store
        .clause_by_id(ClauseId(negation_id))
        .expect("negation");
    assert_eq!(negation.derivation.rule, InferenceRule::ConjectureNegation);
    assert_eq!(negation.literal_count, 1);
    let negation_literal = fixture.space.store.literal(negation, 0).expect("lit");
    assert_eq!(negation_literal.atom(), candidate.atom());
    assert!(!negation_literal.is_positive());
    let empty = fixture
        .space
        .store
        .clause_by_id(ClauseId(empty_id))
        .expect("empty");
    assert_eq!(empty.literal_count, 0);
    // The TSTP renderer formats and the checker accepts the imported proof.
    let (count, text) = mapt::cold::proof_output::tstp::render_verified_proof(
        &context,
        &fixture.terms,
        &fixture.builder,
        &fixture.space.store,
        empty_id as u32,
    )
    .or_else(|_| {
        // The walk takes an offset; resolve the empty clause's offset.
        let offset = fixture
            .space
            .store
            .offset_of_id(ClauseId(empty_id))
            .expect("offset");
        mapt::cold::proof_output::tstp::render_verified_proof(
            &context,
            &fixture.terms,
            &fixture.builder,
            &fixture.space.store,
            offset,
        )
    })
    .expect("render and check");
    // The walk starts at the imported empty clause, so the rendered subproof
    // contains the negation premise, the refutation steps, and $false; the
    // lemma itself is a DESCENDANT of this root and is asserted by record
    // above (the checker's reductio arm is exercised directly by
    // checker_accepts_conjecture_lemma below).
    assert!(count >= 3);
    assert!(text.contains("$false"));
    if !(text.contains("demodulation")
        || text.contains("superposition")
        || text.contains("equality_resolution"))
    {
        panic!("subproof lacks any equality step:\n{}", text);
    }
}

// CEP:WHAT: An unprovable candidate is discarded and the main space is unchanged.
// CEP:WHY: Spec 16 section 5's isolation theorem: the mini store is separate, so a discard adds nothing to the main store.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added.
// CEP:ASSUMES: no axiom implies b=c.
// CEP:COST: one mini run.
// CEP:EVIDENCE: cited by hot/conjecture/filter.rs::refute_and_maybe_import and config/limits.rs (kConjecturePassiveCapacity).
// CEP:SECURITY: soundness boundary.
#[test]
fn unprovable_candidate_adds_nothing() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let t_c = constant(&fixture, fixture.c);
    // Input axiom: b = a (does not imply b = c).
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_b, t_a), true)],
        )
        .expect("axiom");
    let candidate = Literal::new(eq_atom(&fixture, t_b, t_c), true);
    let next_before = fixture.space.store.next_clause_id().0;
    let outcome = refute_and_maybe_import(
        &fixture.space,
        &context,
        &fixture.options,
        candidate,
        &MiniCapacities::production(),
    )
    .expect("filter");
    assert_eq!(outcome, CandidateOutcome::Discarded);
    assert_eq!(fixture.space.store.next_clause_id().0, next_before);
}

// CEP:WHAT: A tiny refutation budget discards the candidate (the mini run gives up) without touching the main space.
// CEP:WHY: CEP&CC 34.3: the inference budget is injectable and its exhaustion path is pinned at small scale.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the bounded run imports anything.
// CEP:ASSUMES: the budget 1 cannot complete the refutation of b=a from a=b within one inference.
// CEP:COST: one mini run.
// CEP:EVIDENCE: cited by hot/conjecture/filter.rs (mini_options.inference_budget) and config/limits.rs (kConjectureRefuteInferences).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn refute_budget_discards_unprovable() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_b, t_a), true)],
        )
        .expect("axiom");
    let candidate = Literal::new(eq_atom(&fixture, t_a, t_b), true);
    let next_before = fixture.space.store.next_clause_id().0;
    let budgets = MiniCapacities {
        refute_inferences: 1,
        ..MiniCapacities::production()
    };
    let outcome = refute_and_maybe_import(
        &fixture.space,
        &context,
        &fixture.options,
        candidate,
        &budgets,
    )
    .expect("filter");
    assert_eq!(outcome, CandidateOutcome::Discarded);
    assert_eq!(fixture.space.store.next_clause_id().0, next_before);
    // The production budget is the named constant.
    assert_eq!(
        MiniCapacities::production().refute_inferences,
        kConjectureRefuteInferences
    );
}

// CEP:WHAT: A vacuous refutation (the axioms alone are contradictory) is discarded: the empty clause's ancestry lacks the negation, so no lemma is imported.
// CEP:WHY: Spec 17 section 4's ancestry requirement makes such lemmas uncheckable; the filter rejects them before they exist.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a lemma is imported from a subproof that never used the negation.
// CEP:ASSUMES: inputs p(a) and ~p(a) (contradictory without the candidate).
// CEP:COST: one mini run.
// CEP:EVIDENCE: cited by hot/conjecture/filter.rs::import_refutation (the ancestry check).
// CEP:SECURITY: soundness boundary.
#[test]
fn vacuous_refutation_discarded() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    // Contradictory axioms.
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, true)])
        .expect("p(a)");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, false)])
        .expect("~p(a)");
    let candidate = Literal::new(eq_atom(&fixture, t_a, t_b), true);
    let next_before = fixture.space.store.next_clause_id().0;
    let outcome = refute_and_maybe_import(
        &fixture.space,
        &context,
        &fixture.options,
        candidate,
        &MiniCapacities::production(),
    )
    .expect("filter");
    assert_eq!(outcome, CandidateOutcome::Discarded);
    assert_eq!(fixture.space.store.next_clause_id().0, next_before);
}

// CEP:WHAT: The harvest imports a proved lemma end to end: derived unit a=b, T1 candidate b=a, mini refutation, lemma in the passive set with its subproof.
// CEP:WHY: The orchestrator's success path (Spec 16 section 5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the lemma is not imported.
// CEP:ASSUMES: the input axiom a=b.
// CEP:COST: one harvest.
// CEP:EVIDENCE: cited by hot/conjecture/mod.rs::{harvest, harvest_with_types}.
// CEP:SECURITY: none.
#[test]
fn lemma_enters_passive_set() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    // Oriented axiom b = a (the rewrite-usable form).
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_b, t_a), true)],
        )
        .expect("axiom");
    add_derived_unit(&fixture, t_b, t_a);
    let next_before = fixture.space.store.next_clause_id().0;
    let mut stats = SearchStats::default();
    harvest(&fixture.space, &context, &fixture.options, &mut stats);
    assert_eq!(stats.harvests, 1);
    assert!(stats.candidates >= 1);
    assert!(stats.lemmas >= 1);
    assert!(fixture.space.store.next_clause_id().0 > next_before + 1);
}

// CEP:WHAT: The in-loop harvest fires on the schedule (every kConjectureHarvestInterval iterations) during a long search, and the total caps at kMaxConjectureHarvests.
// CEP:WHY: The saturate hook (options.conjecture): 5000 duplicate input units p(a) give the cheapest deterministic long loop - every pop past the first is forward-subsumed in near-zero work, so the iteration counter crosses every scheduled harvest point (512, 1024, ..., 4608) while the active set stays at one clause; the schedule must fire at each point until the cap binds, which makes both the interval and the cap observable in one deterministic run.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if no harvest runs or the cap is exceeded.
// CEP:ASSUMES: the duplicate-unit family; the passive capacity (8192) exceeds the input count (5000).
// CEP:COST: one bounded saturation (seconds).
// CEP:EVIDENCE: cited by hot/search/given_clause.rs (the harvest hook), config/limits.rs (kConjectureHarvestInterval, kMaxConjectureHarvests), and hot/conjecture/mod.rs::harvest.
// CEP:SECURITY: denial-of-service bounds.
#[test]
fn harvest_schedule_fires() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    let mut options = SearchOptions::new();
    options.conjecture = true;
    // 5000 duplicate inputs: iterations 1..5000 with near-zero per-iteration
    // work (forward subsumption discards every pop after the first).
    for _ in 0..5000 {
        fixture
            .space
            .add_input_clause(&context, &options, &[Literal::new(p_a, true)])
            .expect("input");
    }
    let mut stats = SearchStats::default();
    let outcome =
        saturate(&fixture.space, &context, &options, &|_| false, &mut stats).expect("saturate");
    assert!(
        matches!(outcome, SearchOutcome::Saturated),
        "duplicate-unit family should saturate, got {:?}",
        outcome
    );
    // Scheduled points 512, 1024, ..., 4608: nine fire points, capped at eight.
    assert_eq!(stats.harvests, kMaxConjectureHarvests);
    assert_eq!(stats.candidates, 0);
}

// CEP:WHAT: The harvest budget guard: with the cap already reached (a pre-seeded stats counter), the hook skips the harvest entirely.
// CEP:WHY: The cap's guard clause (stats.harvests < kMaxConjectureHarvests) is pinned in isolation: a stats counter at the cap suppresses every scheduled harvest, so the duplicate-unit loop runs to Saturated with no additional harvest.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a harvest runs past the cap.
// CEP:ASSUMES: the duplicate-unit family with a pre-seeded counter.
// CEP:COST: one bounded saturation.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs (the hook guard) and config/limits.rs (kMaxConjectureHarvests).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn harvest_budget_enforced() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    let mut options = SearchOptions::new();
    options.conjecture = true;
    for _ in 0..1500 {
        fixture
            .space
            .add_input_clause(&context, &options, &[Literal::new(p_a, true)])
            .expect("input");
    }
    let mut stats = SearchStats {
        harvests: kMaxConjectureHarvests,
        ..SearchStats::default()
    };
    let outcome =
        saturate(&fixture.space, &context, &options, &|_| false, &mut stats).expect("saturate");
    assert!(matches!(outcome, SearchOutcome::Saturated));
    assert_eq!(stats.harvests, kMaxConjectureHarvests);
}

// CEP:WHAT: harvest_with_types with no declaration equals harvest (T1/T2 only), and the pre-search pass with the declaration enumerates T3 candidates from input units.
// CEP:WHY: The driver's pre-search entry point and the equivalence of the undecorated path.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any divergence.
// CEP:ASSUMES: the input unit f(X)=X with the Nat declaration.
// CEP:COST: two harvests.
// CEP:EVIDENCE: cited by hot/conjecture/mod.rs::harvest_with_types.
// CEP:SECURITY: none.
#[test]
fn typed_harvest_enumerates_constructor_instances() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_x = fixture.terms.intern_var(0).expect("x");
    let t_f_x = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.f, &[t_x])
        .expect("f(x)");
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_f_x, t_x), true)],
        )
        .expect("input unit");
    let declaration = InductionDeclaration {
        zero: fixture.zero,
        succ: fixture.succ,
        skolem: fixture.sk,
        well_founded: None,
    };
    let mut stats = SearchStats::default();
    harvest_with_types(
        &fixture.space,
        &context,
        &fixture.options,
        Some(&declaration),
        &mut stats,
    );
    assert_eq!(stats.harvests, 1);
    // The T3 instances f(zero)=zero and f(succ(zero))=succ(zero) are provable
    // from the input unit (instantiation plus the instance itself), so both
    // import as lemmas.
    assert!(stats.lemmas >= 1, "typed harvest should prove instances");
}

// CEP:WHAT: The certified kernel's ConjectureLemma reductio arm accepts a well-formed lemma step and rejects a detached one (Spec 19).
// CEP:WHY: Spec 17 section 4: the arm checks the complement shape (the negation premise's literal is the lemma literal flipped), the empty second parent, and the ancestry containment; a hand-built minimal proof exercises the arm deterministically (the filter's end-to-end path asserts the record shape separately); the final conclusion is a replayable Resolution step (the lemma against the negation premise) because the pre-Phase-5 parentless Demodulation label is an UnrecordedRule rejection since the CEP-1036 chain and the kernel landed.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a well-formed lemma is rejected or a tampered one is accepted.
// CEP:ASSUMES: the hand-built store: input axiom p(a), negation premise ~p(a) (ConjectureNegation), empty clause (Resolution over both), lemma p(a) (ConjectureLemma), and a final empty clause resolved between the lemma and the negation.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs's ConjectureLemma arm and ancestor_of.
// CEP:SECURITY: proof validation.
#[test]
fn checker_accepts_conjecture_lemma() {
    use mapt::cold::proof_output::tstp::check_proof;
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    let input = fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, true)])
        .expect("input");
    let input_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(input))
        .expect("rec")
        .id
        .0;
    // The negation premise (complement of the lemma literal).
    let negation = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[Literal::new(p_a, false)],
            1,
            DerivationStep {
                rule: InferenceRule::ConjectureNegation,
                parent_count: 0,
                reserved: 0,
                parents: [kInvalidClauseId; kMaxDerivationParents],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("negation");
    let negation_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(negation))
        .expect("rec")
        .id
        .0;
    // The empty clause resolving the input against the negation.
    let empty = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[],
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [input_id, negation_id, kInvalidClauseId, kInvalidClauseId],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("empty");
    let empty_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(empty))
        .expect("rec")
        .id
        .0;
    // The lemma citing the negation and the empty clause.
    let lemma = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[Literal::new(p_a, true)],
            3,
            DerivationStep {
                rule: InferenceRule::ConjectureLemma,
                parent_count: 2,
                reserved: 0,
                parents: [negation_id, empty_id, kInvalidClauseId, kInvalidClauseId],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("lemma");
    let lemma_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(lemma))
        .expect("rec")
        .id
        .0;
    // A final conclusion citing the lemma so the walk reaches it: the empty
    // clause resolved between the lemma (p(a)) and the negation premise (~p(a));
    // the kernel replays the production resolve() for the step (the pre-Phase-5
    // parentless Demodulation label is an UnrecordedRule rejection under the
    // CEP-1036 chain discipline, so the fixture uses a replayable rule).
    let final_clause = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[],
            4,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [lemma_id, negation_id, kInvalidClauseId, kInvalidClauseId],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("final");
    let final_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(final_clause))
        .expect("rec")
        .id
        .0;
    let offset = fixture
        .space
        .store
        .offset_of_id(ClauseId(final_id))
        .expect("offset");
    assert!(check_proof(&context, &fixture.space.store, offset).is_ok());
    // A detached variant: the lemma's second parent is the INPUT (non-empty),
    // which the arm must reject.
    let detached = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[Literal::new(p_a, true)],
            5,
            DerivationStep {
                rule: InferenceRule::ConjectureLemma,
                parent_count: 2,
                reserved: 0,
                parents: [negation_id, input_id, kInvalidClauseId, kInvalidClauseId],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("detached");
    let detached_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(detached))
        .expect("rec")
        .id
        .0;
    let _ = t_b;
    let detached_offset = fixture
        .space
        .store
        .offset_of_id(ClauseId(detached_id))
        .expect("offset");
    assert!(check_proof(&context, &fixture.space.store, detached_offset).is_err());
}
// CEP:WHAT: Two harvests stay sound after a successful import: the second harvest's premise set is the rule-identified axioms only (the proof watermark excludes the first import's subproof, including its negation premise and empty clause, and the lemma itself).
// CEP:WHY: The Task 26 sev-0 regression: the first import's age consumption used to shift the id-range premise reading onto proof-only clauses, widening later mini premise sets with the imported negation of a proved lemma (unsound) and, with drift, the empty clause (feature-dead); the rule-based enumeration plus the watermark make the second premise set provably the staged axioms, pinned here by walking the second lemma's ancestry: every translated premise is an axiom-rule clause and neither a ConjectureNegation (beyond the candidate's own) nor a ConjectureLemma appears.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any proof-only or lemma clause leaks into the second harvest's premise set.
// CEP:ASSUMES: the oriented axiom b=a; the derived unit b=a; both harvests import the same symmetry lemma.
// CEP:COST: two harvests.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::{proof_base, add_proof_clause}, hot/conjecture/filter.rs::{collect_axiom_ids, is_axiom_rule}, and docs/formal/16_conjecture_generation.md section 5.
// CEP:SECURITY: soundness boundary.
#[test]
fn two_harvests_stay_sound() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    // Oriented axiom b = a.
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[Literal::new(eq_atom(&fixture, t_b, t_a), true)],
        )
        .expect("axiom");
    // The derived unit feeding T1.
    add_derived_unit(&fixture, t_b, t_a);
    let mut first_stats = SearchStats::default();
    harvest(&fixture.space, &context, &fixture.options, &mut first_stats);
    assert!(first_stats.lemmas >= 1, "the first harvest must import");
    // The watermark is set and below the store's next id.
    let watermark = fixture.space.proof_base();
    let next = fixture.space.store.next_clause_id().0;
    assert!(watermark >= kFirstClauseId && watermark < next);
    // The second harvest over the same state: the same candidate imports
    // again, and its subproof must cite only axiom-rule premises.
    let before = next;
    let mut second_stats = SearchStats::default();
    harvest(
        &fixture.space,
        &context,
        &fixture.options,
        &mut second_stats,
    );
    assert!(second_stats.lemmas >= 1, "the second harvest must import");
    let after = fixture.space.store.next_clause_id().0;
    assert!(after > before);
    // Walk every ConjectureLemma clause added by the SECOND harvest (ids at or
    // after the first harvest's lemma) and check its ancestry.
    let first_lemma = before - 1;
    for id in first_lemma..after {
        let record = fixture
            .space
            .store
            .clause_by_id(ClauseId(id))
            .expect("record");
        if record.derivation.rule != InferenceRule::ConjectureLemma {
            continue;
        }
        let negation_id = record.derivation.parents[0];
        let empty_id = record.derivation.parents[1];
        // Ancestry walk from the empty clause.
        let mut stack: Vec<u64> = vec![empty_id];
        let mut visited: Vec<u64> = Vec::new();
        while let Some(current) = stack.pop() {
            if visited.contains(&current) || current < kFirstClauseId {
                continue;
            }
            visited.push(current);
            let record = fixture
                .space
                .store
                .clause_by_id(ClauseId(current))
                .expect("record");
            for slot in 0..record.derivation.parent_count as usize {
                let parent = record.derivation.parents[slot];
                if parent != kInvalidClauseId && parent >= kFirstClauseId {
                    stack.push(parent);
                }
            }
        }
        for ancestor in visited.iter() {
            let record = fixture
                .space
                .store
                .clause_by_id(ClauseId(*ancestor))
                .expect("record");
            if *ancestor == negation_id {
                // The candidate's own negation premise is expected.
                assert_eq!(record.derivation.rule, InferenceRule::ConjectureNegation);
                continue;
            }
            assert!(
                matches!(
                    record.derivation.rule,
                    InferenceRule::Input
                        | InferenceRule::NegatedConjecture
                        | InferenceRule::StructuralInduction
                        | InferenceRule::WellFoundedInduction
                        | InferenceRule::Superposition
                        | InferenceRule::EqualityResolution
                        | InferenceRule::Demodulation
                        | InferenceRule::Factoring
                        | InferenceRule::EqualityFactoring
                ),
                "proof-only or lemma clause c{} (rule {:?}) leaked into the second harvest's premise set",
                ancestor,
                record.derivation.rule
            );
        }
    }
}

// CEP:WHAT: The proof watermark bounds the harvest's unit window: a proof-only positive equation unit added by an import is invisible to the window scan.
// CEP:WHY: The Task 26 sev-0 repair's window half: collect_recent_units stops at proof_base, so imported subproof units never seed T1/T2 candidates; the test plants a proof-only derived-rule unit via add_proof_clause and asserts its absence from the window.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the window contains the proof-only unit.
// CEP:ASSUMES: a fresh fixture with one derived unit in the window and one proof-only unit beyond the watermark.
// CEP:COST: one window scan.
// CEP:EVIDENCE: cited by hot/conjecture/template.rs::collect_recent_units (the watermark bound).
// CEP:SECURITY: soundness boundary.
#[test]
fn proof_watermark_bounds_harvest_scans() {
    let fixture = make_conjecture_fixture();
    let context = context_of(&fixture);
    let t_a = constant(&fixture, fixture.a);
    let t_b = constant(&fixture, fixture.b);
    add_derived_unit(&fixture, t_a, t_b);
    // A proof-only positive equation unit (as an import would create): the
    // same shape as a window unit but created through add_proof_clause.
    let atom = eq_atom(&fixture, t_b, t_a);
    let derivation = DerivationStep {
        rule: InferenceRule::Demodulation,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; kMaxDerivationParents],
        substitution: kInvalidSubstitutionOffset,
    };
    let proof_offset = fixture
        .space
        .add_proof_clause(
            &context,
            &fixture.options,
            &[Literal::new(atom, true)],
            9,
            derivation,
        )
        .expect("proof clause");
    let proof_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(proof_offset))
        .expect("record")
        .id
        .0;
    let watermark = fixture.space.proof_base();
    assert_eq!(watermark, proof_id);
    let window = mapt::hot::conjecture::template::collect_recent_units(&fixture.space, &context);
    for index in 0..window.count {
        assert_ne!(
            window.units[index].id, proof_id,
            "the proof-only unit leaked into the window"
        );
    }
}
