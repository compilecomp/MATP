// CEP:FILE: tests/security/induction_conjecture_bounds_test.rs
// CEP:WHAT: Security bounds tests of the Phase 4 (revised build order) features: the induction attempts and scan budgets at small scales, the declaration validation matrix, and the conjecture mini-space capacity exhaustions (passive, active, id table) with injectable MiniCapacities.
// CEP:WHY: CEP&CC 34.3 (every budget injectable, every exhaustion path exercised at small scale on the production path) and 22.10 (bounded work as a denial-of-service guard): each named constant's exhaustion must be observable, loud, and isolated - a bounded discard never kills the main search.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any bound violation.
// CEP:ASSUMES: the fixture vocabulary shared with unit/hot/conjecture_test.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by config/limits.rs (the kConjecture* and kInduction* constants) and hot/conjecture/filter.rs (MiniCapacities).
// CEP:SECURITY: every test here pins a resource-exhaustion guard.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::conjecture::filter::{refute_and_maybe_import, CandidateOutcome, MiniCapacities};
use mapt::hot::induction::{add_induction_schemes, InductionDeclaration, InductionError};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::SearchOptions;
use mapt::hot::search::SearchSpace;
use mapt_config::limits::{kFirstClauseId, kInductionScanNodeBudget};

// CEP:WHAT: Arena bytes for the bounds fixture.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kBoundsArena: u32 = 50_331_648;

// CEP:WHAT: The bounds fixture: a/b constants, zero/sk, succ, p/1.
// CEP:WHY: One vocabulary serves the induction and conjecture bound tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
struct BoundsFixture {
    space: SearchSpace<'static>,
    symbols: SymbolTable<'static>,
    terms: TermStore<'static>,
    precedence: PrecedenceTable<'static>,
    options: SearchOptions,
    zero: u32,
    succ: u32,
    sk: u32,
    a: u32,
    b: u32,
    p: u32,
}

// CEP:WHAT: Builds the bounds fixture.
// CEP:WHY: One constructor for this file.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn make_bounds_fixture() -> BoundsFixture {
    let region = allocate_aligned_region(kBoundsArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let a = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let b = builder.declare_function("b", 0, 1, &[], sort_s).expect("b");
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_s)
        .expect("zero");
    let sk = builder
        .declare_function("sk", 0, 1, &[], sort_s)
        .expect("sk");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_s], sort_s)
        .expect("succ");
    let p = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    BoundsFixture {
        space,
        symbols,
        terms,
        precedence,
        options,
        zero,
        succ,
        sk,
        a,
        b,
        p,
    }
}

// CEP:WHAT: The fixture's inference context.
// CEP:WHY: Shared accessor.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
fn context_of(fixture: &BoundsFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Adds the induction-flagship inputs (base, step, negated conjecture over p).
// CEP:WHY: The bound tests need a problem with one occurring unary predicate.
// CEP:STATUS: complete
// CEP:FAILURE: panics on add failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: three adds.
// CEP:EVIDENCE: used by the induction bound tests.
// CEP:SECURITY: none.
fn add_flagship_inputs(fixture: &BoundsFixture) {
    let context = context_of(fixture);
    let t_a = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.a, &[])
        .expect("a");
    let t_zero = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.zero, &[])
        .expect("zero");
    let t_x = fixture.terms.intern_var(0).expect("x");
    let t_succ_x = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.succ, &[t_x])
        .expect("succ(x)");
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    let p_zero = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_zero])
        .expect("p(zero)");
    let p_x = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_x])
        .expect("p(x)");
    let p_succ_x = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_succ_x])
        .expect("p(s(x))");
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
        .expect("negated");
}

// CEP:WHAT: The induction attempts budget is enforced at small scales: budget 0 adds nothing and counts the skip.
// CEP:WHY: CEP&CC 34.3: the injectable bound at its degenerate minimum.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added at budget 0.
// CEP:ASSUMES: one occurring unary predicate.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs (kMaxInductionAttempts) and hot/induction/mod.rs::add_induction_schemes.
// CEP:SECURITY: denial-of-service bound.
#[test]
fn induction_attempts_enforced() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    add_flagship_inputs(&fixture);
    let stats = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &InductionDeclaration {
            zero: fixture.zero,
            succ: fixture.succ,
            skolem: fixture.sk,
            well_founded: None,
        },
        0,
        kInductionScanNodeBudget,
    )
    .expect("schemes");
    assert_eq!(stats.structural_schemes, 0);
    assert_eq!(stats.predicates_skipped, 1);
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 3);
}

// CEP:WHAT: The declaration validation matrix rejects every malformed shape before any scheme exists.
// CEP:WHY: The soundness trust boundary under the full rejection matrix (zero/succ/skolem/well-founded shapes, including unknown symbol ids).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any malformed declaration is accepted.
// CEP:ASSUMES: fixture vocabulary.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::validate_declaration.
// CEP:SECURITY: input validation.
#[test]
fn declaration_matrix_rejects_malformed_shapes() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    add_flagship_inputs(&fixture);
    let good = InductionDeclaration {
        zero: fixture.zero,
        succ: fixture.succ,
        skolem: fixture.sk,
        well_founded: None,
    };
    // Unknown symbols.
    let unknown = 900_000;
    for (zero, succ, skolem) in [
        (unknown, fixture.succ, fixture.sk),
        (fixture.zero, unknown, fixture.sk),
        (fixture.zero, fixture.succ, unknown),
    ] {
        let bad = InductionDeclaration {
            zero,
            succ,
            skolem,
            well_founded: None,
        };
        let result = add_induction_schemes(
            &fixture.space,
            &context,
            &fixture.options,
            &bad,
            128,
            kInductionScanNodeBudget,
        );
        assert!(
            matches!(
                result,
                Err(InductionError::ZeroNotConstant)
                    | Err(InductionError::SuccNotUnary)
                    | Err(InductionError::SkolemNotConstant)
            ),
            "unknown symbol must be rejected"
        );
    }
    // Well-founded shape.
    let mut bad_wf = good;
    bad_wf.well_founded = Some(fixture.p);
    assert_eq!(
        add_induction_schemes(
            &fixture.space,
            &context,
            &fixture.options,
            &bad_wf,
            128,
            kInductionScanNodeBudget
        ),
        Err(InductionError::WellFoundedNotBinary)
    );
    // Nothing was added by any rejected call.
    assert_eq!(fixture.space.store.next_clause_id().0, kFirstClauseId + 3);
}

// CEP:WHAT: The scan node budget is enforced at small scale (budget 1 rejects, budget 2 covers the p(zero) input).
// CEP:WHY: CEP&CC 34.3: the injectable walk bound.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the budget is not enforced or the count is off.
// CEP:ASSUMES: the flagship inputs (the p(zero) atom is one predicate node plus one constant child).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs (kInductionScanNodeBudget) and hot/induction/mod.rs::{scan_input_signature, walk_term}.
// CEP:SECURITY: denial-of-service bound.
#[test]
fn harvest_scan_budget_enforced() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    add_flagship_inputs(&fixture);
    // Budget 1: the first atom's predicate node alone exceeds it.
    let result = add_induction_schemes(
        &fixture.space,
        &context,
        &fixture.options,
        &InductionDeclaration {
            zero: fixture.zero,
            succ: fixture.succ,
            skolem: fixture.sk,
            well_founded: None,
        },
        128,
        1,
    );
    assert_eq!(result, Err(InductionError::ScanBudgetExceeded));
}

// CEP:WHAT: A tiny mini passive capacity discards the candidate (the mini run cannot hold its premises) without touching the main store.
// CEP:WHY: CEP&CC 34.3: the injectable passive bound at exhaustion; the discard isolation is the security property.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added or the filter errors.
// CEP:ASSUMES: two inputs plus the assumption exceed a passive capacity of 2.
// CEP:COST: one filter run.
// CEP:EVIDENCE: cited by config/limits.rs (kConjecturePassiveCapacity) and hot/conjecture/filter.rs (MiniCapacities).
// CEP:SECURITY: memory bound.
#[test]
fn mini_passive_capacity_discards() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    let t_a = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.a, &[])
        .expect("a");
    let t_b = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.b, &[])
        .expect("b");
    let eq_ba = fixture
        .terms
        .intern_eq(&fixture.symbols, t_b, t_a)
        .expect("eq(b,a)");
    let p_a = fixture
        .terms
        .intern_pred(&fixture.symbols, fixture.p, &[t_a])
        .expect("p(a)");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(eq_ba, true)])
        .expect("axiom");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(p_a, true)])
        .expect("axiom 2");
    let candidate = Literal::new(
        fixture
            .terms
            .intern_eq(&fixture.symbols, t_a, t_b)
            .expect("eq(a,b)"),
        true,
    );
    let before = fixture.space.store.next_clause_id().0;
    let budgets = MiniCapacities {
        passive: 2,
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
    assert_eq!(fixture.space.store.next_clause_id().0, before);
}

// CEP:WHAT: A tiny mini active capacity discards the candidate as well.
// CEP:WHY: The active bound's exhaustion path (the mini activation overflows during the bounded run).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added.
// CEP:ASSUMES: the refutation's activation chain exceeds an active capacity of 1.
// CEP:COST: one filter run.
// CEP:EVIDENCE: cited by config/limits.rs (kConjectureActiveCapacity).
// CEP:SECURITY: memory bound.
#[test]
fn mini_active_capacity_discards() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    let t_a = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.a, &[])
        .expect("a");
    let t_b = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.b, &[])
        .expect("b");
    let eq_ba = fixture
        .terms
        .intern_eq(&fixture.symbols, t_b, t_a)
        .expect("eq(b,a)");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(eq_ba, true)])
        .expect("axiom");
    let candidate = Literal::new(
        fixture
            .terms
            .intern_eq(&fixture.symbols, t_a, t_b)
            .expect("eq(a,b)"),
        true,
    );
    let before = fixture.space.store.next_clause_id().0;
    let budgets = MiniCapacities {
        active: 1,
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
    assert_eq!(fixture.space.store.next_clause_id().0, before);
}

// CEP:WHAT: A tiny mini id-table capacity discards the candidate.
// CEP:WHY: The id-side-table bound's exhaustion path (the import rejects a span beyond the injected capacity).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added.
// CEP:ASSUMES: the subproof spans more ids than the injected capacity allows the import to walk.
// CEP:COST: one filter run.
// CEP:EVIDENCE: cited by config/limits.rs (kConjectureIdOffsets) and hot/conjecture/filter.rs::import_refutation.
// CEP:SECURITY: memory bound.
#[test]
fn mini_id_table_discards() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    let t_a = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.a, &[])
        .expect("a");
    let t_b = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.b, &[])
        .expect("b");
    let eq_ba = fixture
        .terms
        .intern_eq(&fixture.symbols, t_b, t_a)
        .expect("eq(b,a)");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(eq_ba, true)])
        .expect("axiom");
    let candidate = Literal::new(
        fixture
            .terms
            .intern_eq(&fixture.symbols, t_a, t_b)
            .expect("eq(a,b)"),
        true,
    );
    let before = fixture.space.store.next_clause_id().0;
    let budgets = MiniCapacities {
        id_offsets: 1,
        ..MiniCapacities::production()
    };
    // The mini space cannot even hold axiom plus assumption: discarded.
    let outcome = refute_and_maybe_import(
        &fixture.space,
        &context,
        &fixture.options,
        candidate,
        &budgets,
    )
    .expect("filter");
    assert_eq!(outcome, CandidateOutcome::Discarded);
    assert_eq!(fixture.space.store.next_clause_id().0, before);
}

// CEP:WHAT: The tree budgets (nodes, entries, pool words) at exhaustion discard without touching the main store.
// CEP:WHY: The remaining mini capacity bounds' exhaustion paths, exercised together (each individually through production-minus-one shapes would need problem-specific tuning; the joint tiny injection pins all three paths at once).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if anything is added.
// CEP:ASSUMES: the tiny budgets cannot host the mini active set's indexing.
// CEP:COST: one filter run.
// CEP:EVIDENCE: cited by config/limits.rs (kConjectureTreeNodes, kConjectureTreeEntries, kConjecturePoolWords).
// CEP:SECURITY: memory bound.
#[test]
fn mini_tree_budget_discards() {
    let fixture = make_bounds_fixture();
    let context = context_of(&fixture);
    let t_a = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.a, &[])
        .expect("a");
    let t_b = fixture
        .terms
        .intern_fun(&fixture.symbols, fixture.b, &[])
        .expect("b");
    let eq_ba = fixture
        .terms
        .intern_eq(&fixture.symbols, t_b, t_a)
        .expect("eq(b,a)");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(eq_ba, true)])
        .expect("axiom");
    let candidate = Literal::new(
        fixture
            .terms
            .intern_eq(&fixture.symbols, t_a, t_b)
            .expect("eq(a,b)"),
        true,
    );
    let before = fixture.space.store.next_clause_id().0;
    let budgets = MiniCapacities {
        tree_nodes: 1,
        tree_entries: 1,
        pool_words: 1,
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
    // Whatever the exhaustion order (construction, activation, or import), the
    // candidate is discarded and the main store is untouched.
    assert_ne!(outcome, CandidateOutcome::Imported);
    assert_eq!(fixture.space.store.next_clause_id().0, before);
}
