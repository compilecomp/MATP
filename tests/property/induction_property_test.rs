// CEP:FILE: tests/property/induction_property_test.rs
// CEP:WHAT: Property tests of automated induction: the generated scheme clauses equal the hand clausification of the induction-axiom instance for random predicate and declaration choices, the scheme installation is deterministic across double runs, and the attempts bound is respected for random budgets.
// CEP:WHY: Design 26 (revised build order Phase 4) and Spec 15: the scheme builders are the soundness-critical core; the correspondence property (generated == hand clausification) is the executable witness of Spec 15 sections 3-4, the determinism property pins CEP&CC 38.10 at the module level, and the bound property pins Law 4's counted skips.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: the fixture vocabulary of unit/hot/induction_test.rs (mirrored here); the deterministic RNG from tests/common.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/induction/mod.rs and hot/induction/scheme.rs property pointers.
// CEP:SECURITY: the bound property exercises the denial-of-service guard.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::DeterministicRng;
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::induction::{add_induction_schemes, InductionDeclaration};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::SearchSpace;
use mapt::hot::search::SearchOptions;
use mapt_config::limits::{kFirstClauseId, kInductionScanNodeBudget, kMaxInductionAttempts};

// CEP:WHAT: Arena bytes for the property fixture.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyArena: u32 = 25_165_824;

// CEP:WHAT: The property fixture: zero/succ/sk/a constants, succ unary, p/q/lt predicates over one sort.
// CEP:WHY: The same vocabulary as the unit tests so the hand-clausification oracle is shared by construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every property.
// CEP:SECURITY: none.
struct PropertyFixture {
    space: SearchSpace<'static>,
    symbols: SymbolTable<'static>,
    terms: TermStore<'static>,
    precedence: PrecedenceTable<'static>,
    options: SearchOptions,
    zero: u32,
    succ: u32,
    sk: u32,
    p: u32,
    q: u32,
    lt: u32,
}

// CEP:WHAT: Builds the property fixture with random unary-predicate occurrences.
// CEP:WHY: Each property run draws which predicates occur (p, q, or both) so the enumeration domain varies.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every property.
// CEP:SECURITY: none.
fn make_property_fixture(rng: &mut DeterministicRng) -> PropertyFixture {
    let region = allocate_aligned_region(kPropertyArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_n = SortId(builder.declare_sort("N").expect("sort"));
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
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    // Random occurrences: each of p, q occurs at zero, a, or succ(a).
    let t_zero = terms.intern_fun(&symbols, zero, &[]).expect("z");
    let t_a = terms.intern_fun(&symbols, a, &[]).expect("a");
    let t_succ_a = terms.intern_fun(&symbols, succ, &[t_a]).expect("s(a)");
    let grounds = [t_zero, t_a, t_succ_a];
    for predicate in [p, q] {
        let draws = 1 + rng.below(3);
        for _ in 0..draws {
            let arg = grounds[rng.below(3) as usize];
            let atom = terms
                .intern_pred(&symbols, predicate, &[arg])
                .expect("atom");
            space
                .add_input_clause(&context, &options, &[Literal::new(atom, rng.below(2) == 0)])
                .expect("input");
        }
    }
    PropertyFixture {
        space,
        symbols,
        terms,
        precedence,
        options,
        zero,
        succ,
        sk,
        p,
        q,
        lt,
    }
}

// CEP:WHAT: Reads one clause's literal (atom, polarity) multiset by id.
// CEP:WHY: The correspondence oracle's reader.
// CEP:STATUS: complete
// CEP:FAILURE: panics on read failure.
// CEP:ASSUMES: live id.
// CEP:COST: O(literals).
// CEP:EVIDENCE: used by the correspondence property.
// CEP:SECURITY: none.
fn read_literals(fixture: &PropertyFixture, id: u64) -> Vec<(TermPtr, bool)> {
    let record = fixture
        .space
        .store
        .clause_by_id(mapt::hot::ir::clause::ClauseId(id))
        .expect("clause");
    let mut out = Vec::new();
    for index in 0..record.literal_count {
        let literal = fixture.space.store.literal(record, index).expect("lit");
        out.push((literal.atom(), literal.is_positive()));
    }
    out
}

// CEP:WHAT: For random fixtures and declarations (with and without the well-order), every generated scheme clause equals the hand clausification of the corresponding induction-axiom instance for its predicate.
// CEP:WHY: Spec 15 sections 3-4's correspondence theorem, executed: the builder's output is pinned against the independently written expected clauses for arbitrary predicate choices, so any builder drift fails the property.
// CEP:STATUS: complete
// CEP:FAILURE: property fails on any literal mismatch.
// CEP:ASSUMES: the scheme ids directly follow the inputs (the installer appends in scan order).
// CEP:COST: K runs x small fixtures.
// CEP:EVIDENCE: cited by hot/induction/scheme.rs (file header HPC-PASS-LEGALITY) and docs/formal/15_structural_induction.md sections 3-4.
// CEP:SECURITY: none.
#[test]
fn schemes_match_hand_clausification() {
    let mut rng = DeterministicRng::new(0x15_C0_FF_EE);
    for run in 0..12 {
        let fixture = make_property_fixture(&mut rng);
        let context = InferenceContext {
            terms: &fixture.terms,
            symbols: &fixture.symbols,
            substitution: &fixture.space.substitution,
            precedence: &fixture.precedence,
            ordering: OrderingKind::Kbo,
        };
        let with_order = run % 2 == 0;
        let declaration = InductionDeclaration {
            zero: fixture.zero,
            succ: fixture.succ,
            skolem: fixture.sk,
            well_founded: if with_order { Some(fixture.lt) } else { None },
        };
        // Capture the input range BEFORE the installation: add_theory_clause
        // consumes input ages, so input_count() afterwards includes the
        // schemes (the installer's ids start right after the last input).
        let input_end = kFirstClauseId + fixture.space.input_count() as u64;
        let stats = add_induction_schemes(
            &fixture.space,
            &context,
            &fixture.options,
            &declaration,
            kMaxInductionAttempts,
            kInductionScanNodeBudget,
        )
        .expect("schemes");
        // Hand clausification oracle for every covered predicate (ascending
        // symbol id: p before q).
        let t_zero = fixture
            .terms
            .intern_fun(&fixture.symbols, fixture.zero, &[])
            .expect("z");
        let t_sk = fixture
            .terms
            .intern_fun(&fixture.symbols, fixture.sk, &[])
            .expect("sk");
        let t_succ_sk = fixture
            .terms
            .intern_fun(&fixture.symbols, fixture.succ, &[t_sk])
            .expect("s(sk)");
        let mut next_id = input_end;
        // Both p and q occur by construction (the fixture adds inputs for
        // each), so the installer covers both, ascending by symbol id.
        for predicate in [fixture.p, fixture.q] {
            let t_x = fixture.terms.intern_var(0).expect("X");
            let t_y = fixture.terms.intern_var(0).expect("Y");
            let t_x1 = fixture.terms.intern_var(1).expect("X1");
            let p_z = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_zero])
                .expect("p(z)");
            let p_sk = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_sk])
                .expect("p(sk)");
            let p_szk = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_succ_sk])
                .expect("p(s(sk))");
            let p_x = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_x])
                .expect("p(X)");
            let p_y = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_y])
                .expect("p(Y)");
            let p_x1 = fixture
                .terms
                .intern_pred(&fixture.symbols, predicate, &[t_x1])
                .expect("p(X1)");
            let first = read_literals(&fixture, next_id);
            assert_eq!(first.len(), 3, "run {} clause {}", run, next_id);
            for expected in [(p_z, false), (p_sk, true), (p_x, true)] {
                assert!(
                    first.contains(&expected),
                    "run {} clause {} missing {:?}",
                    run,
                    next_id,
                    expected
                );
            }
            next_id += 1;
            let second = read_literals(&fixture, next_id);
            assert_eq!(second.len(), 3);
            for expected in [(p_z, false), (p_szk, false), (p_x, true)] {
                assert!(
                    second.contains(&expected),
                    "run {} clause {} missing {:?}",
                    run,
                    next_id,
                    expected
                );
            }
            next_id += 1;
            if with_order {
                let lt_y_sk = fixture
                    .terms
                    .intern_pred(&fixture.symbols, fixture.lt, &[t_y, t_sk])
                    .expect("lt(Y,sk)");
                let third = read_literals(&fixture, next_id);
                assert_eq!(third.len(), 3);
                for expected in [(lt_y_sk, false), (p_y, true), (p_x1, true)] {
                    assert!(
                        third.contains(&expected),
                        "run {} clause {} missing {:?}",
                        run,
                        next_id,
                        expected
                    );
                }
                next_id += 1;
                let p_x0 = fixture
                    .terms
                    .intern_pred(&fixture.symbols, predicate, &[t_y])
                    .expect("p(X0)");
                let fourth = read_literals(&fixture, next_id);
                assert_eq!(fourth.len(), 2);
                for expected in [(p_sk, false), (p_x0, true)] {
                    assert!(
                        fourth.contains(&expected),
                        "run {} clause {} missing {:?}",
                        run,
                        next_id,
                        expected
                    );
                }
                next_id += 1;
            }
        }
        assert_eq!(
            next_id,
            fixture.space.store.next_clause_id().0,
            "run {}: installed clause count mismatch",
            run
        );
        assert_eq!(stats.predicates_skipped, 0);
    }
}

// CEP:WHAT: The scheme installation is deterministic: identical random fixtures produce identical clause-id sequences and identical stats.
// CEP:WHY: CEP&CC 38.10: the two-run discipline at the module level.
// CEP:STATUS: complete
// CEP:FAILURE: property fails on any divergence.
// CEP:ASSUMES: same seed -> same fixture.
// CEP:COST: double runs.
// CEP:EVIDENCE: cited by hot/induction/mod.rs (file header HPC-DETERMINISM).
// CEP:SECURITY: none.
#[test]
fn induction_deterministic_double_run() {
    for seed in [0x11_A2_B3_C4, 0x5D_6E_7F_80] {
        let run = || {
            let mut rng = DeterministicRng::new(seed);
            let fixture = make_property_fixture(&mut rng);
            let context = InferenceContext {
                terms: &fixture.terms,
                symbols: &fixture.symbols,
                substitution: &fixture.space.substitution,
                precedence: &fixture.precedence,
                ordering: OrderingKind::Kbo,
            };
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
            (stats, fixture.space.store.next_clause_id().0)
        };
        let first = run();
        let second = run();
        assert_eq!(first, second, "seed {:x}", seed);
    }
}

// CEP:WHAT: For random budgets, the installed scheme count never exceeds the budget and the skips are counted.
// CEP:WHY: Law 4 + CEP&CC 22.10: the attempts bound holds under arbitrary injectable values.
// CEP:STATUS: complete
// CEP:FAILURE: property fails if the bound is exceeded or the accounting is silent.
// CEP:ASSUMES: both predicates occur in every fixture.
// CEP:COST: K runs.
// CEP:EVIDENCE: cited by hot/induction/mod.rs::add_induction_schemes and config/limits.rs (kMaxInductionAttempts).
// CEP:SECURITY: denial-of-service bound.
#[test]
fn attempts_bound_respected() {
    let mut rng = DeterministicRng::new(0x9A_8B_7C_6D);
    for _ in 0..10 {
        let fixture = make_property_fixture(&mut rng);
        let context = InferenceContext {
            terms: &fixture.terms,
            symbols: &fixture.symbols,
            substitution: &fixture.space.substitution,
            precedence: &fixture.precedence,
            ordering: OrderingKind::Kbo,
        };
        let budget = 1 + rng.below(16) as u32;
        let before = fixture.space.store.next_clause_id().0;
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
            budget,
            kInductionScanNodeBudget,
        )
        .expect("schemes");
        let after = fixture.space.store.next_clause_id().0;
        assert!(after - before <= budget as u64);
        assert!(stats.structural_schemes <= budget);
        let covered = stats.structural_schemes / 2;
        assert_eq!(
            stats.predicates_skipped,
            stats.unary_predicates.saturating_sub(covered)
        );
    }
}
