// CEP:FILE: tests/unit/hot/avatar_learning_test.rs
// CEP:WHAT: Unit tests for bidirectional FOL clause learning over AVATAR (Spec 18): conflict lemma staging and kernel verification, the staging and transfer budgets with counted skips, the transfer policy filters (length, LBD, nameable slots), the passive-set entry of transferred clauses, and the disabled-by-default guarantee.
// CEP:WHY: Spec 18 sections 4-6 and CEP&CC 34.3: every learning path is bounded, counted, and opt-in; the tests exercise each bound at small scales on the production code path and pin the record shapes the certified kernel verifies.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: the pigeonhole fixture from the controller test refutes with via_avatar = true; assertion symbols are reserved before finalize.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/avatar/controller.rs and docs/formal/18_fol_clause_learning.md.
// CEP:SECURITY: every budget and skip counter is exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, symbol_id};
use mapt::cold::kernel::{verify_clause_step_with_options, KernelOptions, KernelVerdict};
use mapt::hot::avatar::controller::{
    saturate_with_avatar, AvatarController, AvatarOptions, AvatarOutcome,
};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClauseId, ClausePtr, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::sat::clause::ClauseStorage;
use mapt::hot::sat::database::AttachOutcome;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::search::given_clause::{SearchOptions, SearchSpace, SearchStats};

const kLearningArenaBytes: u32 = 50_331_648;
const kLearningSymbolCount: u32 = 8;

struct LearningFixture {
    space: SearchSpace<'static>,
    controller: AvatarController<'static>,
    symbols: mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: mapt::cold::symbol_table_builder::SymbolTableBuilder,
    terms: mapt::hot::ir::term::TermStore<'static>,
    precedence: mapt::hot::ordering::precedence::PrecedenceTable<'static>,
    options: SearchOptions,
    assertion_base: u32,
}

fn make_learning_fixture(learning_max_lemmas: u32, learning_max_transfers: u32) -> LearningFixture {
    make_learning_fixture_with_count(
        kLearningSymbolCount,
        learning_max_lemmas,
        learning_max_transfers,
    )
}

// CEP:WHAT: Builds a learning fixture with explicit assertion-symbol count, lemma budget, and transfer budget.
// CEP:WHY: The injectable budgets are the CEP&CC 34.3 test interface; the symbol count scales the nameable-slot space for the policy tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: the reservation happens before finalize (the frozen table carries the 0-ary assertion predicates).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs's evidence map.
// CEP:SECURITY: none.
#[allow(non_snake_case)]
fn make_learning_fixture_with_count(
    learning_symbol_count: u32,
    learning_max_lemmas: u32,
    learning_max_transfers: u32,
) -> LearningFixture {
    let arena = make_arena(kLearningArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b", "c", "d"].iter() {
        let _ = builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("constant");
    }
    for name in ["p", "q", "r"].iter() {
        let _ = builder
            .declare_predicate(name, 2, 1, &[sort_s, sort_s])
            .expect("predicate");
    }
    // Reserve the assertion block BEFORE finalize so the 0-ary assertion
    // predicates are part of the frozen table (Spec 18 section 3).
    let assertion_base = builder
        .reserve_assertion_symbols(learning_symbol_count)
        .expect("reserve");
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let precedence = mapt::hot::ordering::precedence::PrecedenceTable::from_id_order(
        arena,
        builder.symbol_count(),
    )
    .expect("precedence");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 65536, 4096).expect("space");
    let avatar_options = AvatarOptions {
        sat_variables: 64,
        restart_policy: RestartPolicy::Luby,
        record_capacity: 64,
        word_capacity: 512,
        ancestry_bits: 4096,
        min_component_size: mapt_config::limits::kAvatarMinComponentSize,
        conflict_budget: mapt_config::limits::kSatMaxConflicts,
        max_conflict_rounds: 64,
        max_model_rotations: 64,
        learning_symbol_base: assertion_base,
        learning_symbol_count,
        learning_max_lemmas,
        learning_max_transfers,
    };
    let controller = AvatarController::new_with(arena, &avatar_options).expect("controller");
    LearningFixture {
        space,
        controller,
        symbols,
        builder,
        terms,
        precedence,
        options,
        assertion_base,
    }
}

fn context_of(fixture: &LearningFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

fn lit(
    fixture: &LearningFixture,
    name: &str,
    left: TermPtr,
    right: TermPtr,
    positive: bool,
) -> Literal {
    let atom = fixture
        .terms
        .intern_pred(
            &fixture.symbols,
            symbol_id(&fixture.builder, name),
            &[left, right],
        )
        .expect("atom");
    Literal::new(atom, positive)
}

fn var(fixture: &LearningFixture, index: u32) -> TermPtr {
    fixture.terms.intern_var(index).expect("var")
}

fn constant(fixture: &LearningFixture, name: &str) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), &[])
        .expect("constant")
}

// The controller test's pigeonhole: a four-literal clause with two
// variable-disjoint components and one refutation hole per component.
fn add_pigeonhole(fixture: &LearningFixture, context: &InferenceContext<'_>) {
    let (u, v) = (var(fixture, 2), var(fixture, 3));
    let (w, t) = (var(fixture, 4), var(fixture, 5));
    let split = vec![
        lit(fixture, "p", var(fixture, 0), constant(fixture, "a"), true),
        lit(fixture, "p", var(fixture, 0), constant(fixture, "b"), true),
        lit(fixture, "q", var(fixture, 1), constant(fixture, "c"), true),
        lit(fixture, "q", var(fixture, 1), constant(fixture, "d"), true),
    ];
    let hole_p_a = vec![lit(fixture, "p", u, constant(fixture, "a"), false)];
    let hole_p_b = vec![lit(fixture, "p", v, constant(fixture, "b"), false)];
    let hole_q_c = vec![lit(fixture, "q", w, constant(fixture, "c"), false)];
    let hole_q_d = vec![lit(fixture, "q", t, constant(fixture, "d"), false)];
    fixture
        .controller
        .add_input_clause(&fixture.space, context, &fixture.options, &split)
        .expect("add split");
    for hole in [hole_p_a, hole_p_b, hole_q_c, hole_q_d].iter() {
        fixture
            .controller
            .add_input_clause(&fixture.space, context, &fixture.options, hole)
            .expect("add hole");
    }
}

// Registers one SAT learnt clause directly through the solver's public
// registration path (the same register call the CDCL loop makes after every
// conflict), returning the registry entry index.
fn register_learnt(fixture: &LearningFixture, literals: &[SatLiteral], lbd: u8) -> u32 {
    let offset = match fixture
        .controller
        .solver
        .core()
        .add_learnt_clause(literals, lbd)
        .expect("learnt")
    {
        AttachOutcome::Attached(offset) => offset,
        AttachOutcome::UnitEnqueued(offset) => offset,
        other => panic!("unexpected attach outcome {:?}", other),
    };
    let storage: &ClauseStorage<'_> = fixture.controller.solver.core().clauses();
    fixture
        .controller
        .solver
        .registry()
        .register(storage, offset)
        .expect("register")
}

// CEP:WHAT: A conflict round stages the FOL copy of the ban clause as a SatLearn lemma and the certified kernel verifies the staged step (Spec 18 section 4, Spec 19).
// CEP:WHY: The pigeonhole refutation needs the abstraction closure, so conflict rounds fire; each staged lemma is a stored clause record (all-negative 0-ary assertion atoms, one parent: the round's refuting empty clause) and verify_clause_step replays the kernel's SatLearn arm on it.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when no lemma is staged, the shape is wrong, or the kernel rejects the step.
// CEP:ASSUMES: the pigeonhole fixture refutes with via_avatar = true.
// CEP:COST: one avatar saturation plus one step verification per staged lemma.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::add_conflict_lemma_from_buffer and cold/kernel/kernel.rs's SatLearn arm.
// CEP:SECURITY: none.
#[test]
fn conflict_lemma_staged_and_verifiable() {
    let fixture = make_learning_fixture(
        mapt_config::limits::kLearningMaxFolLemmas,
        mapt_config::limits::kLearningMaxLearntTransfers,
    );
    let context = context_of(&fixture);
    add_pigeonhole(&fixture, &context);
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &|_| false,
        &mut stats,
    )
    .expect("avatar saturate");
    assert!(
        matches!(
            outcome,
            AvatarOutcome::Theorem {
                via_avatar: true,
                ..
            }
        ),
        "the pigeonhole refutation needs the abstraction closure"
    );
    assert!(fixture.controller.stats.conflicts.get() >= 2);
    assert!(
        fixture.controller.stats.learning_lemmas.get() >= 1,
        "conflict rounds stage FOL lemmas"
    );
    // Every staged lemma has the SatLearn shape and the kernel verifies it.
    let next = fixture.space.store.next_clause_id().0;
    let mut staged = 0;
    for id in mapt_config::limits::kFirstClauseId..next {
        let record = fixture
            .space
            .store
            .clause_by_id(ClauseId(id))
            .expect("record");
        if record.derivation.rule != InferenceRule::SatLearn {
            continue;
        }
        assert_eq!(
            record.derivation.parent_count, 1,
            "conflict lemmas cite the anchor"
        );
        let anchor_id = record.derivation.parents[0];
        assert_ne!(anchor_id, mapt_config::limits::kInvalidClauseId);
        let anchor = fixture
            .space
            .store
            .clause_by_id(ClauseId(anchor_id))
            .expect("anchor");
        assert_eq!(
            anchor.literal_count, 0,
            "the anchor is the empty refutation"
        );
        for index in 0..record.literal_count {
            let literal = fixture.space.store.literal(record, index).expect("literal");
            assert!(!literal.is_positive(), "conflict lemmas are all-negative");
            let view = fixture.terms.term(literal.atom()).expect("atom view");
            assert_eq!(
                view.tag(),
                mapt::hot::ir::term::TermTag::Predicate,
                "assertion atoms are 0-ary predicates"
            );
            assert_eq!(view.child_count(), 0);
            let slot = view.symbol() - fixture.assertion_base;
            assert!(slot < kLearningSymbolCount);
        }
        let verdict = verify_clause_step_with_options(
            &context,
            &fixture.space.store,
            id,
            mapt_config::limits::kKernelReplayBudget,
            &KernelOptions {
                assertion_base: fixture.assertion_base,
                assertion_count: kLearningSymbolCount,
            },
        )
        .expect("verification finishes");
        assert_eq!(verdict, KernelVerdict::Valid, "the staged lemma verifies");
        staged += 1;
    }
    assert!(staged >= 1);
}

// CEP:WHAT: The staged-lemma budget is enforced: past kLearningMaxFolLemmas-equivalent bounds the staging path skips and counts (Law 4).
// CEP:WHY: CEP&CC 34.3: budgets must be injectable so tests exercise the exhaustion path on the production code path; the skip is counted, never silent.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when staging exceeds the budget or the skips go uncounted.
// CEP:ASSUMES: the pigeonhole fires at least two conflict rounds.
// CEP:COST: one avatar saturation.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::add_conflict_lemma_from_buffer's budget path.
// CEP:SECURITY: staging-work bound.
#[test]
fn conflict_lemma_budget_enforced() {
    let fixture = make_learning_fixture(1, mapt_config::limits::kLearningMaxLearntTransfers);
    let context = context_of(&fixture);
    add_pigeonhole(&fixture, &context);
    let mut stats = SearchStats::default();
    let _outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &|_| false,
        &mut stats,
    )
    .expect("avatar saturate");
    assert_eq!(
        fixture.controller.stats.learning_lemmas.get(),
        1,
        "the budget caps the staged lemmas"
    );
    assert!(
        fixture.controller.stats.learning_skipped.get() >= 1,
        "the skipped staging is counted"
    );
}

// CEP:WHAT: The transfer budget is enforced: past the configured transfer count the transfer path defers with one counted skip (Law 4).
// CEP:WHY: CEP&CC 34.3: the budget is injectable; the deferred entries stay beyond the monotone cursor and are retried on the next unconditional solve.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when transfers exceed the budget or the deferral goes uncounted.
// CEP:ASSUMES: three conforming learnts are registered directly through the solver's registration path.
// CEP:COST: three registrations plus one transfer call.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::transfer_learnts's budget path.
// CEP:SECURITY: transfer-work bound.
#[test]
fn transfer_budget_enforced() {
    let fixture = make_learning_fixture(mapt_config::limits::kLearningMaxFolLemmas, 1);
    let context = context_of(&fixture);
    for _ in 0..3 {
        register_learnt(
            &fixture,
            &[
                SatLiteral::new(SatVar(0), true).expect("literal"),
                SatLiteral::new(SatVar(1), false).expect("literal"),
            ],
            2,
        );
    }
    fixture
        .controller
        .transfer_learnts(&fixture.space, &context)
        .expect("transfer");
    assert_eq!(fixture.controller.stats.learning_transfers.get(), 1);
    assert_eq!(fixture.controller.stats.learning_skipped.get(), 1);
    // The deferred entries transfer on the next call's retry... except the
    // budget is still exhausted, so the deferral is counted again.
    fixture
        .controller
        .transfer_learnts(&fixture.space, &context)
        .expect("transfer");
    assert_eq!(fixture.controller.stats.learning_transfers.get(), 1);
}

// CEP:WHAT: The transfer policy filters: clauses exceeding the literal or LBD bounds are skipped, unnameable slots (at or above the reserved count) skip the clause, and conforming clauses transfer.
// CEP:WHY: Spec 18 section 4: the named bounds (kLearningMaxTransferLiterals, kLearningMaxTransferLbd) keep only small, high-quality lemmas, and the slot policy keeps the FOL copy all-or-nothing nameable.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a policy violation transfers or a conforming clause is skipped.
// CEP:ASSUMES: the reserved count is 8 and the solver has 64 variables.
// CEP:COST: four registrations plus one transfer call.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::transfer_learnts's policy paths.
// CEP:SECURITY: store-footprint and quality bounds.
#[test]
fn transfer_policy_filters() {
    let fixture = make_learning_fixture_with_count(
        8,
        mapt_config::limits::kLearningMaxFolLemmas,
        mapt_config::limits::kLearningMaxLearntTransfers,
    );
    let context = context_of(&fixture);
    // Conforming: 2 literals, LBD 2, slots 0/1.
    register_learnt(
        &fixture,
        &[
            SatLiteral::new(SatVar(0), true).expect("literal"),
            SatLiteral::new(SatVar(1), false).expect("literal"),
        ],
        2,
    );
    // Too long: 20 literals (bound 16) over nameable slots.
    let mut long_clause: Vec<SatLiteral> = Vec::new();
    for slot in 0..20 {
        long_clause.push(SatLiteral::new(SatVar(slot % 8), slot % 2 == 0).expect("literal"));
    }
    register_learnt(&fixture, &long_clause, 2);
    // LBD too high: 9 (bound 8).
    register_learnt(
        &fixture,
        &[
            SatLiteral::new(SatVar(2), true).expect("literal"),
            SatLiteral::new(SatVar(3), false).expect("literal"),
        ],
        9,
    );
    // Unnameable slot: 9 >= the reserved count 8.
    register_learnt(
        &fixture,
        &[
            SatLiteral::new(SatVar(0), true).expect("literal"),
            SatLiteral::new(SatVar(9), false).expect("literal"),
        ],
        2,
    );
    fixture
        .controller
        .transfer_learnts(&fixture.space, &context)
        .expect("transfer");
    assert_eq!(fixture.controller.stats.learning_transfers.get(), 1);
    assert_eq!(fixture.controller.stats.learning_skipped.get(), 3);
}

// CEP:WHAT: Transferred learnt clauses enter the passive set as parentless SatLearn clauses over the mapped assertion atoms.
// CEP:WHY: Spec 18 section 4: the transfer's FOL copy is a search clause (the assertion atoms are foreign but sound additions), so it joins the passive set exactly like any derived clause; the passive length grows by one per transfer.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the transfer does not push to the passive set or the record shape diverges.
// CEP:ASSUMES: one conforming learnt registered directly.
// CEP:COST: one registration plus one transfer call.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::transfer_learnts's passive push.
// CEP:SECURITY: none.
#[test]
fn transfer_learnts_enter_passive() {
    let fixture = make_learning_fixture(
        mapt_config::limits::kLearningMaxFolLemmas,
        mapt_config::limits::kLearningMaxLearntTransfers,
    );
    let context = context_of(&fixture);
    let before = fixture.space.passive.len();
    register_learnt(
        &fixture,
        &[
            SatLiteral::new(SatVar(0), true).expect("literal"),
            SatLiteral::new(SatVar(1), false).expect("literal"),
        ],
        2,
    );
    fixture
        .controller
        .transfer_learnts(&fixture.space, &context)
        .expect("transfer");
    assert_eq!(fixture.controller.stats.learning_transfers.get(), 1);
    assert_eq!(fixture.space.passive.len(), before + 1);
    // The transferred record: parentless SatLearn over the assertion atoms
    // A0 (positive) and A1 (negative), mapped from slots 0/1.
    let next = fixture.space.store.next_clause_id().0;
    let mut found = false;
    for id in mapt_config::limits::kFirstClauseId..next {
        let record = fixture
            .space
            .store
            .clause_by_id(ClauseId(id))
            .expect("record");
        if record.derivation.rule != InferenceRule::SatLearn || record.derivation.parent_count != 0
        {
            continue;
        }
        assert_eq!(record.literal_count, 2);
        let first = fixture.space.store.literal(record, 0).expect("literal");
        let second = fixture.space.store.literal(record, 1).expect("literal");
        let atom0 = fixture.terms.term(first.atom()).expect("view").symbol();
        let atom1 = fixture.terms.term(second.atom()).expect("view").symbol();
        assert_eq!(atom0, fixture.assertion_base);
        assert!(first.is_positive());
        assert_eq!(atom1, fixture.assertion_base + 1);
        assert!(!second.is_positive());
        found = true;
    }
    assert!(found, "the transferred clause record exists");
}

// CEP:WHAT: Learning is disabled by default: the default options carry a zero symbol count and a run with conflict rounds stages and transfers nothing.
// CEP:WHY: Spec 18 section 3: the learning machinery must be opt-in (the assertion symbols do not exist unless reserved), so the default configuration leaves no trace in the store or the stats.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the default configuration stages or transfers anything.
// CEP:ASSUMES: the pigeonhole fires conflict rounds.
// CEP:COST: one avatar saturation.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::{AvatarOptions::default, add_conflict_lemma_from_buffer, transfer_learnts} disable paths.
// CEP:SECURITY: none.
#[test]
fn learning_disabled_by_default() {
    let options = AvatarOptions::default();
    assert_eq!(options.learning_symbol_count, 0);
    let arena = make_arena(kLearningArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b", "c", "d"].iter() {
        let _ = builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("constant");
    }
    for name in ["p", "q", "r"].iter() {
        let _ = builder
            .declare_predicate(name, 2, 1, &[sort_s, sort_s])
            .expect("predicate");
    }
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let precedence = mapt::hot::ordering::precedence::PrecedenceTable::from_id_order(
        arena,
        builder.symbol_count(),
    )
    .expect("precedence");
    let search_options = SearchOptions::new();
    let space = SearchSpace::new_with(arena, &search_options, 4096, 1024, 4096, 8192, 65536, 4096)
        .expect("space");
    let controller = AvatarController::new_with(arena, &options).expect("controller");
    let fixture = LearningFixture {
        space,
        controller,
        symbols,
        builder,
        terms,
        precedence,
        options: search_options,
        assertion_base: 0,
    };
    let context = context_of(&fixture);
    add_pigeonhole(&fixture, &context);
    let mut stats = SearchStats::default();
    let _outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &|_| false,
        &mut stats,
    )
    .expect("avatar saturate");
    assert!(fixture.controller.stats.conflicts.get() >= 2);
    assert_eq!(fixture.controller.stats.learning_lemmas.get(), 0);
    assert_eq!(fixture.controller.stats.learning_transfers.get(), 0);
    assert_eq!(fixture.controller.stats.learning_skipped.get(), 0);
    // No SatLearn record exists.
    let next = fixture.space.store.next_clause_id().0;
    for id in mapt_config::limits::kFirstClauseId..next {
        let record = fixture
            .space
            .store
            .clause_by_id(ClauseId(id))
            .expect("record");
        assert_ne!(
            record.derivation.rule,
            InferenceRule::SatLearn,
            "learning disabled means no SatLearn records"
        );
    }
    let _ = ClausePtr::from_u32(0);
}
