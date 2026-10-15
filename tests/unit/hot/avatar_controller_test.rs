// CEP:FILE: tests/unit/hot/avatar_controller_test.rs
// CEP:WHAT: Unit tests of the AVATAR controller and the saturate_with_avatar protocol: option validation, input splitting, model activation, the conflict-driven refutation of a split pigeonhole-style problem, direct refutations, the injected round/rotation budgets, split derivations, and the drained-waiting saturation terminal.
// CEP:WHY: CEP&CC 34.3: the controller implements design 12.2's four rules; every protocol claim (Spec 12 sections 5-6) must be pinned executably, including both budget exhaustion paths at small scales.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the fixture vocabulary (p/q/r predicates, a-d constants).
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/avatar_controller_test.rs.
// CEP:SECURITY: the budget tests exercise the denial-of-service bounds.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, symbol_id};
use mapt::hot::avatar::controller::{
    saturate_with_avatar, AddOutcome, AvatarController, AvatarOptions, AvatarOutcome,
    ControllerError,
};
use mapt::hot::avatar::splitter::try_split;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClausePtr, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::search::given_clause::{GaveUpReason, SearchOptions, SearchSpace, SearchStats};

// CEP:WHAT: Arena bytes for the controller fixtures (search space + controller structures).
// CEP:WHY: Named fixture bound; larger than the plain loop fixture because the controller adds the solver, table, and bitset.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: covers the small injected capacities.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kControllerArenaBytes: u32 = 50_331_648;

// CEP:WHAT: The controller fixture bundle.
// CEP:WHY: One constructor wires the arena, symbols, stores, space, controller, and context exactly as the driver would.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every test in this file.
// CEP:SECURITY: none.
struct ControllerFixture {
    space: SearchSpace<'static>,
    controller: AvatarController<'static>,
    symbols: mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: mapt::cold::symbol_table_builder::SymbolTableBuilder,
    terms: mapt::hot::ir::term::TermStore<'static>,
    precedence: mapt::hot::ordering::precedence::PrecedenceTable<'static>,
    options: SearchOptions,
}

// CEP:WHAT: Builds the fixture with small injected capacities.
// CEP:WHY: CEP&CC 34.3: small scales keep the tests fast and the bounds exercisable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn make_fixture(max_conflict_rounds: u32, max_model_rotations: u32) -> ControllerFixture {
    let arena = make_arena(kControllerArenaBytes);
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
        max_conflict_rounds,
        max_model_rotations,
    };
    let controller = AvatarController::new_with(arena, &avatar_options).expect("controller");
    ControllerFixture {
        space,
        controller,
        symbols,
        builder,
        terms,
        precedence,
        options,
    }
}

// CEP:WHAT: Builds the inference context over the fixture's space.
// CEP:WHY: The protocol entry points take the context next to the space.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn context_of(fixture: &ControllerFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Builds one p/q/r literal over two argument terms.
// CEP:WHY: Readable clause fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn lit(
    fixture: &ControllerFixture,
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

// CEP:WHAT: Interns a fixture variable.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn var(fixture: &ControllerFixture, index: u32) -> TermPtr {
    fixture.terms.intern_var(index).expect("var")
}

// CEP:WHAT: Interns a fixture constant.
// CEP:WHY: Readable fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn constant(fixture: &ControllerFixture, name: &str) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), &[])
        .expect("constant")
}

// CEP:WHAT: The splittable clause p(x,a) | p(x,b) | q(y,c) | q(y,d).
// CEP:WHY: Two variable-disjoint 2-literal components (the core split fixture).
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture.
// CEP:COST: four interns.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn splittable_clause(fixture: &ControllerFixture) -> Vec<Literal> {
    let (x, y) = (var(fixture, 0), var(fixture, 1));
    vec![
        lit(fixture, "p", x, constant(fixture, "a"), true),
        lit(fixture, "p", x, constant(fixture, "b"), true),
        lit(fixture, "q", y, constant(fixture, "c"), true),
        lit(fixture, "q", y, constant(fixture, "d"), true),
    ]
}

#[test]
// CEP:WHAT: Construction rejects sat_variables below the record capacity, zero capacities, and out-of-range bitsets.
// CEP:WHY: The assertion-variable space must cover every component slot (Spec 12 section 4); validation is construction-time and loud.
// CEP:STATUS: complete
// CEP:FAILURE: panics if an inconsistent option set is accepted.
// CEP:ASSUMES: none.
// CEP:COST: a few constructions.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::controller_validates_solver_variables.
// CEP:SECURITY: input validation.
fn controller_validates_solver_variables() {
    let arena = make_arena(kControllerArenaBytes);
    let bad = AvatarOptions {
        sat_variables: 8,
        record_capacity: 16,
        ..AvatarOptions::default()
    };
    match AvatarController::new_with(arena, &bad) {
        Err(ControllerError::InvalidOptions) => {}
        _ => panic!("variables below the record capacity must be rejected"),
    }
    let arena = make_arena(kControllerArenaBytes);
    let zero_records = AvatarOptions {
        sat_variables: 16,
        record_capacity: 0,
        ..AvatarOptions::default()
    };
    match AvatarController::new_with(arena, &zero_records) {
        Err(ControllerError::InvalidOptions) => {}
        _ => panic!("zero record capacity must be rejected"),
    }
    let arena = make_arena(kControllerArenaBytes);
    let bad_bits = AvatarOptions {
        sat_variables: 16,
        record_capacity: 16,
        ancestry_bits: 100,
        ..AvatarOptions::default()
    };
    match AvatarController::new_with(arena, &bad_bits) {
        Err(ControllerError::InvalidOptions) => {}
        _ => panic!("a non-multiple-of-64 bitset must be rejected"),
    }
}

#[test]
// CEP:WHAT: Adding a splittable input splits it: two fresh components, an abstraction clause in the solver, and the original kept inert.
// CEP:WHY: Design 12.2 rule 1: the clause is replaced by its components; the disjunction a1 | a2 enters the abstraction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a non-split outcome.
// CEP:ASSUMES: fixture.
// CEP:COST: one add.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::split_inputs_create_components.
// CEP:SECURITY: none.
fn split_inputs_create_components() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let literals = splittable_clause(&fixture);
    // The fixture clause really splits (the splitter's own contract).
    assert!(matches!(
        try_split(&fixture.terms, &literals),
        mapt::hot::avatar::splitter::SplitDecision::Splittable(_)
    ));
    match fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &literals)
        .expect("add")
    {
        AddOutcome::Split { original } => {
            assert_ne!(original, 0);
            assert_eq!(fixture.controller.components.component_count(), 2);
            assert_eq!(fixture.controller.stats.splits.get(), 1);
            assert_eq!(fixture.controller.stats.components_fresh.get(), 2);
            // The abstraction is satisfiable with the disjunction present.
            assert_eq!(
                fixture.controller.solver.solve(),
                mapt::hot::sat::solver::SolveResult::Satisfiable
            );
        }
        other => panic!("expected a split, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: Unsplittable inputs take the plain path: added to the passive set, counted unsplit, no components.
// CEP:WHY: Design 12.2's degradation path (single-component clauses stay whole).
// CEP:STATUS: complete
// CEP:FAILURE: panics on a split outcome.
// CEP:ASSUMES: fixture.
// CEP:COST: one add.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::unsplittable_inputs_pass_through.
// CEP:SECURITY: none.
fn unsplittable_inputs_pass_through() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let literals = vec![lit(&fixture, "p", a, a, true)];
    match fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &literals)
        .expect("add")
    {
        AddOutcome::Added(_) => {
            assert_eq!(fixture.controller.components.component_count(), 0);
            assert_eq!(fixture.controller.stats.unsplit.get(), 1);
            assert_eq!(
                fixture.space.passive.len(),
                1,
                "the clause joined the search"
            );
        }
        other => panic!("expected the plain path, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: After a split, the model activates at least one component: materialized clauses join the passive set with their literal tags.
// CEP:WHY: Design 12.2 rule 3: only model-true components are activated (monotone: once materialized, forever searchable).
// CEP:STATUS: complete
// CEP:FAILURE: panics if nothing activates.
// CEP:ASSUMES: the model satisfies the disjunction (at least one true).
// CEP:COST: one solve + activation pass.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::model_activates_components.
// CEP:SECURITY: none.
fn model_activates_components() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let literals = splittable_clause(&fixture);
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &literals)
        .expect("add");
    assert_eq!(
        fixture.controller.solver.solve(),
        mapt::hot::sat::solver::SolveResult::Satisfiable
    );
    let activated = fixture
        .controller
        .activate_under_model(&fixture.space, &context, &fixture.options)
        .expect("activate");
    assert!(activated >= 1, "at least one component activates");
    assert_eq!(fixture.controller.waiting_count(), 2 - activated);
    // Materialized components carry a passive entry.
    assert!(fixture.space.passive.len() >= activated);
    // Idempotence: a second activation pass materializes nothing new under the same model.
    let again = fixture
        .controller
        .activate_under_model(&fixture.space, &context, &fixture.options)
        .expect("activate");
    assert_eq!(again, 0);
}

#[test]
// CEP:WHAT: A split problem whose both components are individually refutable ends in Theorem with via_avatar = true (the abstraction closes after two conflict rounds).
// CEP:WHY: Spec 12 sections 5 and Theorem 1: each first-order refutation adds its conflict clause; the abstraction a1|a2, not-a1, not-a2 is unsatisfiable, so the original problem is refuted.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: ordered resolution refutes each component against its complement clause in two steps.
// CEP:COST: a handful of inferences.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
// CEP:SECURITY: none.
fn refutes_split_pigeonhole() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let split = splittable_clause(&fixture);
    let (u, v) = (var(&fixture, 2), var(&fixture, 3));
    let (w, t) = (var(&fixture, 4), var(&fixture, 5));
    // Unit hole clauses: each component is individually refutable by two unit
    // resolutions (p(x,b) with H2, then the unit remainder with H1 - the ordered
    // path resolves on the strictly maximal p(x,b) first).
    let hole_p_a = vec![lit(&fixture, "p", u, constant(&fixture, "a"), false)];
    let hole_p_b = vec![lit(&fixture, "p", v, constant(&fixture, "b"), false)];
    let hole_q_c = vec![lit(&fixture, "q", w, constant(&fixture, "c"), false)];
    let hole_q_d = vec![lit(&fixture, "q", t, constant(&fixture, "d"), false)];
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &split)
        .expect("add split");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_p_a)
        .expect("add hole p a");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_p_b)
        .expect("add hole p b");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_q_c)
        .expect("add hole q c");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_q_d)
        .expect("add hole q d");
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate");
    match outcome {
        AvatarOutcome::Theorem {
            refutation,
            via_avatar,
        } => {
            assert!(via_avatar, "the refutation needs the abstraction closure");
            assert_ne!(refutation, 0);
            assert!(fixture.controller.stats.conflicts.get() >= 2);
        }
        other => panic!("expected an avatar theorem, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: A direct contradiction without splits ends in Theorem with via_avatar = false.
// CEP:WHY: The empty ancestry path: the refutation uses no component, so no conflict clause is added.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: p(a) and not-p(a) resolve directly.
// CEP:COST: one inference.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::direct_refutation_bypasses_avatar.
// CEP:SECURITY: none.
fn direct_refutation_bypasses_avatar() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    fixture
        .controller
        .add_input_clause(
            &fixture.space,
            &context,
            &fixture.options,
            &[lit(&fixture, "p", a, a, true)],
        )
        .expect("add p");
    fixture
        .controller
        .add_input_clause(
            &fixture.space,
            &context,
            &fixture.options,
            &[lit(&fixture, "p", a, a, false)],
        )
        .expect("add not p");
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate");
    match outcome {
        AvatarOutcome::Theorem {
            via_avatar: false, ..
        } => {
            assert_eq!(fixture.controller.stats.conflicts.get(), 0);
        }
        other => panic!("expected a direct theorem, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: The injected conflict-round budget stops the protocol loudly (one round cannot close a two-conflict problem).
// CEP:WHY: CEP&CC 34.3: the kAvatarMaxConflictRounds bound must be exercisable at a small scale; the budget fires before the second conflict.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: the pigeonhole fixture needs two conflicts.
// CEP:COST: one round.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
// CEP:SECURITY: denial-of-service bound.
fn conflict_round_budget_enforced() {
    let fixture = make_fixture(1, 64);
    let context = context_of(&fixture);
    let split = splittable_clause(&fixture);
    let (u, v) = (var(&fixture, 2), var(&fixture, 3));
    let (w, t) = (var(&fixture, 4), var(&fixture, 5));
    let hole_p_a = vec![lit(&fixture, "p", u, constant(&fixture, "a"), false)];
    let hole_p_b = vec![lit(&fixture, "p", v, constant(&fixture, "b"), false)];
    let hole_q_c = vec![lit(&fixture, "q", w, constant(&fixture, "c"), false)];
    let hole_q_d = vec![lit(&fixture, "q", t, constant(&fixture, "d"), false)];
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &split)
        .expect("add split");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_p_a)
        .expect("add hole p a");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_p_b)
        .expect("add hole p b");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_q_c)
        .expect("add hole q c");
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &hole_q_d)
        .expect("add hole q d");
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate");
    assert_eq!(
        outcome,
        AvatarOutcome::GaveUp(GaveUpReason::AvatarConflictBudget),
        "the one-round budget stops before the abstraction closes"
    );
}

#[test]
// CEP:WHAT: The injected rotation budget of zero stops the saturated-with-waiting case loudly (GaveUp(AvatarModelBudget)).
// CEP:WHY: CEP&CC 34.3: the kAvatarMaxModelRotations bound must be exercisable; zero probes nothing and the waiting set cannot drain.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: the satisfiable split saturates with one waiting component.
// CEP:COST: one round.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
// CEP:SECURITY: denial-of-service bound.
fn model_rotation_budget_enforced() {
    let fixture = make_fixture(64, 0);
    let context = context_of(&fixture);
    let split = splittable_clause(&fixture);
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &split)
        .expect("add split");
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate");
    assert_eq!(
        outcome,
        AvatarOutcome::GaveUp(GaveUpReason::AvatarModelBudget),
        "the zero-rotation budget stops with waiting components"
    );
}

#[test]
// CEP:WHAT: A satisfiable split problem ends in Saturated after the rotation drains the waiting set (every component materialized).
// CEP:WHY: Spec 12 Theorem 3 and the assertability lemma: the rotation activates the waiting component and the (monotone, superset) search saturates without deriving false.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other outcome.
// CEP:ASSUMES: no complementary clauses exist.
// CEP:COST: two rounds.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::saturates_when_waiting_drains.
// CEP:SECURITY: none.
fn saturates_when_waiting_drains() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let split = splittable_clause(&fixture);
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &split)
        .expect("add split");
    let mut stats = SearchStats::default();
    let outcome = saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate");
    assert_eq!(outcome, AvatarOutcome::Saturated);
    assert_eq!(
        fixture.controller.waiting_count(),
        0,
        "the rotation drained the waiting set"
    );
    assert!(fixture.controller.stats.rotations.get() >= 1);
}

#[test]
// CEP:WHAT: Materialized component clauses carry the AvatarSplit derivation (parent = the original) and split_level = slot + 1.
// CEP:WHY: Spec 12 section 4: the unified proof graph reaches components through their originals (design 12.4 shared proof graph).
// CEP:STATUS: complete
// CEP:FAILURE: panics on a wrong derivation.
// CEP:ASSUMES: the split fixture.
// CEP:COST: one activation.
// CEP:EVIDENCE: backs unit/hot/avatar_controller_test.rs::split_derivations_cite_original.
// CEP:SECURITY: none.
fn split_derivations_cite_original() {
    let fixture = make_fixture(64, 64);
    let context = context_of(&fixture);
    let literals = splittable_clause(&fixture);
    let original = match fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &literals)
        .expect("add")
    {
        AddOutcome::Split { original } => original,
        other => panic!("expected a split, got {:?}", other),
    };
    let original_record = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(original))
        .expect("original");
    assert_eq!(original_record.derivation.rule, InferenceRule::Input);
    assert_eq!(
        fixture.controller.solver.solve(),
        mapt::hot::sat::solver::SolveResult::Satisfiable
    );
    fixture
        .controller
        .activate_under_model(&fixture.space, &context, &fixture.options)
        .expect("activate");
    for slot in 0..fixture.controller.components.component_count() {
        if let Some(offset) = fixture.controller.components.materialized(slot) {
            let record = fixture
                .space
                .store
                .clause(ClausePtr::from_u32(offset))
                .expect("component");
            assert_eq!(record.derivation.rule, InferenceRule::AvatarSplit);
            assert_eq!(record.derivation.parent_count, 1);
            assert_eq!(record.derivation.parents[0], original_record.id.0);
            assert_eq!(record.split_level, (slot + 1) as u16);
        }
    }
}

// CEP:WHAT: The never-stop callback.
// CEP:WHY: Budget-free runs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn never_stop(_iterations: u64) -> bool {
    false
}
