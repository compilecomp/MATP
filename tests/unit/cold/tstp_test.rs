// CEP:FILE: tests/unit/cold/tstp_test.rs
// CEP:WHAT: Unit tests of the unified proof reconstruction: the reachable-id walk, TSTP formatting (roles, sources, $false), pruning of unreachable steps, cycle detection, and the replay checker's accept and reject paths (broken resolution, broken factoring, broken avatar split, the demodulation variant check).
// CEP:WHY: CEP&CC 34.3 and design 18.4: proof reconstruction and verification are the soundness certification of the prover; every walk, format, and checker claim (Spec 14) must be pinned executably.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the fixture vocabulary (p/q/r predicates, a-d constants).
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/cold/tstp_test.rs.
// CEP:SECURITY: the reject tests exercise the tamper guards.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::cold::proof_output::tstp::{
    check_proof, reachable_proof_ids, render_verified_proof, write_tstp_proof, TstpError,
};
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClauseId, ClausePtr, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

// CEP:WHAT: The proof fixture: stores, a small search space with an id side table, and the context.
// CEP:WHY: One constructor mirrors the driver's wiring (the id table is required for parent resolution - Spec 14 section 2).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
struct ProofFixture {
    space: SearchSpace<'static>,
    symbols: mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: SymbolTableBuilder,
    terms: mapt::hot::ir::term::TermStore<'static>,
    precedence: mapt::hot::ordering::precedence::PrecedenceTable<'static>,
    options: SearchOptions,
}

// CEP:WHAT: Builds the proof fixture over the standard inference fixture arena.
// CEP:WHY: The standard vocabulary suffices for every proof scenario.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn make_proof_fixture(passive_capacity: u32) -> ProofFixture {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions::new();
    let space = SearchSpace::new_with(
        arena,
        &options,
        passive_capacity,
        4096,
        8192,
        8192,
        65536,
        4096,
    )
    .expect("space");
    ProofFixture {
        space,
        symbols,
        builder,
        terms,
        precedence,
        options,
    }
}

// CEP:WHAT: The context over the fixture's space.
// CEP:WHY: The checker replays rules through the context.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn context_of(fixture: &ProofFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Builds one predicate literal.
// CEP:WHY: Readable proof fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn lit(fixture: &ProofFixture, name: &str, args: &[TermPtr], positive: bool) -> Literal {
    let atom = fixture
        .terms
        .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, name), args)
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
fn var(fixture: &ProofFixture, index: u32) -> TermPtr {
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
fn constant(fixture: &ProofFixture, name: &str) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), &[])
        .expect("constant")
}

// CEP:WHAT: Runs the two-step refutation problem (p|q, -p, -q, plus one unused input) and returns the refutation offset.
// CEP:WHY: One scenario backs the format, walk, prune, and checker-accept tests: q resolves first (the maximal literal), then p, and the unused r(v) input must be pruned.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the loop does not refute.
// CEP:ASSUMES: fixture.
// CEP:COST: a handful of inferences.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn refute_two_step(fixture: &ProofFixture) -> (u32, u64) {
    let context = context_of(fixture);
    let (x, y, z, w) = (
        var(fixture, 0),
        var(fixture, 1),
        var(fixture, 2),
        var(fixture, 3),
    );
    let a2 = constant(fixture, "a");
    let pq = [
        lit(fixture, "p", &[x], true),
        lit(fixture, "q", &[y, a2], true),
    ];
    let neg_p = [lit(fixture, "p", &[z], false)];
    let neg_q = [lit(fixture, "q", &[w, a2], false)];
    let unused = [lit(fixture, "r", &[], true)];
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &pq)
        .expect("add p|q");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &neg_p)
        .expect("add -p");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &neg_q)
        .expect("add -q");
    let unused_offset = fixture
        .space
        .add_input_clause(&context, &fixture.options, &unused)
        .expect("add unused r");
    let unused_id = fixture
        .space
        .store
        .clause(ClausePtr::from_u32(unused_offset))
        .expect("unused record")
        .id
        .0;
    let mut stats = SearchStats::default();
    match saturate(
        &fixture.space,
        &context,
        &fixture.options,
        &never_stop,
        &mut stats,
    )
    .expect("saturate")
    {
        SearchOutcome::Theorem { refutation } => (refutation, unused_id),
        other => panic!("expected a theorem, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: The proof walk resolves every parent id through the side table and returns the ancestry ascending.
// CEP:WHY: Spec 14 section 2: the walk is the id-resolution contract (a table-less store rejects loudly).
// CEP:STATUS: complete
// CEP:FAILURE: panics on an unresolvable parent.
// CEP:ASSUMES: the two-step scenario.
// CEP:COST: one walk.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::proof_walk_resolves_parents.
// CEP:SECURITY: none.
fn proof_walk_resolves_parents() {
    let fixture = make_proof_fixture(4096);
    let (refutation, _unused_id) = refute_two_step(&fixture);
    let ids = reachable_proof_ids(&fixture.space.store, refutation).expect("walk");
    assert!(ids.len() >= 3, "at least the empty clause and its ancestry");
    for id in ids.iter() {
        assert!(
            fixture.space.store.clause_by_id(ClauseId(*id)).is_ok(),
            "id {} must resolve",
            id
        );
    }
    // Ascending (a valid topological order).
    for pair in ids.windows(2) {
        assert!(pair[0] < pair[1]);
    }
}

#[test]
// CEP:WHAT: The rendered TSTP proof contains one cnf statement per reachable clause, the empty clause as $false, correct roles, and inference sources.
// CEP:WHY: Spec 14 sections 4-5: the statement grammar subset and the source presentation.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a missing or malformed statement.
// CEP:ASSUMES: the two-step scenario.
// CEP:COST: one render.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::{formats_refutation_proof, roles_and_sources, empty_clause_renders_false}.
// CEP:SECURITY: none.
fn formats_refutation_proof() {
    let fixture = make_proof_fixture(4096);
    let (refutation, _unused_id) = refute_two_step(&fixture);
    let mut out = String::new();
    let count = write_tstp_proof(
        &fixture.terms,
        &fixture.builder,
        &fixture.space.store,
        refutation,
        &mut out,
    )
    .expect("write");
    let statements: Vec<&str> = out.lines().collect();
    assert_eq!(
        statements.len(),
        count,
        "one statement per reachable clause"
    );
    assert!(statements.iter().all(|line| line.starts_with("cnf(c")));
    // Roles: the inputs are axioms, the empty clause is plain.
    assert!(
        statements.iter().any(|line| line.contains(", axiom, ")),
        "inputs keep the axiom role"
    );
    // Sources: derived clauses cite their parents through inference(...).
    assert!(
        statements
            .iter()
            .any(|line| line.contains("inference(resolution, [], [")),
        "the resolution step cites its parents"
    );
    // The empty clause renders $false and is the last statement.
    let last = statements.last().expect("statements");
    assert!(
        last.contains("plain, $false"),
        "the empty clause renders $false with the plain role: {}",
        last
    );
}

#[test]
// CEP:WHAT: Unreachable clauses are pruned: the unused r(v) input never appears in the proof.
// CEP:WHY: Design 18.2's redundant-step removal (the Phase 4 reachability compression).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the unused clause appears.
// CEP:ASSUMES: the two-step scenario (the unused input's id is captured at add time).
// CEP:COST: one walk.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::prunes_unreachable_steps.
// CEP:SECURITY: none.
fn prunes_unreachable_steps() {
    let fixture = make_proof_fixture(4096);
    let (refutation, unused_id) = refute_two_step(&fixture);
    let ids = reachable_proof_ids(&fixture.space.store, refutation).expect("walk");
    assert!(
        !ids.contains(&unused_id),
        "the unused input (id {}) must be pruned",
        unused_id
    );
}

#[test]
// CEP:WHAT: The checker accepts the loop-produced proof end to end (render_verified_proof verifies then formats).
// CEP:WHY: Design 18.4: every produced proof must pass its own checker.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the honest proof is rejected.
// CEP:ASSUMES: the two-step scenario.
// CEP:COST: one verification.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::checker_accepts_valid_proof and property/tstp_property_test.rs::every_refutation_formats_and_checks.
// CEP:SECURITY: none.
fn checker_accepts_valid_proof() {
    let fixture = make_proof_fixture(4096);
    let (refutation, _unused_id) = refute_two_step(&fixture);
    let context = context_of(&fixture);
    check_proof(&context, &fixture.space.store, refutation).expect("the honest proof checks");
    let (count, text) = render_verified_proof(
        &context,
        &fixture.terms,
        &fixture.builder,
        &fixture.space.store,
        refutation,
    )
    .expect("render verified");
    assert!(count >= 3);
    assert!(text.contains("$false"));
}

#[test]
// CEP:WHAT: A tampered resolution step (a conclusion that no pivot pair reproduces) is rejected with the offending id.
// CEP:WHY: Design 18.4: an invalid step rejects the whole proof.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the tampered step is accepted.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one check.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::checker_rejects_broken_resolution.
// CEP:SECURITY: tamper guard.
fn checker_rejects_broken_resolution() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let b = constant(&fixture, "b");
    let p_a = [lit(&fixture, "p", &[a], true)];
    let neg_p_a = [lit(&fixture, "p", &[a], false)];
    let left = fixture
        .space
        .store
        .new_clause(&fixture.terms, &p_a, 0, input_derivation())
        .expect("c1");
    let right = fixture
        .space
        .store
        .new_clause(&fixture.terms, &neg_p_a, 1, input_derivation())
        .expect("c2");
    let left_id = fixture.space.store.clause(left).expect("read").id.0;
    let right_id = fixture.space.store.clause(right).expect("read").id.0;
    // The broken step: claims q(b) is the resolvent of p(a) and -p(a).
    let q_b = [lit(&fixture, "q", &[b, b], true)];
    let broken = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &q_b,
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    left_id,
                    right_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("broken");
    let broken_id = fixture.space.store.clause(broken).expect("read").id.0;
    // The walk starts at a fake empty clause citing the broken step.
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            3,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 1,
                reserved: 0,
                parents: [
                    broken_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("empty");
    let refutation = empty.as_u32();
    assert_eq!(
        check_proof(&context, &fixture.space.store, refutation),
        Err(TstpError::InvalidStep(broken_id)),
        "the q(b) step is not any resolvent"
    );
}

#[test]
// CEP:WHAT: A tampered factoring step is rejected.
// CEP:WHY: The replay checker covers every rule the loop records.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the tampered step is accepted.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one check.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::checker_rejects_broken_factoring.
// CEP:SECURITY: tamper guard.
fn checker_rejects_broken_factoring() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let (x, y) = (var(&fixture, 0), var(&fixture, 1));
    let a = constant(&fixture, "a");
    let premise = [
        lit(&fixture, "p", &[x], true),
        lit(&fixture, "p", &[y], true),
    ];
    let parent = fixture
        .space
        .store
        .new_clause(&fixture.terms, &premise, 0, input_derivation())
        .expect("parent");
    let parent_id = fixture.space.store.clause(parent).expect("read").id.0;
    // The broken step: claims q(a) is a factor of p(x) | p(y) (the honest factor is p(x)).
    let q_a = [lit(&fixture, "q", &[a, a], true)];
    let broken = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &q_a,
            1,
            DerivationStep {
                rule: InferenceRule::Factoring,
                parent_count: 1,
                reserved: 0,
                parents: [
                    parent_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("broken");
    let broken_id = fixture.space.store.clause(broken).expect("read").id.0;
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            2,
            DerivationStep {
                rule: InferenceRule::Factoring,
                parent_count: 1,
                reserved: 0,
                parents: [
                    broken_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("empty");
    let refutation = empty.as_u32();
    assert_eq!(
        check_proof(&context, &fixture.space.store, refutation),
        Err(TstpError::InvalidStep(broken_id))
    );
}

#[test]
// CEP:WHAT: A tampered avatar split (a conclusion literal absent from the parent) is rejected.
// CEP:WHY: Spec 12 Lemma 1's subclause property is the checker's split contract.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the tampered step is accepted.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one check.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::checker_rejects_broken_avatar_split.
// CEP:SECURITY: tamper guard.
fn checker_rejects_broken_avatar_split() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let (x, y, z) = (var(&fixture, 0), var(&fixture, 1), var(&fixture, 2));
    let parent_literals = [
        lit(&fixture, "p", &[x], true),
        lit(&fixture, "p", &[y], true),
        lit(&fixture, "q", &[z, z], true),
        lit(&fixture, "q", &[x, x], true),
    ];
    let parent = fixture
        .space
        .store
        .new_clause(&fixture.terms, &parent_literals, 0, input_derivation())
        .expect("parent");
    let parent_id = fixture.space.store.clause(parent).expect("read").id.0;
    // The broken component: r(a) is not a subclause of the parent.
    let broken_literals = [lit(&fixture, "r", &[], true)];
    let broken = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &broken_literals,
            1,
            DerivationStep {
                rule: InferenceRule::AvatarSplit,
                parent_count: 1,
                reserved: 0,
                parents: [
                    parent_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("broken");
    let broken_id = fixture.space.store.clause(broken).expect("read").id.0;
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            2,
            DerivationStep {
                rule: InferenceRule::AvatarSplit,
                parent_count: 1,
                reserved: 0,
                parents: [
                    broken_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("empty");
    let refutation = empty.as_u32();
    assert_eq!(
        check_proof(&context, &fixture.space.store, refutation),
        Err(TstpError::InvalidStep(broken_id))
    );
}

#[test]
// CEP:WHAT: A demodulation-shaped step (same literal count and polarity multiset as the parent) passes the Phase 4 structural variant check.
// CEP:WHY: The documented weakening (Spec 14 section 6, ticket CEP-1036): the demodulating rule's identity is not recorded, so the checker verifies the variant property.
// CEP:STATUS: complete
// CEP:FAILURE: panics if an honest demodulation variant is rejected.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one check.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::checker_accepts_demodulation_variant.
// CEP:SECURITY: none.
fn checker_accepts_demodulation_variant() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let parent_literals = [lit(&fixture, "p", &[a], true)];
    let parent = fixture
        .space
        .store
        .new_clause(&fixture.terms, &parent_literals, 0, input_derivation())
        .expect("parent");
    let parent_id = fixture.space.store.clause(parent).expect("read").id.0;
    // The rewritten variant: the atom is rewritten (same literal count and polarity).
    let b = constant(&fixture, "b");
    let mut variant_literals = [lit(&fixture, "p", &[b], true)];
    mapt::hot::inference::compute_selection_flags(
        &context,
        fixture.options.selection,
        &mut variant_literals,
    )
    .expect("flags");
    let variant = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &variant_literals,
            1,
            DerivationStep {
                rule: InferenceRule::Demodulation,
                parent_count: 1,
                reserved: 0,
                parents: [
                    parent_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("variant");
    let variant_id = fixture.space.store.clause(variant).expect("read").id.0;
    let mut complement_literals = [lit(&fixture, "p", &[var(&fixture, 9)], false)];
    mapt::hot::inference::compute_selection_flags(
        &context,
        fixture.options.selection,
        &mut complement_literals,
    )
    .expect("flags");
    let complement = fixture
        .space
        .store
        .new_clause(&fixture.terms, &complement_literals, 2, input_derivation())
        .expect("complement");
    let complement_id = fixture.space.store.clause(complement).expect("read").id.0;
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            3,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    variant_id,
                    complement_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("empty");
    let refutation = empty.as_u32();
    check_proof(&context, &fixture.space.store, refutation)
        .expect("the structural variant passes the Phase 4 demodulation check");
}

#[test]
// CEP:WHAT: A parent id at or above the child id (a corrupted derivation) is detected as a cycle and the walk refuses.
// CEP:WHY: Monotonic ids make parents strictly older (Spec 14 section 2); the violation means corruption.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the corrupted derivation is accepted.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one walk.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::cycle_detected.
// CEP:SECURITY: corruption detection.
fn cycle_detected() {
    let fixture = make_proof_fixture(4096);
    let a = constant(&fixture, "a");
    let literals = [lit(&fixture, "p", &[a], true)];
    let first = fixture
        .space
        .store
        .new_clause(&fixture.terms, &literals, 0, input_derivation())
        .expect("first");
    let first_id = fixture.space.store.clause(first).expect("read").id.0;
    // A second record citing a FUTURE id as its parent.
    let second = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            1,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 1,
                reserved: 0,
                parents: [
                    first_id + 10,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("second");
    let refutation = second.as_u32();
    assert_eq!(
        reachable_proof_ids(&fixture.space.store, refutation),
        Err(TstpError::CycleDetected(first_id + 10))
    );
}

// CEP:WHAT: The Input derivation template.
// CEP:WHY: Hand-built axiom records.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [
            mapt_config::limits::kInvalidClauseId,
            mapt_config::limits::kInvalidClauseId,
            mapt_config::limits::kInvalidClauseId,
            mapt_config::limits::kInvalidClauseId,
        ],
        substitution: mapt_config::limits::kInvalidClauseOffset,
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

#[test]
// CEP:WHAT: Roles and sources: inputs keep the axiom role, derived clauses are plain and cite inference(resolution, [], [parents]).
// CEP:WHY: Spec 14 section 5's presentation contract (the dedicated test for the writer's role/source citations).
// CEP:STATUS: complete
// CEP:FAILURE: panics on a wrong role or source.
// CEP:ASSUMES: the two-step scenario.
// CEP:COST: one render.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::roles_and_sources.
// CEP:SECURITY: none.
fn roles_and_sources() {
    let fixture = make_proof_fixture(4096);
    let (refutation, _unused_id) = refute_two_step(&fixture);
    let mut out = String::new();
    write_tstp_proof(
        &fixture.terms,
        &fixture.builder,
        &fixture.space.store,
        refutation,
        &mut out,
    )
    .expect("write");
    assert!(out.contains(", axiom, "));
    assert!(out.contains("inference(resolution, [], ["));
    assert!(out.contains(", plain, "));
}

#[test]
// CEP:WHAT: The empty clause renders $false.
// CEP:WHY: Spec 14 section 4's grammar for the refuting statement.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any other rendering.
// CEP:ASSUMES: the two-step scenario.
// CEP:COST: one render.
// CEP:EVIDENCE: backs unit/cold/tstp_test.rs::empty_clause_renders_false.
// CEP:SECURITY: none.
fn empty_clause_renders_false() {
    let fixture = make_proof_fixture(4096);
    let (refutation, _unused_id) = refute_two_step(&fixture);
    let mut out = String::new();
    write_tstp_proof(
        &fixture.terms,
        &fixture.builder,
        &fixture.space.store,
        refutation,
        &mut out,
    )
    .expect("write");
    let last = out.lines().last().expect("statements");
    assert!(last.contains("plain, $false"), "the empty clause: {}", last);
}
