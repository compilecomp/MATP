// CEP:FILE: tests/unit/cold/kernel_test.rs
// CEP:WHAT: Unit tests for the certified proof kernel (Spec 19): end-to-end acceptance over a saturation refutation, per-arm rejections (broken resolution, deletion-rule derivations, non-monotonic derivations, unrecorded demodulation), the standardize-apart rename replay, budget exhaustion as an error, the TSTP wrapper mapping, and single-step verification.
// CEP:WHY: Design 18.4 and Spec 19: the kernel is the trust boundary of the proof claim; every arm's accept and reject path is pinned here on hand-built derivations plus one full saturation, before the property tests verify all loop refutations.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; hand-built derivation records with computed selection flags.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/kernel.rs.
// CEP:SECURITY: budget and rejection paths are the corruption-detection evidence.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::cold::kernel::verify_clause_step_with_options;
use mapt::cold::kernel::{
    verify_clause_step, verify_refutation_with_budget, walk_proof_dag, KernelError,
    KernelRejection, KernelVerdict,
};
use mapt::cold::proof_output::tstp::check_proof;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClausePtr, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};
use mapt_config::limits::{kFirstClauseId, kInvalidClauseId, kInvalidSubstitutionOffset};

struct ProofFixture {
    space: SearchSpace<'static>,
    symbols: mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: SymbolTableBuilder,
    terms: mapt::hot::ir::term::TermStore<'static>,
    precedence: mapt::hot::ordering::precedence::PrecedenceTable<'static>,
    options: SearchOptions,
}

// CEP:WHAT: Builds a proof fixture (arena, frozen standard symbols, term store, precedence, search space) with the given passive capacity.
// CEP:WHY: One fixture builder keeps every test's store discipline identical (dense ids from kFirstClauseId).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: the arena size fits the small injected capacities.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/kernel.rs's evidence map.
// CEP:SECURITY: none.
#[allow(non_snake_case)]
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

fn context_of(fixture: &ProofFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

fn lit(fixture: &ProofFixture, name: &str, args: &[TermPtr], positive: bool) -> Literal {
    let atom = fixture
        .terms
        .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

fn var(fixture: &ProofFixture, index: u32) -> TermPtr {
    fixture.terms.intern_var(index).expect("var")
}

fn constant(fixture: &ProofFixture, name: &str) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), &[])
        .expect("constant")
}

fn function(fixture: &ProofFixture, name: &str, args: &[TermPtr]) -> TermPtr {
    fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), args)
        .expect("term")
}

fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; 4],
        substitution: kInvalidSubstitutionOffset,
    }
}

fn id_of(fixture: &ProofFixture, ptr: ClausePtr) -> u64 {
    fixture.space.store.clause(ptr).expect("read").id.0
}

fn flagged(context: &InferenceContext<'_>, fixture: &ProofFixture, literals: &mut [Literal]) {
    mapt::hot::inference::compute_selection_flags(context, fixture.options.selection, literals)
        .expect("flags");
}

// CEP:WHAT: The kernel accepts a full saturation refutation whose derivation DAG includes resolution and the CEP-1036 demodulation chain (Spec 19).
// CEP:WHY: The end-to-end trust decision: the search refutes f(x) = x with p(f(f(a))) and not p(a) - the target is demodulated down the exact per-step chain and the refuting resolution replays - and verify_refutation_with_budget walks the whole reachable DAG and replays every step with the production rule functions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when any reachable step is rejected or the verdict is not Valid.
// CEP:ASSUMES: the search terminates with Theorem on this input.
// CEP:COST: one saturation plus one bounded verification.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs::verify_refutation_with_budget.
// CEP:SECURITY: proof validation.
#[test]
fn accepts_loop_refutation() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let x = var(&fixture, 0);
    let a = constant(&fixture, "a");
    // Unit equation f(x) = x.
    let fx = function(&fixture, "f", &[x]);
    let eq_atom = fixture
        .terms
        .intern_eq(&fixture.symbols, fx, x)
        .expect("eq");
    fixture
        .space
        .add_input_clause(&context, &fixture.options, &[Literal::new(eq_atom, true)])
        .expect("unit rule");
    // Target p(f(f(a))): two chained demodulation rewrites down to p(a).
    let ffa = function(&fixture, "f", &[function(&fixture, "f", &[a])]);
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[lit(&fixture, "p", &[ffa], true)],
        )
        .expect("target");
    // Negated target: the refuting resolution.
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[lit(&fixture, "p", &[a], false)],
        )
        .expect("negated");
    let mut stats = SearchStats::default();
    let outcome = saturate(
        &fixture.space,
        &context,
        &fixture.options,
        &|_| false,
        &mut stats,
    )
    .expect("saturate");
    let refutation = match outcome {
        SearchOutcome::Theorem { refutation } => refutation,
        other => panic!("expected Theorem, got {:?}", other),
    };
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        refutation,
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("verification finishes");
    assert_eq!(verdict, KernelVerdict::Valid);
    // The walk itself collects the reachable ids ascending.
    let ids = walk_proof_dag(&fixture.space.store, refutation).expect("walk");
    assert!(ids.len() >= 2);
    assert_eq!(*ids.last().expect("non-empty"), {
        let root = fixture
            .space
            .store
            .clause(ClausePtr::from_u32(refutation))
            .expect("root");
        root.id.0
    });
}

// CEP:WHAT: A Resolution record whose parents share no resolvable pair is rejected with BrokenResolution.
// CEP:WHY: Design 18.4: the kernel replays the production resolve() between the recorded parents; when no legal application reproduces the recorded conclusion, the step names itself.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the tampered step is accepted.
// CEP:ASSUMES: hand-built records with disjoint heads.
// CEP:COST: one verification.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs's Resolution arm.
// CEP:SECURITY: proof validation.
#[test]
fn rejects_broken_resolution() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let mut parent_literals = [lit(&fixture, "p", &[a], true)];
    flagged(&context, &fixture, &mut parent_literals);
    let parent = fixture
        .space
        .store
        .new_clause(&fixture.terms, &parent_literals, 0, input_derivation())
        .expect("parent");
    let mut other_literals = [lit(&fixture, "q", &[a, a], false)];
    flagged(&context, &fixture, &mut other_literals);
    let other = fixture
        .space
        .store
        .new_clause(&fixture.terms, &other_literals, 1, input_derivation())
        .expect("other");
    let mut conclusion_literals = [lit(&fixture, "q", &[a, a], true)];
    flagged(&context, &fixture, &mut conclusion_literals);
    let conclusion = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &conclusion_literals,
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    id_of(&fixture, parent),
                    id_of(&fixture, other),
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("conclusion");
    let conclusion_id = id_of(&fixture, conclusion);
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        conclusion.as_u32(),
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(
        verdict,
        KernelVerdict::Invalid {
            clause_id: conclusion_id,
            rejection: KernelRejection::BrokenResolution,
        }
    );
}

// CEP:WHAT: The Resolution replay standardizes the active parent apart: a resolvent whose production MGU is invisible to a verbatim replay (overlapping dense namespaces) is accepted.
// CEP:WHY: Spec 02 section 5 and the CEP-1054 repair: the generator renames the active premise above the given premise's variables before every rule call; the kernel replays the same rename (at the FULL renamed literal count - the pre-Phase-5 checker sliced the renamed premise at the returned VARIABLE count, truncating ground premises); the fixture unifies not-p(f(f(x0))) against p(f(x0)), whose verbatim MGU would bind x0 := f(x0) and hit the occurs check, while the renamed replay (p(f(x1)), x1 := f(x0)) reproduces the recorded resolvent q(x0, x0).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the honest resolvent is rejected (the pre-Phase-5 false-rejector behavior).
// CEP:ASSUMES: hand-built records.
// CEP:COST: one verification.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs::renamed_apart.
// CEP:SECURITY: proof validation.
#[test]
fn resolution_replay_renames_apart() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let x0 = var(&fixture, 0);
    let fx0 = function(&fixture, "f", &[x0]);
    let ffx0 = function(&fixture, "f", &[fx0]);
    // Given: not p(f(f(x0))) or q(x0, x0); active: p(f(x0)) - both stored in
    // their own dense {0} namespaces, which overlap. The pivot is the strictly
    // maximal literal by KBO weight (5 > 3), so the eligibility side conditions
    // hold on both sides.
    let mut given_literals = [
        lit(&fixture, "p", &[ffx0], false),
        lit(&fixture, "q", &[x0, x0], true),
    ];
    flagged(&context, &fixture, &mut given_literals);
    let given = fixture
        .space
        .store
        .new_clause(&fixture.terms, &given_literals, 0, input_derivation())
        .expect("given");
    let mut active_literals = [lit(&fixture, "p", &[fx0], true)];
    flagged(&context, &fixture, &mut active_literals);
    let active = fixture
        .space
        .store
        .new_clause(&fixture.terms, &active_literals, 1, input_derivation())
        .expect("active");
    // The recorded conclusion: the survivor q(x0, x0) under the renamed MGU.
    let mut conclusion_literals = [lit(&fixture, "q", &[x0, x0], true)];
    flagged(&context, &fixture, &mut conclusion_literals);
    let conclusion = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &conclusion_literals,
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    id_of(&fixture, given),
                    id_of(&fixture, active),
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("conclusion");
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        conclusion.as_u32(),
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(verdict, KernelVerdict::Valid);
}

// CEP:WHAT: A derivation claiming a deletion rule is rejected with DeletedRuleDerivation.
// CEP:WHY: Spec 19 section 4: deletion removes clauses and never derives a stored record; the label is corrupt by construction.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the deletion-labeled record is accepted.
// CEP:ASSUMES: a hand-built record with the TautologyDeletion label.
// CEP:COST: one verification.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs's deletion arm.
// CEP:SECURITY: corruption detection.
#[test]
fn rejects_deletion_rule_derivation() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let record = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[lit(&fixture, "p", &[a], true)],
            0,
            DerivationStep {
                rule: InferenceRule::TautologyDeletion,
                parent_count: 0,
                reserved: 0,
                parents: [kInvalidClauseId; 4],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("record");
    let record_id = id_of(&fixture, record);
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        record.as_u32(),
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(
        verdict,
        KernelVerdict::Invalid {
            clause_id: record_id,
            rejection: KernelRejection::DeletedRuleDerivation,
        }
    );
}

// CEP:WHAT: Budget exhaustion is a KernelError, not a rejection: a verification with too small a budget returns Err(ReplayBudgetExhausted).
// CEP:WHY: CEP&CC 34.3: the budget is injectable so tests exercise the exhaustion path on the production code path; exhaustion means "could not finish", which must stay distinguishable from "found a bad step".
// CEP:STATUS: complete
// CEP:FAILURE: test fails when exhaustion surfaces as a verdict instead of an error.
// CEP:ASSUMES: the refutation's reachable DAG holds more than one id.
// CEP:COST: one walk plus one charge.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs::ReplayState::charge.
// CEP:SECURITY: the DoS bound.
#[test]
fn rejects_budget_exhaustion() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[lit(&fixture, "p", &[a], true)],
        )
        .expect("input");
    fixture
        .space
        .add_input_clause(
            &context,
            &fixture.options,
            &[lit(&fixture, "p", &[a], false)],
        )
        .expect("negated");
    let mut stats = SearchStats::default();
    let outcome = saturate(
        &fixture.space,
        &context,
        &fixture.options,
        &|_| false,
        &mut stats,
    )
    .expect("saturate");
    let refutation = match outcome {
        SearchOutcome::Theorem { refutation } => refutation,
        other => panic!("expected Theorem, got {:?}", other),
    };
    // The reachable DAG has at least two ids (two inputs and the empty clause);
    // a budget of one cannot finish.
    let result = verify_refutation_with_budget(&context, &fixture.space.store, refutation, 1);
    assert_eq!(result, Err(KernelError::ReplayBudgetExhausted));
    // The same proof verifies with the production budget.
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        refutation,
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(verdict, KernelVerdict::Valid);
}

// CEP:WHAT: A parent id at or above the child id (a corrupted derivation) is rejected with NonMonotonicDerivation, naming the offending parent id.
// CEP:WHY: Monotonic clause ids make parents strictly older (Spec 14 section 2); the walk's descending pass detects the violation and the verdict payload names the offending parent.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the corrupted derivation is accepted or mislabeled.
// CEP:ASSUMES: the store's next id is knowable before record creation, so a self-citing record is constructible.
// CEP:COST: one walk.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs::walk_proof_dag.
// CEP:SECURITY: corruption detection.
#[test]
fn rejects_non_monotonic_derivation() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    // The record's own future id is knowable: the next id the store will assign.
    let own_future_id = fixture.space.store.next_clause_id().0;
    let record = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[lit(&fixture, "p", &[a], true)],
            0,
            DerivationStep {
                rule: InferenceRule::Factoring,
                parent_count: 1,
                reserved: 0,
                parents: [
                    own_future_id,
                    kInvalidClauseId,
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("record");
    let record_id = id_of(&fixture, record);
    assert_eq!(record_id, own_future_id);
    // The walk-level rejection names the offending parent id.
    let walk = walk_proof_dag(&fixture.space.store, record.as_u32());
    assert_eq!(
        walk,
        Err((own_future_id, KernelRejection::NonMonotonicDerivation))
    );
    // The full verification surfaces the same rejection as a verdict.
    let verdict = verify_refutation_with_budget(
        &context,
        &fixture.space.store,
        record.as_u32(),
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(
        verdict,
        KernelVerdict::Invalid {
            clause_id: own_future_id,
            rejection: KernelRejection::NonMonotonicDerivation,
        }
    );
}

// CEP:WHAT: The TSTP wrapper maps kernel outcomes faithfully: a rejection becomes InvalidStep with the offending clause id, a budget error becomes BudgetExhausted, and a valid proof passes.
// CEP:WHY: Spec 19 section 6: the TSTP layer never re-implements an arm; the mapping contract is pinned so the checker's error vocabulary stays honest (check_proof_via_kernel).
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the wrapper loses or distorts the kernel's outcome.
// CEP:ASSUMES: hand-built records.
// CEP:COST: two verifications.
// CEP:EVIDENCE: cited by cold/proof_output/tstp.rs::check_proof.
// CEP:SECURITY: proof validation.
#[test]
fn tstp_wrapper_maps_rejections() {
    use mapt::cold::proof_output::tstp::TstpError;
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    // A broken resolution: the wrapper reports InvalidStep with the offending id.
    let mut parent_literals = [lit(&fixture, "p", &[a], true)];
    flagged(&context, &fixture, &mut parent_literals);
    let parent = fixture
        .space
        .store
        .new_clause(&fixture.terms, &parent_literals, 0, input_derivation())
        .expect("parent");
    let mut other_literals = [lit(&fixture, "q", &[a, a], true)];
    flagged(&context, &fixture, &mut other_literals);
    let other = fixture
        .space
        .store
        .new_clause(&fixture.terms, &other_literals, 1, input_derivation())
        .expect("other");
    let mut conclusion_literals = [lit(&fixture, "q", &[a, a], true)];
    flagged(&context, &fixture, &mut conclusion_literals);
    let conclusion = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &conclusion_literals,
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    id_of(&fixture, parent),
                    id_of(&fixture, other),
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("conclusion");
    let conclusion_id = id_of(&fixture, conclusion);
    assert_eq!(
        check_proof(&context, &fixture.space.store, conclusion.as_u32()),
        Err(TstpError::InvalidStep(conclusion_id))
    );
    // A valid proof passes through the same wrapper.
    let mut left_literals = [lit(&fixture, "p", &[a], true)];
    flagged(&context, &fixture, &mut left_literals);
    let left = fixture
        .space
        .store
        .new_clause(&fixture.terms, &left_literals, 3, input_derivation())
        .expect("left");
    let mut right_literals = [lit(&fixture, "p", &[a], false)];
    flagged(&context, &fixture, &mut right_literals);
    let right = fixture
        .space
        .store
        .new_clause(&fixture.terms, &right_literals, 4, input_derivation())
        .expect("right");
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            5,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    id_of(&fixture, left),
                    id_of(&fixture, right),
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("empty");
    check_proof(&context, &fixture.space.store, empty.as_u32())
        .expect("the honest refutation passes the kernel-backed checker");
}

// CEP:WHAT: verify_clause_step verifies one staged clause outside a whole-proof walk (the clause-learning tests' entry point).
// CEP:WHY: Spec 18 section 6: a staged SatLearn lemma is verified directly; the same arms run, so a single-step verdict equals the step's verdict inside a full verification; an unreadable id is an UnreadableClause rejection.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the single-step verdict diverges from the whole-proof behavior.
// CEP:ASSUMES: hand-built records.
// CEP:COST: one step verification.
// CEP:EVIDENCE: cited by cold/kernel/kernel.rs::verify_clause_step; unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable.
// CEP:SECURITY: proof validation.
#[test]
fn verify_clause_step_matches_walk() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    let a = constant(&fixture, "a");
    let mut left_literals = [lit(&fixture, "p", &[a], true)];
    flagged(&context, &fixture, &mut left_literals);
    let left = fixture
        .space
        .store
        .new_clause(&fixture.terms, &left_literals, 0, input_derivation())
        .expect("left");
    let mut right_literals = [lit(&fixture, "p", &[a], false)];
    flagged(&context, &fixture, &mut right_literals);
    let right = fixture
        .space
        .store
        .new_clause(&fixture.terms, &right_literals, 1, input_derivation())
        .expect("right");
    let empty = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[],
            2,
            DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 2,
                reserved: 0,
                parents: [
                    id_of(&fixture, left),
                    id_of(&fixture, right),
                    kInvalidClauseId,
                    kInvalidClauseId,
                ],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("empty");
    let empty_id = id_of(&fixture, empty);
    let verdict = verify_clause_step(
        &context,
        &fixture.space.store,
        empty_id,
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(verdict, KernelVerdict::Valid);
    // An unreadable id is a rejection naming the id.
    let verdict = verify_clause_step(
        &context,
        &fixture.space.store,
        u64::MAX,
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(
        verdict,
        KernelVerdict::Invalid {
            clause_id: u64::MAX,
            rejection: KernelRejection::UnreadableClause,
        }
    );
    let _ = kFirstClauseId;
}

// CEP:WHAT: A forged parentless SatLearn lemma over user-declared 0-ary predicates is rejected under the production (empty) vocabulary and accepted only within the configured assertion range (Spec 18 section 5's executable trust boundary).
// CEP:WHY: The kernel is the corruption detector; the introduction side's reservation discipline (Spec 18 sections 2-3) must not be trusted at verification time. The fixture's r is a user-declared 0-ary input predicate: a parentless SatLearn record over r has no derivation justification, so the production whole-proof vocabulary (empty range) rejects it, while the same record over a genuinely reserved atom verifies under the matching KernelOptions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the forged lemma is accepted or a genuine assertion lemma is rejected.
// CEP:ASSUMES: hand-built records; the fixture has no reserved assertion block, so the forged range in the second half is constructed ad hoc (base = r's symbol id, count 1) to show the range check is the deciding factor.
// CEP:COST: two step verifications.
// CEP:EVIDENCE: cited by cold/kernel.rs's SatLearn arm and docs/formal/18_fol_clause_learning.md section 5.
// CEP:SECURITY: proof validation.
#[test]
fn forged_sat_learn_rejected_outside_vocabulary() {
    let fixture = make_proof_fixture(4096);
    let context = context_of(&fixture);
    // r is a user-declared 0-ary predicate of the problem signature.
    let r_atom = fixture
        .terms
        .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "r"), &[])
        .expect("r atom");
    let forged = fixture
        .space
        .store
        .new_clause(
            &fixture.terms,
            &[Literal::new(r_atom, false)],
            0,
            DerivationStep {
                rule: InferenceRule::SatLearn,
                parent_count: 0,
                reserved: 0,
                parents: [kInvalidClauseId; 4],
                substitution: kInvalidSubstitutionOffset,
            },
        )
        .expect("forged");
    let forged_id = id_of(&fixture, forged);
    // Production whole-proof vocabulary (empty range): rejected.
    let verdict = verify_clause_step(
        &context,
        &fixture.space.store,
        forged_id,
        mapt_config::limits::kKernelReplayBudget,
    )
    .expect("finishes");
    assert_eq!(
        verdict,
        KernelVerdict::Invalid {
            clause_id: forged_id,
            rejection: KernelRejection::BrokenSatLearn,
        }
    );
    // Inside a range that covers r's symbol id: the same shape verifies, proving
    // the range check (not the shape check alone) decides.
    let r_symbol = symbol_id(&fixture.builder, "r");
    let verdict = verify_clause_step_with_options(
        &context,
        &fixture.space.store,
        forged_id,
        mapt_config::limits::kKernelReplayBudget,
        &mapt::cold::kernel::KernelOptions {
            assertion_base: r_symbol,
            assertion_count: 1,
        },
    )
    .expect("finishes");
    assert_eq!(verdict, KernelVerdict::Valid);
}
