// CEP:FILE: tests/unit/hot/sat_cdcl_test.rs
// CEP:WHAT: Unit tests for CDCL conflict analysis: level and reason recording, the first-UIP walk on hand-built implication graphs, backjump level and LBD derivation, learnt-clause minimization, and generation hygiene.
// CEP:WHY: CEP&CC 32.8 and Formal Spec 06: the learnt clause is the engine's only learning mechanism; a wrong UIP or backjump level produces unsound or looping search; every graph below is hand-traced against the BCP watch semantics (clauses attach at level 0, decisions falsify watches, blockers prevent premature units).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; conflicts produced by BCP.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/cdcl.rs and the level/reason extensions of hot/sat/database.rs.
// CEP:SECURITY: level-zero and malformed conflicts are exercised here.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::cdcl::{CdclError, ConflictAnalyzer};
use mapt::hot::sat::database::SatCore;
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::vsids::VsidsHeap;

// CEP:WHAT: Variables used by the hand-built implication graphs.
// CEP:WHY: Named constant keeps the graphs readable (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kGraphVariables: u32 = 12;

// CEP:WHAT: Arena bytes for one core plus analyzer plus VSIDS heap.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kGraphArenaBytes: u32 = 4_194_304;

// CEP:WHAT: Builds a literal or fails the test.
// CEP:WHY: Readable graph construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kGraphVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Propagates and extracts the conflict offset, panicking when there is none.
// CEP:WHY: Graph fixtures must reach their conflict through BCP, never by construction shortcuts.
// CEP:STATUS: complete
// CEP:FAILURE: panics when propagation does not conflict.
// CEP:ASSUMES: the graph is in a conflicting state.
// CEP:COST: one propagation.
// CEP:EVIDENCE: used by the graph fixtures in this file.
// CEP:SECURITY: none.
fn propagate_conflict(core: &SatCore<'_>) -> u32 {
    match core.propagate().expect("propagate") {
        PropagationOutcome::Conflict(offset) => offset,
        PropagationOutcome::NoConflict => panic!("expected the graph to conflict"),
    }
}

// CEP:WHAT: Graph 1: level-0 unit over 0; level-1 decision 1 propagating 2 and 3; binary conflict clause over the propagated pair.
// CEP:WHY: The propagated pair is assigned in one dequeue batch, so the first watch scan sees a true blocker and the second scan reports the conflict at level 1; the walk resolves 2 and 3 through their reasons into the decision literal 1, producing the unit learnt clause (-1).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction step.
// CEP:ASSUMES: fresh arena.
// CEP:COST: constant.
// CEP:EVIDENCE: used by first_uip_is_last_current_level_literal and repeated_analyses_are_independent.
// CEP:SECURITY: none.
fn build_level_one_conflict() -> (
    SatCore<'static>,
    ConflictAnalyzer<'static>,
    VsidsHeap<'static>,
    u32,
) {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    let _ = core.add_clause(&[lit(0, true)]).expect("unit 0");
    let _ = core
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("clause 2");
    let _ = core
        .add_clause(&[lit(1, false), lit(3, true)])
        .expect("clause 3");
    let _ = core
        .add_clause(&[lit(2, false), lit(3, false)])
        .expect("conflict clause");
    let _ = core.propagate().expect("propagate level 0");
    core.decide(lit(1, true)).expect("decide 1");
    let conflict = propagate_conflict(&core);
    (core, analyzer, vsids, conflict)
}

// CEP:WHAT: Graph 2: level-2 conflict over a ternary clause; the level-1 pair blocks and moves watches so the conflict waits for the level-2 decision.
// CEP:WHY: Produces a two-level learnt clause (-4, -2, -3) with backjump level 1 and LBD 2.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction step.
// CEP:ASSUMES: fresh arena.
// CEP:COST: constant.
// CEP:EVIDENCE: used by backjump_level_is_max_other_level and lbd_counts_distinct_levels.
// CEP:SECURITY: none.
fn build_level_two_conflict() -> (
    SatCore<'static>,
    ConflictAnalyzer<'static>,
    VsidsHeap<'static>,
    u32,
) {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    let _ = core.add_clause(&[lit(0, true)]).expect("unit 0");
    let _ = core
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("clause 2");
    let _ = core
        .add_clause(&[lit(1, false), lit(3, true)])
        .expect("clause 3");
    // The conflict clause over 2, 3 (level 1) and 5, 6 (level 2): at level 1 the scans
    // move the watches onto 5 and 6 (both unassigned spares); at level 2 the decision on
    // 4 propagates 5 and 6 true in one batch, so the first falsification blocks on the
    // true other watch and the second reports the conflict.
    let _ = core
        .add_clause(&[lit(2, false), lit(3, false), lit(5, false), lit(6, false)])
        .expect("conflict clause");
    let _ = core
        .add_clause(&[lit(4, false), lit(5, true)])
        .expect("clause 5");
    let _ = core
        .add_clause(&[lit(4, false), lit(6, true)])
        .expect("clause 6");
    let _ = core.propagate().expect("propagate level 0");
    core.decide(lit(1, true)).expect("decide 1");
    let _ = core.propagate().expect("propagate level 1");
    core.decide(lit(4, true)).expect("decide 4");
    let conflict = propagate_conflict(&core);
    (core, analyzer, vsids, conflict)
}

// CEP:WHAT: Graph 3: level-2 conflict with a chained level-1 propagation, producing a learnt clause with one covered literal for minimization.
// CEP:WHY: The learnt clause before minimization is (-4, -3, -2); literal ~3's reason (-2 v 3) is covered by ~2 in the learnt set (dropped), while ~2's reason (-1 v 2) reaches the decision 1 (kept).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction step.
// CEP:ASSUMES: fresh arena.
// CEP:COST: constant.
// CEP:EVIDENCE: used by minimization_removes_redundant_literals and minimization_keeps_decision_literals.
// CEP:SECURITY: none.
fn build_minimization_conflict() -> (
    SatCore<'static>,
    ConflictAnalyzer<'static>,
    VsidsHeap<'static>,
    u32,
) {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    let _ = core.add_clause(&[lit(0, true)]).expect("unit 0");
    // Level 1 chain: decide 1, propagate 2 (reason A), then 3 (reason B, chained through 2).
    let _ = core
        .add_clause(&[lit(1, false), lit(2, true)])
        .expect("clause A");
    let _ = core
        .add_clause(&[lit(2, false), lit(3, true)])
        .expect("clause B");
    // Conflict clause over 2, 3 (level 1) and 5, 6 (level 2 propagated by the decision
    // on 4); the pre-minimization learnt clause is (-4, -3, -2) where ~3 is covered.
    let _ = core
        .add_clause(&[lit(2, false), lit(3, false), lit(5, false), lit(6, false)])
        .expect("conflict clause");
    let _ = core
        .add_clause(&[lit(4, false), lit(5, true)])
        .expect("clause E");
    let _ = core
        .add_clause(&[lit(4, false), lit(6, true)])
        .expect("clause F");
    let _ = core.propagate().expect("propagate level 0");
    core.decide(lit(1, true)).expect("decide 1");
    let _ = core.propagate().expect("propagate level 1");
    core.decide(lit(4, true)).expect("decide 4");
    let conflict = propagate_conflict(&core);
    (core, analyzer, vsids, conflict)
}

// CEP:WHAT: Verifies BCP records levels and reasons for propagated literals.
// CEP:WHY: The implication graph is walkable only if assign_with_reason was used by BCP and attach.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missing level or reason.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs assign_with_reason and hot/sat/bcp.rs scan_watch_list.
// CEP:SECURITY: none.
#[test]
fn reasons_recorded() {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    // Unit clause forces variable 1 at level 0 with the unit as its reason.
    let unit = core.add_clause(&[lit(1, true)]).expect("unit");
    let offset = match unit {
        mapt::hot::sat::database::AttachOutcome::UnitEnqueued(offset) => offset,
        other => panic!("expected unit enqueue, got {:?}", other),
    };
    let _ = core.propagate().expect("propagate");
    assert_eq!(core.level_of(1), 0);
    assert_eq!(core.reason_of(1), offset);
    // A propagated literal at a deeper level: decide variable 2, then (-2 v 3) propagates 3.
    let attached = core
        .add_clause(&[lit(2, false), lit(3, true)])
        .expect("clause");
    let _ = attached;
    core.decide(lit(2, true)).expect("decide");
    let outcome = core.propagate().expect("propagate");
    assert_eq!(outcome, PropagationOutcome::NoConflict);
    assert_eq!(core.level_of(3), 1);
    let reason = core.reason_of(3);
    assert_ne!(
        reason,
        mapt_config::limits::kInvalidClauseOffset,
        "propagated literals must carry their reason clause"
    );
}

// CEP:WHAT: Verifies decisions and root assignments carry no reason.
// CEP:WHY: Reasonless assignments terminate reason chains; treating a decision as propagated would corrupt analysis.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a phantom reason.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs decide and assign.
// CEP:SECURITY: none.
#[test]
fn root_assignment_has_no_reason() {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    core.assign(lit(0, true)).expect("assign");
    assert_eq!(core.reason_of(0), mapt_config::limits::kInvalidClauseOffset);
    core.decide(lit(1, false)).expect("decide");
    assert_eq!(core.reason_of(1), mapt_config::limits::kInvalidClauseOffset);
    assert_eq!(core.level_of(1), 1);
}

// CEP:WHAT: Verifies cancel_until clears levels and reasons of popped variables.
// CEP:WHY: Stale levels would corrupt every later analysis.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on stale state.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs cancel_until.
// CEP:SECURITY: none.
#[test]
fn cancel_clears_levels() {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let _ = core
        .add_clause(&[lit(1, false), lit(3, true)])
        .expect("clause");
    core.decide(lit(1, true)).expect("decide");
    let _ = core.propagate().expect("propagate");
    assert_eq!(core.level_of(3), 1);
    assert_ne!(core.reason_of(3), mapt_config::limits::kInvalidClauseOffset);
    core.cancel_until(0);
    assert_eq!(core.level_of(1), 0);
    assert_eq!(core.level_of(3), 0);
    assert_eq!(core.reason_of(3), mapt_config::limits::kInvalidClauseOffset);
}

// CEP:WHAT: Verifies the first UIP is the last current-level literal on the trail and the learnt clause is its negation.
// CEP:WHY: Spec 06 sections 4-5: the walk resolves every current-level literal except one; here the conflict (-2, -3) at level 1 resolves 2 and 3 through their binary reasons into the decision literal 1, so the learnt clause is the unit (-1).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong asserting literal.
// CEP:ASSUMES: graph 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: none.
#[test]
fn first_uip_is_last_current_level_literal() {
    let (core, analyzer, vsids, conflict) = build_level_one_conflict();
    let mut buffer = [lit(0, true); 64];
    let outcome = analyzer
        .analyze(&core, &vsids, conflict, &mut buffer)
        .expect("analyze");
    assert_eq!(
        outcome.literal_count, 1,
        "the walk must resolve 2 and 3 into the decision literal 1"
    );
    assert_eq!(buffer[0], lit(1, false), "the asserting literal is ~1");
    assert_eq!(
        outcome.backjump_level, 0,
        "a unit learnt clause backjumps to level 0"
    );
}

// CEP:WHAT: Verifies the backjump level is the maximum level among non-asserting literals.
// CEP:WHY: Design 11.1 S22; graph 2 yields the learnt clause (-4, -2, -3) with the level-1 literals below the level-2 asserting literal.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong level or count.
// CEP:ASSUMES: graph 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: none.
#[test]
fn backjump_level_is_max_other_level() {
    let (core, analyzer, vsids, conflict) = build_level_two_conflict();
    let mut buffer = [lit(0, true); 64];
    let analysis = analyzer
        .analyze(&core, &vsids, conflict, &mut buffer)
        .expect("analyze");
    assert_eq!(analysis.literal_count, 3, "learnt is (-4, -2, -3)");
    assert_eq!(buffer[0], lit(4, false), "asserting literal is ~4");
    assert_eq!(
        analysis.backjump_level, 1,
        "backjump to the level of the level-1 literals"
    );
}

// CEP:WHAT: Verifies the LBD counts distinct decision levels.
// CEP:WHY: Design 11.1 S23; graph 2's learnt clause spans levels 2 and 1.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a wrong count.
// CEP:ASSUMES: graph 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: none.
#[test]
fn lbd_counts_distinct_levels() {
    let (core, analyzer, vsids, conflict) = build_level_two_conflict();
    let mut buffer = [lit(0, true); 64];
    let analysis = analyzer
        .analyze(&core, &vsids, conflict, &mut buffer)
        .expect("analyze");
    assert_eq!(analysis.lbd, 2, "one literal at level 2, two at level 1");
}

// CEP:WHAT: Verifies repeated analyses are independent (generation hygiene).
// CEP:WHY: Stale seen marks would corrupt every analysis after the first.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the replayed analysis differs.
// CEP:ASSUMES: graph 1, replayed after cancellation.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: none.
#[test]
fn repeated_analyses_are_independent() {
    let (core, analyzer, vsids, conflict) = build_level_one_conflict();
    let mut first = [lit(0, true); 64];
    let outcome_first = analyzer
        .analyze(&core, &vsids, conflict, &mut first)
        .expect("first analyze");
    // Replay the same decisions on the same clause set.
    core.cancel_until(0);
    core.decide(lit(1, true)).expect("decide again");
    let conflict_two = propagate_conflict(&core);
    let mut second = [lit(0, true); 64];
    let outcome_second = analyzer
        .analyze(&core, &vsids, conflict_two, &mut second)
        .expect("second analyze");
    assert_eq!(outcome_first, outcome_second);
    assert_eq!(first[0], second[0]);
}

// CEP:WHAT: Verifies analysis at level zero is rejected loudly.
// CEP:WHY: A level-0 conflict is UNSAT, decided by the caller before analysis.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if level zero is accepted.
// CEP:ASSUMES: two units and a falsified binary clause at level 0.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs analyze.
// CEP:SECURITY: caller-discipline enforcement.
#[test]
fn level_zero_rejected() {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    // Units over 5 and 6 plus (-5 v -6): the second dequeue falsifies the last non-false
    // literal of the binary clause, conflicting at level 0.
    let _ = core.add_clause(&[lit(5, true)]).expect("unit 5");
    let _ = core.add_clause(&[lit(6, true)]).expect("unit 6");
    let _ = core
        .add_clause(&[lit(5, false), lit(6, false)])
        .expect("binary");
    let conflict = propagate_conflict(&core);
    let mut buffer = [lit(0, true); 64];
    assert_eq!(
        analyzer.analyze(&core, &vsids, conflict, &mut buffer),
        Err(CdclError::LevelZeroConflict)
    );
}

// CEP:WHAT: Verifies minimization drops literals whose reason chains are covered by the learnt set.
// CEP:WHY: Spec 06 section 6: graph 3's pre-minimization learnt clause is (-4, -3, -2); ~3's reason (-2 v 3) is covered by ~2 (seen), so ~3 is dropped, while ~2's reason (-1 v 2) reaches the decision 1 and ~2 stays.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the covered literal survives or the decision-blocked literal is dropped.
// CEP:ASSUMES: graph 3.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs literal_redundant.
// CEP:SECURITY: none.
#[test]
fn minimization_removes_redundant_literals() {
    let (core, analyzer, vsids, conflict) = build_minimization_conflict();
    let mut buffer = [lit(0, true); 64];
    let analysis = analyzer
        .analyze(&core, &vsids, conflict, &mut buffer)
        .expect("analyze");
    assert_eq!(
        analysis.literal_count, 2,
        "minimization must drop the covered literal ~3 and keep ~2"
    );
    assert_eq!(buffer[0], lit(4, false));
    assert_eq!(buffer[1].variable(), SatVar(2));
    assert_eq!(analysis.backjump_level, 1);
}

// CEP:WHAT: Verifies decision literals never enter the learnt clause through minimization and decision-blocked literals survive.
// CEP:WHY: A decision has no reason clause; the chain check must stop at it and keep the literal.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if variable 1 (the decision) leaks into the learnt clause.
// CEP:ASSUMES: graph 3.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs literal_redundant.
// CEP:SECURITY: none.
#[test]
fn minimization_keeps_decision_literals() {
    let (core, analyzer, vsids, conflict) = build_minimization_conflict();
    let mut buffer = [lit(0, true); 64];
    let analysis = analyzer
        .analyze(&core, &vsids, conflict, &mut buffer)
        .expect("analyze");
    let mut saw_two = false;
    for literal in buffer.iter().take(analysis.literal_count as usize) {
        assert_ne!(
            literal.variable(),
            SatVar(1),
            "the level-1 decision must never enter the learnt clause here"
        );
        if literal.variable() == SatVar(2) {
            saw_two = true;
        }
    }
    assert!(saw_two, "the decision-blocked literal ~2 must survive");
}

// CEP:WHAT: Verifies analysis construction requires arena room.
// CEP:WHY: Law 6: allocation failures are loud.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a tiny arena is accepted.
// CEP:ASSUMES: undersized arena.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs new.
// CEP:SECURITY: none.
#[test]
fn construction_requires_arena_room() {
    let arena = make_arena(64);
    assert!(ConflictAnalyzer::new(arena, kGraphVariables).is_err());
}

// CEP:WHAT: Verifies a conflict clause with no literal at the current level is rejected as malformed.
// CEP:WHY: Caller discipline (clauses only at level 0) makes this state unreachable through the solver; the analyzer still refuses it loudly (Law 6) instead of walking the trail into an underflow.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the malformed conflict is analyzed.
// CEP:ASSUMES: a fully level-0-falsified clause plus an unrelated level-1 decision.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/cdcl.rs CdclError.
// CEP:SECURITY: caller-discipline enforcement.
#[test]
fn malformed_conflict_rejected() {
    let arena = make_arena(kGraphArenaBytes);
    let core = SatCore::new(arena, kGraphVariables).expect("core");
    let analyzer = ConflictAnalyzer::new(arena, kGraphVariables).expect("analyzer");
    let vsids = VsidsHeap::new(arena, kGraphVariables).expect("vsids");
    // Level 0: units over 0 and 1, then a clause (-0, -1) that is fully falsified at
    // level 0; attach succeeds (both watches false) and BCP never rescans it.
    let _ = core.add_clause(&[lit(0, true)]).expect("unit 0");
    let _ = core.add_clause(&[lit(1, true)]).expect("unit 1");
    let attached = core
        .add_clause(&[lit(0, false), lit(1, false)])
        .expect("falsified clause");
    let offset = match attached {
        mapt::hot::sat::database::AttachOutcome::Attached(offset) => offset,
        other => panic!("expected attach, got {:?}", other),
    };
    let _ = core.propagate().expect("propagate");
    // Level 1: decide an unrelated variable; the analyzer is then handed the falsified
    // clause directly, which has no literal at the current level.
    core.decide(lit(5, true)).expect("decide 5");
    let mut buffer = [lit(0, true); 64];
    assert_eq!(
        analyzer.analyze(&core, &vsids, offset, &mut buffer),
        Err(CdclError::MalformedConflict)
    );
}
