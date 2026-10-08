// CEP:FILE: tests/unit/hot/sat_trail_test.rs
// CEP:WHAT: Unit tests for the SAT trail: pushes, levels, queue head, and cancellation.
// CEP:WHY: CEP&CC 32.8: the trail is the assignment stack BCP drains and backtracking rewinds.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/trail.rs.
// CEP:SECURITY: capacity and level bounds are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::hot::sat::literal::SatLiteral;
use mapt::hot::sat::literal::SatVar;
use mapt::hot::sat::trail::{SatTrail, SatTrailError};

// CEP:WHAT: Builds three literals for trail tests.
// CEP:WHY: Shared fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lits() -> [SatLiteral; 3] {
    [
        SatLiteral::new(SatVar(0), true).expect("lit"),
        SatLiteral::new(SatVar(1), false).expect("lit"),
        SatLiteral::new(SatVar(2), true).expect("lit"),
    ]
}

// CEP:WHAT: Verifies the initial trail state.
// CEP:WHY: One empty root level, empty stack, queue at zero.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on nonzero initial state.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs new.
// CEP:SECURITY: none.
#[test]
fn initial_state() {
    let arena = make_arena(1 << 24);
    let trail = SatTrail::new(arena, 16).expect("trail");
    assert_eq!(trail.len(), 0);
    assert_eq!(trail.level(), 0);
    assert_eq!(trail.qhead(), 0);
    assert_eq!(trail.current_level_start(), 0);
}

// CEP:WHAT: Verifies pushes and readback.
// CEP:WHY: FIFO order is the propagation contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on order or content drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs push_assignment.
// CEP:SECURITY: none.
#[test]
fn push_and_read_back() {
    let arena = make_arena(1 << 24);
    let trail = SatTrail::new(arena, 16).expect("trail");
    let literals = lits();
    trail.push_assignment(literals[0]).expect("push");
    trail.push_assignment(literals[1]).expect("push");
    assert_eq!(trail.len(), 2);
    assert_eq!(trail.literal_at(0), Some(literals[0]));
    assert_eq!(trail.literal_at(1), Some(literals[1]));
    assert_eq!(trail.literal_at(2), None);
    assert_eq!(trail.level(), 0, "assignments stay at the root level");
}

// CEP:WHAT: Verifies decision levels.
// CEP:WHY: Level starts define backtracking points.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on level accounting drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs push_decision/level_start.
// CEP:SECURITY: none.
#[test]
fn levels() {
    let arena = make_arena(1 << 24);
    let trail = SatTrail::new(arena, 16).expect("trail");
    let literals = lits();
    trail.push_assignment(literals[0]).expect("root assignment");
    trail.push_decision(literals[1]).expect("decision level 1");
    trail
        .push_assignment(literals[2])
        .expect("level 1 assignment");
    assert_eq!(trail.level(), 1);
    assert_eq!(trail.current_level_start(), 1);
    assert_eq!(trail.level_start(0), 0);
    assert_eq!(trail.level_start(1), 1);
}

// CEP:WHAT: Verifies cancellation pops entries and rewinds the queue head.
// CEP:WHY: Backtracking correctness.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on leftover entries.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs cancel_until.
// CEP:SECURITY: none.
#[test]
fn cancel_until() {
    let arena = make_arena(1 << 24);
    let trail = SatTrail::new(arena, 16).expect("trail");
    let literals = lits();
    trail.push_assignment(literals[0]).expect("root");
    trail.push_decision(literals[1]).expect("level 1");
    trail.push_assignment(literals[2]).expect("level 1 body");
    trail.advance_qhead();
    trail.advance_qhead();
    trail.cancel_until(0);
    assert_eq!(trail.len(), 1);
    assert_eq!(trail.level(), 0);
    assert_eq!(
        trail.qhead(),
        1,
        "queue head rewinds to the kept length at most"
    );
}

// CEP:WHAT: Verifies the queue head never passes the length.
// CEP:WHY: advance_qhead clamping.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if qhead exceeds len.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs advance_qhead.
// CEP:SECURITY: none.
#[test]
fn qhead_clamped() {
    let arena = make_arena(1 << 24);
    let trail = SatTrail::new(arena, 16).expect("trail");
    let literals = lits();
    trail.push_assignment(literals[0]).expect("push");
    trail.advance_qhead();
    trail.advance_qhead();
    trail.advance_qhead();
    assert!(trail.qhead() <= trail.len());
}

// CEP:WHAT: Verifies NotInitialized surfaces when the arena cannot hold the arrays.
// CEP:WHY: Allocation failure must be a documented error, not a panic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a panic occurs.
// CEP:ASSUMES: tiny arena.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/trail.rs new.
// CEP:SECURITY: none.
#[test]
fn allocation_failure_is_error() {
    let small = common::make_arena(1_024);
    assert!(
        matches!(
            SatTrail::new(small, mapt_config::limits::kMaxSatVariables),
            Err(SatTrailError::NotInitialized)
        ),
        "trail arrays must fit the arena or fail loudly"
    );
    assert!(
        matches!(SatTrail::new(small, 0), Err(SatTrailError::NotInitialized)),
        "zero-variable trails must be rejected"
    );
}
