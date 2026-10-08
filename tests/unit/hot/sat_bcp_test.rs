// CEP:FILE: tests/unit/hot/sat_bcp_test.rs
// CEP:WHAT: Unit tests for the BCP engine: unit enqueues, implication chains, conflicts, watch moves, queue draining, and backtracking restoration.
// CEP:WHY: CEP&CC 32.8 and design 11.2: BCP is the hottest path in the system; soundness and watch invariants must be proven at the unit level before the property tests hammer them.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/bcp.rs.
// CEP:SECURITY: none.

#[path = "../../common/mod.rs"]
mod common;

use common::make_sat_fixture;
use mapt::hot::sat::bcp::PropagationOutcome;
use mapt::hot::sat::database::AttachOutcome;
use mapt::hot::sat::literal::{SatLiteral, SatVar};

// CEP:WHAT: Builds a literal at a variable.
// CEP:WHY: Terse fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: variable below the declared count.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Verifies core initialization state.
// CEP:WHY: All-unassigned, empty trail, one root level.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on nonzero state.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs new.
// CEP:SECURITY: none.
#[test]
fn core_initializes() {
    let (_arena, core) = make_sat_fixture(8);
    assert_eq!(core.variable_count(), 8);
    assert_eq!(core.trail().len(), 0);
    assert_eq!(core.trail().level(), 0);
}

// CEP:WHAT: Verifies unit clauses enqueue their literal.
// CEP:WHY: Design 11.3: units have no watches; they enter the trail directly.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if units are dropped.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs attach_clause.
// CEP:SECURITY: none.
#[test]
fn unit_clause_enqueues() {
    let (_arena, core) = make_sat_fixture(4);
    let outcome = core.add_clause(&[lit(0, true)]).expect("unit");
    assert!(matches!(outcome, AttachOutcome::UnitEnqueued(_)));
    assert_eq!(core.trail().len(), 1);
    assert_eq!(
        core.propagate().expect("propagate"),
        PropagationOutcome::NoConflict
    );
}

// CEP:WHAT: Verifies falsified units report conflict.
// CEP:WHY: A unit whose literal is already false is an immediate conflict.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the conflict is dropped.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs attach_clause.
// CEP:SECURITY: none.
#[test]
fn falsified_unit_conflicts() {
    let (_arena, core) = make_sat_fixture(4);
    let outcome = core.add_clause(&[lit(0, true)]).expect("unit");
    assert!(matches!(outcome, AttachOutcome::UnitEnqueued(_)));
    let _ = core.propagate();
    let conflict = core.add_clause(&[lit(0, false)]).expect("second unit");
    assert_eq!(conflict, AttachOutcome::Conflict);
}

// CEP:WHAT: Verifies propagation drains the queue to fixpoint.
// CEP:WHY: The queue-head contract (qhead == len after a clean run).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the queue is left undrained.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs propagate.
// CEP:SECURITY: none.
#[test]
fn propagation_drains_queue() {
    let (_arena, core) = make_sat_fixture(4);
    // Implication chain: not-x0 forces x1; x1 forces x2; x2 forces not-x3.
    core.add_clause(&[lit(0, true), lit(1, true)])
        .expect("clause");
    core.add_clause(&[lit(1, false), lit(2, true)])
        .expect("clause");
    core.add_clause(&[lit(2, false), lit(3, false)])
        .expect("clause");
    core.decide(lit(0, false)).expect("decision");
    let outcome = core.propagate().expect("propagate");
    assert_eq!(outcome, PropagationOutcome::NoConflict);
    assert_eq!(core.trail().qhead(), core.trail().len());
    assert_eq!(
        core.value_of_literal(lit(1, true)),
        mapt::hot::sat::assignment::SatValue::True
    );
    assert_eq!(
        core.value_of_literal(lit(2, true)),
        mapt::hot::sat::assignment::SatValue::True
    );
    assert_eq!(
        core.value_of_literal(lit(3, false)),
        mapt::hot::sat::assignment::SatValue::True
    );
}

// CEP:WHAT: Verifies an implication chain through multiple clauses.
// CEP:WHY: The FIFO queue must process derived assignments recursively.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the chain stops early.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs propagate.
// CEP:SECURITY: none.
#[test]
fn implication_chain() {
    let (_arena, core) = make_sat_fixture(6);
    for variable in 0..5u32 {
        core.add_clause(&[lit(variable, false), lit(variable + 1, true)])
            .expect("chain clause");
    }
    core.add_clause(&[lit(0, true)]).expect("unit start");
    let outcome = core.propagate().expect("propagate");
    assert_eq!(outcome, PropagationOutcome::NoConflict);
    for variable in 0..=5u32 {
        assert_eq!(
            core.value_of_literal(lit(variable, true)),
            mapt::hot::sat::assignment::SatValue::True,
            "variable {} must be propagated to true",
            variable
        );
    }
}

// CEP:WHAT: Verifies conflicts are detected with the offending clause.
// CEP:WHY: Conflict analysis (Phase 2) consumes the clause offset.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the conflict is missed.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs propagate.
// CEP:SECURITY: none.
#[test]
fn conflict_detected() {
    let (_arena, core) = make_sat_fixture(4);
    core.add_clause(&[lit(0, true), lit(1, true)])
        .expect("clause");
    core.add_clause(&[lit(0, false), lit(1, true)])
        .expect("clause");
    core.decide(lit(1, false)).expect("decision");
    let outcome = core.propagate().expect("propagate");
    match outcome {
        PropagationOutcome::Conflict(_) => {}
        other => panic!("expected conflict, got {:?}", other),
    }
}

// CEP:WHAT: Verifies watch moves preserve clause contents.
// CEP:WHY: Moving a watch swaps literals inside the clause; the multiset of literals must be unchanged.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if literals are lost or duplicated.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/bcp.rs move_watch.
// CEP:SECURITY: none.
#[test]
fn watch_moves_preserve_clause_contents() {
    let (_arena, core) = make_sat_fixture(6);
    let outcome = core
        .add_clause(&[lit(0, true), lit(1, true), lit(2, true), lit(3, false)])
        .expect("clause");
    let offset = match outcome {
        AttachOutcome::Attached(offset) => offset,
        other => panic!("expected Attached, got {:?}", other),
    };
    core.decide(lit(1, false)).expect("falsify watch 1");
    let outcome = core.propagate().expect("propagate");
    assert_eq!(outcome, PropagationOutcome::NoConflict);
    let mut literals = Vec::new();
    let header = core.clauses().header(offset).expect("header");
    for index in 0..header.length {
        literals.push(core.clauses().literal(offset, index).expect("literal"));
    }
    let expected = [lit(0, true), lit(1, true), lit(2, true), lit(3, false)];
    for candidate in expected.iter() {
        assert!(
            literals.iter().any(|found| found == candidate),
            "literal {:?} must survive the watch move",
            candidate.encoding()
        );
    }
    assert_eq!(literals.len(), expected.len());
    // With x1 false, the watch moves from x1 to x2; x0 and x2 stay unassigned because the
    // clause still has two non-false literals and therefore is not unit.
    assert_eq!(
        core.value_of_literal(lit(0, true)),
        mapt::hot::sat::assignment::SatValue::Unassigned,
        "the clause is not unit while x0 and x2 are unassigned"
    );
    assert_eq!(
        core.value_of_literal(lit(2, true)),
        mapt::hot::sat::assignment::SatValue::Unassigned
    );
    // The clause must now be reachable from the lists of its new watch pair (x0, x2).
    for slot in 0..2u32 {
        let watched = core.clauses().literal(offset, slot).expect("watched");
        let mut cursor = core.watches().head(watched);
        let mut found = false;
        while cursor != mapt_config::limits::kInvalidClauseOffset {
            if cursor == offset {
                found = true;
                break;
            }
            let lit0 = core.clauses().literal(cursor, 0).expect("lit0");
            let link_slot = if lit0 == watched { 0 } else { 1 };
            cursor = core
                .clauses()
                .next_in_watch(cursor, link_slot)
                .expect("link");
        }
        assert!(found, "clause must be reachable from its moved watch");
    }
}

// CEP:WHAT: Verifies backtracking clears exactly the popped assignments.
// CEP:WHY: Trail and value array consistency.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on leftover or over-cleared assignments.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs cancel_until.
// CEP:SECURITY: none.
#[test]
fn cancel_restores_assignments() {
    let (_arena, core) = make_sat_fixture(4);
    core.add_clause(&[lit(0, true), lit(1, true)])
        .expect("clause");
    core.decide(lit(0, false)).expect("decision");
    let _ = core.propagate();
    assert_eq!(
        core.value_of_literal(lit(1, true)),
        mapt::hot::sat::assignment::SatValue::True
    );
    core.cancel_until(0);
    assert_eq!(
        core.value_of_literal(lit(0, false)),
        mapt::hot::sat::assignment::SatValue::Unassigned,
        "the decision must be unassigned"
    );
    assert_eq!(
        core.value_of_literal(lit(1, true)),
        mapt::hot::sat::assignment::SatValue::Unassigned,
        "the propagated literal must be unassigned"
    );
    assert_eq!(core.trail().len(), 0);
}
