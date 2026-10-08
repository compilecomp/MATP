// CEP:FILE: tests/unit/hot/sat_literal_test.rs
// CEP:WHAT: Unit tests for SAT literals and the assignment store: encoding round trips, negation, bounds, and value semantics.
// CEP:WHY: CEP&CC 32.8: literal encoding is the foundation of the watch scheme.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/literal.rs and hot/sat/assignment.rs.
// CEP:SECURITY: the variable bound is exercised here and in security/literal_encoding_test.rs.

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, make_sat_fixture};
use mapt::hot::sat::assignment::{AssignmentStore, SatValue, SatVarRaw};
use mapt::hot::sat::literal::{SatLiteral, SatLiteralError, SatVar};
use mapt_config::limits::kMaxSatVariables;

// CEP:WHAT: Verifies encoding round trips for both polarities.
// CEP:WHY: The packed encoding is the watch-head index; any drift breaks every list.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on encoding drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/literal.rs.
// CEP:SECURITY: none.
#[test]
fn encoding_roundtrip() {
    let positive = SatLiteral::new(SatVar(7), true).expect("literal");
    let negative = SatLiteral::new(SatVar(7), false).expect("literal");
    assert_eq!(positive.variable(), SatVar(7));
    assert!(positive.is_positive());
    assert_eq!(negative.variable(), SatVar(7));
    assert!(!negative.is_positive());
    assert_eq!(positive.encoding() | 1, negative.encoding());
}

// CEP:WHAT: Verifies negation is an involution.
// CEP:WHY: BCP negates constantly; double negation must return the original encoding.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on negation drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/literal.rs negate.
// CEP:SECURITY: none.
#[test]
fn negate_roundtrip() {
    let literal = SatLiteral::new(SatVar(123), false).expect("literal");
    assert_eq!(literal.negate().negate().encoding(), literal.encoding());
}

// CEP:WHAT: Verifies out-of-range variables are rejected.
// CEP:WHY: The variable bound is the watch-head memory-safety boundary.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if an oversize variable is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/literal.rs new.
// CEP:SECURITY: variable bound.
#[test]
fn out_of_range_variable_rejected() {
    assert_eq!(
        SatLiteral::new(SatVar(kMaxSatVariables), true),
        Err(SatLiteralError::VariableOutOfRange)
    );
    assert!(SatLiteral::new(SatVar(kMaxSatVariables - 1), true).is_ok());
}

// CEP:WHAT: Verifies assignment store initialization and value writes.
// CEP:WHY: All-unassigned initial state (CEP&CC 22.4 no uninitialized reads).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on phantom assignments.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/assignment.rs.
// CEP:SECURITY: none.
#[test]
fn assignment_store_values() {
    let arena = make_arena(1 << 24);
    let store = AssignmentStore::new(arena, 8).expect("store");
    assert_eq!(store.variable_count(), 8);
    for variable in 0..8u32 {
        assert_eq!(store.value(SatVarRaw(variable)), SatValue::Unassigned);
    }
    store.set_value(SatVarRaw(3), SatValue::True).expect("set");
    assert_eq!(store.value(SatVarRaw(3)), SatValue::True);
    store
        .set_value(SatVarRaw(3), SatValue::Unassigned)
        .expect("clear");
    assert_eq!(store.value(SatVarRaw(3)), SatValue::Unassigned);
    assert!(
        matches!(
            store.set_value(SatVarRaw(8), SatValue::True),
            Err(mapt::hot::sat::assignment::AssignmentError::VariableOutOfRange)
        ),
        "writes beyond the declared count must be rejected"
    );
    assert!(
        matches!(
            AssignmentStore::new(arena, 0),
            Err(mapt::hot::sat::assignment::AssignmentError::VariableOutOfRange)
        ),
        "zero-variable stores must be rejected"
    );
}

// CEP:WHAT: Verifies literal value evaluation through the SAT core.
// CEP:WHY: Polarity-aware evaluation is the BCP decision predicate.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on evaluation errors.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/database.rs value_of_literal.
// CEP:SECURITY: none.
#[test]
fn value_evaluation() {
    let (_arena, core) = make_sat_fixture(4);
    let positive = SatLiteral::new(SatVar(0), true).expect("literal");
    let negative = SatLiteral::new(SatVar(0), false).expect("literal");
    assert_eq!(core.value_of_literal(positive), SatValue::Unassigned);
    assert_eq!(core.value_of_literal(negative), SatValue::Unassigned);
    core.assign(positive).expect("assign");
    assert_eq!(core.value_of_literal(positive), SatValue::True);
    assert_eq!(core.value_of_literal(negative), SatValue::False);
    assert_eq!(
        core.assign(negative),
        Err(mapt::hot::sat::database::SatCoreError::InvariantViolation),
        "assigning an already-false literal must be a loud invariant violation"
    );
}
