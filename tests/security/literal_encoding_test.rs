// CEP:FILE: tests/security/literal_encoding_test.rs
// CEP:WHAT: Security tests for SAT literal encoding: the variable bound holds at the extremes and watch-head indexing stays in range.
// CEP:WHY: CEP&CC 22.6: the packed encoding feeds watch-head indexing; an out-of-range variable would be an out-of-bounds index, so the bound is proven at both extremes.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any bound violation.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/sat/literal.rs and hot/sat/watch_lists.rs.
// CEP:SECURITY: this file IS the security evidence for literal encoding.

#[path = "../common/mod.rs"]
mod common;

use mapt::hot::sat::literal::{SatLiteral, SatLiteralError, SatVar};
use mapt_config::limits::{kInvalidClauseOffset, kMaxSatVariables};

// CEP:WHAT: Verifies the variable bound at both extremes.
// CEP:WHY: The maximum legal variable must encode and decode exactly; one past it must be refused.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the boundary is off by one.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/literal.rs new.
// CEP:SECURITY: boundary correctness.
#[test]
fn variable_bound_extremes() {
    let top = SatLiteral::new(SatVar(kMaxSatVariables - 1), false).expect("top variable");
    assert_eq!(top.variable(), SatVar(kMaxSatVariables - 1));
    assert!(!top.is_positive());
    assert_eq!(top.encoding() >> 1, kMaxSatVariables - 1);
    assert_eq!(
        SatLiteral::new(SatVar(kMaxSatVariables), true),
        Err(SatLiteralError::VariableOutOfRange)
    );
    assert_eq!(
        SatLiteral::new(SatVar(u32::MAX), false),
        Err(SatLiteralError::VariableOutOfRange)
    );
    let zero = SatLiteral::new(SatVar(0), true).expect("zero variable");
    assert_eq!(zero.encoding(), 0);
    assert_eq!(zero.negate().encoding(), 1);
}

// CEP:WHAT: Verifies watch-head indexing stays in range for every legal literal.
// CEP:WHY: The encoding doubles the variable count; the maximum encoding must be a legal head index.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any legal literal misses the head array.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/sat/watch_lists.rs head.
// CEP:SECURITY: index bound.
#[test]
fn watch_head_indexing_in_range() {
    let (_arena, core) = common::make_sat_fixture(16);
    for variable in 0..16u32 {
        for positive in [true, false] {
            let literal = SatLiteral::new(SatVar(variable), positive).expect("literal");
            // Reading heads through the public API must return the sentinel, never panic.
            assert_eq!(core.watches().head(literal), kInvalidClauseOffset);
            assert!(core.watches().set_head(literal, 7));
        }
    }
    // A variable above the declared count is a legal literal at the encoding level (the global
    // bound is kMaxSatVariables) but must be refused by the core's per-instance bounds.
    let beyond_declared = SatLiteral::new(SatVar(16), true).expect("legal at encoding level");
    assert!(
        !core.watches().set_head(beyond_declared, 7),
        "head writes beyond the declared variable count must be refused"
    );
    assert_eq!(core.watches().head(beyond_declared), kInvalidClauseOffset);
    assert_eq!(
        SatLiteral::new(SatVar(kMaxSatVariables), true),
        Err(SatLiteralError::VariableOutOfRange),
        "the global encoding bound must still hold"
    );
}
