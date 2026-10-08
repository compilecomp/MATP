// CEP:FILE: tests/contract/term_contract_test.rs
// CEP:WHAT: Contract tests for term construction: depth bound, weight bound, and symbol validation are explicit errors.
// CEP:WHY: CEP&CC Law 6 and design 5.1: resource bounds must fail loudly at the documented limits.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on contract violations.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/term.rs depth and weight contracts.
// CEP:SECURITY: recursion and overflow bounds are security mitigations.

#[path = "../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::ir::term::TermError;
use mapt_config::limits::kMaxTermDepth;

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn symbol_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Verifies the depth bound is enforced at construction.
// CEP:WHY: Prevents stack overflow during traversal (design 5.1, CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if deeper terms are accepted.
// CEP:ASSUMES: chain terms deepen by one per level.
// CEP:COST: builds a kMaxTermDepth-deep chain.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_tagged.
// CEP:SECURITY: recursion bound.
#[test]
fn deep_term_rejected() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let f_id = symbol_id(&builder, "f");
    let mut current = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let mut depth = 0;
    loop {
        match terms.intern_fun(&symbols, f_id, &[current]) {
            Ok(next) => {
                current = next;
                depth += 1;
                assert!(
                    depth <= kMaxTermDepth as u32,
                    "depth must stop at the bound"
                );
            }
            Err(TermError::DepthExceeded) => break,
            Err(other) => panic!("unexpected error: {:?}", other),
        }
    }
    assert_eq!(
        depth, kMaxTermDepth as u32,
        "the chain must reach exactly the bound"
    );
}

// CEP:WHAT: Verifies the weight bound is enforced.
// CEP:WHY: Prevents cached-weight overflow (design 5.1, CEP&CC 22.6).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if heavier terms are accepted.
// CEP:ASSUMES: kMaxTermWeight is reachable by widening terms before the depth bound.
// CEP:COST: builds terms up to the weight bound.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_tagged.
// CEP:SECURITY: overflow bound.
#[test]
fn weight_exceeded_rejected() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let h_id = symbol_id(&builder, "h");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    // Widening doubling: t_{n+1} = h(t_n, t_n); weight doubles each step, so the bound is reached in ~30 steps, well below the depth bound.
    let mut current = a;
    let mut stopped = false;
    for _ in 0..40 {
        match terms.intern_fun(&symbols, h_id, &[current, current]) {
            Ok(next) => current = next,
            Err(TermError::WeightExceeded) => {
                stopped = true;
                break;
            }
            Err(other) => panic!("unexpected error: {:?}", other),
        }
    }
    assert!(
        stopped,
        "the weight bound must eventually stop construction"
    );
    let final_weight = terms.term(current).expect("read").weight();
    assert!(final_weight as u64 * 3 > mapt_config::limits::kMaxTermWeight as u64);
}

// CEP:WHAT: Verifies unknown symbols and kind mismatches are refused.
// CEP:WHY: Symbol validation contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if invalid symbol use is accepted.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/term.rs intern_fun.
// CEP:SECURITY: symbol bound.
#[test]
fn symbol_validation_contract() {
    let (_arena, symbols, builder, terms, _clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let huge = mapt_config::limits::kMaxSymbolCount + 1;
    assert_eq!(
        terms.intern_fun(&symbols, huge, &[a]),
        Err(TermError::UnknownSymbol)
    );
    let sort_id = symbol_id(&builder, "S");
    assert_eq!(
        terms.intern_fun(&symbols, sort_id, &[a]),
        Err(TermError::SymbolKindMismatch),
        "sorts must not build function terms"
    );
}
