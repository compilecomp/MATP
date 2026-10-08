// CEP:FILE: tests/security/symbol_bounds_test.rs
// CEP:WHAT: Security tests for symbol bounds: unknown IDs are rejected, arity is enforced, and the frozen table refuses corrupted pools.
// CEP:WHY: CEP&CC 22.5: symbol IDs arriving from untrusted input are the attack surface of the frozen table; every bound must be proven adversarially.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any bound violation.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/symbol_table.rs and config/security_policy.rs.
// CEP:SECURITY: this file IS the security evidence for symbol handling.

#[path = "../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::hot::ir::symbol_table::SymbolError;

// CEP:WHAT: Verifies unknown symbol IDs are rejected across the entire attack range.
// CEP:WHY: IDs from untrusted input must never index out of bounds.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any out-of-range ID is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs info.
// CEP:SECURITY: bounds enforcement.
#[test]
fn unknown_id_rejected() {
    let (_arena, symbols, builder, _terms, _clauses) = make_term_fixture();
    let count = symbols.symbol_count();
    let adversarial = [count, count + 1, count * 2, u32::MAX, u32::MAX - 1, 1 << 30];
    for id in adversarial.iter() {
        assert_eq!(symbols.info(*id), Err(SymbolError::UnknownSymbol));
        assert_eq!(symbols.sort_signature(*id), Err(SymbolError::UnknownSymbol));
    }
    for id in 0..count {
        assert!(symbols.info(id).is_ok());
    }
    let _ = builder;
}

// CEP:WHAT: Verifies the arity bound is enforced end to end.
// CEP:WHY: Oversize arity would overflow fixed signature storage.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if oversize arity is accepted anywhere.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_symbol.
// CEP:SECURITY: arity bound.
#[test]
fn arity_bound_enforced() {
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    let sort = mapt::hot::ir::symbol_table::SortId(builder.declare_sort("S").expect("sort"));
    assert_eq!(
        builder.declare_function(
            "wide",
            mapt_config::limits::kMaxSymbolArity + 1,
            1,
            &[sort; mapt_config::limits::kMaxSymbolArity as usize + 1],
            sort
        ),
        Err(mapt::cold::symbol_table_builder::BuilderError::ArityExceeded),
        "the builder must refuse arity above the bound"
    );
    let at_bound = builder
        .declare_function(
            "atbound",
            mapt_config::limits::kMaxSymbolArity,
            1,
            &[sort; mapt_config::limits::kMaxSymbolArity as usize],
            sort,
        )
        .expect("arity at the bound is legal");
    assert!(at_bound < mapt_config::limits::kMaxSymbolCount);
}

// CEP:WHAT: Verifies the frozen table refuses an out-of-pool signature.
// CEP:WHY: Freeze is the trust boundary; a corrupted pool offset must be caught there.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if freeze accepts a bad pool.
// CEP:ASSUMES: direct arena corruption through the public API.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs freeze.
// CEP:SECURITY: freeze validation.
#[test]
fn corrupted_pool_rejected() {
    let (arena, _symbols, _builder, _terms, _clauses) = make_term_fixture();
    let entries = arena
        .alloc_array::<mapt::hot::ir::symbol_table::SymbolInfo>(1)
        .expect("entries");
    let pool = arena
        .alloc_array::<mapt::hot::ir::symbol_table::SortId>(1)
        .expect("pool");
    {
        let slot = arena
            .array_mut::<mapt::hot::ir::symbol_table::SymbolInfo>(entries)
            .expect("mut");
        slot[0] = mapt::hot::ir::symbol_table::SymbolInfo {
            kind: mapt::hot::ir::symbol_table::SymbolKind::Function,
            arity: 1,
            flags: 0,
            weight: 1,
            sort_signature: 99_999,
            sort_signature_len: 2,
            reserved: 0,
        };
    }
    assert!(
        matches!(
            mapt::hot::ir::symbol_table::SymbolTable::freeze(arena, entries, pool),
            Err(SymbolError::InvalidTable)
        ),
        "an out-of-pool signature must be rejected at freeze"
    );
}
