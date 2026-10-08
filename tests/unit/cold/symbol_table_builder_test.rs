// CEP:FILE: tests/unit/cold/symbol_table_builder_test.rs
// CEP:WHAT: Unit tests for the CEP-1 symbol table builder: declarations, dedup, bounds, flags, and finalization.
// CEP:WHY: CEP&CC 32.8: the builder is the trust boundary producing the frozen hot table.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/symbol_table_builder.rs.
// CEP:SECURITY: count, name, and arity bounds are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::cold::symbol_table_builder::{BuilderError, SymbolTableBuilder};
use mapt::hot::ir::symbol_table::{SortId, SymbolKind};
use mapt_config::security_policy::{kMaxInputSymbolCount, kMaxSymbolNameBytes};

// CEP:WHAT: Verifies sort declaration and ID assignment order.
// CEP:WHY: Deterministic dense IDs are the design contract (design 5.6).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on nondeterministic IDs.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_sort.
// CEP:SECURITY: none.
#[test]
fn declare_sort() {
    let mut builder = SymbolTableBuilder::new();
    let first = builder.declare_sort("S").expect("first sort");
    let second = builder.declare_sort("T").expect("second sort");
    assert_eq!(first, 0);
    assert_eq!(second, 1);
    assert_eq!(builder.symbol_count(), 2);
    let again = builder.declare_sort("S").expect("idempotent redeclaration");
    assert_eq!(
        again, first,
        "redeclaration with the same signature returns the same ID"
    );
    assert_eq!(builder.symbol_count(), 2);
}

// CEP:WHAT: Verifies function declaration with signature validation.
// CEP:WHY: Sort references must be declared sorts.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if bad sorts are accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_function.
// CEP:SECURITY: signature validation.
#[test]
fn declare_function() {
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let f = builder
        .declare_function("f", 1, 1, &[sort], sort)
        .expect("f/1");
    assert_eq!(builder.name_of(f), Some("f"));
    let undefined_sort = SortId(99);
    assert_eq!(
        builder.declare_function("bad", 1, 1, &[undefined_sort], sort),
        Err(BuilderError::InvalidSort),
        "undeclared sorts must be rejected"
    );
}

// CEP:WHAT: Verifies predicate declaration lazily declares the Boolean sort.
// CEP:WHY: Predicates return Booleans by construction.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the Boolean sort is missing or duplicated.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_predicate.
// CEP:SECURITY: none.
#[test]
fn declare_predicate() {
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let p = builder.declare_predicate("p", 1, 1, &[sort]).expect("p/1");
    let boolean = builder.boolean_sort_id().expect("boolean sort exists");
    let table = builder
        .finalize(make_arena(common::kTestArenaBytes))
        .expect("freeze");
    let signature = table.sort_signature(p).expect("signature");
    assert_eq!(signature.len(), 2);
    assert_eq!(signature[1], boolean);
    assert_eq!(table.info(boolean.0).expect("read").kind, SymbolKind::Sort);
}

// CEP:WHAT: Verifies duplicate detection with mismatched signatures.
// CEP:WHY: Silent merging would corrupt the table.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a mismatch is accepted.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_symbol.
// CEP:SECURITY: none.
#[test]
fn duplicate_detection() {
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let _ = builder
        .declare_function("f", 1, 1, &[sort], sort)
        .expect("f/1");
    assert_eq!(
        builder.declare_function("f", 2, 1, &[sort, sort], sort),
        Err(BuilderError::DuplicateName),
        "same name with a different arity must be rejected"
    );
    assert_eq!(
        builder.declare_sort("f"),
        Err(BuilderError::DuplicateName),
        "same name with a different kind must be rejected"
    );
}

// CEP:WHAT: Verifies name, arity, and weight bound enforcement.
// CEP:WHY: Denial-of-service mitigation (CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any bound is missing.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_symbol.
// CEP:SECURITY: bounds enforcement.
#[test]
fn bound_enforcement() {
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    let long_name = "x".repeat(kMaxSymbolNameBytes as usize + 1);
    assert_eq!(
        builder.declare_sort(&long_name),
        Err(BuilderError::NameTooLong)
    );
    assert_eq!(
        builder.declare_function(
            "wide",
            mapt_config::limits::kMaxSymbolArity + 1,
            1,
            &[sort],
            sort
        ),
        Err(BuilderError::ArityExceeded)
    );
    assert_eq!(
        builder.declare_function("zero", 0, 0, &[], sort),
        Err(BuilderError::InvalidWeight),
        "zero weights break KBO admissibility and must be rejected"
    );
}

// CEP:WHAT: Verifies the symbol count bound.
// CEP:WHY: Input-side bound below the global capacity.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if the bound is not enforced.
// CEP:ASSUMES: kMaxInputSymbolCount is reachable in test time.
// CEP:COST: O(kMaxInputSymbolCount) declarations.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs declare_symbol.
// CEP:SECURITY: count bound.
#[test]
fn symbol_count_bound() {
    let mut builder = SymbolTableBuilder::new();
    let sort = SortId(builder.declare_sort("S").expect("sort"));
    for index in 0..kMaxInputSymbolCount - 1 {
        let _ = builder
            .declare_function(&format!("s{}", index), 0, 1, &[], sort)
            .expect("declaration within the bound");
    }
    assert_eq!(
        builder.declare_function("overflow", 0, 1, &[], sort),
        Err(BuilderError::TooManySymbols),
        "the input symbol bound must be enforced"
    );
}

// CEP:WHAT: Verifies flags mark entries through finalization.
// CEP:WHY: Flag round trip through freeze.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if flags are lost.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/symbol_table_builder.rs mark_builtin.
// CEP:SECURITY: none.
#[test]
fn flags() {
    let mut builder = SymbolTableBuilder::new();
    let sort_id = builder.declare_sort("S").expect("sort");
    builder.mark_builtin(sort_id);
    builder.mark_theory(sort_id);
    let table = builder
        .finalize(make_arena(common::kTestArenaBytes))
        .expect("freeze");
    let info = table.info(sort_id).expect("read");
    assert!(info.flags & mapt::hot::ir::symbol_table::kSymbolFlagBuiltin != 0);
    assert!(info.flags & mapt::hot::ir::symbol_table::kSymbolFlagTheory != 0);
}
