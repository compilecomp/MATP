// CEP:FILE: tests/unit/hot/symbol_table_test.rs
// CEP:WHAT: Unit tests for the frozen symbol table: freeze validation, lookups, signatures, flags, and bounds.
// CEP:WHY: CEP&CC 32.8: the frozen table is the hot-path symbol authority; every validation must be proven.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/ir/symbol_table.rs.
// CEP:SECURITY: unknown IDs and bad pools are exercised here.

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, make_term_fixture};
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::symbol_table::{
    kSymbolFlagBuiltin, SortId, SymbolError, SymbolInfo, SymbolKind, SymbolTable,
};
use mapt::hot::memory::arena::ArenaRange;

// CEP:WHAT: Verifies lookups on the standard fixture.
// CEP:WHY: info() is the hottest table operation.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on lookup errors.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs info.
// CEP:SECURITY: none.
#[test]
fn lookups() {
    let (_arena, symbols, builder, _terms, _clauses) = make_term_fixture();
    let count = symbols.symbol_count();
    assert_eq!(count, builder.symbol_count());
    for id in 0..count {
        let info = symbols.info(id).expect("known id");
        assert!(info.weight >= 1);
    }
    assert!(
        matches!(symbols.info(count), Err(SymbolError::UnknownSymbol)),
        "one past the end must be unknown"
    );
}

// CEP:WHAT: Verifies kind round trips through the fixed representation.
// CEP:WHY: The u8 representation must preserve the kind.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on kind corruption.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs SymbolKind.
// CEP:SECURITY: none.
#[test]
fn kind_roundtrip() {
    let (_arena, symbols, builder, _terms, _clauses) = make_term_fixture();
    let sort_id = fixture_id(&builder, "S");
    assert_eq!(symbols.info(sort_id).expect("read").kind, SymbolKind::Sort);
    let f_id = fixture_id(&builder, "f");
    assert_eq!(symbols.info(f_id).expect("read").kind, SymbolKind::Function);
    let p_id = fixture_id(&builder, "p");
    assert_eq!(
        symbols.info(p_id).expect("read").kind,
        SymbolKind::Predicate
    );
}

// CEP:WHAT: Verifies signature slices.
// CEP:WHY: Sort signatures feed sort-correctness checks.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on signature length or content mismatch.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs sort_signature.
// CEP:SECURITY: none.
#[test]
fn signature_slice() {
    let (_arena, symbols, builder, _terms, _clauses) = make_term_fixture();
    let h_id = fixture_id(&builder, "h");
    let signature = symbols.sort_signature(h_id).expect("signature");
    assert_eq!(
        signature.len(),
        3,
        "h/2 has two argument sorts plus return sort"
    );
}

// CEP:WHAT: Verifies flag masks mark built-in symbols.
// CEP:WHY: Flag bit discipline (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if flags do not round trip.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs flags.
// CEP:SECURITY: none.
#[test]
fn flag_masks() {
    let arena = make_arena(common::kTestArenaBytes);
    let mut builder = SymbolTableBuilder::new();
    let id = builder.declare_sort("S").expect("sort");
    builder.mark_builtin(id);
    let symbols = builder.finalize(arena).expect("freeze");
    let info = symbols.info(id).expect("read");
    assert!(info.flags & kSymbolFlagBuiltin != 0);
}

// CEP:WHAT: Verifies freeze rejects structurally invalid tables.
// CEP:WHY: Freeze is the trust boundary (CEP&CC 22.3).
// CEP:STATUS: complete
// CEP:FAILURE: test fails if a bad table freezes.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs freeze.
// CEP:SECURITY: freeze validation.
#[test]
fn freeze_rejects_bad_tables() {
    let arena = make_arena(common::kTestArenaBytes);
    let bad_range = ArenaRange::new(0, 3).expect("range");
    assert!(
        matches!(
            SymbolTable::freeze(arena, bad_range, bad_range),
            Err(SymbolError::InvalidTable)
        ),
        "misaligned entry arrays must be rejected"
    );
    let entries = arena.alloc_array::<SymbolInfo>(1).expect("entries");
    let pool = arena.alloc_array::<SortId>(1).expect("pool");
    {
        let slot = arena.array_mut::<SymbolInfo>(entries).expect("mut");
        slot[0] = SymbolInfo {
            kind: SymbolKind::Function,
            arity: 1,
            flags: 0,
            weight: 0,
            sort_signature: 0,
            sort_signature_len: 2,
            reserved: 0,
        };
    }
    assert!(
        matches!(
            SymbolTable::freeze(arena, entries, pool),
            Err(SymbolError::InvalidTable)
        ),
        "zero weight and wrong signature length must be rejected"
    );
}

// CEP:WHAT: Verifies symbol weights fall back to the default.
// CEP:WHY: The fallback rule must be deterministic.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on unexpected weight.
// CEP:ASSUMES: standard fixture weights are 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/symbol_table.rs symbol_weight.
// CEP:SECURITY: none.
#[test]
fn symbol_weight() {
    let (_arena, symbols, builder, _terms, _clauses) = make_term_fixture();
    let f_id = fixture_id(&builder, "f");
    assert_eq!(symbols.symbol_weight(f_id), Ok(1));
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fixture_id(builder: &SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}
