// CEP:FILE: tests/common/mod.rs
// CEP:WHAT: Shared test fixtures: arena construction, symbol table fixtures, and deterministic pseudo-random generators for property and fuzz tests.
// CEP:WHY: Test code is CEP-2 tooling (design: CEP-2 for benchmarking and tooling); a single fixture module keeps tests deterministic (fixed seeds, CEP&CC 28.3) and avoids duplicating setup that would drift.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly; production code never does).
// CEP:ASSUMES: each test owns its arena; fixtures never share state.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: used by every test target under tests/.
// CEP:SECURITY: no untrusted input; fixed seeds only.

#![allow(dead_code)]
#![allow(non_upper_case_globals)]

use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::ir::clause::ClauseStore;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::TermStore;
use mapt::hot::memory::arena::Arena;
use mapt::hot::sat::database::SatCore;

/// CEP:WHAT: Standard arena capacity for tests (48 MiB).
/// CEP:WHY: One term hash table (8 MiB) plus one SAT core (16 MiB) plus test data fits with slack; named instead of a magic number (CEP&CC 11.3).
/// CEP:CLASS: CEP-2
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: all test targets allocate with this constant.
/// CEP:SECURITY: none.
pub const kTestArenaBytes: u32 = 50_331_648;

// CEP:WHAT: Creates a leaked arena of the given capacity for one test.
// CEP:WHY: Stores borrow the arena for 'static; leaking one arena per test is the simplest sound lifetime strategy for test code.
// CEP:STATUS: complete
// CEP:FAILURE: panics on allocation or construction failure (test fixture failure).
// CEP:ASSUMES: one arena per test.
// CEP:COST: one system allocation.
// CEP:EVIDENCE: used by every test target.
// CEP:SECURITY: none.
pub fn make_arena(capacity_bytes: u32) -> &'static Arena {
    let region = allocate_aligned_region(capacity_bytes).expect("region allocation failed");
    Box::leak(Box::new(
        Arena::new(region).expect("arena construction failed"),
    ))
}

// CEP:WHAT: Declares the standard fixture symbols: sorts S, T; constants a, b; unary f, g; binary h; predicates p/1, q/2, r/0.
// CEP:WHY: A fixed vocabulary makes term-level tests readable and their golden outputs stable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on declaration failure.
// CEP:ASSUMES: fresh builder.
// CEP:COST: constant.
// CEP:EVIDENCE: term, clause, printer, and golden tests.
// CEP:SECURITY: none.
pub fn standard_symbols() -> SymbolTableBuilder {
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort S"));
    let sort_t = SortId(builder.declare_sort("T").expect("sort T"));
    let _ = builder
        .declare_function("a", 0, 1, &[], sort_s)
        .expect("constant a");
    let _ = builder
        .declare_function("b", 0, 1, &[], sort_s)
        .expect("constant b");
    let _ = builder
        .declare_function("f", 1, 1, &[sort_s], sort_s)
        .expect("function f");
    let _ = builder
        .declare_function("g", 1, 1, &[sort_s], sort_s)
        .expect("function g");
    let _ = builder
        .declare_function("h", 2, 1, &[sort_s, sort_s], sort_s)
        .expect("function h");
    let _ = builder
        .declare_predicate("p", 1, 1, &[sort_s])
        .expect("predicate p");
    let _ = builder
        .declare_predicate("q", 2, 1, &[sort_s, sort_t])
        .expect("predicate q");
    let _ = builder
        .declare_predicate("r", 0, 1, &[])
        .expect("predicate r");
    builder
}

// CEP:WHAT: Builds the full term fixture: leaked arena, frozen symbol table, builder, term store, clause store.
// CEP:WHY: One call sets up the Phase 1 stack for a test.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one arena plus the term hash table.
// CEP:EVIDENCE: term, clause, printer, verifier, golden tests.
// CEP:SECURITY: none.
pub fn make_term_fixture() -> (
    &'static Arena,
    SymbolTable<'static>,
    SymbolTableBuilder,
    TermStore<'static>,
    ClauseStore<'static>,
) {
    let arena = make_arena(kTestArenaBytes);
    let builder = standard_symbols();
    let symbols = builder.finalize(arena).expect("freeze failed");
    let terms = TermStore::new(arena).expect("term store failed");
    let clauses = ClauseStore::new(arena);
    (arena, symbols, builder, terms, clauses)
}

// CEP:WHAT: Arena capacity for SAT-only fixtures (1 MiB).
// CEP:WHY: SAT state is sized by the declared variable count (trail and level arrays scale with it), so small fixtures need no term-table-sized arenas; named instead of a magic number (CEP&CC 11.3).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: SAT unit, property, and fuzz tests.
// CEP:SECURITY: none.
pub const kSatFixtureArenaBytes: u32 = 1_048_576;

// CEP:WHAT: Builds a SAT fixture with a leaked arena.
// CEP:WHY: One call sets up the SAT core for a test; the arena is sized for SAT state only (no term table), so property tests running hundreds of fixtures stay within test-process memory.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one 1 MiB arena plus SAT state arrays.
// CEP:EVIDENCE: SAT unit, property, and fuzz tests.
// CEP:SECURITY: none.
pub fn make_sat_fixture(variables: u32) -> (&'static Arena, SatCore<'static>) {
    let arena = make_arena(kSatFixtureArenaBytes);
    let core = SatCore::new(arena, variables).expect("sat core failed");
    (arena, core)
}

// CEP:WHAT: Deterministic linear congruential generator for property and fuzz tests.
// CEP:WHY: Property tests need reproducible randomness; the LCG is fixed-seed and identical across platforms (CEP&CC 28.3 determinism; no std RandomState anywhere).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: single-threaded use.
// CEP:COST: one multiply-add per value.
// CEP:EVIDENCE: property and fuzz tests re-run identical sequences.
// CEP:SECURITY: none; not used for cryptography.
pub struct DeterministicRng {
    state: u64,
}

impl DeterministicRng {
    // CEP:WHAT: Creates a generator with a fixed seed.
    // CEP:WHY: Reproducibility of every property test run.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: property tests.
    // CEP:SECURITY: none.
    pub fn new(seed: u64) -> DeterministicRng {
        DeterministicRng { state: seed }
    }

    // CEP:WHAT: Returns the next pseudo-random u64.
    // CEP:WHY: The generator core; Numerical Recipes constants are published reference values.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: one multiply, one add.
    // CEP:EVIDENCE: property tests.
    // CEP:SECURITY: none.
    pub fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    // CEP:WHAT: Returns a pseudo-random value below bound.
    // CEP:WHY: Bounded choices (variable picks, clause lengths).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns 0 when bound is 0 (documented).
    // CEP:ASSUMES: bound > 0 for meaningful results.
    // CEP:COST: one modulo on top of next_u64.
    // CEP:EVIDENCE: property tests.
    // CEP:SECURITY: none.
    pub fn below(&mut self, bound: u64) -> u64 {
        if bound == 0 {
            return 0;
        }
        self.next_u64() % bound
    }
}
