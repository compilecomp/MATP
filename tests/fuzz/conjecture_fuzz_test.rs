// CEP:FILE: tests/fuzz/conjecture_fuzz_test.rs
// CEP:WHAT: Fuzz tests of automated conjecture generation: random clause sets with random harvests never panic, respect every named budget, and produce identical results on double runs of the same seed.
// CEP:WHY: CEP&CC 28.3 (deterministic fuzzing) and the Phase 4 (revised) isolation theorem: the harvest runs against arbitrary store states - malformed or adversarial clause shapes included - and the invariants (no panic, budget ceilings, determinism) must hold for every seed.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: the fixture vocabulary; the deterministic RNG.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/conjecture/mod.rs fuzz pointers.
// CEP:SECURITY: the budget ceilings are the denial-of-service guards under fuzz.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::DeterministicRng;
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::conjecture::harvest;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::SortId;
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::{SearchOptions, SearchSpace, SearchStats};
use mapt_config::limits::{
    kInvalidClauseId, kInvalidSubstitutionOffset, kMaxConjectureCandidates, kMaxDerivationParents,
};

// CEP:WHAT: Arena bytes for the fuzz fixture.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kFuzzArena: u32 = 50_331_648;

// CEP:WHAT: Builds one random store state and runs one harvest, returning the observables.
// CEP:WHY: The shared body of the no-panic and determinism properties: random inputs (0-6 clauses of 1-3 literals over random ground atoms and polarities, including non-equation and negative shapes the templates must skip) plus random derived units (0-4, random orientation), then one harvest; the tuple of (stats, next id) is the comparable observable.
// CEP:STATUS: complete
// CEP:FAILURE: panics only on fixture construction failure.
// CEP:ASSUMES: fresh arena per run.
// CEP:COST: one harvest per run.
// CEP:EVIDENCE: used by both fuzz tests.
// CEP:SECURITY: none.
fn run_random_harvest(seed: u64) -> (u32, u32, u32, u64) {
    let mut rng = DeterministicRng::new(seed);
    let region = allocate_aligned_region(kFuzzArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b", "c", "d"] {
        builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("const");
    }
    let _succ = builder
        .declare_function("succ", 1, 1, &[sort_s], sort_s)
        .expect("succ");
    builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
    let symbols = builder.finalize(arena).expect("freeze");
    let terms = TermStore::new(arena).expect("terms");
    let precedence = PrecedenceTable::from_id_order(arena, builder.symbol_count()).expect("prec");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 4096, 8192, 8192, 65536, 8192).expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let symbol_of = |name: &str| {
        (0..builder.symbol_count())
            .find(|id| builder.name_of(*id) == Some(name))
            .expect("symbol")
    };
    let constant_ids: Vec<u32> = ["a", "b", "c", "d"].iter().map(|n| symbol_of(n)).collect();
    let predicate_id = symbol_of("p");
    let constants: Vec<TermPtr> = constant_ids
        .iter()
        .map(|id| terms.intern_fun(&symbols, *id, &[]).expect("const"))
        .collect();
    // Random input clauses: predicate literals and occasional equations.
    let input_draws = rng.below(7);
    for _ in 0..input_draws {
        let literal_count = 1 + rng.below(3);
        let mut literals: Vec<Literal> = Vec::new();
        for _ in 0..literal_count {
            let left = constants[rng.below(4) as usize];
            let right = constants[rng.below(4) as usize];
            let atom = if rng.below(4) == 0 {
                terms.intern_eq(&symbols, left, right).expect("eq")
            } else {
                terms
                    .intern_pred(&symbols, predicate_id, &[left])
                    .expect("p")
            };
            literals.push(Literal::new(atom, rng.below(2) == 0));
        }
        space
            .add_input_clause(&context, &options, &literals)
            .expect("input");
    }
    // Random derived units.
    let derived_draws = rng.below(5);
    for _ in 0..derived_draws {
        let left = constants[rng.below(4) as usize];
        let right = constants[rng.below(4) as usize];
        let atom = terms.intern_eq(&symbols, left, right).expect("eq");
        let derivation = DerivationStep {
            rule: InferenceRule::Demodulation,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; kMaxDerivationParents],
            substitution: kInvalidSubstitutionOffset,
        };
        space
            .add_derived_clause(&context, &options, &[Literal::new(atom, true)], derivation)
            .expect("derived");
    }
    let mut stats = SearchStats::default();
    harvest(&space, &context, &options, &mut stats);
    (
        stats.harvests,
        stats.candidates,
        stats.lemmas,
        space.store.next_clause_id().0,
    )
}

// CEP:WHAT: Random harvests never panic and respect every budget: candidates per harvest <= kMaxConjectureCandidates, harvests <= 1 per call, lemmas <= candidates.
// CEP:WHY: The fuzz-level budget invariant (Law 4): whatever the store state, the harvest's accounting stays within the named ceilings.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any budget violation.
// CEP:ASSUMES: none.
// CEP:COST: K random runs.
// CEP:EVIDENCE: cited by hot/conjecture/{mod,template,filter}.rs (budget ceilings).
// CEP:SECURITY: denial-of-service guards under fuzz.
#[test]
fn random_harvests_respect_budgets() {
    for seed in 0..64u64 {
        let (harvests, candidates, lemmas, _next) = run_random_harvest(seed ^ 0xF7_F7_F7);
        assert_eq!(harvests, 1, "seed {}", seed);
        assert!(candidates <= kMaxConjectureCandidates, "seed {}", seed);
        assert!(lemmas <= candidates, "seed {}", seed);
    }
}

// CEP:WHAT: The same seed produces the same observables (double-run determinism under fuzz).
// CEP:WHY: CEP&CC 38.10: the harvest is a pure function of the store state and the RNG stream.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any divergence.
// CEP:ASSUMES: none.
// CEP:COST: double runs.
// CEP:EVIDENCE: cited by hot/conjecture/mod.rs (file header HPC-DETERMINISM).
// CEP:SECURITY: none.
#[test]
fn random_harvests_are_deterministic() {
    for seed in [0u64, 1, 42, 0xFFFF_FFFF, 0x1234_5678_9ABC_DEF0] {
        assert_eq!(
            run_random_harvest(seed),
            run_random_harvest(seed),
            "seed {}",
            seed
        );
    }
}
