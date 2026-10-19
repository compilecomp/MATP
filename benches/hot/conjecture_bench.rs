// CEP:FILE: benches/hot/conjecture_bench.rs
// CEP:WHAT: Conjecture-generation benchmarks (bench CEP-BENCH-0037): cycles per candidate enumeration (window scan plus the three templates on a fourteen-unit window) and cycles per bounded mini refutation (the discarded path: the worst-case per-candidate speculative budget on a fresh mini space).
// CEP:WHY: Design 26 (revised build order Phase 4) and CEP&CC 23: the harvest is speculative work inside the search loop - both its enumeration and its per-candidate filter cost must carry OPT-0 cycle evidence; the discarded path is the representative worst case because an unprovable candidate consumes the entire kConjectureRefuteInferences budget without importing anything (the imported path's store growth would make repeated measurement non-uniform, and its cost is bounded above by the same budget).
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: panics on harness failure (bench tooling may fail loudly; it is not production code).
// CEP:ASSUMES: The cycle counter is accurate (harness asserts it); measurements run single-threaded.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: cited by hot/conjecture/{mod,template,filter}.rs (CEP:COST) and scripts/bench_gate.py baselines conjecture_enumeration and conjecture_filter_discard.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "harness.rs"]
mod harness;

use harness::{measure_cycles, write_artifact, Measurement};
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::conjecture::filter::{refute_and_maybe_import, CandidateOutcome, MiniCapacities};
use mapt::hot::conjecture::template::{collect_recent_units, enumerate_candidates};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::SearchOptions;
use mapt::hot::search::SearchSpace;
use mapt_config::limits::{kInvalidClauseId, kInvalidSubstitutionOffset, kMaxDerivationParents};

// CEP:WHAT: Arena bytes for the conjecture bench.
// CEP:WHY: Named fixture size (CEP&CC 11.3); sized for repeated mini spaces.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_ARENA: u32 = 268_435_456;

// CEP:WHAT: The number of derived units in the enumeration fixture's window.
// CEP:WHY: Named fixture size: a fourteen-unit window exercises T1 and T2 pairing across a realistic front.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const KBENCH_UNITS: usize = 14;

// CEP:WHAT: Builds the bench fixture: eight constants over one sort, the input axiom b=a (oriented), and KBENCH_UNITS derived unit equations (a two-term cycle plus distinct pairs, so T1 and T2 both fire).
// CEP:WHY: One constructor keeps the measured scenario identical across runs; the derived units are marked Demodulation (the T1/T2 source filter).
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_fixture() -> (
    &'static Arena,
    SymbolTable<'static>,
    SymbolTableBuilder,
    TermStore<'static>,
    PrecedenceTable<'static>,
    SearchSpace<'static>,
    SearchOptions,
    TermPtr,
    TermPtr,
) {
    let region = allocate_aligned_region(KBENCH_ARENA).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let mut constants: Vec<u32> = Vec::new();
    for index in 0..8 {
        constants.push(
            builder
                .declare_function(&format!("k{}", index), 0, 1, &[], sort_s)
                .expect("constant"),
        );
    }
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
    let const_terms: Vec<TermPtr> = constants
        .iter()
        .map(|id| terms.intern_fun(&symbols, *id, &[]).expect("const"))
        .collect();
    // The input axiom (oriented): k1 = k0.
    let axiom = terms
        .intern_eq(&symbols, const_terms[1], const_terms[0])
        .expect("eq");
    space
        .add_input_clause(&context, &options, &[Literal::new(axiom, true)])
        .expect("axiom");
    // Derived units: a chain k2=k1, k3=k2, ... plus a two-term cycle, so the
    // window mixes T1 and both T2 directions.
    let mut left = const_terms[2];
    let mut right = const_terms[1];
    for index in 0..KBENCH_UNITS {
        let hi = const_terms[(index % 6) + 2];
        let lo = const_terms[((index + 3) % 6) + 2];
        let (l, r) = if hi.as_u32() > lo.as_u32() {
            (hi, lo)
        } else {
            (lo, hi)
        };
        let atom = terms.intern_eq(&symbols, l, r).expect("eq");
        let derivation = DerivationStep {
            rule: InferenceRule::Demodulation,
            parent_count: 0,
            reserved: 0,
            parents: [kInvalidClauseId; kMaxDerivationParents],
            substitution: kInvalidSubstitutionOffset,
        };
        space
            .add_derived_clause(&context, &options, &[Literal::new(atom, true)], derivation)
            .expect("derived unit");
        let _ = (left, right);
        left = l;
        right = r;
    }
    (
        arena,
        symbols,
        builder,
        terms,
        precedence,
        space,
        options,
        const_terms[0],
        const_terms[1],
    )
}

// CEP:WHAT: The bench entry point: builds the fixture and records the two measurements (enumeration and the discarded-path filter).
// CEP:WHY: CEP&CC 10.2: every function carries a preceding CEP comment block, bench mains included.
// CEP:STATUS: complete
// CEP:FAILURE: panics on measurement failure (bench tooling may fail loudly).
// CEP:ASSUMES: the harness's cycle counter assertions hold.
// CEP:COST: the measured operations' costs are the artifact.
// CEP:EVIDENCE: this file's artifacts under benches/artifacts/.
// CEP:SECURITY: no untrusted input.
fn main() {
    let (arena, symbols, _builder, terms, precedence, space, options, t_k0, _t_k1) = make_fixture();
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };

    // Measurement 1: cycles per candidate enumeration (window scan +
    // templates; the interning is warm after the first run, isolating the
    // scan-and-join loops).
    let (enum_median, enum_min) = measure_cycles(2000, |_| {
        let window = collect_recent_units(&space, &context);
        let candidates = enumerate_candidates(&space, &context, &window, None);
        candidates.count as u64
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0037",
        name: "conjecture_enumeration",
        iterations: 2000,
        cycles_median: enum_median,
        cycles_min: enum_min,
    });
    println!(
        "conjecture_enumeration: {:.2} cycles median (min {:.2})",
        enum_median, enum_min
    );

    // Measurement 2: cycles per bounded mini refutation on the discarded path
    // (the unprovable candidate k7 = k0 - no axiom mentions k7 - consumes the
    // whole refute budget on a fresh mini space without touching the main
    // store, which keeps repeated measurement uniform).
    let t_k7 = terms
        .intern_fun(
            &symbols,
            (0.._builder.symbol_count())
                .find(|id| _builder.name_of(*id) == Some("k7"))
                .expect("k7"),
            &[],
        )
        .expect("k7 term");
    let unprovable = terms
        .intern_eq(&symbols, t_k7, t_k0)
        .map(|atom| Literal::new(atom, true))
        .expect("candidate");
    let (filter_median, filter_min) = measure_cycles(8, |_| {
        match refute_and_maybe_import(
            &space,
            &context,
            &options,
            unprovable,
            &MiniCapacities::production(),
        )
        .expect("filter")
        {
            CandidateOutcome::Discarded => 1,
            CandidateOutcome::Imported => panic!("the unprovable candidate imported"),
            CandidateOutcome::Aborted => panic!("arena pressure aborted the bench"),
        }
    });
    write_artifact(&Measurement {
        bench_id: "CEP-BENCH-0037",
        name: "conjecture_filter_discard",
        iterations: 8,
        cycles_median: filter_median,
        cycles_min: filter_min,
    });
    println!(
        "conjecture_filter_discard: {:.2} cycles median (min {:.2})",
        filter_median, filter_min
    );
    let _ = arena;
}
