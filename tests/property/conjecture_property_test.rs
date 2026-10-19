// CEP:FILE: tests/property/conjecture_property_test.rs
// CEP:WHAT: Property tests of automated conjecture generation: only refutation-proved lemmas are ever added (every ConjectureLemma clause in the store passes the reductio invariants: a ConjectureNegation complement parent, an empty-clause parent, ancestry containment), the harvest is deterministic across double runs, and the harvest never modifies or removes existing clauses.
// CEP:WHY: Spec 16 section 6's soundness theorem and section 5's isolation theorem, executed: the no-unproven-lemma invariant is the feature's security boundary, the determinism property pins CEP&CC 38.10 at the module level, and the preservation property pins the store's append-only discipline under harvesting.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: the fixture vocabulary (oriented unit equations over a/b/c and constructor instances); the deterministic RNG.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/conjecture/{mod,filter}.rs property pointers.
// CEP:SECURITY: the reductio oracle is the soundness certification.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::DeterministicRng;
use mapt::cold::arena_host::allocate_aligned_region;
use mapt::cold::symbol_table_builder::SymbolTableBuilder;
use mapt::hot::conjecture::harvest_with_types;
use mapt::hot::induction::InductionDeclaration;
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{ClauseId, DerivationStep, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::symbol_table::{SortId, SymbolTable};
use mapt::hot::ir::term::{TermPtr, TermStore};
use mapt::hot::memory::arena::Arena;
use mapt::hot::ordering::precedence::PrecedenceTable;
use mapt::hot::search::given_clause::{SearchOptions, SearchSpace, SearchStats};
use mapt_config::limits::{
    kFirstClauseId, kInvalidClauseId, kInvalidSubstitutionOffset, kMaxDerivationParents,
};

// CEP:WHAT: Arena bytes for the property fixture.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kPropertyArena: u32 = 50_331_648;

// CEP:WHAT: The conjecture property fixture: a/b/c constants, zero/sk constants, succ unary, p/1 predicate, with random oriented unit-equation inputs and random derived units.
// CEP:WHY: Each property run draws a small random problem (2-4 input units over a/b/c in oriented form, 1-3 derived units) so the harvest's candidate set and filter outcomes vary.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every property.
// CEP:SECURITY: none.
struct ConjecturePropertyFixture {
    space: SearchSpace<'static>,
    symbols: SymbolTable<'static>,
    terms: TermStore<'static>,
    precedence: PrecedenceTable<'static>,
    options: SearchOptions,
    zero: u32,
    succ: u32,
    sk: u32,
}

// CEP:WHAT: Builds the random conjecture fixture.
// CEP:WHY: One constructor for the three properties.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any construction failure.
// CEP:ASSUMES: none.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by every property.
// CEP:SECURITY: none.
fn make_conjecture_property_fixture(rng: &mut DeterministicRng) -> ConjecturePropertyFixture {
    let region = allocate_aligned_region(kPropertyArena).expect("region");
    let arena: &'static Arena = Box::leak(Box::new(Arena::new(region).expect("arena")));
    let mut builder = SymbolTableBuilder::new();
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    let _a = builder.declare_function("a", 0, 1, &[], sort_s).expect("a");
    let _b = builder.declare_function("b", 0, 1, &[], sort_s).expect("b");
    let _c = builder.declare_function("c", 0, 1, &[], sort_s).expect("c");
    let zero = builder
        .declare_function("zero", 0, 1, &[], sort_s)
        .expect("zero");
    let sk = builder
        .declare_function("sk", 0, 1, &[], sort_s)
        .expect("sk");
    let succ = builder
        .declare_function("succ", 1, 1, &[sort_s], sort_s)
        .expect("succ");
    let _p = builder.declare_predicate("p", 1, 1, &[sort_s]).expect("p");
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
    // Random oriented input units eq(X_hi, X_lo) among the three constants
    // (the stored orientation is the rewrite-usable form; ids rank a < b < c).
    let ids: Vec<u32> = ["a", "b", "c"]
        .iter()
        .map(|name| {
            (0..builder.symbol_count())
                .find(|id| builder.name_of(*id) == Some(*name))
                .expect("symbol")
        })
        .collect();
    let terms_for: Vec<TermPtr> = ids
        .iter()
        .map(|id| terms.intern_fun(&symbols, *id, &[]).expect("const"))
        .collect();
    let input_draws = 2 + rng.below(3);
    for _ in 0..input_draws {
        let left = rng.below(3) as usize;
        let right = rng.below(3) as usize;
        if left == right {
            continue;
        }
        let (hi, lo) = if left > right {
            (left, right)
        } else {
            (right, left)
        };
        let atom = terms
            .intern_eq(&symbols, terms_for[hi], terms_for[lo])
            .expect("eq");
        space
            .add_input_clause(&context, &options, &[Literal::new(atom, true)])
            .expect("input unit");
    }
    // Random derived units (the T1/T2 source pool), marked Demodulation.
    let derived_draws = 1 + rng.below(3);
    for _ in 0..derived_draws {
        let left = rng.below(3) as usize;
        let right = rng.below(3) as usize;
        if left == right {
            continue;
        }
        let (hi, lo) = if left > right {
            (left, right)
        } else {
            (right, left)
        };
        let atom = terms
            .intern_eq(&symbols, terms_for[hi], terms_for[lo])
            .expect("eq");
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
    }
    ConjecturePropertyFixture {
        space,
        symbols,
        terms,
        precedence,
        options,
        zero,
        succ,
        sk,
    }
}

// CEP:WHAT: The reductio oracle: one ConjectureLemma clause passes every invariant of Spec 17 section 4.
// CEP:WHY: The executable form of the soundness certification: parent 0 is a ConjectureNegation clause with the literal-wise complement multiset, parent 1 is the empty clause, both parents are older, and the negation is an ancestor of the empty clause (a bounded walk without the cold checker's allocation).
// CEP:STATUS: complete
// CEP:FAILURE: returns Err with the offending fact.
// CEP:ASSUMES: the id is a ConjectureLemma clause.
// CEP:COST: O(clause literals + ancestry).
// CEP:EVIDENCE: used by only_proved_lemmas_added.
// CEP:SECURITY: the soundness oracle.
fn reductio_holds(fixture: &ConjecturePropertyFixture, lemma_id: u64) -> Result<(), &'static str> {
    let lemma = fixture
        .space
        .store
        .clause_by_id(ClauseId(lemma_id))
        .map_err(|_| "unreadable lemma")?;
    if lemma.derivation.parent_count != 2 {
        return Err("parent count");
    }
    let negation_id = lemma.derivation.parents[0];
    let empty_id = lemma.derivation.parents[1];
    if negation_id >= lemma_id || empty_id >= lemma_id {
        return Err("parent order");
    }
    let negation = fixture
        .space
        .store
        .clause_by_id(ClauseId(negation_id))
        .map_err(|_| "unreadable negation")?;
    if negation.derivation.rule != InferenceRule::ConjectureNegation {
        return Err("negation rule");
    }
    if negation.literal_count != lemma.literal_count {
        return Err("complement count");
    }
    for index in 0..lemma.literal_count {
        let literal = fixture
            .space
            .store
            .literal(lemma, index)
            .map_err(|_| "unreadable lemma literal")?;
        let mut matched = false;
        for other_index in 0..negation.literal_count {
            let other = fixture
                .space
                .store
                .literal(negation, other_index)
                .map_err(|_| "unreadable negation literal")?;
            if other.atom() == literal.atom() && other.is_positive() != literal.is_positive() {
                matched = true;
                break;
            }
        }
        if !matched {
            return Err("complement shape");
        }
    }
    let empty = fixture
        .space
        .store
        .clause_by_id(ClauseId(empty_id))
        .map_err(|_| "unreadable empty")?;
    if empty.literal_count != 0 {
        return Err("empty parent");
    }
    // Ancestry containment: the full closure walk.
    if full_ancestry_contains(fixture, empty_id, negation_id) {
        Ok(())
    } else {
        Err("ancestry containment")
    }
}

// CEP:WHAT: Full ancestry containment via a bounded iterative walk over every parent.
// CEP:WHY: The complete closure check (every parent chain explored), bounded by the id span times the parent count.
// CEP:STATUS: complete
// CEP:FAILURE: false when not contained.
// CEP:ASSUMES: both ids are live.
// CEP:COST: O(id span) worst case.
// CEP:EVIDENCE: used by reductio_holds.
// CEP:SECURITY: none.
fn full_ancestry_contains(fixture: &ConjecturePropertyFixture, from: u64, target: u64) -> bool {
    let next = fixture.space.store.next_clause_id().0;
    let span = (next - kFirstClauseId) as usize;
    let mut visited: Vec<bool> = vec![false; span + 1];
    let mut stack: Vec<u64> = vec![from];
    while let Some(current) = stack.pop() {
        if current < kFirstClauseId || current >= next {
            continue;
        }
        let slot = (current - kFirstClauseId) as usize;
        if slot >= visited.len() || visited[slot] {
            continue;
        }
        visited[slot] = true;
        if current == target {
            return true;
        }
        let record = match fixture.space.store.clause_by_id(ClauseId(current)) {
            Ok(record) => record,
            Err(_) => return false,
        };
        for slot_index in 0..record.derivation.parent_count as usize {
            let parent = record.derivation.parents[slot_index];
            if parent != kInvalidClauseId && parent >= kFirstClauseId {
                stack.push(parent);
            }
        }
    }
    false
}

// CEP:WHAT: After a harvest over random problems, every ConjectureLemma clause in the store passes the reductio oracle (only proved lemmas exist).
// CEP:WHY: Spec 16 section 6's soundness theorem, executed over random candidate sets.
// CEP:STATUS: complete
// CEP:FAILURE: property fails if any lemma fails the oracle.
// CEP:ASSUMES: the harvest ran to completion.
// CEP:COST: K runs.
// CEP:EVIDENCE: cited by hot/conjecture/{mod,filter}.rs (no-unproven-lemma invariant) and docs/formal/16_conjecture_generation.md section 6.
// CEP:SECURITY: soundness certification.
#[test]
fn only_proved_lemmas_added() {
    let mut rng = DeterministicRng::new(0xC0DE_C701);
    for _ in 0..10 {
        let fixture = make_conjecture_property_fixture(&mut rng);
        let context = InferenceContext {
            terms: &fixture.terms,
            symbols: &fixture.symbols,
            substitution: &fixture.space.substitution,
            precedence: &fixture.precedence,
            ordering: OrderingKind::Kbo,
        };
        let declaration = InductionDeclaration {
            zero: fixture.zero,
            succ: fixture.succ,
            skolem: fixture.sk,
            well_founded: None,
        };
        let mut stats = SearchStats::default();
        harvest_with_types(
            &fixture.space,
            &context,
            &fixture.options,
            Some(&declaration),
            &mut stats,
        );
        // Every lemma in the store passes the oracle.
        let mut lemmas = 0;
        let next = fixture.space.store.next_clause_id().0;
        for id in kFirstClauseId..next {
            let record = fixture
                .space
                .store
                .clause_by_id(ClauseId(id))
                .expect("record");
            if record.derivation.rule == InferenceRule::ConjectureLemma {
                lemmas += 1;
                assert_eq!(
                    reductio_holds(&fixture, id),
                    Ok(()),
                    "lemma c{} fails the reductio oracle",
                    id
                );
            }
        }
        assert_eq!(lemmas, stats.lemmas as u64);
    }
}

// CEP:WHAT: The harvest is deterministic: identical random fixtures produce identical lemma counts, candidate counts, and final id counters.
// CEP:WHY: CEP&CC 38.10: the two-run discipline at the harvest level.
// CEP:STATUS: complete
// CEP:FAILURE: property fails on any divergence.
// CEP:ASSUMES: same seed -> same fixture.
// CEP:COST: double runs.
// CEP:EVIDENCE: cited by hot/conjecture/mod.rs (file header HPC-DETERMINISM).
// CEP:SECURITY: none.
#[test]
fn harvest_deterministic_double_run() {
    for seed in [0xD373_B011, 0x225F_6A7B] {
        let run = || {
            let mut rng = DeterministicRng::new(seed);
            let fixture = make_conjecture_property_fixture(&mut rng);
            let context = InferenceContext {
                terms: &fixture.terms,
                symbols: &fixture.symbols,
                substitution: &fixture.space.substitution,
                precedence: &fixture.precedence,
                ordering: OrderingKind::Kbo,
            };
            let mut stats = SearchStats::default();
            harvest_with_types(&fixture.space, &context, &fixture.options, None, &mut stats);
            (
                stats.harvests,
                stats.candidates,
                stats.lemmas,
                fixture.space.store.next_clause_id().0,
            )
        };
        assert_eq!(run(), run(), "seed {:x}", seed);
    }
}

// CEP:WHAT: The harvest preserves every pre-existing clause: ids, literal counts, and derivation rules are unchanged.
// CEP:WHY: Spec 16 section 5's isolation theorem (the store is append-only under harvesting; nothing is rewritten or removed).
// CEP:STATUS: complete
// CEP:FAILURE: property fails on any mutation.
// CEP:ASSUMES: the snapshot before the harvest.
// CEP:COST: K runs.
// CEP:EVIDENCE: cited by hot/conjecture/filter.rs (isolation) and docs/formal/16_conjecture_generation.md section 5.
// CEP:SECURITY: store integrity.
#[test]
fn harvest_preserves_existing_clauses() {
    let mut rng = DeterministicRng::new(0x150E_9D04);
    for _ in 0..8 {
        let fixture = make_conjecture_property_fixture(&mut rng);
        let context = InferenceContext {
            terms: &fixture.terms,
            symbols: &fixture.symbols,
            substitution: &fixture.space.substitution,
            precedence: &fixture.precedence,
            ordering: OrderingKind::Kbo,
        };
        let before = fixture.space.store.next_clause_id().0;
        let mut snapshot: Vec<(u64, u16, InferenceRule)> = Vec::new();
        for id in kFirstClauseId..before {
            let record = fixture
                .space
                .store
                .clause_by_id(ClauseId(id))
                .expect("record");
            snapshot.push((id, record.literal_count, record.derivation.rule));
        }
        let mut stats = SearchStats::default();
        harvest_with_types(&fixture.space, &context, &fixture.options, None, &mut stats);
        for (id, literal_count, rule) in snapshot.iter() {
            let record = fixture
                .space
                .store
                .clause_by_id(ClauseId(*id))
                .expect("record");
            assert_eq!(record.literal_count, *literal_count, "clause {}", id);
            assert_eq!(record.derivation.rule, *rule, "clause {}", id);
        }
        assert!(fixture.space.store.next_clause_id().0 >= before);
    }
}
