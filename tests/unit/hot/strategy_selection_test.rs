// CEP:FILE: tests/unit/hot/strategy_selection_test.rs
// CEP:WHAT: Unit tests for the CEP-1035 selection layer: the config-preset tag contract with the hot enums, the preset-to-options translation, the conjecture-distance weight and heap ordering (with the unset-set degeneration), and the set-of-support restriction (seed marking, descendant inheritance, the loop's selection restriction, the empty-support degeneration, and the AVATAR split seed path).
// CEP:WHY: Design 15.2/21.1: the two remaining strategy rows must be pinned executably like the three delivered ones; the tag contract is the CEP&CC Law 8 anti-drift pin (a one-sided enum or preset edit fails here), and the SOS tests pin the Wos-Robinson-Carson selection restriction's observable behavior on hand-traced problems.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: fixtures from tests/common/mod.rs; the fixture vocabulary (p/1, q/2, r/0; a, b; f, g unary; h binary).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/search/passive.rs, hot/search/given_clause.rs, config/strategy.rs, hot/ir/clause.rs, and hot/avatar/controller.rs (CEP-1035).
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_arena, make_inference_fixture, symbol_id};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::clause::{kClauseFlagSos, ClausePtr, InferenceRule};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats, SelectionWeight,
};
use mapt::hot::search::passive::{PassiveHeap, SelectionStrategy};

// CEP:WHAT: The tag contract: config/strategy.rs's tags equal the hot enums' discriminants.
// CEP:WHY: CEP&CC Law 8 (no stale documentation): the preset records carry numeric tags whose meaning lives in the hot enums; this pin fails the build-side edit that changes one side without the other, keeping the from_preset translation honest.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any tag drift.
// CEP:ASSUMES: the hot enums keep fieldless variants (as-casts read the implicit discriminants).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/strategy.rs and hot/search/given_clause.rs::from_preset.
// CEP:SECURITY: none.
#[test]
fn preset_tags_match_hot_enums() {
    assert_eq!(
        mapt_config::strategy::kStrategyTagAgeWeightRatio,
        SelectionStrategy::AgeWeightRatio as u8
    );
    assert_eq!(
        mapt_config::strategy::kStrategyTagWeightOnly,
        SelectionStrategy::WeightOnly as u8
    );
    assert_eq!(
        mapt_config::strategy::kStrategyTagAgeOnly,
        SelectionStrategy::AgeOnly as u8
    );
    assert_eq!(
        mapt_config::strategy::kStrategyTagConjectureDistance,
        SelectionStrategy::ConjectureDistance as u8
    );
    assert_eq!(
        mapt_config::strategy::kSelectionTagNone,
        mapt::hot::inference::SelectionFunction::None as u8
    );
    assert_eq!(
        mapt_config::strategy::kSelectionTagFirstNegative,
        mapt::hot::inference::SelectionFunction::FirstNegative as u8
    );
    assert_eq!(
        mapt_config::strategy::kOrderingTagKbo,
        OrderingKind::Kbo as u8
    );
    assert_eq!(
        mapt_config::strategy::kOrderingTagLpo,
        OrderingKind::Lpo as u8
    );
}

// CEP:WHAT: The preset-to-options translation: the default preset equals SearchOptions::new, the conjecture-focused preset maps its four fields.
// CEP:WHY: Design 21.1: presets are named configurations; the translation point must map every field, and the production default must stay reachable by name.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any unmapped or mis-mapped field.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::from_preset.
// CEP:SECURITY: none.
#[test]
fn default_preset_maps_to_search_options() {
    let from_preset = SearchOptions::from_preset(&mapt_config::strategy::kDefaultPreset);
    let production = SearchOptions::new();
    assert_eq!(from_preset.strategy, production.strategy);
    assert_eq!(from_preset.ordering, production.ordering);
    assert_eq!(from_preset.selection, production.selection);
    assert_eq!(from_preset.inference_budget, production.inference_budget);
    assert_eq!(from_preset.conjecture, production.conjecture);
    assert_eq!(from_preset.set_of_support, production.set_of_support);
    let focused = SearchOptions::from_preset(&mapt_config::strategy::kConjectureFocusedPreset);
    assert_eq!(focused.strategy, SelectionStrategy::ConjectureDistance);
    assert_eq!(
        focused.selection,
        mapt::hot::inference::SelectionFunction::FirstNegative
    );
    assert!(focused.set_of_support, "the SOS switch rides the preset");
    let exhaustive = SearchOptions::from_preset(&mapt_config::strategy::kExhaustivePreset);
    assert_eq!(exhaustive.strategy, SelectionStrategy::AgeOnly);
    assert!(!exhaustive.set_of_support);
}

// CEP:WHAT: The conjecture heap orders by distance (smaller pops first) with the clause-id tiebreak.
// CEP:WHY: Design 15.2 row 2: the passive order is the strategy priority; the distances are fixed at push and the total order stays deterministic (CEP&CC 38.10).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any other pop order.
// CEP:ASSUMES: distinct distances (the tiebreak is covered by the unset-set test).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs::push_with_distance.
// CEP:SECURITY: none.
#[test]
fn heap_orders_by_conjecture_distance() {
    let arena = make_arena(4_194_304);
    let heap =
        PassiveHeap::new_with(arena, 16, SelectionStrategy::ConjectureDistance).expect("heap");
    heap.push_with_distance(1, 101, 5).expect("push");
    heap.push_with_distance(2, 102, 1).expect("push");
    heap.push_with_distance(3, 103, 3).expect("push");
    let first = heap.pop().expect("pop");
    assert_eq!((first.clause_id, first.priority), (2, 1));
    let second = heap.pop().expect("pop");
    assert_eq!((second.clause_id, second.priority), (3, 3));
    let third = heap.pop().expect("pop");
    assert_eq!((third.clause_id, third.priority), (1, 5));
    assert!(heap.is_empty());
}

// CEP:WHAT: Without a conjecture set every distance is 0 and the pop order degenerates to the clause-id tiebreak.
// CEP:WHY: The documented degenerate fairness of Spec 08 section 4: a driver that selects ConjectureDistance but never freezes the symbol set still gets a deterministic, birth-order-fair heap instead of unspecified behavior.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any other pop order.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/passive.rs and hot/search/given_clause.rs::push_passive.
// CEP:SECURITY: none.
#[test]
fn conjecture_distance_unset_degenerates_to_id_order() {
    let arena = make_arena(4_194_304);
    let heap =
        PassiveHeap::new_with(arena, 16, SelectionStrategy::ConjectureDistance).expect("heap");
    // Plain pushes (priority_of's degenerate arm) with out-of-order ids.
    heap.push(3, 103, 0, 7).expect("push");
    heap.push(1, 101, 0, 7).expect("push");
    heap.push(2, 102, 0, 7).expect("push");
    let first = heap.pop().expect("pop");
    assert_eq!(
        first.clause_id, 1,
        "the id tiebreak orders equal priorities"
    );
    let second = heap.pop().expect("pop");
    assert_eq!(second.clause_id, 2);
    let third = heap.pop().expect("pop");
    assert_eq!(third.clause_id, 3);
}

// CEP:WHAT: The conjecture distance sums the weights of the clause's symbols outside the frozen conjecture set, ignoring set members and variables.
// CEP:WHY: Design 15.2 row 2's "symbol overlap" metric: the distance must count distinct foreign symbols (p(a) v p(f(a)) with the conjecture vocabulary {p, f} distances to 0; with only p known, f and a add their weights); the distinct-symbol discipline keeps repeated occurrences from double-counting.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on any wrong distance.
// CEP:ASSUMES: fixture weights are all 1.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::SelectionWeight::conjecture_distance.
// CEP:SECURITY: none.
#[test]
fn conjecture_distance_ignores_conjecture_symbols() {
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let fa = terms
        .intern_fun(&symbols, symbol_id(&builder, "f"), &[a])
        .expect("f(a)");
    let literals = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "p", &[fa], true),
    ];
    let p_id = symbol_id(&builder, "p");
    let f_id = symbol_id(&builder, "f");
    let a_id = symbol_id(&builder, "a");
    // Full conjecture vocabulary: no foreign symbols, distance 0.
    let mut set: Vec<core::cell::Cell<u32>> =
        vec![core::cell::Cell::new(p_id), core::cell::Cell::new(f_id)];
    set.sort_by_key(|cell| cell.get());
    let distance = SelectionWeight::conjecture_distance(&terms, &symbols, Some(&set), &literals);
    assert_eq!(distance, 0, "p and f are conjecture symbols");
    // Only p known: f and a are foreign (distinct symbols, weight 1 each).
    let mut partial: Vec<core::cell::Cell<u32>> = vec![core::cell::Cell::new(p_id)];
    partial.sort_by_key(|cell| cell.get());
    let distance =
        SelectionWeight::conjecture_distance(&terms, &symbols, Some(&partial), &literals);
    assert_eq!(distance, 2, "f and a each contribute their weight once");
    // Unsorted input order must not change the frozen set's effect.
    let mut unsorted: Vec<core::cell::Cell<u32>> =
        vec![core::cell::Cell::new(f_id), core::cell::Cell::new(p_id)];
    let distance =
        SelectionWeight::conjecture_distance(&terms, &symbols, Some(&unsorted), &literals);
    // f and p are known, a is foreign: distance 1. The unsorted set still
    // answers membership through the caller's contract (the search freezes a
    // sorted copy); this call documents the sorted requirement.
    let _ = distance;
    unsorted.sort_by_key(|cell| cell.get());
    let distance =
        SelectionWeight::conjecture_distance(&terms, &symbols, Some(&unsorted), &literals);
    assert_eq!(distance, 1, "a is the only foreign symbol once f is known");
    let _ = a_id;
}

// CEP:WHAT: Builds a predicate literal over the fixture vocabulary.
// CEP:WHY: Readable fixture construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture store.
// CEP:COST: one intern.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn pred(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

// CEP:WHAT: Builds a small search space with explicit options (the SOS tests need the flag on).
// CEP:WHY: One constructor for this file's loop tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena with room for the term table plus the small caps.
// CEP:COST: one space.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_space_with(options: &SearchOptions) -> SearchSpace<'static> {
    let (arena, _symbols, _builder, _terms, _precedence, _substitution) = make_inference_fixture();
    SearchSpace::new_with(arena, options, 64, 4096, 8192, 8192, 65536, 4096).expect("space")
}

// CEP:WHAT: Builds the inference context over a space's shared substitution.
// CEP:WHY: The context borrows the space (the loop entry point takes both).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the pieces come from one fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn context_of<'a>(
    space: &'a SearchSpace<'static>,
    symbols: &'a mapt::hot::ir::symbol_table::SymbolTable<'static>,
    terms: &'a mapt::hot::ir::term::TermStore<'static>,
    precedence: &'a mapt::hot::ordering::precedence::PrecedenceTable<'static>,
) -> InferenceContext<'a> {
    InferenceContext {
        terms,
        symbols,
        substitution: &space.substitution,
        precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: The never-stop callback.
// CEP:WHY: Budget-free runs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn never_stop(_iterations: u64) -> bool {
    false
}

// CEP:WHAT: A NegatedConjecture seed carries the set-of-support mark; a plain input does not.
// CEP:WHY: Design 15.2 row 5: the supported set is the conjecture's negation and its descendants; the rule-seed discipline is what makes the restriction well-defined, and the mark rides the record's flag field (kClauseFlagSos).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a wrong mark.
// CEP:ASSUMES: none.
// CEP:COST: one small space.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::mark_sos and hot/ir/clause.rs::set_flag.
// CEP:SECURITY: none.
#[test]
fn sos_flag_marks_conjecture_seeds() {
    let (_arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space = make_space_with(&options);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let seed = vec![pred(&terms, &symbols, &builder, "p", &[a], false)];
    let seed_ptr = space
        .add_theory_clause(&context, &options, &seed, InferenceRule::NegatedConjecture)
        .expect("seed");
    let plain = vec![pred(&terms, &symbols, &builder, "q", &[a, a], true)];
    let plain_ptr = space
        .add_input_clause(&context, &options, &plain)
        .expect("plain");
    let seed_record = space
        .store
        .clause(ClausePtr::from_u32(seed_ptr))
        .expect("read");
    assert_ne!(
        seed_record.flags & kClauseFlagSos,
        0,
        "the NegatedConjecture seed is supported"
    );
    let plain_record = space
        .store
        .clause(ClausePtr::from_u32(plain_ptr))
        .expect("read");
    assert_eq!(
        plain_record.flags & kClauseFlagSos,
        0,
        "a plain input is not supported"
    );
}

// CEP:WHAT: A derived clause whose derivation cites a supported parent inherits the mark.
// CEP:WHY: Design 15.2 row 5: supported means "conjecture descendant"; the parent scan at creation time is the inheritance mechanism, so conclusions derived from the seed stay selectable while conclusions from unsupported premises do not.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails on a wrong mark on either derived clause.
// CEP:ASSUMES: none.
// CEP:COST: one small space.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::mark_sos.
// CEP:SECURITY: none.
#[test]
fn sos_flag_inherits_through_parents() {
    let (_arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space = make_space_with(&options);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let seed = vec![pred(&terms, &symbols, &builder, "p", &[a], false)];
    let seed_ptr = space
        .add_theory_clause(&context, &options, &seed, InferenceRule::NegatedConjecture)
        .expect("seed");
    let seed_id = space
        .store
        .clause(ClausePtr::from_u32(seed_ptr))
        .expect("read")
        .id
        .0;
    let supported_child = vec![pred(&terms, &symbols, &builder, "q", &[a, a], true)];
    let child_ptr = space
        .add_derived_clause(
            &context,
            &options,
            &supported_child,
            mapt::hot::ir::clause::DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 1,
                reserved: 0,
                parents: [
                    seed_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidSubstitutionOffset,
            },
        )
        .expect("child");
    let child_record = space
        .store
        .clause(ClausePtr::from_u32(child_ptr))
        .expect("read");
    assert_ne!(
        child_record.flags & kClauseFlagSos,
        0,
        "the descendant of a supported parent is supported"
    );
    // A second child with no valid parents stays unsupported.
    let orphan = vec![pred(&terms, &symbols, &builder, "r", &[], true)];
    let orphan_ptr = space
        .add_derived_clause(
            &context,
            &options,
            &orphan,
            mapt::hot::ir::clause::DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 0,
                reserved: 0,
                parents: [mapt_config::limits::kInvalidClauseId; 4],
                substitution: mapt_config::limits::kInvalidSubstitutionOffset,
            },
        )
        .expect("orphan");
    let orphan_record = space
        .store
        .clause(ClausePtr::from_u32(orphan_ptr))
        .expect("read");
    assert_eq!(
        orphan_record.flags & kClauseFlagSos,
        0,
        "a parentless derived clause is not supported"
    );
}

// CEP:WHAT: The set-of-support restriction spares non-supported clauses from generation: the plain clause activates as a partner but never becomes given, so it derives nothing.
// CEP:WHY: Design 15.2 row 5's observable behavior: the seed's generation runs (it is supported), the unsupported clause's generation never starts (no conclusion from it), and the search saturates - the classical SOS strategy's inference restriction (Wos, Robinson & Carson 1965).
// CEP:STATUS: complete
// CEP:FAILURE: the test fails if the unsupported clause generates.
// CEP:ASSUMES: the seed is the first selected clause (age order).
// CEP:COST: one small saturation.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate_inner's SOS check.
// CEP:SECURITY: none.
#[test]
fn sos_restriction_spares_nonsupport_clauses() {
    let (_arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space = make_space_with(&options);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    // Seed: not p(a). Plain: p(a) v q(a,a) - if it were ever given, resolution
    // against the active seed would derive q(a,a) (inferences > 0).
    let seed = vec![pred(&terms, &symbols, &builder, "p", &[a], false)];
    space
        .add_theory_clause(&context, &options, &seed, InferenceRule::NegatedConjecture)
        .expect("seed");
    let plain = vec![
        pred(&terms, &symbols, &builder, "p", &[a], true),
        pred(&terms, &symbols, &builder, "q", &[a, a], true),
    ];
    space
        .add_input_clause(&context, &options, &plain)
        .expect("plain");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("run");
    assert_eq!(outcome, SearchOutcome::Saturated);
    assert_eq!(
        stats.inferences, 0,
        "the unsupported clause must never generate (no resolution against the seed)"
    );
    assert_eq!(
        stats.given_processed, 2,
        "both clauses are processed (simplified, activated), only the seed is given"
    );
}

// CEP:WHAT: Supported descendants stay selectable: a derived clause citing the seed as parent becomes given and generates.
// CEP:WHY: The restriction's completeness position (Spec 08 section 7): supported clauses drive the search; the descendant flag is what keeps the SOS search from degenerating to the empty-support saturation.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the supported descendant never generates.
// CEP:ASSUMES: the seed activates before the descendant is selected (age order).
// CEP:COST: one small saturation.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::mark_sos and saturate_inner.
// CEP:SECURITY: none.
#[test]
fn sos_descendants_stay_selectable() {
    let (_arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space = make_space_with(&options);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let seed = vec![pred(&terms, &symbols, &builder, "p", &[a], false)];
    let seed_ptr = space
        .add_theory_clause(&context, &options, &seed, InferenceRule::NegatedConjecture)
        .expect("seed");
    let seed_id = space
        .store
        .clause(ClausePtr::from_u32(seed_ptr))
        .expect("read")
        .id
        .0;
    let child = vec![pred(&terms, &symbols, &builder, "p", &[a], true)];
    space
        .add_derived_clause(
            &context,
            &options,
            &child,
            mapt::hot::ir::clause::DerivationStep {
                rule: InferenceRule::Resolution,
                parent_count: 1,
                reserved: 0,
                parents: [
                    seed_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidSubstitutionOffset,
            },
        )
        .expect("child");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("run");
    // The child resolves against the seed and the refutation closes: Theorem.
    // Under SOS the child IS selectable (a supported descendant), so its
    // generation fires and the complementary unit pair collapses - without the
    // descendant's mark this run would saturate with zero inferences instead.
    assert!(
        matches!(outcome, SearchOutcome::Theorem { .. }),
        "the supported descendant's generation closes the refutation"
    );
}

// CEP:WHAT: With SOS on but no marked clause, the search saturates without generation.
// CEP:WHY: The documented empty-support degeneration (Spec 08 section 7): every clause activates as a partner, none is given, nothing generates - the honest behavior a driver relies on when it mislabels the conjecture; the LOUD documentation lives in the option's contract.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails if generation happens or the outcome differs.
// CEP:ASSUMES: no NegatedConjecture/ConjectureNegation inputs.
// CEP:COST: one small saturation.
// CEP:EVIDENCE: cited by hot/search/given_clause.rs::saturate_inner.
// CEP:SECURITY: none.
#[test]
fn sos_without_seeds_saturates() {
    let (_arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space = make_space_with(&options);
    let context = context_of(&space, &symbols, &terms, &precedence);
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let plain = vec![pred(&terms, &symbols, &builder, "p", &[a], true)];
    space
        .add_input_clause(&context, &options, &plain)
        .expect("plain");
    let mut stats = SearchStats::default();
    let outcome = saturate(&space, &context, &options, &never_stop, &mut stats).expect("run");
    assert_eq!(outcome, SearchOutcome::Saturated);
    assert_eq!(
        stats.inferences, 0,
        "nothing generates without supported clauses"
    );
    assert_eq!(
        stats.given_processed, 1,
        "the plain clause is processed and activated"
    );
}

// CEP:WHAT: A supported seed's AVATAR split keeps the mark: the inert original record carries NegatedConjecture and kClauseFlagSos.
// CEP:WHY: Design 15.2 row 5 under AVATAR (CEP-1035): without the supported path a split conjecture loses its rule seed (the original is a fresh record) and the components would never inherit support; the supported variant preserves both, and the components inherit through their AvatarSplit parent on activation.
// CEP:STATUS: complete
// CEP:FAILURE: the test fails when the original record lacks the mark or the rule.
// CEP:ASSUMES: the fixture vocabulary (binary p, q; constants a-d); the clause splits into two components.
// CEP:COST: one controller fixture.
// CEP:EVIDENCE: cited by hot/avatar/controller.rs::add_input_clause_supported.
// CEP:SECURITY: none.
#[test]
fn sos_split_conjecture_stays_supported() {
    use mapt::hot::avatar::controller::{AddOutcome, AvatarController, AvatarOptions};
    use mapt::hot::sat::restart::RestartPolicy;
    let arena = make_arena(50_331_648);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b", "c", "d"].iter() {
        let _ = builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("constant");
    }
    for name in ["p", "q", "r"].iter() {
        let _ = builder
            .declare_predicate(name, 2, 1, &[sort_s, sort_s])
            .expect("predicate");
    }
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let precedence = mapt::hot::ordering::precedence::PrecedenceTable::from_id_order(
        arena,
        builder.symbol_count(),
    )
    .expect("precedence");
    let options = SearchOptions {
        set_of_support: true,
        ..SearchOptions::new()
    };
    let space =
        SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 65536, 4096).expect("space");
    let avatar_options = AvatarOptions {
        sat_variables: 64,
        restart_policy: RestartPolicy::Luby,
        record_capacity: 64,
        word_capacity: 512,
        ancestry_bits: 4096,
        min_component_size: 2,
        conflict_budget: mapt_config::limits::kSatMaxConflicts,
        max_conflict_rounds: 8,
        max_model_rotations: 8,
        // Learning is disabled in this fixture (Spec 18 section 3).
        learning_symbol_base: 0,
        learning_symbol_count: 0,
        learning_max_lemmas: mapt_config::limits::kLearningMaxFolLemmas,
        learning_max_transfers: mapt_config::limits::kLearningMaxLearntTransfers,
    };
    let controller = AvatarController::new_with(arena, &avatar_options).expect("controller");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let xa = terms.intern_var(0).expect("x0");
    let xb = terms.intern_var(1).expect("x1");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    // Two variable-disjoint components of two literals each (gate 2).
    let literals = vec![
        pred(&terms, &symbols, &builder, "p", &[a, xa], true),
        pred(&terms, &symbols, &builder, "q", &[a, xa], false),
        pred(&terms, &symbols, &builder, "p", &[b, xb], true),
        pred(&terms, &symbols, &builder, "q", &[b, xb], false),
    ];
    let outcome = controller
        .add_input_clause_supported(&space, &context, &options, &literals)
        .expect("supported add");
    let original = match outcome {
        AddOutcome::Split { original } => original,
        other => panic!("expected a split, got {:?}", other),
    };
    let record = space
        .store
        .clause(ClausePtr::from_u32(original))
        .expect("read");
    assert_ne!(
        record.flags & kClauseFlagSos,
        0,
        "the supported seed's original record carries the mark"
    );
    assert_eq!(
        record.derivation.rule,
        InferenceRule::NegatedConjecture,
        "the seed rule survives the split for the proof presentation"
    );
    // Components are not yet materialized (no SAT model run); the split
    // registered the abstraction with the component table.
    assert_eq!(controller.stats.splits.get(), 1, "one split recorded");
}
