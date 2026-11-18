// CEP:FILE: config/strategy.rs
// CEP:WHAT: The named strategy presets of design 21.1/15.2 (CEP-1035): the tag vocabulary shared with the hot crate's strategy enums, the preset record, and the deterministic default table.
// CEP:WHY: Design 21.1: "a strategy is a named configuration that specifies: inference rules to use, selection heuristic, weight function, simplification level, AVATAR on/off, theory reasoning on/off, restart strategy, time slice" and "strategies are defined in config/strategy.rs"; this crate is the dependency-free constant layer (no_std, no functions), so the presets are plain records of tag values whose mapping onto the hot enums (mapt_hot::search::passive::SelectionStrategy, mapt_hot::inference::{SelectionFunction, OrderingKind}) is pinned mechanically by the unit test unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums - the tags here and the enum discriminants there are one contract edited in lockstep (CEP&CC Law 8: the pin test fails loudly when they drift); the presets give the CEP-1 driver and the portfolio manager named, deterministic starting configurations instead of ad-hoc field bundles, and the schedule of design 21.2 is the preset table's order.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: compile-time constants; mapping drift fails the pin test, never a runtime fault.
// CEP:ASSUMES: the tag values match the hot enums' explicit discriminants (pin-tested); tag semantics are documented per constant.
// CEP:COST: compile-time only; no runtime instructions.
// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{preset_tags_match_hot_enums, default_preset_maps_to_search_options}.
// CEP:SECURITY: no_std, zero dependencies, constants only; no hidden parameter sources (CEP&CC Law 2).

//! Named strategy presets (design 21.1/15.2): the tag vocabulary, the preset record, and the default table.
//!
//! Every value is a compile-time constant with a documented source; the crate carries no functions. The tag values are the contract counterpart of the hot crate's strategy enum discriminants and are pinned by a unit test on the hot side, so a one-sided edit fails loudly instead of silently reinterpreting a preset.

// CEP:WHAT: Naming-lint allowance for kPascalCase constants.
// CEP:WHY: CEP&CC 50.5 (the crate-wide exemption documented in config/lib.rs): the design document mandates kPascalCase.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: config/lib.rs crate attributes.
// CEP:SECURITY: none.
#![allow(non_upper_case_globals)]

/// CEP:WHAT: Passive-set strategy tag: age/weight ratio (design 15.2 row 1, the default).
/// CEP:WHY: Matches mapt_hot::search::passive::SelectionStrategy::AgeWeightRatio (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kStrategyTagAgeWeightRatio: u8 = 0;
/// CEP:WHAT: Passive-set strategy tag: weight-only (design 15.2 row 3; not fair in isolation, Spec 08 section 4).
/// CEP:WHY: Matches mapt_hot::search::passive::SelectionStrategy::WeightOnly (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kStrategyTagWeightOnly: u8 = 1;
/// CEP:WHAT: Passive-set strategy tag: age-only breadth-first (design 15.2 row 4).
/// CEP:WHY: Matches mapt_hot::search::passive::SelectionStrategy::AgeOnly (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kStrategyTagAgeOnly: u8 = 2;
/// CEP:WHAT: Passive-set strategy tag: conjecture distance (design 15.2 row 2, CEP-1035).
/// CEP:WHY: Matches mapt_hot::search::passive::SelectionStrategy::ConjectureDistance (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kStrategyTagConjectureDistance: u8 = 3;

/// CEP:WHAT: Literal-selection tag: no selection, pure maximality (design 10.2 default).
/// CEP:WHY: Matches mapt_hot::inference::SelectionFunction::None (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kSelectionTagNone: u8 = 0;
/// CEP:WHAT: Literal-selection tag: first negative literal (design 10.2).
/// CEP:WHY: Matches mapt_hot::inference::SelectionFunction::FirstNegative (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kSelectionTagFirstNegative: u8 = 1;

/// CEP:WHAT: Ordering tag: Knuth-Bendix ordering (design 8.3 default).
/// CEP:WHY: Matches mapt_hot::inference::OrderingKind::Kbo (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kOrderingTagKbo: u8 = 0;
/// CEP:WHAT: Ordering tag: lexicographic path ordering (design 8.3 alternative).
/// CEP:WHY: Matches mapt_hot::inference::OrderingKind::Lpo (pin-tested).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: discriminant contract.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kOrderingTagLpo: u8 = 1;

/// CEP:WHAT: One named strategy preset (design 21.1): the passive-set strategy, literal selection, and term ordering as tag values plus the set-of-support, conjecture-harvest, and AVATAR switches.
/// CEP:WHY: Design 21.1's strategy record narrowed to the fields the current search layer consumes (SearchOptions); the missing design rows (theory reasoning on/off, restart strategy, time slice) are Phase 5 concerns and are deliberately absent rather than stubbed (CEP&CC Law 2: no silent assumptions); the record is Copy so presets live in one static table.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: tag values valid per the constants above; the hot-side translator rejects nothing (every tag combination is legal).
/// CEP:COST: 6 bytes per record.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StrategyPreset {
    /// CEP:WHAT: The passive-set strategy tag (kStrategyTag*).
    /// CEP:WHY: Design 15.2's priority function.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: valid tag.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
    /// CEP:SECURITY: none.
    pub passive_strategy: u8,
    /// CEP:WHAT: The literal-selection tag (kSelectionTag*).
    /// CEP:WHY: Design 10.2's selection function.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: valid tag.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
    /// CEP:SECURITY: none.
    pub selection_function: u8,
    /// CEP:WHAT: The term-ordering tag (kOrderingTag*).
    /// CEP:WHY: Design 8.3's ordering choice.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: valid tag.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
    /// CEP:SECURITY: none.
    pub ordering: u8,
    /// CEP:WHAT: Whether the set-of-support selection restriction is on (design 15.2 row 5, CEP-1035).
    /// CEP:WHY: The restriction is a search-level switch (which clauses may become given), orthogonal to the priority function; completeness position: refutationally complete when the non-supported clause set is satisfiable and the conjecture's negation is present (Wos, Robinson & Carson 1965; Spec 08 section 7).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the driver marks the conjecture inputs (NegatedConjecture rule) or the search degenerates to no generation (documented in Spec 08).
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{default_preset_maps_to_search_options, sos_restriction_spares_nonsupport_clauses}.
    /// CEP:SECURITY: none.
    pub set_of_support: bool,
    /// CEP:WHAT: Whether the in-loop conjecture harvest is on (Spec 16).
    /// CEP:WHY: SearchOptions.conjecture; speculative work with a fixed schedule.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: harvest budgets are the named constants.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::harvest_schedule_fires.
    /// CEP:SECURITY: the schedule bounds speculative work.
    pub conjecture: bool,
    /// CEP:WHAT: Whether AVATAR splitting is on (design 12).
    /// CEP:WHY: SearchOptions-level switch consumed by the AVATAR driver (saturate_with_avatar).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the caller picks the matching saturation entry point.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: none.
    pub avatar: bool,
}

/// CEP:WHAT: The default preset: age/weight ratio, no literal selection, KBO, no set of support, no harvest, AVATAR off.
/// CEP:WHY: Design 15.2 row 1 is the documented default and SearchOptions::new mirrors it; the preset keeps the default reachable by name from config-driven callers.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
/// CEP:SECURITY: none.
pub const kDefaultPreset: StrategyPreset = StrategyPreset {
    passive_strategy: kStrategyTagAgeWeightRatio,
    selection_function: kSelectionTagNone,
    ordering: kOrderingTagKbo,
    set_of_support: false,
    conjecture: false,
    avatar: false,
};

/// CEP:WHAT: The conjecture-focused preset: conjecture-distance selection with the set-of-support restriction and first-negative literal selection, KBO.
/// CEP:WHY: Design 15.2 rows 2 and 5 together (CEP-1035): focus selection on conjecture vocabulary and restrict given-clause selection to conjecture descendants - the standard SOS configuration for conjecture disproval; the harvest stays off (the driver opts in) and AVATAR stays off (the driver picks the entry point).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: the driver sets the conjecture symbol set and marks the conjecture inputs.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::{default_preset_maps_to_search_options, sos_restriction_spares_nonsupport_clauses}.
/// CEP:SECURITY: none.
pub const kConjectureFocusedPreset: StrategyPreset = StrategyPreset {
    passive_strategy: kStrategyTagConjectureDistance,
    selection_function: kSelectionTagFirstNegative,
    ordering: kOrderingTagKbo,
    set_of_support: true,
    conjecture: false,
    avatar: false,
};

/// CEP:WHAT: The exhaustive preset: age-only breadth-first selection, no literal selection, KBO, no restrictions.
/// CEP:WHY: Design 15.2 row 4: the unconditionally fair strategy (Spec 08 section 4) as the exhaustive-saturation configuration; completeness claims without fairness preconditions use this preset.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::default_preset_maps_to_search_options.
/// CEP:SECURITY: none.
pub const kExhaustivePreset: StrategyPreset = StrategyPreset {
    passive_strategy: kStrategyTagAgeOnly,
    selection_function: kSelectionTagNone,
    ordering: kOrderingTagKbo,
    set_of_support: false,
    conjecture: false,
    avatar: false,
};

/// CEP:WHAT: The deterministic preset schedule (design 21.2): the three named presets in table order.
/// CEP:WHY: Design 21.2: "MAPT can generate a schedule of strategies to run. The schedule is a sequence of (strategy, time_slice) pairs. The schedule is deterministic." - this table is the deterministic sequence; the slice durations are the driver's budget domain (the hot crate stays clock-free), so the schedule here is the preset ORDER and the driver attaches the slices.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: consumed in table order.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/hot/strategy_selection_test.rs::preset_tags_match_hot_enums.
/// CEP:SECURITY: none.
pub const kStrategySchedule: [StrategyPreset; 3] =
    [kDefaultPreset, kConjectureFocusedPreset, kExhaustivePreset];
