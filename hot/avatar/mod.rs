// CEP:FILE: hot/avatar/mod.rs
// CEP:WHAT: The AVATAR integration module (design 12): the splitter (variable-dependency connected components), the component table (hash-consed components with dense assertion variables), and the controller (the four-rule loop over the Phase 3 given-clause engine).
// CEP:WHY: Design 26 Phase 4 build order: AVATAR is the ATP-SAT bridge - design 12.4's integration rules (no serialization: components and their clauses live in the shared arena; no locks: the controller and the abstraction solver run on the search thread; no FFI: both engines are Rust in one crate; shared proof graph: component clauses carry AvatarSplit derivations in the same store and derivation DAG; shared resource budgets: the abstraction solver's conflict budget and the component-table capacities are named constants from config/limits.rs).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: all backing memory comes from the caller-provided arena shared with the search space.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs; unit/hot/avatar_component_test.rs; unit/hot/avatar_controller_test.rs; property/avatar_property_test.rs.
// CEP:SECURITY: all capacities are named bounds (kAvatarComponentCapacity, kAvatarComponentWordCapacity, kAvatarSplitNodeBudget, kAvatarMaxConflictRounds, kAvatarMaxModelRotations).
// CEP:UNSAFE: none; the module is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the splitter, interning, activation order, and round protocol are pure functions of the input.
// CEP:HPC-PASS-LEGALITY: Formal Spec 12 (12_avatar_splitting.md) fixes the splitting lemma, the interning contract, the monotone-activation soundness and completeness theorems, the saturation theorem, and the degradation policy; every legality comment in this module cites it.

pub mod component;
pub mod controller;
pub mod splitter;

pub use component::{canonical_component_words, AvatarError, ComponentTable, Interned};
pub use controller::{
    saturate_with_avatar, AddOutcome, AvatarController, AvatarOptions, AvatarOutcome, AvatarStats,
    ControllerError,
};
pub use splitter::{try_split, try_split_with, SplitDecision, SplitView};
