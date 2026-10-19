// CEP:FILE: config/limits.rs
// CEP:WHAT: Named resource limits and capacity constants for every MAPT engine (ATP, SAT, arena, IR, preprocessing, portfolio).
// CEP:WHY: CEP&CC Law 7 and 11 ban hard-coded assumptions and magic numbers; every bound in MAPT must be a named, justified, enforced constant so limits double as security mitigations (CEP&CC 22.10, design 20.1, 25.3).
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Static assertions at the end of this file fail compilation if any invariant between constants is violated.
// CEP:ASSUMES: Values are engine-wide budgets chosen for a 64-bit workstation-class target with at least 4 GiB RAM; they are compile-time configuration, not measured facts.
// CEP:COST: compile-time only; no runtime instructions.
// CEP:EVIDENCE: unit test unit/config/limits_test.rs re-validates the invariants at runtime.
// CEP:SECURITY: These limits are the primary denial-of-service mitigation for untrusted input (design 25.1); none may be raised without a security review.

/// CEP:WHAT: Internal IR contract version, embedded in serialized IR.
/// CEP:WHY: CEP&CC 38.17 requires a versioned IR; mismatched versions must be detectable.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; consumers compare this constant against serialized headers.
/// CEP:ASSUMES: Bumped on every breaking IR layout change.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/config/limits_test.rs.
/// CEP:SECURITY: version confusion is a correctness defect; the check is mandatory.
pub const kIrVersion: u32 = 1;

/// CEP:WHAT: Total capacity of the shared arena region in bytes (256 MiB).
/// CEP:WHY: The arena is the single allocation domain for all engines (design 8.1); a fixed named capacity makes exhaustion an explicit, checkable error instead of unbounded growth (CEP&CC 22.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: Arena allocation returns ArenaError::Exhausted beyond this capacity; never panics, never grows.
/// CEP:ASSUMES: Capacity fits in a u32 byte offset; enforced by static assertion below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/arena_test.rs, property/arena_property_test.rs.
/// CEP:SECURITY: bounds worst-case memory consumption from untrusted problems.
pub const kArenaCapacityBytes: u32 = 268_435_456;

/// CEP:WHAT: Maximum alignment accepted by the arena allocator in bytes.
/// CEP:WHY: Alignments larger than one cache line are never required by Phase 1 layouts; bounding alignment keeps the power-of-two proof cheap and explicit (CEP&CC 11.1).
/// CEP:STATUS: complete
/// CEP:FAILURE: Arena allocation returns ArenaError::Misaligned for alignments above this bound.
/// CEP:ASSUMES: Must be a power of two and at most the smallest target cache line (see target modules); enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/arena_test.rs::alignment_rejected.
/// CEP:SECURITY: prevents attacker-controlled alignment from stalling the bump pointer.
pub const kMaxAlignment: u32 = 64;

/// CEP:WHAT: Maximum term depth accepted by term construction.
/// CEP:WHY: Bounds recursive traversal stack usage and unification cost (design 5.1); prevents stack overflow from malicious input (CEP&CC 22.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: Term construction returns TermError::DepthExceeded.
/// CEP:ASSUMES: Fits in the u16 depth field of the term header; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: contract/term_contract_test.rs::deep_term_rejected.
/// CEP:SECURITY: bounds recursion depth for untrusted TPTP/SMT input.
pub const kMaxTermDepth: u16 = 128;

/// CEP:WHAT: Maximum cached term weight before term construction refuses the term.
/// CEP:WHY: Weight is cached on the term header (design 8.3) and accumulated bottom-up; the bound makes overflow of the u32 field impossible by construction instead of by hope (CEP&CC 22.6).
/// CEP:STATUS: complete
/// CEP:FAILURE: Term construction returns TermError::WeightExceeded.
/// CEP:ASSUMES: Chosen below u32::MAX so that parent weight accumulation cannot overflow before the check fires.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: fuzz/term_fuzz_test.rs.
/// CEP:SECURITY: integer-overflow mitigation for untrusted input.
pub const kMaxTermWeight: u32 = 1 << 30;

/// CEP:WHAT: Capacity of the hash-consing table in slots (2^21, power of two).
/// CEP:WHY: Open addressing with linear probing requires a power-of-two capacity for mask-based indexing (design 5.1); the table never resizes, so capacity is chosen at build time.
/// CEP:STATUS: complete
/// CEP:FAILURE: Term interning returns TermError::TableFull when the load-factor bound is reached.
/// CEP:ASSUMES: Power of two; enforced by static assertion below.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs, property/term_property_test.rs.
/// CEP:SECURITY: bounds memory for untrusted symbol-heavy input.
pub const kTermHashTableCapacity: u32 = 2_097_152;

/// CEP:WHAT: Maximum hash-consing table load factor in percent before interning is refused.
/// CEP:WHY: Design 5.1 fixes the load-factor target at 0.65; probing cost degrades beyond it, so the bound is enforced, not advisory.
/// CEP:STATUS: complete
/// CEP:FAILURE: Term interning returns TermError::TableFull when live entries would exceed this fraction of capacity.
/// CEP:ASSUMES: Strictly less than 100; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::table_full_after_load_factor_bound.
/// CEP:SECURITY: bounds worst-case probe chains (denial-of-service mitigation).
pub const kTermHashTableLoadFactorPercent: u32 = 65;

/// CEP:WHAT: Maximum number of distinct function/predicate/sort symbols (2^16).
/// CEP:WHY: The frozen symbol table and all symbol IDs are dense u32 values bounded by this constant (design 5.6); bounding prevents symbol-table exhaustion attacks (CEP&CC 22.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: Symbol insertion returns SymbolError::TableFull.
/// CEP:ASSUMES: Fits the u32 symbol field of the term header with room for the reserved invalid sentinel; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/symbol_bounds_test.rs.
/// CEP:SECURITY: bounds symbol-table memory for untrusted input.
pub const kMaxSymbolCount: u32 = 65_536;

/// CEP:WHAT: Maximum arity of any function or predicate symbol.
/// CEP:WHY: The frozen symbol table stores fixed-size sort signatures; bounding arity keeps them allocation-free (design 5.6) and bounds child arrays.
/// CEP:STATUS: complete
/// CEP:FAILURE: Symbol insertion returns SymbolError::ArityExceeded.
/// CEP:ASSUMES: Fits the u16 arity and child-count fields; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/symbol_bounds_test.rs::arity_bound_enforced.
/// CEP:SECURITY: bounds per-symbol memory for untrusted input.
pub const kMaxSymbolArity: u16 = 32;

/// CEP:WHAT: Maximum literals per ATP clause.
/// CEP:WHY: Clause size is bounded by design 5.3 so overflow storage and iteration stay bounded.
/// CEP:STATUS: complete
/// CEP:FAILURE: Clause construction returns ClauseError::TooManyLiterals.
/// CEP:ASSUMES: At least kInlineClauseLiterals; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs.
/// CEP:SECURITY: bounds clause memory for untrusted input.
pub const kMaxClauseLiterals: u16 = 512;

/// CEP:WHAT: Literals stored inline in the clause header before the overflow array is used.
/// CEP:WHY: Design 5.3 fixes inline storage at 8 literals, covering over 95 percent of clauses and eliminating one pointer indirection on the hot path.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a layout constant.
/// CEP:ASSUMES: At most kMaxClauseLiterals; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::inline_and_overflow_layout.
/// CEP:SECURITY: none; layout only.
pub const kInlineClauseLiterals: usize = 8;

/// CEP:WHAT: Maximum parent clauses recorded in one derivation step.
/// CEP:WHY: Design 5.4 fixes the bounded parent array at 4 entries; all Phase 1 inference rules use at most two parents.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a layout constant.
/// CEP:ASSUMES: Exactly matches the fixed parents array length; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::derivation_step_layout.
/// CEP:SECURITY: none; layout only.
pub const kMaxDerivationParents: usize = 4;

/// CEP:WHAT: Reserved value meaning "no clause" in u32 clause offsets.
/// CEP:WHY: Sentinel-free optional offsets require a reserved value; using all-ones makes it recognizable in a debugger and impossible as a real arena offset (capacity is far smaller).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: kArenaCapacityBytes is far below this value; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
/// CEP:SECURITY: sentinel misuse is caught by bounds checks in accessors.
pub const kInvalidClauseOffset: u32 = u32::MAX;

/// CEP:WHAT: Reserved value meaning "no term" in u32 term offsets.
/// CEP:WHY: Same sentinel discipline as kInvalidClauseOffset for the ATP term store.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: kArenaCapacityBytes is far below this value; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs.
/// CEP:SECURITY: sentinel misuse is caught by bounds checks in accessors.
pub const kInvalidTermOffset: u32 = u32::MAX;

/// CEP:WHAT: Reserved value meaning "no substitution" in u32 substitution offsets.
/// CEP:WHY: Same sentinel discipline for derivation-step substitution references (design 5.4).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: kArenaCapacityBytes is far below this value; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs.
/// CEP:SECURITY: sentinel misuse is caught by bounds checks in accessors.
pub const kInvalidSubstitutionOffset: u32 = u32::MAX;

/// CEP:WHAT: Reserved symbol ID meaning "no symbol".
/// CEP:WHY: Sentinel discipline for symbol references; distinct from all dense symbol IDs.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: kMaxSymbolCount is far below this value; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/symbol_bounds_test.rs.
/// CEP:SECURITY: sentinel misuse is caught by ID bounds checks.
pub const kInvalidSymbolId: u32 = u32::MAX;

/// CEP:WHAT: First valid ATP clause ID; zero is the reserved invalid ID.
/// CEP:WHY: Design 5.3 requires stable monotonic clause IDs; reserving zero gives every live clause a nonzero, falsifiable identity.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: The clause counter starts at this value.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::ids_are_monotonic.
/// CEP:SECURITY: none; identity discipline only.
pub const kFirstClauseId: u64 = 1;

/// CEP:WHAT: Reserved value meaning "no clause" in u64 clause IDs.
/// CEP:WHY: Derivation-step parent slots must distinguish "absent parent" from a real ID.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a sentinel constant.
/// CEP:ASSUMES: Clause counters never reach this value because kMaxClauses is far smaller; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs.
/// CEP:SECURITY: none.
pub const kInvalidClauseId: u64 = 0;

/// CEP:WHAT: Maximum distinct variables per clause / per substitution binding array.
/// CEP:WHY: Design 5.5 bounds the flat substitution array with this constant, giving O(1) lookup with no hashing and a hard memory bound.
/// CEP:STATUS: complete
/// CEP:FAILURE: Substitution binding returns SubstitutionError::TooManyVariables.
/// CEP:ASSUMES: Phase 1 substitutions are per-clause; cross-clause inference substitutions revisit this bound in Phase 2 (ticket CEP-1002).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs, contract coverage in substitution tests.
/// CEP:SECURITY: bounds substitution memory.
pub const kMaxVariablesPerClause: u32 = 64;

/// CEP:WHAT: Maximum depth of recursive unification or matching attempts.
/// CEP:WHY: Design 8.2 bounds the binding trail and recursion; unification itself arrives in Phase 2 but the budget constant is fixed now (design 20.1).
/// CEP:STATUS: complete
/// CEP:FAILURE: Unification will return UnifyError::DepthExceeded (Phase 2).
/// CEP:ASSUMES: Larger than kMaxTermDepth so legal deep terms remain unifiable.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 2; unit tests will cite this constant.
/// CEP:SECURITY: bounds recursion for untrusted input.
pub const kMaxUnificationDepth: u32 = 256;

/// CEP:WHAT: Maximum entries on the substitution binding trail used for backtracking.
/// CEP:WHY: The trail is a fixed arena array (no allocation); the bound makes exhaustion explicit (design 8.2).
/// CEP:STATUS: complete
/// CEP:FAILURE: Substitution bind returns SubstitutionError::TrailFull.
/// CEP:ASSUMES: At least kMaxVariablesPerClause times a safety margin for repeated bind/undo cycles.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/substitution_test.rs::trail_undo_restores_state.
/// CEP:SECURITY: bounds trail memory.
pub const kMaxSubstitutionTrailDepth: u32 = 4_096;

/// CEP:WHAT: Maximum Boolean variables in the SAT engine (2^21).
/// CEP:WHY: Assignment, phase, and watch-head arrays are sized by this bound and allocated once before the hot path (design 11.1 S1/S6/S8).
/// CEP:STATUS: complete
/// CEP:FAILURE: SAT clause creation returns SatError::VariableOutOfRange.
/// CEP:ASSUMES: Variable indices fit u32 with the sign bit shifted in; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/literal_encoding_test.rs.
/// CEP:SECURITY: bounds SAT state memory for untrusted DIMACS input.
pub const kMaxSatVariables: u32 = 2_097_152;

/// CEP:WHAT: Maximum literals in one SAT clause.
/// CEP:WHY: Watched-literal clause storage is length-prefixed in the arena; the bound keeps scans bounded (design 11.1 S3).
/// CEP:STATUS: complete
/// CEP:FAILURE: SAT clause creation returns SatError::TooManyLiterals.
/// CEP:ASSUMES: Fits the u32 clause length field.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: fuzz/sat_fuzz_test.rs.
/// CEP:SECURITY: bounds per-clause memory and BCP scan length.
pub const kMaxSatClauseLiterals: u32 = 512;

/// CEP:WHAT: Maximum learnt clauses retained before deletion policy runs (design 11.6).
/// CEP:WHY: Learnt-clause growth is the dominant memory risk in CDCL; the named threshold is enforced by the database (Phase 2 implements deletion; the budget is fixed now).
/// CEP:STATUS: complete
/// CEP:FAILURE: Database reports SatError::LearntBudgetExceeded when deletion is not yet available (Phase 1).
/// CEP:ASSUMES: Deletion policy (S25/S26) is Phase 2 scope; ticket CEP-1003.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 2; constant validated in limits_test.
/// CEP:SECURITY: bounds learnt-clause memory.
pub const kSatMaxLearntClauses: u32 = 100_000;

/// CEP:WHAT: Base conflict interval for the Luby restart sequence (design 11.5).
/// CEP:WHY: Restarts are Phase 2 (S16); the base interval is a named constant so the strategy is configuration, not a magic number (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; consumed by Phase 2 restart scheduling.
/// CEP:ASSUMES: Positive; standard Luby base.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 2; ticket CEP-1004.
/// CEP:SECURITY: none.
pub const kSatRestartBaseInterval: u32 = 100;

/// CEP:WHAT: Maximum wall-clock seconds for one search run (design 20.1).
/// CEP:WHY: Global time budget; enforced every kBudgetCheckInterval iterations to keep the check off the per-iteration hot path (design 20.2).
/// CEP:STATUS: complete
/// CEP:FAILURE: Search returns Result::Timeout when exceeded (search loop is Phase 3; the budget is fixed now).
/// CEP:ASSUMES: Time source is a budgeted cold call (CEP&CC 25.3.1 allows std::time only outside the hot path).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3; ticket CEP-1005.
/// CEP:SECURITY: CPU-time denial-of-service mitigation.
pub const kMaxSearchTimeSeconds: u64 = 60;

/// CEP:WHAT: Maximum total inference steps for one search run.
/// CEP:WHY: Design 20.2 checks this every iteration; the bound makes search termination unconditional.
/// CEP:STATUS: complete
/// CEP:FAILURE: Search returns Result::InferenceLimit.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: CPU-time denial-of-service mitigation.
pub const kMaxInferences: u64 = 100_000_000;

/// CEP:WHAT: Maximum clauses in the ATP clause database.
/// CEP:WHY: Design 20.1 bounds clause count; checked when adding a clause.
/// CEP:STATUS: complete
/// CEP:FAILURE: Search returns Result::MemoryExhausted.
/// CEP:ASSUMES: Far below u64::MAX so monotonic IDs never collide with the sentinel; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: memory denial-of-service mitigation.
pub const kMaxClauses: u64 = 10_000_000;

/// CEP:WHAT: Maximum accepted input file size in bytes (64 MiB).
/// CEP:WHY: Parser bound kMaxInputBytes from design 6.3; all input is untrusted (CEP&CC 22.5).
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::TooLarge (parser is Phase 3).
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3; ticket CEP-1006.
/// CEP:SECURITY: memory denial-of-service mitigation.
pub const kMaxInputBytes: u64 = 67_108_864;

/// CEP:WHAT: Maximum AST nodes in one parsed formula.
/// CEP:WHY: Parser bound kMaxFormulaNodes from design 6.3; prevents CPU exhaustion during parsing.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::TooLarge.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: CPU denial-of-service mitigation.
pub const kMaxFormulaNodes: u64 = 10_000_000;

/// CEP:WHAT: Maximum quantifier nesting depth in input formulas.
/// CEP:WHY: Parser bound kMaxQuantifierDepth from design 6.3; prevents exponential CNF blowup from nesting.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::TooDeep.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: CPU denial-of-service mitigation.
pub const kMaxQuantifierDepth: u32 = 100;

/// CEP:WHAT: Maximum recursive descent depth in parsers.
/// CEP:WHY: Parser bound kMaxParseDepth from design 6.2; prevents stack overflow (CEP&CC 22.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::TooDeep.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: stack-overflow mitigation.
pub const kMaxParseDepth: u32 = 1_024;

/// CEP:WHAT: Maximum TPTP include nesting depth.
/// CEP:WHY: Parser bound kMaxIncludeDepth from design 6.3; prevents infinite include loops.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::IncludeTooDeep.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: resource-exhaustion mitigation.
pub const kMaxIncludeDepth: u32 = 16;

/// CEP:WHAT: Maximum number of include files resolved per parse.
/// CEP:WHY: Parser bound kMaxIncludeCount from design 6.3.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing returns ParseError::TooManyIncludes.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: resource-exhaustion mitigation.
pub const kMaxIncludeCount: u32 = 64;

/// CEP:WHAT: Maximum CNF expansion ratio before definitional encoding aborts.
/// CEP:WHY: Design 7.2 stage 5: exceeding the ratio aborts preprocessing with a documented fallback instead of unbounded blowup.
/// CEP:STATUS: complete
/// CEP:FAILURE: Preprocessing aborts the stage and proceeds with current clauses (design 7.3).
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: CPU denial-of-service mitigation.
pub const kMaxCnfExpansionRatio: u32 = 8;

/// CEP:WHAT: Maximum bounded rewrite passes during simplification.
/// CEP:WHY: Design 7.2 stage 10 fixes a pass bound so simplification terminates.
/// CEP:STATUS: complete
/// CEP:FAILURE: Simplification stops after this many rounds.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: termination guarantee.
pub const kMaxSimplifyRounds: u32 = 3;

/// CEP:WHAT: Maximum arena fragmentation ratio in percent before compaction is requested.
/// CEP:WHY: Design 8.1 triggers cold compaction above this ratio; the threshold is configuration.
/// CEP:STATUS: complete
/// CEP:FAILURE: Compaction (CEP-1 cold pass) is scheduled; search continues.
/// CEP:ASSUMES: Below 100; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3; ticket CEP-1007.
/// CEP:SECURITY: memory-pressure mitigation.
pub const kMaxArenaFragmentationRatioPercent: u32 = 50;

/// CEP:WHAT: Maximum milliseconds allowed for an index rebuild before giving up.
/// CEP:WHY: Design 9.5: rebuild cost is bounded; exceeding the bound returns GaveUp.
/// CEP:STATUS: complete
/// CEP:FAILURE: Search returns Result::GaveUp with reason index_rebuild_timeout.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 2 (indexing).
/// CEP:SECURITY: CPU denial-of-service mitigation.
pub const kMaxIndexRebuildTimeMs: u64 = 1_000;

/// CEP:WHAT: Maximum inferences generated per given clause per iteration.
/// CEP:WHY: Design 10.3 defers excess inferences to the next iteration so one clause cannot flood the passive set.
/// CEP:STATUS: complete
/// CEP:FAILURE: Excess inferences are deferred, never dropped.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: fairness/throughput guard.
pub const kMaxInferencesPerClause: u32 = 10_000;

/// CEP:WHAT: Iterations between time-budget checks in the search loop.
/// CEP:WHY: Design 20.2: time is checked every kBudgetCheckInterval iterations because a clock read per iteration is unaffordable in CEP-0.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a scheduling constant.
/// CEP:ASSUMES: Power of two so the modulo lowers to a mask; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: none.
pub const kBudgetCheckInterval: u64 = 1_024;

/// CEP:WHAT: Maximum milliseconds for the safe-state transition after budget exhaustion.
/// CEP:WHY: Design 20.3 bounds shutdown; overrun aborts with a diagnostic.
/// CEP:STATUS: complete
/// CEP:FAILURE: Abort with diagnostic if the transition exceeds the bound.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: hang mitigation.
pub const kSafeStateTransitionMs: u64 = 100;

/// CEP:WHAT: Portfolio worker thread count.
/// CEP:WHY: Design 19.4 fixes the worker count as a named constant; threads are created before the hot path.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; consumed by Phase 4 portfolio manager.
/// CEP:ASSUMES: At least 1; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4; ticket CEP-1008.
/// CEP:SECURITY: thread-count denial-of-service mitigation.
pub const kPortfolioThreadCount: u32 = 8;

/// CEP:WHAT: Time slice per strategy in milliseconds (design 15.4).
/// CEP:WHY: Portfolio scheduling constant; named so strategy control remains configuration.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; consumed by Phase 4.
/// CEP:ASSUMES: At least 1.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4.
/// CEP:SECURITY: none.
pub const kPortfolioTimeSliceMs: u64 = 1_000;

/// CEP:WHAT: Maximum weight of a clause shared between portfolio workers.
/// CEP:WHY: Design 19.2: heavier clauses are not shared; the threshold is configuration.
/// CEP:STATUS: complete
/// CEP:FAILURE: Sharing is refused above the bound.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4.
/// CEP:SECURITY: bounds inter-worker traffic.
pub const kSharedClauseMaxWeight: u32 = 100;

/// CEP:WHAT: Maximum LBD of a clause shared between portfolio workers.
/// CEP:WHY: Design 19.2: high-LBD clauses are low quality and not shared.
/// CEP:STATUS: complete
/// CEP:FAILURE: Sharing is refused above the bound.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4.
/// CEP:SECURITY: bounds inter-worker traffic.
pub const kSharedClauseMaxLbd: u8 = 8;

/// CEP:WHAT: Minimum literal count for an AVATAR split component.
/// CEP:WHY: Design 12.3: components below this threshold are not split.
/// CEP:STATUS: complete
/// CEP:FAILURE: Splitting is skipped for small components.
/// CEP:ASSUMES: At least 1; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 4.
/// CEP:SECURITY: none.
pub const kAvatarMinComponentSize: u16 = 2;

/// CEP:WHAT: Minimum inferences per second before adaptive strategy switching triggers.
/// CEP:WHY: Design 15.5: a stalled strategy is switched; the threshold is configuration.
/// CEP:STATUS: complete
/// CEP:FAILURE: Strategy switch (cold) is triggered.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: none.
pub const kMinInferenceRate: u64 = 1_000;

/// CEP:WHAT: Maximum proof steps recorded before proof logging refuses new steps.
/// CEP:WHY: Design 11.1 S42: the proof-step buffer is bounded by kMaxProofSteps.
/// CEP:STATUS: complete
/// CEP:FAILURE: Proof logging returns Result::MemoryExhausted.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3.
/// CEP:SECURITY: memory denial-of-service mitigation.
pub const kMaxProofSteps: u64 = 100_000_000;

/// CEP:WHAT: Maximum diagnostics emitted per run before suppression.
/// CEP:WHY: CEP&CC 38.15 requires diagnostics bounded in count; unbounded diagnostics are a denial-of-service vector.
/// CEP:STATUS: complete
/// CEP:FAILURE: Further diagnostics are suppressed with a single terminal notice.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3 diagnostics module.
/// CEP:SECURITY: output-flooding mitigation.
pub const kMaxDiagnosticsCount: u32 = 1_000;

/// CEP:WHAT: Maximum bytes of a single diagnostic message.
/// CEP:WHY: CEP&CC 38.15 requires diagnostics bounded in size.
/// CEP:STATUS: complete
/// CEP:FAILURE: Message is truncated deterministically.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: reserved for Phase 3 diagnostics module.
/// CEP:SECURITY: output-flooding mitigation.
pub const kMaxDiagnosticBytes: u32 = 4_096;

/// CEP:WHAT: Default KBO weight of function and predicate symbols.
/// CEP:WHY: Design 8.3 requires symbol weights of at least 1 for KBO admissibility; the default is named configuration, not a magic number (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a default value.
/// CEP:ASSUMES: At least 1; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
/// CEP:SECURITY: none.
pub const kDefaultSymbolWeight: u32 = 1;

/// CEP:WHAT: KBO weight of variables (must be at least 1 for admissibility, design 8.3).
/// CEP:WHY: Term weight accumulation must treat variables uniformly; the value is named configuration.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a default value.
/// CEP:ASSUMES: At least 1; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/term_test.rs::weight_accumulation.
/// CEP:SECURITY: none.
pub const kKboVariableWeight: u32 = 1;

/// CEP:WHAT: Weight of a variable in the clause-selection weight function (design 15.3 fixes it at 0).
/// CEP:WHY: Selection weighting is distinct from KBO weighting; both are named to prevent silent conflation.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a default value.
/// CEP:ASSUMES: None.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::clause_weight_is_sum_of_atom_weights.
/// CEP:SECURITY: none.
pub const kSelectionVariableWeight: u32 = 0;

/// CEP:WHAT: Number of watch-list heads: two per Boolean variable (one per literal polarity).
/// CEP:WHY: Design 11.1 S6: watch lists are indexed by literal encoding; the derived count keeps sizing consistent with kMaxSatVariables.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a derived sizing constant.
/// CEP:ASSUMES: Exactly two literals per variable; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
/// CEP:SECURITY: none.
pub const kSatWatchListCount: u32 = kMaxSatVariables * 2;

/// CEP:WHAT: Maximum entries on the SAT trail (one assignment per variable).
/// CEP:WHY: A variable is assigned at most once between backtracks, so the trail is bounded by the variable count (design 11.1 S5).
/// CEP:STATUS: complete
/// CEP:FAILURE: Trail push returns SatError::TrailFull.
/// CEP:ASSUMES: Backtracking pops entries before variables are reassigned; invariant verified by property tests.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_trail_test.rs, property/bcp_property_test.rs.
/// CEP:SECURITY: bounds trail memory.
pub const kSatTrailCapacity: u32 = kMaxSatVariables;

/// CEP:WHAT: Maximum decision levels tracked by the trail.
/// CEP:WHY: Level start indices are stored per level; bounded by the variable count because each level owns at least one assignment.
/// CEP:STATUS: complete
/// CEP:FAILURE: Level push returns SatError::TooManyLevels.
/// CEP:ASSUMES: At least one assignment per level.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_trail_test.rs.
/// CEP:SECURITY: bounds level-array memory.
pub const kMaxDecisionLevels: u32 = kMaxSatVariables;

/// CEP:WHAT: VSIDS activity decay in percent: each conflict multiplies the activity increment by 100 / kSatVsidsDecayPercent.
/// CEP:WHY: Design 11.1 S13 (activity decay / update): the geometric decay of the increment makes recent conflicts dominate variable ordering; the percent form keeps the constant an integer like every other named limit (design 20.1) while the f64 arithmetic happens only inside the VSIDS heap.
/// CEP:STATUS: complete
/// CEP:FAILURE: Static assertions reject values outside 1..=99.
/// CEP:ASSUMES: 95 percent (MiniSat-style 0.95 decay per conflict, Moskewicz et al. DAC 2001).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::decay_grows_increment; property/cdcl_property_test.rs.
/// CEP:SECURITY: none.
pub const kSatVsidsDecayPercent: u32 = 95;

/// CEP:WHAT: VSIDS activity ceiling at which all scores and the increment are rescaled.
/// CEP:WHY: Design 11.1 S7 stores activities as f64; unbounded bumping over a long search would overflow to infinity and destroy the heap ordering; the MiniSat rescale discipline (multiply all activities and the increment by the rescale factor once the increment passes the ceiling) keeps every score finite and the comparison total, which preserves determinism (CEP&CC 38.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a maintenance threshold, not an error path.
/// CEP:ASSUMES: 1e100 leaves many orders of magnitude before f64 overflow.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::rescale_keeps_scores_finite.
/// CEP:SECURITY: none.
pub const kSatVsidsActivityCeiling: f64 = 1e100;

/// CEP:WHAT: Factor applied to every activity and to the increment during a VSIDS rescale.
/// CEP:WHY: The reciprocal scale of the ceiling restores scores to a small range while preserving the heap order in practice (multiplication by a positive constant is weakly order-preserving on non-negative finite doubles; ties it creates are resolved deterministically by the index tie-break).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: kSatVsidsActivityCeiling * kSatVsidsRescaleFactor <= 1.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::rescale_keeps_scores_finite.
/// CEP:SECURITY: none.
pub const kSatVsidsRescaleFactor: f64 = 1e-100;

/// CEP:WHAT: Default decision polarity (phase) for variables with no saved phase.
/// CEP:WHY: Design 11.1 S14 (phase selection: saved phase or constant phase); false mirrors the MiniSat default of trying the negated literal first, which empirically shortens refutations.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: phase saving starts from this constant.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_vsids_test.rs::saved_phase_defaults_to_constant.
/// CEP:SECURITY: none.
pub const kSatDefaultPhasePositive: bool = false;

/// CEP:WHAT: Maximum number of conflicts one CDCL solve may process before returning Indeterminate.
/// CEP:WHY: Design 20.1 named-limit discipline: every engine has an explicit budget so unbounded search is impossible (CEP&CC 22.10); CDCL terminates in theory, but a defensive budget converts pathological inputs into an explicit bounded-failure result instead of an unbounded run.
/// CEP:STATUS: complete
/// CEP:FAILURE: CdclSolver::solve returns Indeterminate(CdclError::ConflictBudgetExceeded) past the budget.
/// CEP:ASSUMES: Same order as the ATP inference budget kMaxInferences.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
/// CEP:SECURITY: denial-of-service bound on adversarial formulas.
pub const kSatMaxConflicts: u64 = 100_000_000;

/// CEP:WHAT: Geometric restart growth factor in percent (each restart multiplies the interval by this factor / 100).
/// CEP:WHY: Design 11.5: "Geometric restarts are available as an alternative" to Luby; the percent form keeps the named-constant discipline (design 20.1, CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: Static assertions reject values below 100 (which would shrink intervals without bound).
/// CEP:ASSUMES: 150 percent (1.5x growth, a common middle ground between Luby and pure doubling).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_restart_test.rs::geometric_intervals_grow.
/// CEP:SECURITY: none.
pub const kSatRestartGeometricFactorPercent: u32 = 150;

/// CEP:WHAT: Maximum ordering-comparison steps (recursive clause examinations) in one KBO/LPO comparison.
/// CEP:WHY: LPO recursion can multiply comparisons exponentially on pathological terms; the step budget turns that into a loud bounded failure (CEP&CC 22.10 unbounded-recursion ban) while leaving every realistic comparison unaffected.
/// CEP:STATUS: complete
/// CEP:FAILURE: Ordering comparison returns OrderingError::StepBudgetExceeded past the budget.
/// CEP:ASSUMES: 65,536 steps is far above any realistic comparison (ground terms below the depth and weight caps).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::ordering_step_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on adversarial term pairs.
pub const kMaxOrderingSteps: u32 = 65_536;

/// CEP:WHAT: Maximum node count of one discrimination tree.
/// CEP:WHY: Design 9.2: nodes are allocated contiguously in the arena; a named cap bounds arena consumption by the index (design 20.1) and makes exhaustion an explicit error instead of arena starvation.
/// CEP:STATUS: complete
/// CEP:FAILURE: Insert returns IndexError::TreeFull at the cap.
/// CEP:ASSUMES: 2^20 nodes x 20 bytes = 20 MiB, sized against kMaxClauses-scale workloads.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::discrimination_tree_node_cap_enforced.
/// CEP:SECURITY: bounds index memory under untrusted insert floods.
pub const kDiscriminationTreeNodes: u32 = 1_048_576;

/// CEP:WHAT: Maximum payload entries (leaf list nodes) of one discrimination tree.
/// CEP:WHY: Every indexed (term, payload) pair allocates one leaf entry; the cap is the second explicit bound on index memory next to the node cap (design 20.1).
/// CEP:STATUS: complete
/// CEP:FAILURE: Insert returns IndexError::EntryBudgetExceeded at the cap.
/// CEP:ASSUMES: 2^22 entries x 16 bytes = 64 MiB, above the clause budget kMaxClauses with one entry per indexed literal.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/phase2_bounds_test.rs::discrimination_tree_entry_budget_enforced.
/// CEP:SECURITY: bounds index memory under untrusted insert floods.
pub const kDiscriminationTreeEntries: u32 = 4_194_304;

/// CEP:WHAT: Reserved edge symbol encoding equality atoms in the discrimination tree (they carry no symbol-table ID).
/// CEP:WHY: Equality atoms are indexed like function applications (design 5.1 Eq(left, right)); the reserved value must not collide with any real symbol ID (dense below kMaxSymbolCount) nor with kInvalidSymbolId.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a representation constant.
/// CEP:ASSUMES: kMaxSymbolCount and kInvalidSymbolId leave the value unreachable by real symbols; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::equality_terms_indexed.
/// CEP:SECURITY: none.
pub const kIndexEqualitySymbol: u32 = u32::MAX - 1;

/// CEP:WHAT: Sentinel node index meaning "no node" inside the discrimination tree.
/// CEP:WHY: Intrusive child and sibling links terminate in a named sentinel instead of a magic -1 or reused invalid offset (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: u32::MAX-2 is never a valid node index because node count is capped below it.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs.
/// CEP:SECURITY: none.
pub const kInvalidIndexNode: u32 = u32::MAX - 2;

/// CEP:WHAT: Sentinel entry index meaning "no payload entry" inside a discrimination-tree leaf list.
/// CEP:WHY: Leaf lists are singly linked through arena entries; the terminator is a named constant (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: u32::MAX-2 never aliases a real entry because the entry count is capped below it.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs.
/// CEP:SECURITY: none.
pub const kInvalidIndexEntry: u32 = u32::MAX - 2;

/// CEP:WHAT: Maximum flat preorder symbols of a term indexed into, or queried against, one discrimination tree.
/// CEP:WHY: The tree walk and insert operate on flattened symbol sequences held in fixed stack buffers; the named capacity keeps the hot path allocation-free with a loud TermTooLarge error at the bound (CEP&CC 22.10, Law 6) instead of unbounded buffering.
/// CEP:STATUS: complete
/// CEP:FAILURE: Index insert/delete/retrieve return IndexError::TermTooLarge past the capacity.
/// CEP:ASSUMES: 1024 symbols covers realistic indexed and query terms (the clause-literal bound kMaxClauseLiterals x max symbol fan-out stays above it; deeper terms are pathological and rejected loudly).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::term_capacity_enforced; security/phase2_bounds_test.rs::index_capacity_enforced.
/// CEP:SECURITY: denial-of-service bound on index work per term.
pub const kIndexTermCapacity: u32 = 1024;

/// CEP:WHAT: Capacity of the SAT clause registry (problem plus learnt clause records, design 11.1 S4 enumerable database).
/// CEP:WHY: CEP-1003 (Phase 3) requires an enumerable clause database for the learnt-clause deletion policy (S25/S26) and for SAT preprocessing enumeration; a named capacity keeps the registry a fixed arena allocation with a loud RegistryFull error at the bound instead of unbounded growth.
/// CEP:STATUS: complete
/// CEP:FAILURE: clause registration returns SatCoreError::Storage(RegistryFull) past the capacity.
/// CEP:ASSUMES: 262_144 live clause records cover production workloads (kSatMaxLearntClauses = 100_000 learnts plus problem clauses); the capacity is injectable for tests.
/// CEP:COST: 16 bytes per entry plus 8 bytes of reduction scratch, 6 MiB together at the default capacity.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{registry_enumerates, capacity_enforced}; security/phase3_bounds_test.rs::registry_capacity_enforced.
/// CEP:SECURITY: memory-exhaustion bound on the tracked clause count.
pub const kSatRegistryCapacity: u32 = 262_144;

/// CEP:WHAT: Divisor of the learnt-clause reduction (the fraction of live learnts kept after a reduction round, design 11.6).
/// CEP:WHY: MiniSat-style database reduction deletes the worst half when the learnt budget is reached; the divisor names that fraction so the policy is a documented constant rather than a magic 2.
/// CEP:STATUS: complete
/// CEP:FAILURE: reduction never deletes more than live_count - live_count/divisor clauses; locked clauses are never deleted.
/// CEP:ASSUMES: >= 2; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::{reduction_keeps_best_half, locked_clauses_survive}.
/// CEP:SECURITY: none.
pub const kSatLearntReduceDivisor: u32 = 2;

/// CEP:WHAT: Clause-activity rescale ceiling for the SAT registry (design 11.1 S24 activity scores as f64).
/// CEP:WHY: Unbounded activity counters overflow to infinity and destroy the deletion ordering; rescaling all scores when the maximum exceeds the ceiling keeps the ordering total and deterministic (same discipline as the VSIDs heap, kSatVsidsActivityCeiling).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: >= 1.0; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::activity_rescale_preserves_order.
/// CEP:SECURITY: none.
pub const kSatClauseActivityCeiling: f64 = 1e100;

/// CEP:WHAT: Clause-activity rescale factor for the SAT registry.
/// CEP:WHY: Multiplier applied to every activity score on rescale; 1e-100 paired with the 1e100 ceiling keeps scores finite.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: ceiling * factor <= 1.0; enforced by static assertion.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_registry_test.rs::activity_rescale_preserves_order.
/// CEP:SECURITY: none.
pub const kSatClauseActivityRescaleFactor: f64 = 1e-100;

/// CEP:WHAT: Capacity of the DRAT proof step buffer (design 11.1 S42, bounded by kMaxProofSteps as the count bound).
/// CEP:WHY: Proof steps are recorded into a fixed arena buffer so proof logging is allocation-free on the hot path; the arena capacity is the structural bound while kMaxProofSteps (1e8) is the semantic count bound that a real proof cannot exceed before the arena does.
/// CEP:STATUS: complete
/// CEP:FAILURE: recording returns ProofError::StepBufferFull past the capacity; the solver surfaces it as Indeterminate (never silent truncation, CEP&CC Law 6).
/// CEP:ASSUMES: 1_048_576 steps cover production certificates (one add per learnt clause plus deletions); injectable for tests.
/// CEP:COST: 12 bytes per step, 12 MiB at the default capacity.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, capacity_enforced}; security/phase3_bounds_test.rs::proof_step_budget_enforced.
/// CEP:SECURITY: memory-exhaustion bound on proof size.
pub const kSatProofStepCapacity: u32 = 1_048_576;

/// CEP:WHAT: Capacity of the proof clause-offset to proof-id map.
/// CEP:WHY: DRAT deletions reference clauses by their addition-time identity; the recorder maintains an append-only (clause offset, proof id) map keyed by monotonically increasing arena offsets, binary-searched on deletion.
/// CEP:STATUS: complete
/// CEP:FAILURE: recording returns ProofError::MapFull past the capacity.
/// CEP:ASSUMES: one map entry per added clause, so kSatProofMapCapacity >= the maximum clause count of any proof run (1_048_576); injectable for tests.
/// CEP:COST: 8 bytes per entry, 8 MiB at the default capacity.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
/// CEP:SECURITY: memory-exhaustion bound.
pub const kSatProofMapCapacity: u32 = 1_048_576;

/// CEP:WHAT: Capacity of the proof literal blob (concatenated clause literals of all recorded steps).
/// CEP:WHY: Each step references its literals by (offset, length) into one flat arena blob, keeping the step records at a fixed 12 bytes regardless of clause length.
/// CEP:STATUS: complete
/// CEP:FAILURE: recording returns ProofError::LiteralBlobFull past the capacity.
/// CEP:ASSUMES: 4_194_304 literals (16 MiB) cover the default step capacity at an average clause length of 4; injectable for tests.
/// CEP:COST: 4 bytes per literal.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{literals_stored_verbatim, capacity_enforced}.
/// CEP:SECURITY: memory-exhaustion bound.
pub const kSatProofLiteralCapacity: u32 = 4_194_304;

/// CEP:WHAT: Sentinel proof id marking "no proof record" (clause added before proof recording was enabled or already deleted).
/// CEP:WHY: The offset-to-id map stores dense u32 ids; a sentinel keeps the "unmapped" state representable without Option on the hot path.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: never a valid proof id (valid ids start at 1); enforced by static assertion against the id base.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
/// CEP:SECURITY: none.
pub const kInvalidProofId: u32 = u32::MAX;

/// CEP:WHAT: First proof id assigned to a recorded clause addition.
/// CEP:WHY: Id 0 is reserved so kInvalidProofId (u32::MAX) and 0 never collide with valid ids and so DRAT ids are 1-based like the clause ids of the ATP side.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: fixed at 1.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::ids_are_monotonic.
/// CEP:SECURITY: none.
pub const kFirstProofId: u32 = 1;

/// CEP:WHAT: Maximum number of assumption literals per incremental solve call (design 11.1 S38).
/// CEP:WHY: Assumptions are pushed as decision levels and the failed-assumption core is collected into a fixed buffer; the named bound keeps both allocation-free with a loud error at the limit.
/// CEP:STATUS: complete
/// CEP:FAILURE: solve_with_assumptions returns AssumptionError::TooManyAssumptions past the capacity.
/// CEP:ASSUMES: 4_096 assumptions cover AVATAR component activations (Phase 4) and preprocessing probes; each assumption is a distinct variable or a repeat of a prior one (repeats are idempotent decisions).
/// CEP:COST: 4 bytes per slot, 16 KiB at the default capacity.
/// CEP:EVIDENCE: unit/hot/sat_assumptions_test.rs::{assumption_count_enforced, repeated_assumption_is_idempotent}.
/// CEP:SECURITY: denial-of-service bound on assumption-driven level depth.
pub const kMaxAssumptions: u32 = 4_096;

/// CEP:WHAT: Pair budget of one SAT preprocessing subsumption round (design 11.1 S30).
/// CEP:WHY: Pairwise subsumption is O(n^2); the budget bounds the work per round with an honest partial-round outcome (the pass stops and reports what it did) instead of unbounded scanning.
/// CEP:STATUS: complete
/// CEP:FAILURE: the subsumption round stops early with rounds_done < requested; the stats report the pairs examined (never silent, CEP&CC Law 6).
/// CEP:ASSUMES: 262_144 pair checks per round cover production preprocessing sizes; injectable for tests.
/// CEP:COST: one comparison-dominated check per pair.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{subsumption_deletes, pair_budget_stops_early}; security/phase3_bounds_test.rs::subsumption_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on preprocessing.
pub const kSatSubsumptionPairBudget: u32 = 262_144;

/// CEP:WHAT: Candidate budget of one SAT vivification round (design 11.1 S36).
/// CEP:WHY: Each vivification candidate costs up to kSatVivifyPropagationBudget propagation steps; bounding the candidate count bounds the whole pass.
/// CEP:STATUS: complete
/// CEP:FAILURE: the vivification round stops early with candidates_checked < candidates; reported in stats.
/// CEP:ASSUMES: 10_000 candidates per round cover production preprocessing; injectable for tests.
/// CEP:COST: bounded by candidates x propagation budget.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{vivification_shortens_clause, candidate_budget_stops_early}.
/// CEP:SECURITY: denial-of-service bound on preprocessing.
pub const kSatVivifyCandidateLimit: u32 = 10_000;

/// CEP:WHAT: Propagation-step budget of one SAT vivification round.
/// CEP:WHY: Vivification drives the BCP engine under assumed negations; the budget bounds total propagation work per round with a loud partial outcome.
/// CEP:STATUS: complete
/// CEP:FAILURE: the round stops early; stats report the budget exhaustion.
/// CEP:ASSUMES: 100_000 propagation steps per round; injectable for tests.
/// CEP:COST: one BCP step per budget unit.
/// CEP:EVIDENCE: unit/hot/sat_preprocess_test.rs::{vivification_shortens_clause, propagation_budget_stops_early}; security/phase3_bounds_test.rs::vivify_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on preprocessing.
pub const kSatVivifyPropagationBudget: u32 = 100_000;

/// CEP:WHAT: Maximum clauses one RUP/RAT check step of the internal DRAT checker may scan (design 11.1 S43).
/// CEP:WHY: A RAT check scans every clause containing the negated pivot; the named bound turns adversarial proof files into a loud CheckBudgetExceeded instead of unbounded scanning.
/// CEP:STATUS: complete
/// CEP:FAILURE: the checker reports the step as unverifiable (CheckBudgetExceeded) rather than silently passing it.
/// CEP:ASSUMES: 65_536 candidate clauses per pivot cover real proofs; injectable for tests.
/// CEP:COST: bounded scan per RAT step.
/// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{rat_step_verified, budget_enforced}.
/// CEP:SECURITY: denial-of-service bound on proof checking.
pub const kDratRatScanLimit: u32 = 65_536;

/// CEP:WHAT: Capacity of the passive-set priority heap of the ATP clause database (design 8.4).
/// CEP:WHY: The passive set is a flat binary heap in the arena; a named capacity keeps insertion allocation-free with a loud PassiveSetFull error at the bound.
/// CEP:STATUS: complete
/// CEP:FAILURE: passive insertion returns SearchError::PassiveFull past the capacity.
/// CEP:ASSUMES: 1_048_576 pending clauses cover production search runs (the kMaxClauses semantic bound remains 1e7); injectable for tests.
/// CEP:COST: 24 bytes per entry, 24 MiB at the default capacity.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{heap_orders_by_key, capacity_enforced}; security/phase3_bounds_test.rs::passive_capacity_enforced.
/// CEP:SECURITY: memory-exhaustion bound on the search state.
pub const kPassiveHeapCapacity: u32 = 1_048_576;

/// CEP:WHAT: Capacity of the active-set clause array and its feature-vector index (design 8.4/9.3).
/// CEP:WHY: The active set holds one dense slot per processed clause plus its sparse feature vector; named capacities keep both fixed arena allocations.
/// CEP:STATUS: complete
/// CEP:FAILURE: active insertion returns SearchError::ActiveFull past the capacity.
/// CEP:ASSUMES: 262_144 active clauses cover production search runs; injectable for tests.
/// CEP:COST: 12 bytes per slot.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, capacity_enforced}.
/// CEP:SECURITY: memory-exhaustion bound on the search state.
pub const kActiveSetCapacity: u32 = 262_144;

/// CEP:WHAT: Capacity of the feature-vector word pool backing the active set's feature-vector index (design 9.3).
/// CEP:WHY: Feature vectors are sparse (symbol, count) pairs appended into one shared arena pool; the pool is never compacted on active-set deletion (swap-remove drops the reference; pool garbage is reclaimed only by arena reset), so the capacity bounds the worst case loudly.
/// CEP:STATUS: complete
/// CEP:FAILURE: active insertion returns SearchError::FeaturePoolFull past the capacity.
/// CEP:ASSUMES: 4_194_304 words (16 MiB) at an average of 10 words per clause cover the active capacity; injectable for tests.
/// CEP:COST: 4 bytes per word.
/// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, pool_capacity_enforced}.
/// CEP:SECURITY: memory-exhaustion bound on the search state.
pub const kFeatureVectorPoolWords: u32 = 4_194_304;

/// CEP:WHAT: Maximum (symbol, count) pairs in one clause feature vector.
/// CEP:WHY: A clause with more distinct symbols than the bound is unfilterable (its vector passes every filter, falling through to full verification) - a sound degradation documented here instead of a hard failure, because subsumption remains correct, only slower.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; build_feature_vector reports truncated = true and the filter passes such clauses.
/// CEP:ASSUMES: 256 distinct symbols per clause cover realistic clauses (kMaxClauseLiterals x typical argument count).
/// CEP:COST: 2 words per pair.
/// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{filter_is_sound_on_truncated_vectors, pair_bound_enforced}.
/// CEP:SECURITY: none (sound degradation, not a resource bound).
pub const kFeatureVectorSlots: u32 = 256;

/// CEP:WHAT: Fixed-point scale of the age/weight selection ratio (design 15.2 "minimum age / weight ratio").
/// CEP:WHY: The priority key is computed as age * scale / weight in u64 fixed point (deterministic integer division, no floating point on the selection path); the scale names the precision.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: 2^16 scale keeps priorities exact for weights up to 2^16 and one-sided error of at most 1 unit otherwise (ties broken by clause id, so determinism is preserved regardless).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{ratio_priority_order, tie_breaks_by_clause_id}.
/// CEP:SECURITY: none.
pub const kSelectionRatioScale: u64 = 65_536;

/// CEP:WHAT: Maximum conclusions one given-clause generation step buffers before deferring to the next iteration (design 10.3).
/// CEP:WHY: The inference generator emits into a fixed caller buffer; when the buffer fills or kMaxInferencesPerClause is reached, the generator returns its cursor and the loop defers the remainder to the next iteration, which is what bounds per-clause work.
/// CEP:STATUS: complete
/// CEP:FAILURE: none (deferral is the designed behavior, not a failure).
/// CEP:ASSUMES: 64 conclusions per step keep the buffer at 64 x kMaxClauseLiterals literals worst case (32 KiB stack); injectable for tests via the buffer size itself.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced}.
/// CEP:SECURITY: denial-of-service bound on per-iteration work.
pub const kInferenceBufferClauses: usize = 64;

/// CEP:WHAT: Maximum literals of one buffered inference conclusion.
/// CEP:WHY: The generator's conclusion buffer holds kInferenceBufferClauses clauses inline; conclusions longer than this bound are structurally legal clauses (up to kMaxClauseLiterals) but pathological for search, and the generator counts and drops them loudly instead of sizing the whole buffer at the structural maximum (which would cost 256 KiB of stack).
/// CEP:STATUS: complete
/// CEP:FAILURE: the generator counts the dropped conclusion in its stats; the rules return InferenceError::ConclusionTooLong through the same path as the structural bound.
/// CEP:ASSUMES: 64 literals cover realistic resolvents and demodulants (premises are bounded by kMaxClauseLiterals but search conclusions are typically single digits).
/// CEP:COST: 8 bytes per literal slot, 32 KiB for the whole buffer at kInferenceBufferClauses.
/// CEP:EVIDENCE: unit/hot/given_clause_test.rs::{inference_deferral_resumes, per_clause_bound_enforced}.
/// CEP:SECURITY: denial-of-service bound on per-conclusion buffering.
pub const kInferenceClauseLiterals: usize = 64;

/// CEP:WHAT: Maximum distinct variables shared by the premises of one ATP inference (standardize-apart namespace bound).
/// CEP:WHY: The substitution engine namespaces variables by dense per-clause index below kMaxVariablesPerClause (Spec 02 section 5); two premises are renamed apart into one shared namespace at inference time, so vars(left) + vars(right) <= kMaxVariablesPerClause is a structural soundness precondition enforced loudly.
/// CEP:STATUS: complete
/// CEP:FAILURE: inference generation returns InferenceError::VariableBudgetExceeded when the premises cannot share a namespace; the pair is skipped and counted.
/// CEP:ASSUMES: real premise pairs satisfy the bound (clauses with more than kMaxVariablesPerClause/2 variables are pathological); premises are re-standardized to dense [0, n) namespaces at clause creation by the search loop.
/// CEP:COST: one addition and comparison per candidate pair.
/// CEP:EVIDENCE: unit/hot/inference_test.rs::{premises_renamed_apart, namespace_budget_enforced}.
/// CEP:SECURITY: soundness precondition, not a resource bound.
pub const kMaxInferenceVariables: u32 = kMaxVariablesPerClause;

/// CEP:WHAT: Capacity of the AVATAR component table (interned split components; design 12.2/12.3).
/// CEP:WHY: Components are hash-consed into an open-addressing table so identical components from different splits share one propositional assertion variable (Voronkov 2014, section on component sharing); a named power-of-two capacity keeps the table a fixed arena allocation with a loud ComponentTableFull error at the bound.
/// CEP:STATUS: complete
/// CEP:FAILURE: split registration returns AvatarError::ComponentTableFull past the capacity; the controller falls back to adding the unsplit clause (sound, documented degradation).
/// CEP:ASSUMES: 65_536 interned components cover realistic splits (each split needs at least two components of at least kAvatarMinComponentSize literals); the assertion-variable space is exactly this capacity (dense 0-based variables, Spec 12 section 4).
/// CEP:COST: 12 bytes per slot (open addressing over 8-byte canonical words plus the record array), about 3 MiB at the default capacity.
/// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, capacity_enforced}; security/phase4_bounds_test.rs::component_table_capacity_enforced.
/// CEP:SECURITY: memory-exhaustion bound on the abstraction state.
pub const kAvatarComponentCapacity: u32 = 65_536;

/// CEP:WHAT: Capacity of the AVATAR component table's canonical-word blob (design 12.2).
/// CEP:WHY: Each interned component stores its canonical literal words (one u32 per literal) in one shared bump region; 1_048_576 words (4 MiB) host the full 65_536-component capacity at an average of 16 literals per component, and the blob exhaustion is a loud WordBudgetExceeded that degrades to the unsplit clause (sound, Spec 12 section 7).
/// CEP:STATUS: complete
/// CEP:FAILURE: interning returns AvatarError::WordBudgetExceeded past the blob; the controller keeps the clause whole.
/// CEP:ASSUMES: the blob capacity >= record capacity (each record needs at least one word); enforced by static assertion.
/// CEP:COST: 4 MiB fixed arena allocation.
/// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::word_budget_enforced; security/phase4_bounds_test.rs::component_word_budget_enforced.
/// CEP:SECURITY: memory-exhaustion bound on the abstraction state.
pub const kAvatarComponentWordCapacity: u32 = 1_048_576;

/// CEP:WHAT: Node budget of one AVATAR splitter variable walk (design 12.3).
/// CEP:WHY: The variable-dependency walk is iterative but its cost is proportional to the atom's tree size; hash-consed DAGs can expand exponentially as trees, so the named budget turns adversarial terms into a sound Unsplittable degradation instead of unbounded work (CEP&CC 22.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: try_split returns Unsplittable when the budget is exhausted (never an error; the clause stays whole).
/// CEP:ASSUMES: 4_096 nodes cover realistic clause atoms (the index's kIndexTermCapacity uses the same scale for flat symbol sequences).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::walk_budget_degrades_to_unsplittable; security/phase4_bounds_test.rs::splitter_node_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on adversarial term sizes.
pub const kAvatarSplitNodeBudget: u32 = 4_096;

/// CEP:WHAT: Maximum conflict-driven re-solve rounds of the AVATAR abstraction loop (design 12.2 rule 4).
/// CEP:WHY: Each round adds one conflict clause and excludes at least the model that produced it (the model satisfies every assertion variable of the refutation's component ancestry, so the added clause falsifies it); the abstraction has finitely many models, but the named round budget converts pathological oscillation into a loud bounded give-up long before memory bounds fire.
/// CEP:STATUS: complete
/// CEP:FAILURE: saturate_with_avatar returns GaveUp(GaveUpReason::AvatarConflictBudget) past the budget.
/// CEP:ASSUMES: 4_096 rounds cover real refutations (each round requires a complete first-order refutation of the activated component set).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::conflict_round_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on the abstraction loop.
pub const kAvatarMaxConflictRounds: u32 = 4_096;

/// CEP:WHAT: Maximum model-rotation attempts at first-order saturation with waiting components (design 12.2 rule 3).
/// CEP:WHY: When the search saturates while some components wait, the controller tries to activate waiting components by solving the abstraction under each waiting assertion variable as an assumption (Spec 12 section 6); the named bound caps the per-saturation rotation sweep.
/// CEP:STATUS: complete
/// CEP:FAILURE: saturate_with_avatar returns GaveUp(GaveUpReason::AvatarModelBudget) past the budget instead of claiming Saturated without having tested every waiting component.
/// CEP:ASSUMES: 4_096 rotation attempts cover the waiting set at the component capacity (the sweep stops early once any assumption solve is satisfiable).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::model_rotation_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on the rotation sweep.
pub const kAvatarMaxModelRotations: u32 = 4_096;

/// CEP:WHAT: Capacity of the clause-id-to-offset side table of the clause store.
/// CEP:WHY: Proof reconstruction (design 18.2) and AVATAR ancestry collection (design 12.2 rule 4) walk the derivation DAG by parent clause id; the dense side array (index = id - kFirstClauseId) makes the id-to-record lookup O(1) without a per-record linked list; 4_194_304 slots x 4 bytes = 16 MiB, and the minimum 152-byte clause footprint means the 256 MiB arena can hold at most about 1.76M clauses, so the side table always outlives the arena (the bound is unreachable, documented in Spec 14 section 2).
/// CEP:STATUS: complete
/// CEP:FAILURE: clause creation returns ClauseError::ArenaFull before the side table can fill (the unreachability argument above); a defensive check still rejects the write loudly.
/// CEP:ASSUMES: clause ids stay dense and monotonic from kFirstClauseId (the store's contract).
/// CEP:COST: 16 MiB fixed arena allocation at store construction.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::{ids_are_monotonic, side_table_resolves_ids, side_table_capacity_enforced}; unit/cold/tstp_test.rs::proof_walk_resolves_parents.
/// CEP:SECURITY: bounds the side table under record floods.
pub const kClauseOffsetTableCapacity: u32 = 4_194_304;

/// CEP:WHAT: Ring capacity of one Chase-Lev work-stealing deque (design 19.3).
/// CEP:WHY: The deque is a fixed power-of-two ring masked by capacity-1 (Chase and Lev 2005, SPAA); the named capacity bounds the deferred-import backlog of one portfolio worker.
/// CEP:STATUS: complete
/// CEP:FAILURE: owner push returns DequeError::Full past the capacity (the owner then drops the oldest by popping first, a documented degradation).
/// CEP:ASSUMES: 8_192 pending imports per worker cover realistic share bursts; storage is supplied by the CEP-1 caller (the hot module is storage-agnostic).
/// CEP:COST: 8 bytes per slot, 64 KiB per deque at the default capacity.
/// CEP:EVIDENCE: unit/hot/chase_lev_test.rs::{owner_fifo_order, capacity_enforced, steal_returns_empty_when_idle}.
/// CEP:SECURITY: memory bound supplied by the caller.
pub const kChaseLevCapacity: u32 = 8_192;

/// CEP:WHAT: Ring capacity of the bounded MPMC clause-sharing pool (design 19.2).
/// CEP:WHY: The pool is a Vyukov-style bounded MPMC queue (one sequence number per cell); the named power-of-two capacity bounds shared-clause memory for the whole portfolio.
/// CEP:STATUS: complete
/// CEP:FAILURE: enqueue returns PoolError::Full past the capacity (exporters count the drop in stats; never silent).
/// CEP:ASSUMES: 1_024 in-flight shared clauses cover realistic exchange rates; storage is supplied by the CEP-1 caller.
/// CEP:COST: one kSharedClauseMaxWords-word record per cell, 2 MiB at the default capacity and word budget.
/// CEP:EVIDENCE: unit/hot/mpmc_pool_test.rs::{fifo_order_single_thread, exactly_once_delivery_under_threads, capacity_enforced}.
/// CEP:SECURITY: memory bound supplied by the caller.
pub const kMpmcPoolCapacity: u32 = 1_024;

/// CEP:WHAT: Word budget of one portable shared-clause record (design 19.2).
/// CEP:WHY: Shared clauses cross worker arenas by value, encoded as u64 words (header, per-literal headers, one word per term node - Spec 13 section 4); the named budget bounds the per-clause encoding cost, and clauses whose encoding exceeds it are not exported (counted loudly in the exporter's stats as a documented degradation next to the design 19.2 weight/LBD/rule filters).
/// CEP:STATUS: complete
/// CEP:FAILURE: the codec returns CodecError::TooLarge and the exporter skips the clause (counted).
/// CEP:ASSUMES: 256 words cover shareable clauses (weight below kSharedClauseMaxWeight = 100 plus literal headers; the bound is the ceiling of 1 + kMaxClauseLiterals/4 literals x average depth for weight-100 clauses).
/// CEP:COST: 2 KiB per record.
/// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, word_bound_enforced}.
/// CEP:SECURITY: denial-of-service bound on per-clause encoding.
pub const kSharedClauseMaxWords: usize = 256;

/// CEP:WHAT: Maximum worker count of one portfolio run (design 19.1).
/// CEP:WHY: The manager validates the worker count against a named ceiling before spawning threads (threads are created once at initialization, design 19.4); the default count stays kPortfolioThreadCount while the ceiling documents the hard bound.
/// CEP:STATUS: complete
/// CEP:FAILURE: portfolio construction returns PortfolioError::TooManyWorkers past the ceiling.
/// CEP:ASSUMES: 64 workers fit every supported host (kPortfolioThreadCount = 8 by default).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::worker_count_validated.
/// CEP:SECURITY: resource-exhaustion bound on thread creation.
pub const kPortfolioMaxWorkers: u32 = 64;

/// CEP:WHAT: Maximum clauses one portfolio worker exports per slice boundary.
/// CEP:WHY: Export scans the exporting worker's clause store by id range at slice boundaries (Spec 13 section 5); the per-slice export bound keeps one worker's scan-and-encode cost loud and bounded instead of proportional to unbounded slice growth.
/// CEP:STATUS: complete
/// CEP:FAILURE: the export stops early at the bound and resumes from the same id at the next boundary (progress is preserved; counted in stats).
/// CEP:ASSUMES: 256 exports per slice cover realistic derivation rates between import drains.
/// CEP:COST: one codec encode per exported clause.
/// CEP:EVIDENCE: unit/cold/portfolio_test.rs::exports_bounded_per_slice.
/// CEP:SECURITY: denial-of-service bound on export work.
pub const kPortfolioExportPerSlice: u32 = 256;

/// CEP:WHAT: Maximum induction scheme clauses added by one add_induction_schemes call.
/// CEP:WHY: The user-pinned budget of the automated-induction feature (revised build order Phase 4): every predicate of a declared datatype shape receives at most two scheme clauses (Spec 15 section 4), so the total scheme mass is bounded by a named constant, never by the predicate count of the input signature (CEP&CC 22.10, 39.1: no unbounded resource); predicates beyond the bound are skipped and counted, never silently dropped.
/// CEP:STATUS: complete
/// CEP:FAILURE: schemes stop at the bound; the stats report scanned predicates, added schemes, and skipped predicates (Law 4: bounded drops are counted).
/// CEP:ASSUMES: 128 scheme clauses (64 predicates x 2 clauses) cover realistic inductive-problem signatures.
/// CEP:COST: one counter check per scheme clause.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::attempts_budget_enforced; security/induction_conjecture_bounds_test.rs::induction_attempts_enforced.
/// CEP:SECURITY: denial-of-service bound on scheme mass.
pub const kMaxInductionAttempts: u32 = 128;

/// CEP:WHAT: Minimum scheme clauses one structural induction scheme contributes.
/// CEP:WHY: The clausal form of the induction axiom for one predicate is exactly two clauses (Spec 15 section 3); the constant names the granularity so the attempts budget arithmetic (kMaxInductionAttempts >= 2) is explicit rather than a bare literal.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: Spec 15 section 3 fixes the two-clause shape.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
/// CEP:SECURITY: none.
pub const kInductionSchemeClauses: u32 = 2;

/// CEP:WHAT: Given-clause iterations between two in-loop conjecture harvests.
/// CEP:WHY: Harvesting derived unit equations (Spec 16) runs on a fixed schedule so the search stays deterministic (CEP&CC 38.10): every kConjectureHarvestInterval loop iterations, if the option is enabled and the harvest budget remains, the loop pauses generation for one bounded harvest pass.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; the schedule is advisory state, not a failure source.
/// CEP:ASSUMES: 512 given-clause iterations between harvests keep the speculative share of the loop small.
/// CEP:COST: one modulo per iteration (folded into the existing budget-check interval discipline).
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::harvest_schedule_fires.
/// CEP:SECURITY: schedule bound for speculative work.
pub const kConjectureHarvestInterval: u64 = 512;

/// CEP:WHAT: Maximum in-loop conjecture harvests per saturate call.
/// CEP:WHY: Bounds the total speculative share of one search: with kMaxConjectureCandidates candidates per harvest and kConjectureRefuteInferences per refutation run, the worst-case speculative inference count is (kMaxConjectureHarvests + 1) x kMaxConjectureCandidates x kConjectureRefuteInferences (the +1 covers the driver-invoked pre-search harvest), asserted below to stay within kMaxInferences (CEP&CC 23: the cost is measurable and named).
/// CEP:STATUS: complete
/// CEP:FAILURE: harvests stop at the bound; the stats report harvests run, candidates tried, and lemmas imported (Law 4).
/// CEP:ASSUMES: 8 in-loop harvests per search balance speculation against search progress.
/// CEP:COST: one counter check per harvest.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::harvest_budget_enforced.
/// CEP:SECURITY: denial-of-service bound on speculative work.
pub const kMaxConjectureHarvests: u32 = 8;

/// CEP:WHAT: Maximum conjecture candidates considered by one harvest pass.
/// CEP:WHY: Each candidate costs one bounded mini-refutation (Spec 16 section 5), so the per-harvest candidate bound times the refutation budget is the per-harvest work bound; candidates are enumerated in clause-id order with templates in fixed order (T1 symmetry, T2 transitivity, T3 constructor instances), so the prefix cut at the bound is deterministic (CEP&CC 38.10).
/// CEP:STATUS: complete
/// CEP:FAILURE: candidates beyond the bound are skipped and counted, never silently dropped.
/// CEP:ASSUMES: 16 candidates per harvest cover the recent-derivation window in practice.
/// CEP:COST: one counter check per candidate.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
/// CEP:SECURITY: denial-of-service bound.
pub const kMaxConjectureCandidates: u32 = 16;

/// CEP:WHAT: Most recent derived unit equations scanned by the transitivity template.
/// CEP:WHY: T2 pairs a fresh unit equation with an older one whose left or right side matches by term identity (hash-consed pointer equality, Spec 01 section 3); scanning the most recent kConjectureTransitivityWindow units in descending id order bounds the pairing work to O(window) per fresh unit and keeps the enumeration deterministic.
/// CEP:STATUS: complete
/// CEP:FAILURE: pairs beyond the window are not considered; the template is not a completeness argument (Spec 16 section 6).
/// CEP:ASSUMES: 64 recent units cover the working set of an active derivation front.
/// CEP:COST: O(window) term-identity checks per fresh unit.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::transitivity_pairs_recent_units.
/// CEP:SECURITY: work bound per template.
pub const kConjectureTransitivityWindow: u32 = 64;

/// CEP:WHAT: Maximum distinct variables of a unit equation eligible for constructor instantiation (T3).
/// CEP:WHY: The template instantiates every variable of the unit at the canonical base pattern (all zero) and the canonical step pattern (all successor of zero) of the declared datatype (Spec 16 section 4), so the candidate count per unit is exactly two regardless of variable count, but the instantiation cost grows with the variable count and is bounded by this named cutoff.
/// CEP:STATUS: complete
/// CEP:FAILURE: units with more variables are skipped by T3 and counted; T1 and T2 still apply.
/// CEP:ASSUMES: units relevant to induction base and step cases carry at most two variables.
/// CEP:COST: one variable count per unit.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
/// CEP:SECURITY: work bound per template.
pub const kConjectureInstanceVariables: u32 = 2;

/// CEP:WHAT: Passive-set capacity of one conjecture mini-refutation search space.
/// CEP:WHY: The mini search space (Spec 16 section 5) is a full SearchSpace with injectable small capacities so one refutation attempt is memory-bounded by named constants (CEP&CC 39.1) instead of inheriting the production capacities.
/// CEP:STATUS: complete
/// CEP:FAILURE: the attempt is discarded (the candidate never becomes a lemma); the main search is unaffected.
/// CEP:ASSUMES: 1024 passive slots exceed the refutation depth of realistic unit-equation lemmas.
/// CEP:COST: passive slots live in the shared arena; 1024 slots are bounded by the arena budget.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjecturePassiveCapacity: u32 = 1024;

/// CEP:WHAT: Active-set capacity of one conjecture mini-refutation search space.
/// CEP:WHY: Companion of kConjecturePassiveCapacity (the active set of the mini space).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(MemoryBudget); the candidate is discarded.
/// CEP:ASSUMES: 512 active slots exceed the premise count of realistic unit-equation refutations.
/// CEP:COST: active slots live in the shared arena.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_active_capacity_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjectureActiveCapacity: u32 = 512;

/// CEP:WHAT: Discrimination-tree node budget of one conjecture mini-refutation search space.
/// CEP:WHY: Companion of kConjecturePassiveCapacity (the indexing trees of the mini space).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(MemoryBudget); the candidate is discarded.
/// CEP:ASSUMES: 4096 tree nodes cover the mini space's active-set indexing.
/// CEP:COST: tree nodes live in the shared arena.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_tree_budget_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjectureTreeNodes: u32 = 4096;

/// CEP:WHAT: Discrimination-tree entry budget of one conjecture mini-refutation search space.
/// CEP:WHY: Companion of kConjecturePassiveCapacity (the indexing entries of the mini space).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(MemoryBudget); the candidate is discarded.
/// CEP:ASSUMES: 4096 entries cover the mini space's active-set indexing.
/// CEP:COST: entries live in the shared arena.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_tree_budget_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjectureTreeEntries: u32 = 4096;

/// CEP:WHAT: Feature-vector pool words of one conjecture mini-refutation search space.
/// CEP:WHY: Companion of kConjecturePassiveCapacity (the subsumption filter pool of the mini space).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(MemoryBudget); the candidate is discarded.
/// CEP:ASSUMES: 32768 words cover the mini space's feature vectors.
/// CEP:COST: pool words live in the shared arena.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_tree_budget_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjecturePoolWords: u32 = 32_768;

/// CEP:WHAT: Clause-id offset-table capacity of one conjecture mini-refutation search space.
/// CEP:WHY: Companion of kConjecturePassiveCapacity (the id side table that proof walks need; the import path resolves mini ids through it).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(MemoryBudget); the candidate is discarded.
/// CEP:ASSUMES: 4096 entries cover the mini space's clause count plus the imported prefix.
/// CEP:COST: table slots live in the shared arena.
/// CEP:EVIDENCE: security/induction_conjecture_bounds_test.rs::mini_id_table_discards.
/// CEP:SECURITY: memory bound per refutation attempt.
pub const kConjectureIdOffsets: u32 = 4096;

/// CEP:WHAT: Maximum axiom clauses collected for one conjecture mini-refutation premise set.
/// CEP:WHY: The premise enumeration (Spec 16 section 5, Task 26 sev-0 repair) fills a fixed array (no allocation in the no_std hot crate) with the rule-identified axiom ids ascending below the proof watermark; the prefix truncation at this bound is SOUND (a lemma proved from an axiom subset is proved from the full set) and deterministic, and the bound is asserted to leave the mini passive set room for the premises plus the negation premise.
/// CEP:STATUS: complete
/// CEP:FAILURE: axioms beyond the bound are not fed to the mini run (the prefix is used; the truncation is the documented bound, never an error).
/// CEP:ASSUMES: the value plus one negation premise fits the mini passive capacity.
/// CEP:COST: kConjectureMaxAxioms x 8 bytes on the stack per candidate.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::two_harvests_stay_sound; security/induction_conjecture_bounds_test.rs::mini_passive_capacity_discards.
/// CEP:SECURITY: memory and work bound on the premise set.
pub const kConjectureMaxAxioms: usize = 1023;

/// CEP:WHAT: Inference budget of one conjecture mini-refutation run.
/// CEP:WHY: The speculative work per candidate is bounded by a named inference budget (CEP&CC 23: measurable cost; 22.10: bounded work): the mini saturate runs with this budget and any GaveUp outcome discards the candidate without touching the main search (Spec 16 section 5).
/// CEP:STATUS: complete
/// CEP:FAILURE: the mini run returns GaveUp(InferenceBudget); the candidate is discarded.
/// CEP:ASSUMES: 4096 inferences refute the negation of realistic unit-equation lemmas or give up honestly.
/// CEP:COST: bounded by the constant; the total speculative bound is asserted below.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::refute_budget_discards_unprovable.
/// CEP:SECURITY: denial-of-service bound per candidate.
pub const kConjectureRefuteInferences: u64 = 4096;

/// CEP:WHAT: Maximum term nodes visited by one induction input-signature scan.
/// CEP:WHY: The induction module walks every input clause's atoms once to collect occurring predicate symbols and to prove the declaration's skolem constant absent (Spec 15 section 2); the walk is structurally bounded (clauses x literals x term weight), and this named budget is the loud defense-in-depth ceiling (CEP&CC 22.10) - exceeding it rejects the declaration instead of trusting the structural argument.
/// CEP:STATUS: complete
/// CEP:FAILURE: InductionError::ScanBudgetExceeded; no schemes are added.
/// CEP:ASSUMES: 4M nodes exceed every legal input (the arena bounds total term records far below this); the budget exists to fail loudly on structural-bounds erosion.
/// CEP:COST: one counter per visited node.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::scan_budget_rejects_runaway_input.
/// CEP:SECURITY: denial-of-service bound on the validation walk.
pub const kInductionScanNodeBudget: u32 = 4_194_304;

/// CEP:WHAT: Maximum distinct occurring unary predicates collected by one induction scan.
/// CEP:WHY: The scan's predicate list is a fixed array (no allocation in the no_std hot crate), so the collection bound is a named constant; predicates beyond the bound are skipped and counted exactly like attempts-budget skips (Law 4), and the array is sized so the attempts budget always binds first for structural-only declarations (asserted below).
/// CEP:STATUS: complete
/// CEP:FAILURE: predicates beyond the bound are skipped and counted in stats.predicates_skipped.
/// CEP:ASSUMES: 256 distinct unary predicates exceed every realistic inductive problem signature.
/// CEP:COST: 1 KiB stack array (256 x 4 bytes).
/// CEP:EVIDENCE: unit/hot/induction_test.rs::attempts_budget_enforced.
/// CEP:SECURITY: memory bound on the scan's collection.
pub const kInductionMaxPredicates: usize = 256;

// CEP:WHAT: Static invariant checks for limit constants.
// CEP:WHY: CEP&CC Law 3 bans comment-only invariants; every cross-constant assumption above is enforced here at compile time.
// CEP:STATUS: complete
// CEP:FAILURE: Compilation fails if any invariant is violated.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/config/limits_test.rs repeats the same checks at runtime for defense in depth.
// CEP:SECURITY: integer-safety enforcement (CEP&CC 22.6).

/// CEP:WHAT: Maximum value of u16 as u32.
/// CEP:WHY: Named constant for the arity ceiling check (CEP&CC 11.3) that avoids the
/// always-true comparison lint while keeping the bound explicit.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: u16 is 16 bits on all supported targets (pinned by layout asserts).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/config/limits_test.rs.
/// CEP:SECURITY: none.
const kMaxU16Value: u32 = 65_535;

const _: () = {
    assert!(kArenaCapacityBytes < kInvalidClauseOffset);
    assert!(kArenaCapacityBytes < kInvalidTermOffset);
    assert!(kArenaCapacityBytes < kInvalidSubstitutionOffset);
    assert!(kMaxSymbolCount < kInvalidSymbolId);
    assert!(kFirstClauseId > kInvalidClauseId);
    assert!(kMaxClauses < u64::MAX - kFirstClauseId);
    assert!(kTermHashTableCapacity.count_ones() == 1);
    assert!(kTermHashTableLoadFactorPercent < 100);
    assert!(kInlineClauseLiterals <= kMaxClauseLiterals as usize);
    assert!(kMaxClauseLiterals as usize <= u16::MAX as usize);
    assert!(kMaxDerivationParents == 4);
    assert!(kMaxSatVariables <= u32::MAX / 2);
    assert!(kMaxSymbolArity as u32 <= kMaxU16Value);
    assert!(kMaxAlignment.count_ones() == 1);
    assert!(kMaxAlignment <= 64);
    assert!(kBudgetCheckInterval.count_ones() == 1);
    assert!(kPortfolioThreadCount >= 1);
    assert!(kAvatarMinComponentSize >= 1);
    assert!(kMaxArenaFragmentationRatioPercent < 100);
    assert!(kDefaultSymbolWeight >= 1);
    assert!(kKboVariableWeight >= 1);
    assert!(kSatWatchListCount == kMaxSatVariables * 2);
    assert!(kMaxTermDepth >= 1);
    assert!(kMaxTermWeight < u32::MAX);
    assert!(kMaxSubstitutionTrailDepth >= kMaxVariablesPerClause);
    assert!(kMaxUnificationDepth >= kMaxTermDepth as u32);
    assert!(kSatVsidsDecayPercent >= 1);
    assert!(kSatVsidsDecayPercent < 100);
    assert!(kSatVsidsActivityCeiling > 0.0);
    assert!(kSatVsidsActivityCeiling * kSatVsidsRescaleFactor <= 1.0);
    assert!(kSatRestartGeometricFactorPercent >= 100);
    assert!(kMaxOrderingSteps >= kMaxTermDepth as u32);
    assert!(kDiscriminationTreeNodes < kInvalidIndexNode);
    assert!(kDiscriminationTreeEntries < kInvalidIndexEntry);
    assert!(kIndexEqualitySymbol > kMaxSymbolCount);
    assert!(kIndexEqualitySymbol < kInvalidSymbolId);
    assert!(kIndexEqualitySymbol != kInvalidIndexNode);
    assert!(kSatMaxConflicts >= 1);
    assert!(kSatRegistryCapacity >= kSatMaxLearntClauses);
    assert!(kSatLearntReduceDivisor >= 2);
    assert!(kSatClauseActivityCeiling > 0.0);
    assert!(kSatClauseActivityCeiling * kSatClauseActivityRescaleFactor <= 1.0);
    assert!(kSatProofStepCapacity >= 1);
    assert!(kSatProofMapCapacity >= 1);
    assert!(kSatProofLiteralCapacity >= kSatProofStepCapacity);
    assert!(kFirstProofId >= 1);
    assert!(kFirstProofId != kInvalidProofId);
    assert!(kMaxAssumptions >= 1);
    assert!(kMaxAssumptions < kMaxSatVariables);
    assert!(kSatSubsumptionPairBudget >= 1);
    assert!(kSatVivifyCandidateLimit >= 1);
    assert!(kSatVivifyPropagationBudget >= 1);
    assert!(kDratRatScanLimit >= 1);
    assert!(kPassiveHeapCapacity >= 1);
    assert!(kActiveSetCapacity >= 1);
    assert!(kFeatureVectorPoolWords >= kFeatureVectorSlots * 2);
    assert!(kFeatureVectorSlots >= 1);
    assert!(kSelectionRatioScale >= 1);
    assert!(kInferenceBufferClauses >= 1);
    assert!(kInferenceClauseLiterals >= kInlineClauseLiterals);
    assert!(kInferenceClauseLiterals <= kMaxClauseLiterals as usize);
    assert!(kMaxInferenceVariables == kMaxVariablesPerClause);
    // Phase 4 (Integration) invariants: AVATAR, concurrency, proof reconstruction.
    assert!(kAvatarComponentCapacity.count_ones() == 1);
    assert!(kAvatarComponentCapacity <= kMaxSatVariables);
    assert!(kAvatarComponentWordCapacity >= kAvatarComponentCapacity);
    assert!(kAvatarSplitNodeBudget >= kMaxTermDepth as u32);
    assert!(kAvatarMaxConflictRounds >= 1);
    assert!(kAvatarMaxModelRotations >= 1);
    assert!(kClauseOffsetTableCapacity >= 1);
    assert!(kClauseOffsetTableCapacity < kMaxClauses as u32);
    assert!(kChaseLevCapacity.count_ones() == 1);
    assert!(kChaseLevCapacity >= 2);
    assert!(kMpmcPoolCapacity.count_ones() == 1);
    assert!(kMpmcPoolCapacity >= 2);
    assert!(kSharedClauseMaxWords >= 4);
    assert!(kPortfolioMaxWorkers >= kPortfolioThreadCount);
    assert!(kPortfolioExportPerSlice >= 1);
    assert!(kAvatarMinComponentSize <= kMaxClauseLiterals / 2);
    // Phase 4 (revised build order) invariants: automated induction, conjecture generation.
    assert!(kMaxInductionAttempts >= kInductionSchemeClauses);
    assert!(kInductionSchemeClauses == 2);
    assert!(kConjectureHarvestInterval >= 1);
    assert!(kMaxConjectureHarvests >= 1);
    assert!(kMaxConjectureCandidates >= 1);
    assert!(kConjectureTransitivityWindow >= 1);
    assert!(kConjectureInstanceVariables >= 1);
    assert!(kConjectureInstanceVariables <= kMaxVariablesPerClause);
    assert!(kConjecturePassiveCapacity >= 1);
    assert!(kConjectureActiveCapacity >= 1);
    assert!(kConjectureTreeNodes >= 1);
    assert!(kConjectureTreeEntries >= 1);
    assert!(kConjecturePoolWords >= 1);
    assert!(kConjectureIdOffsets >= 1);
    assert!(kConjectureRefuteInferences >= 1);
    assert!(kConjectureMaxAxioms >= 1);
    assert!(kConjectureMaxAxioms < kConjecturePassiveCapacity as usize);
    assert!(kInductionScanNodeBudget >= 1);
    assert!(
        kInductionScanNodeBudget as u64
            <= kMaxClauses * kMaxClauseLiterals as u64 * kMaxTermWeight as u64
    );
    assert!(
        kInductionMaxPredicates * kInductionSchemeClauses as usize
            >= kMaxInductionAttempts as usize
    );
    // The total speculative inference work (in-loop harvests plus the one
    // driver-invoked pre-search harvest) never exceeds the main budget.
    assert!(
        (kMaxConjectureHarvests as u64 + 1)
            * kMaxConjectureCandidates as u64
            * kConjectureRefuteInferences
            <= kMaxInferences
    );
};
