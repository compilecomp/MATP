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
/// CEP:WHY: The reciprocal scale of the ceiling restores scores to a small range while preserving their order exactly (multiplication by a positive constant is order-preserving on non-negative finite doubles).
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
};
