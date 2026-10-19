# MAPT Ticket Index

Work items referenced by CEP:TODO, CEP:OPTNOTE, and CEP:ASSUMES fields across the codebase. Anonymous work markers are banned (CEP&CC 10.10); every deferral has an owner and a ticket here.

| Ticket | Owner | Component | Summary | Phase |
|---|---|---|---|---|
| CEP-1002 | mapt-team | hot/unification | CLOSED in Phase 2: unification, matching (with the application witness), and composition delivered in hot/unification/unify.rs against Spec 02; the cross-clause variable bound stays at kMaxVariablesPerClause (renamed-apart discipline is the callers' contract, Spec 02 section 5) | 2 |
| CEP-1003 | mapt-team | hot/sat | CLOSED in Phase 3: registry (enumerable offsets, tombstones, activity with rescale) and the deletion policy delivered in hot/sat/registry.rs per Spec 06 section 9 (LBD asc, age desc; the activity key is vacuous in the strict order, documented in the comparator); S27 full compaction stays open under CEP-1007 | 3 |
| CEP-1004 | mapt-team | hot/sat | CLOSED in Phase 2: Luby and geometric restart scheduling delivered in hot/sat/restart.rs with the design 11.5 sequence pinned by unit tests | 2 |
| CEP-1013 | mapt-team | hot/ordering | CLOSED in Phase 2: KBO and LPO delivered in hot/ordering with the ID-order and validated-rank precedence tables; Spec 03 fixes the theorems | 2 |
| CEP-1005 | mapt-team | search | CLOSED in Phase 3: the injected should-stop callback is checked every kBudgetCheckInterval iterations in hot/search/given_clause.rs::saturate (hot stays clock-free; the CEP-1 driver supplies wall time; tests inject deterministic predicates) | 3 |
| CEP-1006 | mapt-team | cold/parsing | TPTP/SMT-LIB/DIMACS parsers with the full §6.3 bound set | 3 |
| CEP-1007 | mapt-team | hot/memory | Arena compaction (cold) above kMaxArenaFragmentationRatioPercent | 3 |
| CEP-1008 | mapt-team | concurrency | CLOSED in Phase 4: portfolio manager (scoped threads, wall-clock slices, first-to-finish, graceful shutdown), bounded MPMC sharing pool, Chase-Lev work-stealing deques (pool-spill frames), portable clause codec, and the CI tsan job delivered per Spec 13; thread pinning and NUMA-aware placement deferred to CEP-1037 | 4 |
| CEP-1009 | mapt-team | hot/ir | Cached-slice term reads to remove per-read bounds checks in the probe path; measure first | 2 |
| CEP-1010 | mapt-team | hot/ir | Hash-word caching in term records to shorten probe misses; measure first | 2 |
| CEP-1011 | mapt-team | hot/ir | CLOSED in Phase 4: literal avatar_component_tag accessors (mask 0x07, theory bit preserved) set on every materialized component clause; the authoritative identity is the clause record's split_level (u16) per Spec 12 section 4 | 4 |
| CEP-1012 | mapt-team | hot/ir | Theory-laden literal flags (design 5.2) | 5 |
| CEP-1013 | mapt-team | hot/ordering | KBO and LPO with cached comparison (design 8.3); formal spec 03 | 2 |
| CEP-1014 | mapt-team | hot/ir | Merge-sort path for overflow-clause canonicalization if profiling demands | 2 |
| CEP-1015 | mapt-team | hot/sat | Batched literal-read API for the BCP scan; measure first | 2 |
| CEP-1016 | mapt-team | hot/sat | Struct-of-arrays value+reason row to shorten BCP value evaluation; measure first | 2 |
| CEP-1017 | mapt-team | hot/sat | Blocking-literal cache in watch lists (MiniSat blocker); measure first | 2 |
| CEP-1018 | mapt-team | target | CI target matrix execution on arm64 and riscv64 runners | CI |
| CEP-1024 | mapt-team | hot/unification | Cheaper match witness: a variable-disjointness precondition (per-clause namespace map) to replace the O(|p|) application pass on success; measure first | 3 |
| CEP-1025 | mapt-team | hot/ordering | Cached variable-occurrence counts (or bitset signatures) on term headers to shorten the KBO equal-weight path; measure first | 3 |
| CEP-1026 | mapt-team | hot/ordering | LPO comparison cache keyed by term-offset pairs for saturation workloads; measure first | 3 |
| CEP-1027 | mapt-team | hot/index | Indexed candidate retrieval for the loop's scans: the flat-sequence tree cannot see cross-length unifications (p(x) invisible to the query p(f(a))), so generation and subsumption scan the active array with head prefilters (Spec 08 section 5); restore indexed retrieval via hash-bucketed child sets, arity-aware flattening, or subtree iterators; also covers the superposition-from subterm scan | 3 |
| CEP-1028 | mapt-team | hot/index | CLOSED in Phase 3: the feature-vector filter (symbol-count dominance + literal count, sound per Spec 08 section 3) delivered in hot/index/feature_vector.rs and wired into forward/backward subsumption | 3 |
| CEP-1029 | mapt-team | hot/index | Remaining index types of design 9.1 (substitution tree, perfect hash, inverted) and the index multiplexer of design 9.4; narrowed in Phase 3: the atom and rule trees are maintained and queried by tests, but the loop's candidate path scans (see CEP-1027), so these types have no consumer until indexed retrieval lands | 3 |
| CEP-1030 | mapt-team | hot/sat | Two-level bucket heap for VSIDS (E-prover style) to cut sift costs | 3 |
| CEP-1031 | mapt-team | hot/sat | Batched literal reads (CEP-1015) and a watched-binaries fast path inside conflict analysis | 3 |
| CEP-1032 | mapt-team | hot/sat | Solver-loop micro-optimizations: batched trail reads and copy-free learnt handoff; measure first | 3 |
| CEP-1033 | mapt-team | hot/ordering | Higher-order orderings (Application/Lambda heads) for the Phase 5 fragment | 5 |
| CEP-1034 | mapt-team | hot/inference | Subsumption resolution (Riazanov 2003) and condensation (design 10.1 rows deferred with Phase 3 scope: the build order names superposition + resolution + factoring); both strengthen clauses beyond demodulation | 4 |
| CEP-1035 | mapt-team | search | Conjecture-distance and set-of-support selection strategies (design 15.2 rows 2 and 5) and the config/strategy.rs module (design 15.2); the three deterministic strategies (ratio, weight, age) are delivered | 4 |
| CEP-1036 | mapt-team | hot/ir | Record the demodulating rule's clause id in DerivationStep parents[1] so the TSTP replay checker can fully replay demodulation steps (the Phase 4 structural variant check is the interim, Spec 14 section 6) | 4 |
| CEP-1037 | mapt-team | target | Thread pinning and NUMA-aware arena placement (design 19.1/19.8) behind a target/ abstraction; blocked on the OS-affinity bindings decision (unsafe libc is deferred, not half-implemented) | 5 |
| CEP-1038 | mapt-team | cold/portfolio | Worker-arena pooling across portfolio runs (the Phase 4 workers leak their arenas until process exit - the documented fixture discipline) | 4 |
| CEP-1039 | mapt-team | hot/avatar | Derived-clause splitting (Phase 4 splits inputs only, Spec 12 section 7) and full-record deferred-import frames beyond the pool-spill protocol | 5 |
| CEP-1036 | mapt-team | cold | LRAT text emission (hint-annotated additions; the recorder already carries stable ids, but conflict analysis does not record the hint chain - co-design with the analyzer when an external LRAT consumer exists) | 4 |
| CEP-1019 | mapt-team | benches | Cross-host benchmark regression tier: dedicated measurement host or per-op reference normalization so the fine-grained 13.4 gate can run on shared CI runners without flaking (fleet medians for throughput-bound micro-ops swing up to 2.3x; observed runs 37963490245 vs 37964196220) | 2 |
| CEP-1050 | mapt-team | hot/search | Generator bound-error drop policy: a conclusion whose materialization exceeds kMaxTermDepth/kMaxTermWeight currently terminates the whole search with Err (the documented abort discipline) after the honest-error fix (Spec 17 section 5, map_term_error); decide and implement drop-and-count semantics (trail unwind to the attempt depth + stats.dropped) so deep/wide-term searches end in GaveUp rather than Error; needs its own trail-safety review of every rule Err path | 2 |
| CEP-1051 | mapt-team | cold/parsing | TPTP/TFF inductive-datatype declaration mapping to InductionDeclaration (zero/succ by declaration, not convention) once the input layer exists; also the TFF-sorted list/tree constructor shapes (untyped detection is ambiguous for binary constructors, Spec 15 section 2's rationale) | 5 |
| CEP-1052 | mapt-team | hot/conjecture | Additional bounded templates if the CASC-shaped evaluation justifies them: residue generalization from failed induction branches, lemma chaining beyond the T2 window, and per-predicate scheme targeting; every template must keep the Spec 16 section 2 soundness position (the filter is the only soundness mechanism) | 4 |
| CEP-1053 | mapt-team | hot/induction | Goal-directed multi-literal induction lifting (the Wand-Khasidashvili IH-as-literals scheme for conjectures that are not single-predicate goals); requires extending the Spec 15 clausification with the literal-wise distribution and its soundness theorem | 4 |
