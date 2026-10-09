# MAPT Ticket Index

Work items referenced by CEP:TODO, CEP:OPTNOTE, and CEP:ASSUMES fields across the codebase. Anonymous work markers are banned (CEP&CC 10.10); every deferral has an owner and a ticket here.

| Ticket | Owner | Component | Summary | Phase |
|---|---|---|---|---|
| CEP-1002 | mapt-team | hot/unification | CLOSED in Phase 2: unification, matching (with the application witness), and composition delivered in hot/unification/unify.rs against Spec 02; the cross-clause variable bound stays at kMaxVariablesPerClause (renamed-apart discipline is the callers' contract, Spec 02 section 5) | 2 |
| CEP-1003 | mapt-team | hot/sat | Learnt-clause deletion policy (S25/S26): LBD-first, age, activity; needs a clause registry (enumerable offsets) and tombstone unlinking in the bump arena, co-designed with S27 compaction | 3 (moved from 2: design 26 Phase 2 lists only conflict analysis, learning, backjump) |
| CEP-1004 | mapt-team | hot/sat | CLOSED in Phase 2: Luby and geometric restart scheduling delivered in hot/sat/restart.rs with the design 11.5 sequence pinned by unit tests | 2 |
| CEP-1013 | mapt-team | hot/ordering | CLOSED in Phase 2: KBO and LPO delivered in hot/ordering with the ID-order and validated-rank precedence tables; Spec 03 fixes the theorems | 2 |
| CEP-1005 | mapt-team | search | Time-budget enforcement every kBudgetCheckInterval iterations | 3 |
| CEP-1006 | mapt-team | cold/parsing | TPTP/SMT-LIB/DIMACS parsers with the full §6.3 bound set | 3 |
| CEP-1007 | mapt-team | hot/memory | Arena compaction (cold) above kMaxArenaFragmentationRatioPercent | 3 |
| CEP-1008 | mapt-team | concurrency | Portfolio manager, clause sharing pool, work stealing (design 19) | 4 |
| CEP-1009 | mapt-team | hot/ir | Cached-slice term reads to remove per-read bounds checks in the probe path; measure first | 2 |
| CEP-1010 | mapt-team | hot/ir | Hash-word caching in term records to shorten probe misses; measure first | 2 |
| CEP-1011 | mapt-team | hot/ir | AVATAR component tags on literals (design 5.2) | 4 |
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
| CEP-1027 | mapt-team | hot/index | Hash-bucketed child sets for wide discrimination-tree nodes, plus prefix (subterm) retrieval for subsumption on subterms | 3 |
| CEP-1028 | mapt-team | hot/index | Feature-vector filter (design 9.3) in front of the discrimination tree | 3 |
| CEP-1029 | mapt-team | hot/index | Remaining index types of design 9.1 (substitution tree, perfect hash, inverted) and the index multiplexer of design 9.4 | 3 |
| CEP-1030 | mapt-team | hot/sat | Two-level bucket heap for VSIDS (E-prover style) to cut sift costs | 3 |
| CEP-1031 | mapt-team | hot/sat | Batched literal reads (CEP-1015) and a watched-binaries fast path inside conflict analysis | 3 |
| CEP-1032 | mapt-team | hot/sat | Solver-loop micro-optimizations: batched trail reads and copy-free learnt handoff; measure first | 3 |
| CEP-1033 | mapt-team | hot/ordering | Higher-order orderings (Application/Lambda heads) for the Phase 5 fragment | 5 |
| CEP-1019 | mapt-team | benches | Cross-host benchmark regression tier: dedicated measurement host or per-op reference normalization so the fine-grained 13.4 gate can run on shared CI runners without flaking (fleet medians for throughput-bound micro-ops swing up to 2.3x; observed runs 37963490245 vs 37964196220) | 2 |
