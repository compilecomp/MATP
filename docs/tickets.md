# MAPT Ticket Index

Work items referenced by CEP:TODO, CEP:OPTNOTE, and CEP:ASSUMES fields across the codebase. Anonymous work markers are banned (CEP&CC 10.10); every deferral has an owner and a ticket here.

| Ticket | Owner | Component | Summary | Phase |
|---|---|---|---|---|
| CEP-1002 | mapt-team | hot/unification | Unification and matching algorithms over the Phase 1 substitution engine, plus the explicit compose operation (design 5.5 "Composition: Explicit. Allocates into the arena"; Spec 02 section 3 fixes the semantics); revisit the cross-clause variable bound | 2 |
| CEP-1003 | mapt-team | hot/sat | Learnt-clause deletion policy (S25/S26): LBD-first, age, activity | 2 |
| CEP-1004 | mapt-team | hot/sat | Luby restart scheduling (S16) on top of kSatRestartBaseInterval | 2 |
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
| CEP-1019 | mapt-team | benches | Cross-host benchmark regression tier: dedicated measurement host or per-op reference normalization so the fine-grained 13.4 gate can run on shared CI runners without flaking (fleet medians for throughput-bound micro-ops swing up to 2.3x; observed runs 37963490245 vs 37964196220) | 2 |
