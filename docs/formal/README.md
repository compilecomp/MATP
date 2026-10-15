# Formal Specifications Index

These documents are normative for MAPT (design section 23): every `CEP:HPC-PASS-LEGALITY` comment must cite a specific definition or theorem here, and every hot component must be justified by one of these documents or be quarantined (design section 23.3).

| # | Document | Scope | Status |
|---|---|---|---|
| 01 | `01_fol_syntax_semantics.md` | Signature, terms, hash-consing canonicality, literals, clauses, canonical order, IR contract | Complete (Phase 1 scope) |
| 02 | `02_substitution_unification.md` | Substitution algebra, application, trail discipline, MGU and matching definitions and algorithms | Complete (algorithms delivered in Phase 2) |
| 03 | `03_term_orderings.md` | Term orderings: precedence, KBO, LPO, theorems and measurement | Complete (Phase 2 scope; ticket CEP-1013 closed) |
| 04 | `04_term_indexing.md` | Discrimination tree: flat sequences, matching rule, retrieval theorems | Complete (Phase 2 scope) |
| 05 | `05_sat_cdcl_foundations.md` | SAT literals, clauses, trails, watched literals, BCP soundness and completeness; section 6 amendment: deleted-record lazy unlinking (Phase 3) | Complete (Phase 1 scope + Phase 3 amendment) |
| 06 | `06_cdcl_conflict_analysis.md` | Implication graphs, first-UIP analysis, learning, minimization, backjumping, VSIDS, phase saving, restarts; section 9: clause registry and learnt-clause deletion (Phase 3) | Complete (Phase 2 scope + Phase 3 amendment) |
| 07 | `07_inference_rules.md` | The inference rules: renaming theorems, eligibility, resolution, factoring, equality factoring, superposition, equality resolution, demodulation, subsumption, tautology, duplicate removal | Complete (Phase 3 scope) |
| 08 | `08_given_clause_loop.md` | The given-clause loop, clause database, selection fairness, feature-vector filter, generation strategy, loop contract | Complete (Phase 3 scope) |
| 09 | `09_sat_preprocessing.md` | SAT preprocessing: tautology, duplicates, subsumption, strengthening, vivification; preservation theorems; proof-trace order | Complete (Phase 3 scope) |
| 10 | `10_incremental_solving.md` | Assumption solving, root levels, final analysis, failed cores, incremental hygiene | Complete (Phase 3 scope) |
| 11 | `11_drat_proof_logging.md` | DRAT recording, step kinds, RUP/RAT semantics, text format, internal checker | Complete (Phase 3 scope) |
| 12 | `12_avatar_splitting.md` | AVATAR: splitting lemma, component interning, monotone-activation protocol, conflict soundness, assertability lemma, saturation terminal, degradation policy | Complete (Phase 4 scope) |
| 13 | `13_portfolio_concurrency.md` | Bounded MPMC pool, Chase-Lev deque, portable clause codec, worker protocol, import soundness, first-to-finish linearization | Complete (Phase 4 scope) |
| 14 | `14_unified_proof_reconstruction.md` | Derivation walk, reachability pruning, TSTP grammar subset, AVATAR presentation, replay checker | Complete (Phase 4 scope; demodulation full replay deferred - ticket CEP-1036) |
| 15+ | reserved | DPLL(T), theory reasoning, benchmark suite — Phases 5-6 | Not started |

Numbering follows the design document's plan; gaps are reserved for their future owners as listed in `docs/tickets.md` (15 onward: DPLL(T) integration, theory reasoning, benchmark suite).
