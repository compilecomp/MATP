# Formal Specifications Index

These documents are normative for MAPT (design section 23): every `CEP:HPC-PASS-LEGALITY` comment must cite a specific definition or theorem here, and every hot component must be justified by one of these documents or be quarantined (design section 23.3).

| # | Document | Scope | Status |
|---|---|---|---|
| 01 | `01_fol_syntax_semantics.md` | Signature, terms, hash-consing canonicality, literals, clauses, canonical order, IR contract | Complete (Phase 1 scope) |
| 02 | `02_substitution_unification.md` | Substitution algebra, application, trail discipline, MGU and matching definitions and algorithms | Complete (algorithms delivered in Phase 2) |
| 03 | `03_term_orderings.md` | Term orderings: precedence, KBO, LPO, theorems and measurement | Complete (Phase 2 scope; ticket CEP-1013 closed) |
| 04 | `04_term_indexing.md` | Discrimination tree: flat sequences, matching rule, retrieval theorems | Complete (Phase 2 scope) |
| 05 | `05_sat_cdcl_foundations.md` | SAT literals, clauses, trails, watched literals, BCP soundness and completeness | Complete (Phase 1 scope) |
| 06 | `06_cdcl_conflict_analysis.md` | Implication graphs, first-UIP analysis, learning, minimization, backjumping, VSIDS, phase saving, restarts | Complete (Phase 2 scope) |
| 07+ | reserved | Given-clause loop, superposition legality, SAT preprocessing, AVATAR, DPLL(T), benchmark suite — Phases 3-6 | Not started |

Numbering follows the design document's plan; gaps are reserved for their future owners as listed in `docs/tickets.md`.
