# Formal Specifications Index

These documents are normative for MAPT (design section 23): every `CEP:HPC-PASS-LEGALITY` comment must cite a specific definition or theorem here, and every hot component must be justified by one of these documents or be quarantined (design section 23.3).

| # | Document | Scope | Status |
|---|---|---|---|
| 01 | `01_fol_syntax_semantics.md` | Signature, terms, hash-consing canonicality, literals, clauses, canonical order, IR contract | Complete (Phase 1 scope) |
| 02 | `02_substitution_unification.md` | Substitution algebra, application, trail discipline, MGU and matching definitions (Phase 2 fixed-point) | Complete (Phase 1 scope; algorithm in Phase 2) |
| 03 | reserved | Term orderings (KBO, LPO) — Phase 2 | Not started (ticket CEP-1013) |
| 04 | reserved | Term and clause indexing (discrimination trees, feature vectors) — Phase 2 | Not started |
| 05 | `05_sat_cdcl_foundations.md` | SAT literals, clauses, trails, watched literals, BCP soundness and completeness | Complete (Phase 1 scope) |
| 06+ | reserved | Given-clause loop, superposition legality, CDCL conflict analysis, AVATAR, DPLL(T), benchmark suite — Phases 2-6 | Not started |

Numbering follows the design document's plan; gaps are reserved for their future owners as listed in `docs/tickets.md`.
