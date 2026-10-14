# Formal Specification 10: Incremental Solving with Assumptions and Failed Cores

Version: 0.1
Status: complete for the Phase 3 scope (design 11.1 S38/S39/S40, 12; design 26 build order "SAT: incremental solving + assumptions")
Role: normative reference for `CdclSolver::solve_with_assumptions` and `ConflictAnalyzer::analyze_final` (`hot/sat/solver.rs`, `hot/sat/cdcl.rs`); cited by their `CEP:HPC-PASS-LEGALITY` fields.
References: design 11.1 S38-S40, 12.2; Eén & Sörensson 2003 (MiniSat assumptions); Marques-Silva & Sakallah 1996; Formal Spec 06 (CDCL).

## 1. The interface

`solve_with_assumptions(A)` returns Satisfiable (the formula ∧ A is satisfiable; the model extends A), Unsatisfiable (the formula alone is refuted), UnsatUnderAssumptions (the formula ∧ A is unsatisfiable; a failed core is extractable), or Indeterminate (a budget).

## 2. Assumption semantics

Assumption literals are hypotheses of the call, not formula clauses: each is pushed as its own decision level (levels 1..=root where root = the number of pushed assumptions; satisfied duplicates skip without new levels). The proof trace records each as a hypothesis unit (AssumptionAdd) and removes it at the call's end (AssumptionDelete) — plain DRAT has no hypothesis syntax, so the units render as ordinary unit clauses; the checker skips justification for hypothesis steps (Spec 11 section 3).

## 3. The search under assumptions

The CDCL loop runs with root as the backjump floor: backjumps clamp to max(target, root) and restarts return to root. Conflicts at levels above root behave exactly as in Spec 06. A conflict at level 0 refutes the formula alone.

**Lemma (assertion validity).** A multi-literal learnt clause's asserting literal is always at the conflict level (> root), so clamped backtracking unassigns it and the clause asserts at root — the Phase 2 order (add/backjump/assert, Spec 06 section 3) extends to the clamped case unchanged. ∎

## 4. Final analysis and the failed core

A conflict at or below root cannot be undone (the assumption levels are fixed hypotheses), so instead of learning, the analyzer performs **final analysis**: the falsified clause's variables are resolved against their reason clauses, in reverse trail order, until only decision literals remain (the reason chain is well-founded: reason literals sit strictly earlier on the trail, Spec 06 section 2). The surviving decisions at levels ≥ 1 are exactly the assumptions responsible — the **failed core**.

**Theorem (core validity).** The formula entails ¬(core conjunction). *Proof.* Final analysis is resolution of the falsified clause with reason clauses on resolved variables (each step eliminates a variable present in both, Spec 06 section 3's argument); level-0 literals drop because their negations are root-entailed. The result is a clause over assumption literals entailed by the formula. ∎ Verified executably against a brute-force oracle (`property/sat_incremental_property_test.rs::cores_are_valid`).

**The falsified-assumption case.** An assumption already false under level 0 or an earlier assumption: the seed is the assumption literal itself; final analysis collects the responsible assumptions (the level-0 case gives the singleton core — the formula alone entails the assumption's negation).

## 5. Incremental hygiene

A Satisfiable call defers cleanup so the model stays readable; the next interaction (add or solve) flushes: backtrack to 0, delete every learnt clause of the call (they may depend on the hypothesis units — keeping them would corrupt later solves of the base formula), and delete the hypothesis units from the trace. NOTE: preprocessing (simplify) is NOT a flush point — with a deferred cleanup pending (level above 0), a direct simplify call fails loudly with the level invariant rather than silently mis-preprocessing; callers must add or solve first to flush. The deletion boundary is the registry entry index at call entry (offsets and indices are monotonic). Non-Satisfiable outcomes clean up immediately.
