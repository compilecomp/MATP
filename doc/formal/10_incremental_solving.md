# Formal Specification 10: Incremental Solving with Assumptions and Failed Cores

## Abstract

This document is the normative reference for `CdclSolver::solve_with_assumptions` and `ConflictAnalyzer::analyze_final` (`hot/sat/solver.rs`, `hot/sat/cdcl.rs`), cited by their `CEP:HPC-PASS-LEGALITY` fields (design 11.1 S38/S39/S40, 12.2). It defines the assumption interface and its four outcomes, the hypothesis-unit proof-trace semantics, the search under a backjump floor, final analysis with failed-core extraction, and the incremental hygiene rules. Inputs are assumption literals and the solver state; outputs are `AssumptionOutcome` verdicts with extractable failed cores. References: Eén & Sörensson 2003 (MiniSat assumptions); Marques-Silva & Sakallah 1996; Formal Spec 06 (CDCL).

## Formal Definitions

### 1. The interface

`solve_with_assumptions(A)` returns Satisfiable (the formula ∧ A is satisfiable; the model extends A), Unsatisfiable (the formula alone is refuted), UnsatUnderAssumptions (the formula ∧ A is unsatisfiable; a failed core is extractable), or Indeterminate (a budget).

### 2. Assumption semantics

Assumption literals are hypotheses of the call, not formula clauses: each is pushed as its own decision level (levels 1..=root where root = the number of pushed assumptions; satisfied duplicates skip without new levels). The proof trace records each as a hypothesis unit (AssumptionAdd) and removes it at the call's end (AssumptionDelete) — plain DRAT has no hypothesis syntax, so the units render as ordinary unit clauses; the checker skips justification for hypothesis steps (Spec 11 section 3).

### 4. Final analysis and the failed core

A conflict at or below root cannot be undone (the assumption levels are fixed hypotheses), so instead of learning, the analyzer performs **final analysis**: the falsified clause's variables are resolved against their reason clauses, in reverse trail order, until only decision literals remain (the reason chain is well-founded: reason literals sit strictly earlier on the trail, Spec 06 section 2). The surviving decisions at levels ≥ 1 are exactly the assumptions responsible — the **failed core**.

**Theorem (core validity).** The formula entails ¬(core conjunction). *Proof.* Final analysis is resolution of the falsified clause with reason clauses on resolved variables (each step eliminates a variable present in both, Spec 06 section 3's argument); level-0 literals drop because their negations are root-entailed. The result is a clause over assumption literals entailed by the formula. ∎ Verified executably against a brute-force oracle (`property/sat_incremental_property_test.rs::cores_are_valid`).

**The falsified-assumption case.** An assumption already false under level 0 or an earlier assumption: the seed is the assumption literal itself; final analysis collects the responsible assumptions (the level-0 case gives the singleton core — the formula alone entails the assumption's negation).

## Algorithm

### 3. The search under assumptions

The CDCL loop runs with root as the backjump floor: backjumps clamp to max(target, root) and restarts return to root. Conflicts at levels above root behave exactly as in Spec 06. A conflict at level 0 refutes the formula alone.

**Lemma (assertion validity).** A multi-literal learnt clause's asserting literal is always at the conflict level (> root), so clamped backtracking unassigns it and the clause asserts at root — the Phase 2 order (add/backjump/assert, Spec 06 section 3) extends to the clamped case unchanged. ∎

The call sequence: push assumptions as decision levels (section 2), run the loop of Spec 06 with the clamped backjumps, and on a conflict at or below root run `analyze_final(&self, core: &SatCore<'_>, seed: &[SatLiteral], output: &mut [SatLiteral]) -> Result<usize, CdclError>` in reverse trail order to extract the failed core. Time per call is the CDCL cost of Spec 06 plus O(trail length) for final analysis; space is the solver state plus the core buffer. Assumptions: assumption literals are distinct or deduplicated by the satisfied-duplicate rule; budgets of Spec 06 apply unchanged.

### 5. Incremental hygiene

A Satisfiable call defers cleanup so the model stays readable; the next interaction (add or solve) flushes: backtrack to 0, delete every learnt clause of the call (they may depend on the hypothesis units — keeping them would corrupt later solves of the base formula), and delete the hypothesis units from the trace. NOTE: preprocessing (simplify) is NOT a flush point — with a deferred cleanup pending (level above 0), a direct simplify call fails loudly with the level invariant rather than silently mis-preprocessing; callers must add or solve first to flush. The deletion boundary is the registry entry index at call entry (offsets and indices are monotonic). Non-Satisfiable outcomes clean up immediately.

## Invariants

1. Hypothesis discipline: assumptions are decision-level hypotheses of the call, recorded as AssumptionAdd and removed as AssumptionDelete in the trace (section 2).
2. Assertion validity under clamping: learnt clauses assert at root after clamped backjumps (Lemma of section 3).
3. Core validity: the formula entails the negation of every extracted core conjunction (Theorem of section 4; `property/sat_incremental_property_test.rs::cores_are_valid`).
4. Base-formula integrity: a flushed call leaves the base formula's model set unchanged (learnt clauses depending on hypothesis units are deleted, section 5).
5. Monotone deletion boundary: the registry entry index at call entry bounds the call's deletions; offsets and indices never move backwards (section 5).
6. Loud refusal: simplify above level 0 fails with the level invariant instead of proceeding (section 5).

## Integration Points

Depends on:

- `hot/sat/cdcl.rs` (`ConflictAnalyzer::analyze_final`) for final analysis over reasons and levels (Spec 06).
- `hot/sat/solver.rs` (`CdclSolver::solve_with_assumptions(&self, assumptions: &[SatLiteral]) -> AssumptionOutcome`, `CdclSolver::failed_assumptions_into(&self, out: &mut [SatLiteral]) -> usize`) for the interface and core extraction.
- `hot/sat/registry.rs` and the proof recorder for the deletion boundary and hypothesis-unit trace steps.

Depended on by:

- `hot/avatar/controller.rs`, which solves per split stack and retracts on failed cores (Specification 12 section 4).
- `hot/conjecture/filter.rs`, whose mini refutations are bounded assumption solves (Specification 16).
- `cold/proof_output/`, which replays the hypothesis-unit steps (Specification 11 section 3).

## Known Limitations

- Budget exhaustion returns Indeterminate; no core is extractable in that case (section 1).
- Failed cores are extracted only under UnsatUnderAssumptions; Satisfiable and Unsatisfiable outcomes carry no core.
- Preprocessing is not a flush point (section 5); callers must order add/solve before simplify.
- Assumption levels are capped by the solver's level capacity (the trail bounds of Spec 05 section 7); pushing more assumptions than the cap fails loudly.
