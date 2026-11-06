# Formal Specification 09: SAT Preprocessing: Tautology Deletion, Duplicate Removal, Subsumption, Self-Subsuming Strengthening, Vivification

## Abstract

This document is the normative reference for `hot/sat/preprocess.rs`, cited by its `CEP:HPC-PASS-LEGALITY` and `CEP:HPC-PASS-*` block (design 11.1 S30/S33/S34/S36, 7.2 stage 10; design 26 build order "SAT: preprocessing (subsumption, vivification)"). It defines the four database rewrites of the simplification pass, their theory-preservation theorems, the proof-trace order of every add-delete pair, and the combined preservation of a bounded pass. Inputs are the solver's clause database with the registry and proof recorder; outputs are rewritten databases, an honest partial or complete status per round, and traceable deletions with RUP-justifiable replacement additions. References: Eén & Biere 2011 (vivification, "SAT Solving with Preprocessing"); Heule & Järvisalo & Biere (clause elimination); Formal Spec 05 (BCP).

## Formal Definitions

### 1. Scope

The pass rewrites the solver's clause database in place (through the registry's enumerable database), bounded by rounds (`kMaxSimplifyRounds`), pair checks (`kSatSubsumptionPairBudget`), vivification candidates (`kSatVivifyCandidateLimit`), and vivification propagation steps (`kSatVivifyPropagationBudget`); every stop is an honest partial status. Proof-trace integration: deletions are always traceable (DRAT deletions need no justification); each replacement addition is RUP-justifiable at its recording point (sections 3-5).

### 2. Tautology deletion and duplicate-literal removal

**Tautology (S33).** A clause containing x and ¬x is removed. *Preservation*: a tautology is satisfied by every assignment, so removing it preserves satisfiability and every model.

**Duplicates (S34).** C = A ∨ x ∨ x becomes C' = A ∨ x. *Preservation*: C and C' are logically equivalent. **Trace order**: add C' first — assuming ¬C' falsifies x and A, which falsifies C (x occurs twice), so C propagates the conflict; C' is RUP against the database containing C — then delete C.

### 3. Subsumption (S30)

C subsumes D iff lit(C) ⊆ lit(D) (propositional: sorted two-pointer inclusion). Deletion of D. *Preservation*: C ⊆ D means every model of C satisfies D, so D is entailed and its removal preserves the models of the remaining set exactly.

### 4. Self-subsuming resolution (S30, strengthening)

From C = A ∨ x and D = B ∨ ¬x with A ⊆ B: replace D by D' = B \ {¬x} (equivalently A ∪ (B \ {¬x}) = B \ {¬x} since A ⊆ B).

**Theorem.** D is equivalent to D' given C. *Proof.* D' is the resolvent of C and D on x; resolution is sound (Spec 07 section 4 restricted to the propositional fragment), so C ∧ D ⊨ D'. Conversely no case analysis is needed: D' ⊆ D as literal sets (D' is D minus the ¬x disjunct), and a sub-clause entails its superset, so D' ⊨ D outright — hence D' ⊨ C ∧ D. With C in the database, replacing D by D' preserves the theory. ∎ **Trace order**: add D' first — under ¬D', the unit propagation of C (A false forces x) and D (¬x side forced by B\{¬x} false) fires both x (from C) and ¬x (from D) — a propagation conflict, so D' is RUP — then delete D.

### 5. Vivification (S36)

For candidate C = l₁ ∨ … ∨ l_k (temporarily isolated from the database by the raw deleted mark): decide ¬l₁, propagate, decide ¬l₂, propagate, …; if a conflict arises after ¬l₁ … ¬l_j (j ≤ k), replace C by C' = l₁ ∨ … ∨ l_j.

**Theorem.** The database minus C entails C'. *Proof.* The check itself is the derivation: assuming ¬l₁ … ¬l_j over the database minus C propagates to a conflict, so (database \ {C}) ⊨ l₁ ∨ … ∨ l_j. ∎ **Trace order**: delete C first (C' is RUP against the database minus C, exactly what the check used), then add C'. The candidate's raw mark is restored when no prefix conflicts (no rewrite).

### 6. Refutation during preprocessing

A falsified unit addition (root conflict) or an empty strengthened clause refutes the formula: the pass returns Unsatisfiable with the empty clause recorded in the trace (Spec 11 section 4).

### 7. Combined preservation

**Theorem.** A completed pass preserves satisfiability, and a pass that stops at a budget preserves satisfiability of the processed prefix (every completed rewrite is one of sections 2-5). *Proof.* Each rewrite preserves the theory (sections 2-5); budget stops leave the database in a theory-preserving state because each rewrite is atomic (add-then-delete or delete-then-add). ∎ Verified executably against a brute-force oracle (`property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability`).

## Algorithm

The pass (`pub fn simplify(solver: &CdclSolver<'_>, options: &SimplifyOptions) -> Result<SimplifyOutcome, CdclError>`) runs in rounds over the registry's enumerable database:

1. Round entry: scan registered live clauses; apply the tautology and duplicate checks of section 2 (delete, or add-then-delete in the trace order stated there).
2. Pair phase: for each candidate pair under `kSatSubsumptionPairBudget`, run the subsumption test of section 3 (delete) and the self-subsuming strengthening of section 4 (add D', delete D).
3. Vivification phase: for each candidate under `kSatVivifyCandidateLimit`, run the prefix search of section 5 within `kSatVivifyPropagationBudget`; rewrite only on a prefix conflict, restoring the raw mark otherwise.
4. Repeat for at most `kMaxSimplifyRounds` rounds; every budget or round stop returns the honest partial status. A root conflict or empty strengthened clause short-circuits to Unsatisfiable with the empty clause in the trace (section 6).

Each rewrite is atomic in the trace (its stated add-delete order); space is O(database + workspace); time is O(rounds x pairs x clause length) under the budgets. Assumptions: the solver is at level 0 (the level invariant is checked loudly); the registry and proof recorder are attached when tracing is required.

## Invariants

1. Per-rewrite preservation: each of sections 2 through 5 preserves the theory of the database (Theorems stated per section).
2. Combined preservation: a completed pass, and every prefix of a budget-stopped pass, preserves satisfiability (Theorem of section 7; `property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability`).
3. Trace integrity: every replacement addition is RUP-justifiable at its recording point under the stated trace order; deletions are always traceable (sections 2, 4, 5).
4. Honesty: a budget stop is reported as a partial status; a refutation is reported as Unsatisfiable with the empty clause recorded (sections 1 and 6).
5. Level invariant: the pass refuses to run above level 0 instead of silently mis-preprocessing (Algorithm assumptions).
6. Candidate isolation: vivification's temporary raw mark is restored whenever no rewrite happens (section 5).

## Integration Points

Depends on:

- `hot/sat/solver.rs` (`CdclSolver::core(&self) -> &SatCore<'a>`, `CdclSolver::registry(&self) -> &ClauseRegistry<'a>`, `CdclSolver::proof(&self) -> Option<&ProofRecorder<'a>>`) for database, registry, and trace access.
- `hot/sat/registry.rs` (`ClauseRegistry::delete(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<(), RegistryError>`) for enumeration and tombstoning.
- `hot/sat/bcp.rs` (Specification 05) for vivification's bounded propagation.

Depended on by:

- The solver's setup phase, which calls `simplify` before the first solve; the cold proof pipeline replays the recorded additions and deletions (Specification 11).
- `tests/property/sat_preprocess_property_test.rs` and `tests/unit/hot/sat_preprocess_test.rs`, the executable evidence for invariants 1 through 4.

## Known Limitations

- Every phase is budget-bounded and stops honestly partial; no completeness claim is made beyond the processed prefix (section 7).
- Blocked-clause elimination and other Heule/Järvisalo/Biere techniques beyond sections 2 through 5 are out of scope; the pass implements exactly the four rewrites specified.
- Vivification rewrites a candidate at most once per round; iterating to a fixpoint across rounds is bounded by `kMaxSimplifyRounds`, not guaranteed.
