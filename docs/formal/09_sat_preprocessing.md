# Formal Specification 09: SAT Preprocessing — Tautology Deletion, Duplicate Removal, Subsumption, Self-Subsuming Strengthening, Vivification

Version: 0.1
Status: complete for the Phase 3 scope (design 11.1 S30/S33/S34/S36, 7.2 stage 10; design 26 build order "SAT: preprocessing (subsumption, vivification)")
Role: normative reference for `hot/sat/preprocess.rs`; cited by its `CEP:HPC-PASS-LEGALITY` and `CEP:HPC-PASS-*` block.
References: design 11.1 (S30-S37), 7.2 (stage 10); Eén & Biere 2011 (vivification, "SAT Solving with Preprocessing"); Heule & Järvisalo & Biere (clause elimination); Formal Spec 05 (BCP).

## 1. Scope

The pass rewrites the solver's clause database in place (through the registry's enumerable database), bounded by rounds (`kMaxSimplifyRounds`), pair checks (`kSatSubsumptionPairBudget`), vivification candidates (`kSatVivifyCandidateLimit`), and vivification propagation steps (`kSatVivifyPropagationBudget`); every stop is an honest partial status. Proof-trace integration: deletions are always traceable (DRAT deletions need no justification); each replacement addition is RUP-justifiable at its recording point (sections 3-5).

## 2. Tautology deletion and duplicate-literal removal

**Tautology (S33).** A clause containing x and ¬x is removed. *Preservation*: a tautology is satisfied by every assignment, so removing it preserves satisfiability and every model.

**Duplicates (S34).** C = A ∨ x ∨ x becomes C' = A ∨ x. *Preservation*: C and C' are logically equivalent. **Trace order**: add C' first — assuming ¬C' falsifies x and A, which falsifies C (x occurs twice), so C propagates the conflict; C' is RUP against the database containing C — then delete C.

## 3. Subsumption (S30)

C subsumes D iff lit(C) ⊆ lit(D) (propositional: sorted two-pointer inclusion). Deletion of D. *Preservation*: C ⊆ D means every model of C satisfies D, so D is entailed and its removal preserves the models of the remaining set exactly.

## 4. Self-subsuming resolution (S30, strengthening)

From C = A ∨ x and D = B ∨ ¬x with A ⊆ B: replace D by D' = B \ {¬x} (equivalently A ∪ (B \ {¬x}) = B \ {¬x} since A ⊆ B).

**Theorem.** D is equivalent to D' given C. *Proof.* D' is the resolvent of C and D on x; resolution is sound (Spec 07 section 4 restricted to the propositional fragment), so C ∧ D ⊨ D'. Conversely no case analysis is needed: D' ⊆ D as literal sets (D' is D minus the ¬x disjunct), and a sub-clause entails its superset, so D' ⊨ D outright — hence D' ⊨ C ∧ D. With C in the database, replacing D by D' preserves the theory. ∎ **Trace order**: add D' first — under ¬D', the unit propagation of C (A false forces x) and D (¬x side forced by B\{¬x} false) fires both x (from C) and ¬x (from D) — a propagation conflict, so D' is RUP — then delete D.

## 5. Vivification (S36)

For candidate C = l₁ ∨ … ∨ l_k (temporarily isolated from the database by the raw deleted mark): decide ¬l₁, propagate, decide ¬l₂, propagate, …; if a conflict arises after ¬l₁ … ¬l_j (j ≤ k), replace C by C' = l₁ ∨ … ∨ l_j.

**Theorem.** The database minus C entails C'. *Proof.* The check itself is the derivation: assuming ¬l₁ … ¬l_j over the database minus C propagates to a conflict, so (database \ {C}) ⊨ l₁ ∨ … ∨ l_j. ∎ **Trace order**: delete C first (C' is RUP against the database minus C, exactly what the check used), then add C'. The candidate's raw mark is restored when no prefix conflicts (no rewrite).

## 6. Refutation during preprocessing

A falsified unit addition (root conflict) or an empty strengthened clause refutes the formula: the pass returns Unsatisfiable with the empty clause recorded in the trace (Spec 11 section 4).

## 7. Combined preservation

**Theorem.** A completed pass preserves satisfiability, and a pass that stops at a budget preserves satisfiability of the processed prefix (every completed rewrite is one of sections 2-5). *Proof.* Each rewrite preserves the theory (sections 2-5); budget stops leave the database in a theory-preserving state because each rewrite is atomic (add-then-delete or delete-then-add). ∎ Verified executably against a brute-force oracle (`property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability`).
