# Formal Specification 09: SAT Preprocessing: Tautology Deletion, Duplicate Removal, Subsumption, Self-Subsuming Strengthening, Vivification, Probing, Hyper-Binary Resolution, Bounded Variable Elimination, Blocked-Clause Elimination

## Abstract

This document is the normative reference for `hot/sat/preprocess.rs`, cited by its `CEP:HPC-PASS-LEGALITY` and `CEP:HPC-PASS-*` block (design 11.1 S30-S37, 7.2 stage 10; design 26 build order "SAT: preprocessing (subsumption, vivification)", completed to the full S30-S37 inventory under ticket CEP-1063). It defines the eight database rewrites of the simplification pass, their theory-preservation theorems, the proof-trace order of every add-delete pair, and the model reconstruction for the equisatisfiable deletions. Inputs are the solver's clause database with the registry and proof recorder; outputs are rewritten databases, an honest partial or complete status per round, traceable deletions with RUP-justifiable replacement additions, and the model-extension stack entries the solver's `model_value` consumes. References: Eén & Biere 2011 (vivification, "SAT Solving with Preprocessing"); Heule & Järvisalo & Biere (clause elimination); Bacchus (hyper-binary resolution); Formal Spec 05 (BCP).

## Formal Definitions

### 1. Scope

The pass rewrites the solver's clause database in place (through the registry's enumerable database), bounded by rounds (`kMaxSimplifyRounds`), pair checks (`kSatSubsumptionPairBudget`), vivification candidates (`kSatVivifyCandidateLimit`), vivification propagation steps (`kSatVivifyPropagationBudget`), probe excursions (`kSatProbeBudget`), hyper-binary pair checks (`kSatHyperBinaryPairBudget`, collection cap `kSatHyperBinaryClauseLimit`), BVE variable attempts (`kSatBveVariableLimit`, occurrence cap `kSatBveOccurrenceLimit`, resolvent bound `kSatBveResolventBudget`), and BCE checks (`kSatBceCheckBudget`), with the model-extension stack bounded by `kSatBceStackDepth` entries of `kSatExtEntryLiterals` cells; every stop is an honest partial status. Proof-trace integration: deletions are always traceable (DRAT deletions need no justification); each replacement addition is RUP-justifiable at its recording point (sections 2-9).

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

### 7. Failed-literal probing (S35)

For a candidate literal l with value Unassigned at level 0 (candidates are the literals of the live clauses, in registry and storage order): decide l, propagate; on conflict, add the unit ¬l as a derived clause. Literals already assigned are skipped (a True literal is satisfied; a False literal's negation is already a unit and re-deriving it would only duplicate).

**Theorem.** The conflict under the assumption l proves database ⊨ ¬l, so the unit addition is RUP. *Proof.* RUP against database D checks D ∧ l for a propagation conflict — exactly the check performed. ∎ **Trace order**: the unit addition (nothing is deleted). The excursion is fully canceled before the addition. *Relation to vivification*: vivification derives the same units only when the conflict shortens some clause to a unit; probing derives every failed-literal unit in one decide+propagate excursion regardless of clause shapes.

### 8. Hyper-binary resolution (S37)

The live binary clauses are collected into a fixed snapshot (cap `kSatHyperBinaryClauseLimit`; overflow stops the round honestly). For each ordered pair with a pivot x in the first binary whose negation occurs in the second, the resolvent (first \ {x}) ∪ (second \ {¬x}) is added through the shared derived-add path — a unit when the non-pivot literals coincide, else a binary. Tautological resolvents are skipped; resolvents equal to a snapshot binary are skipped (the next round's subsumption scan removes any remaining exact duplicates).

**Theorem.** The resolvent is RUP-derivable. *Proof.* For binaries (x ∨ a) and (¬x ∨ b): assuming ¬(a ∨ b) falsifies a and b, which forces x (from the first) and ¬x (from the second) — a propagation conflict. ∎ The classic unit case (x ∨ a), (¬x ∨ a) ⊨ a is the a = b instance. **Trace order**: the addition (nothing is deleted by this rewrite).

### 9. Bounded variable elimination (S32)

For a candidate variable v (unassigned at level 0; attempted in variable order under `kSatBveVariableLimit`): collect the live clauses containing v (occ_pos) and ¬v (occ_neg) into fixed buffers (overflow skips the candidate). Preconditions, checked before any mutation: every resolvent (pos \ {v}) ∪ (neg \ {¬v}) of a pos-clause and a neg-clause is non-tautological (tautological resolvents are satisfied by every assignment and are exactly the ones whose absence the flip theorem of section 12 tolerates), committed count ≤ `kSatBveResolventBudget`, every resolvent fits `kMaxSatClauseLiterals`, the reconstruction payload (one length marker plus the literals per clause) fits `kSatExtEntryLiterals`, and the model-extension stack has a free entry. On success: add all non-tautological resolvents (RUP — see below), record the deleted clauses onto the stack (kind 1 entry: the variable plus its deleted clauses), then delete every clause containing v.

**Theorem (trace).** Each resolvent is RUP at its recording point (the parents are still present). *Proof.* Assuming ¬(A ∨ B) falsifies A and B, which forces v from (v ∨ A) and ¬v from (¬v ∨ B) — a propagation conflict. ∎ **Theorem (satisfiability).** The reduced database is satisfiable iff the original is. *Proof.* (⇐) a model of the original restricted to the other variables satisfies the resolvents. (⇒) given a model M of the reduced database, at most one side can be falsified (a falsified clause on each side would force v to both values); flipping v to the falsified side satisfies every clause of that side — for each clause of the other side, either its resolvent with a falsified clause is committed (its remainder is satisfied because the falsified side's remainder is all-false) or that resolvent was tautological (a complementary pair, whose true member still satisfies the clause) — and v does not occur in the reduced database, so the flip preserves it. ∎ **Trace order**: add resolvents, record, delete the parents.

### 10. Blocked-clause elimination (S31)

For a candidate clause C with 2 ≤ |C| ≤ `kSatBceMaxClauseLength` and a blocking-literal candidate l ∈ C (tried in sorted order): C is blocked w.r.t. l iff every live clause D containing ¬l resolves with C on l to a tautology, i.e. D contains ¬x for some x ∈ C \ {l}. Candidates whose ¬l-occurrence set is empty are skipped (vacuous blockedness is the pure-literal rule's territory and its deletion here would starve the weaker rewrites of their resolution partners); occurrence overflow (buffer cap) skips the candidate. On success: record C and l onto the model-extension stack (kind 0 entry), then delete C. No additions are made, so the trace carries only the deletion.

**Theorem (satisfiability).** Deleting a blocked clause preserves satisfiability. *Proof.* A model of the reduced database satisfies the deleted clause after setting l true: every clause that setting could break contains ¬l, and each such clause contains ¬x for some x ∈ C \ {l}, which the extension leaves untouched unless demanded by an even later reconstruction step — the reverse-order reconstruction of section 12 keeps every step's clause satisfied. ∎ **Trace order**: the deletion (DRAT deletions need no justification).

### 11. The model-extension stack and reconstruction

The solver holds a bounded inline stack (`kSatBceStackDepth` entries of `kSatExtEntryLiterals` cells) with two entry kinds, appended only by the sanctioned preprocessing path and read only by `model_value`: kind 0 records a blocked clause (its literals plus the blocking literal), kind 1 records an eliminated variable (its deleted clauses as a flat length-marked payload). `model_value` resolves a variable's value as the trail value, unless a stack entry consumes it: entries are processed newest-first, an entry consumes its anchor variable when its clauses are unsatisfied under the trail plus the newer entries' overrides (kind 0: the blocked clause is unsatisfied → the blocking literal's polarity; kind 1: a deleted clause of the variable is falsified → the side flip of section 9's theorem), and the first consuming entry's override is the effective value.

**Theorem (reconstruction).** Processing the entries newest-first yields a model of the preprocessed database extended to a model of the original. *Proof.* Induction over the entries from the newest: the reconstruction at entry i sees exactly the trail and the newer entries' overrides — the same assignment state the elimination-time argument of section 9 (for kind 1) and the blockedness argument of section 10 (for kind 0) reasoned about; each entry either is already satisfied (consumes nothing) or its override satisfies its own clauses, and the eliminated-variable flip's resolvent argument together with the blocked clause's blockedness guarantee no other entry's clauses are broken. ∎ Cost: one trail load without entries; O(stack × entry size) worst case with the reconstruction active.

### 12. Refutation during preprocessing (summary)

A falsified unit addition (root conflict), an empty strengthened clause, or a refuting derived addition (unit or resolvent against an already-entailed negation) refutes the formula: the pass returns Unsatisfiable with the empty clause recorded in the trace (Spec 11 section 4). Section 6 states the vivification-side rule; probing, hyper-binary, and BVE additions share the same `add_derived_clause` path, so their refuting sub-cases are covered by the same mechanism.

### 13. Combined preservation

**Theorem.** A completed pass preserves satisfiability, and a pass that stops at a budget preserves satisfiability of the processed prefix (every completed rewrite is one of sections 2-10). *Proof.* Each rewrite preserves satisfiability (sections 2-10, with sections 9-10 via the reconstruction of section 11); budget stops leave the database in a theory-preserving state because each rewrite is atomic (add-then-delete, record-then-delete, or delete-only). ∎ Verified executably against a brute-force oracle (`property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability`) and, for the reconstruction, by the model checks `unit/hot/sat_preprocess_test.rs::{bve_model_extension_satisfies_original, bce_model_extension_satisfies_original}`.

## Algorithm

The pass (`pub fn simplify(solver: &CdclSolver<'_>, options: &SimplifyOptions) -> Result<SimplifyOutcome, CdclError>`) runs in rounds over the registry's enumerable database:

1. Round entry: scan registered live clauses; apply the tautology and duplicate checks of section 2 (delete, or add-then-delete in the trace order stated there).
2. Pair phase: for each candidate pair under `kSatSubsumptionPairBudget`, run the subsumption test of section 3 (delete) and the self-subsuming strengthening of section 4 (add D', delete D).
3. Vivification phase: for each candidate under `kSatVivifyCandidateLimit`, run the prefix search of section 5 within `kSatVivifyPropagationBudget`; rewrite only on a prefix conflict, restoring the raw mark otherwise.
4. Probing phase: for each candidate literal of a live clause under `kSatProbeBudget`, run the failed-literal check of section 7 (decide, propagate, cancel); add the negated unit on conflict.
5. Hyper-binary phase: collect the live binaries (cap `kSatHyperBinaryClauseLimit`) and, for each pair under `kSatHyperBinaryPairBudget`, add the resolvents of section 8.
6. BVE phase: for each unassigned variable under `kSatBveVariableLimit`, run the elimination of section 9 under its preconditions and budgets.
7. BCE phase: for each live clause of eligible length, run the blockedness check of section 10 under `kSatBceCheckBudget`; record and delete on success.
8. Repeat for at most `kMaxSimplifyRounds` rounds; every budget or round stop returns the honest partial status. A refutation short-circuits to Unsatisfiable with the empty clause in the trace (section 12).

Each rewrite is atomic in the trace (its stated order); space is O(database + workspace + stack); time is O(rounds x (clauses + budgeted pairs + budgeted probes + budgeted BVE candidates + budgeted BCE checks)) under the budgets. Assumptions: the solver is at level 0 (the level invariant is checked loudly); the registry and proof recorder are attached when tracing is required.

## Invariants

1. Per-rewrite preservation: each of sections 2 through 10 preserves satisfiability (theorems stated per section).
2. Combined preservation: a completed pass, and every prefix of a budget-stopped pass, preserves satisfiability (section 13; `property/sat_preprocess_property_test.rs::preprocessing_preserves_satisfiability`).
3. Trace integrity: every replacement addition is RUP-justifiable at its recording point under the stated trace order; deletions are always traceable (sections 2, 4, 5, 8, 9).
4. Model reconstruction: every equisatisfiable deletion (BCE, BVE) appends a stack entry before its deletions, and `model_value`'s newest-first reconstruction yields a model of the original formula (section 11; the two model-extension unit tests).
5. Honesty: a budget stop is reported as a partial status; a refutation is reported as Unsatisfiable with the empty clause recorded (sections 1 and 12); every skip (occurrence, length, resolvent, payload, stack bounds) is counted in the stats and mutates nothing.
6. Level invariant: the pass refuses to run above level 0 instead of silently mis-preprocessing (Algorithm assumptions).
7. Candidate isolation: vivification's temporary raw mark is restored whenever no rewrite happens (section 5).

## Integration Points

Depends on:

- `hot/sat/solver.rs` (`CdclSolver::core(&self) -> &SatCore<'a>`, `CdclSolver::registry(&self) -> &ClauseRegistry<'a>`, `CdclSolver::proof(&self) -> Option<&ProofRecorder<'a>>`, `CdclSolver::ext_entry_count`, `CdclSolver::bce_record`, `CdclSolver::bve_record`) for database, registry, trace, and reconstruction-stack access.
- `hot/sat/registry.rs` (`ClauseRegistry::delete(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<(), RegistryError>`) for enumeration and tombstoning.
- `hot/sat/bcp.rs` (Specification 05) for vivification's and probing's bounded propagation.

Depended on by:

- The solver's setup phase, which calls `simplify` before the first solve; the cold proof pipeline replays the recorded additions and deletions (Specification 11); `model_value` consumes the stack (section 11).
- `tests/property/sat_preprocess_property_test.rs`, `tests/unit/hot/sat_preprocess_test.rs`, and `tests/security/phase3_bounds_test.rs`, the executable evidence for invariants 1 through 6.

## Known Limitations

- Every phase is budget-bounded and stops honestly partial; no completeness claim is made beyond the processed prefix (section 13).
- Vacuous blockedness (a blocking candidate whose negation occurs in no clause) is not eliminated (section 10): the pure-literal-flavored deletion is left out so the weaker rewrites keep their resolution partners.
- BVE resolvent deduplication and a BCE occurrence index are deferred pending measurement on production preprocessing workloads (the budgets bound the additions and checks instead; the next round's subsumption scan removes exact duplicate clauses).
- Eliminated variables are not frozen: the search may spend one decision on a variable that no clause constrains (bounded by the variable count; freezing is a solver-state change deferred with the measured follow-ups).
- Vivification rewrites a candidate at most once per round; iterating to a fixpoint across rounds is bounded by `kMaxSimplifyRounds`, not guaranteed.
