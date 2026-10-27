# Formal Spec 17: Proof Recording for Induction Schemes and Conjecture Lemmas

## 1. Scope

This specification extends Formal Spec 14 (unified proof reconstruction) with the recording, presentation, and checking obligations of the revised-build-order Phase 4 inference vocabulary:

- `StructuralInduction` / `WellFoundedInduction` — parentless theory axioms (Spec 15),
- `ConjectureNegation` — a mini-refutation premise (Spec 16),
- `ConjectureLemma` — the reductio step over an imported subproof (Spec 16 section 3.6).

It also records the **sub-DAG composition** discipline (the import's id-translation invariants) that makes proofs spanning the main search and imported subproofs well-formed for the existing walk, writer, and checker.

## 2. Invariants preserved

Every Spec 14 invariant continues to hold for proofs containing the new rules:

- **Monotonic ids.** Imported clauses are created in the main store after all existing ids, and every translated parent is strictly older than its child (the import walks ascending over the mini store's monotonic ids, and mini inputs translate to pre-existing main ids). The walk's `CycleDetected` argument is untouched.
- **Reachability pruning.** The walk from any refutation reaches exactly the clauses used; imported subproof clauses are reachable through the lemma's parents and unreachable otherwise (they never enter the passive set, Spec 16 section 3.6), so a proof that does not use a lemma pays nothing for its subproof.
- **Roles and sources.** The writer emits the schemes with the `axiom` role and the source names `structural_induction` / `well_founded_induction`; `ConjectureNegation` statements are `plain` (they are discharged internal premises); `ConjectureLemma` statements carry the TSTP `lemma` role with the source `conjecture_lemma`.

## 3. The id-translation invariants of the import

Let `T` be the translation (mini id -> main id) built by the import (Spec 16 section 3.6). The invariants, all verified by construction and pinned executably:

- **I1 (input fidelity):** for every mini input `i`, `T(i) = kFirstClauseId + i` (the order-preserving re-add); no clause is created for an input.
- **I2 (rule and age preservation):** for every imported non-input clause `c`, the main copy's derivation rule equals `c`'s rule and its age equals `c`'s age.
- **I3 (parent translation):** for every imported clause `c` with parents `p1..pk`, the main copy's parents are `T(p1)..T(pk)`; every parent is in the reachable closure (the closure is ancestor-complete), so no translated parent is invalid.
- **I4 (substitution discipline):** every derivation in the main store — imported or native — carries `substitution = kInvalidSubstitutionOffset` (the production discipline; the checker replays rules rather than trusting recorded substitutions).
- **I5 (substitution identity):** `ConjectureLemma` steps cite exactly two parents: `[T(negation_premise), T(empty_clause)]`.
- **I6 (watermark separation, the Task 26 repair):** the search space tracks the first proof-only id (the import watermark); every harvest scan (the premise enumeration, the unit window, the constructor-instance scan) stops at it, so imported clauses can neither seed candidates nor enter later mini premise sets. The invariant is what keeps I1's positional mapping meaningful across multiple imports.

## 4. The checker's new rules

The replay checker - since the Phase 5 kernel delegation, the certified kernel itself (`cold/kernel.rs`, Formal Spec 19; the ConjectureLemma arm) - accepts a step exactly as follows:

| Rule | Acceptance condition |
|---|---|
| `StructuralInduction`, `WellFoundedInduction` | `parent_count == 0` (theory-axiom introduction; the walk existence-checks the clause). The clause shape itself is fixed by the induction module and pinned against Spec 15 sections 3.2/4.2 by the unit tests — the same situation as published AVATAR proofs' black-box rules (Spec 14 section 5), except here the introduced clause is fully auditable by name and shape. |
| `ConjectureNegation` | `parent_count == 0` (premise introduction; discharged by the reductio check below). |
| `ConjectureLemma` | The **mechanical reductio check**: (i) `parent_count == 2`; (ii) parent 0 is a `ConjectureNegation` clause with the same literal count as the lemma, whose literals are exactly the lemma's literals with polarity flipped (multiset match on hash-consed atoms); (iii) parent 1 is the empty clause; (iv) both parents are strictly older; (v) parent 0 is an **ancestor** of parent 1 (`ancestor_of`: the visited-bitmap linear walk over the derivation DAG). |

**Theorem (adequacy of the reductio check).** If every other step in the proof is sound (each replayed or structurally checked per Spec 14 and this spec) and a `ConjectureLemma` step passes the check, then the lemma is entailed by the proof's axiom set.

*Proof.* Parent 1's ancestry (which contains parent 0 by (v)) is a refutation of the axiom set plus the negation premise; by (ii) the negation premise is exactly the negation of the lemma; by the soundness of the subproof's rules the axiom set plus `~phi` is unsatisfiable, hence the axiom set entails `phi`. ∎

The vacuous-refutation rejection (Spec 16 section 3.5) guarantees (v) can always be satisfied for imports: the filter never produces a lemma whose subproof lacks the negation.

## 5. Engine corrections delivered with this spec

Recording the new proof kinds exposed and fixed three pre-existing defects, each with an executable pin (the corrections are part of this spec's evidence chain because the new proofs would otherwise be unrecordable, uncheckable, or misreported):

1. **Term-bound error misclassification** (`hot/unification/substitution.rs::map_term_error`): `TermError::DepthExceeded` / `WeightExceeded` were mapped to `InvalidPointer` (legal bound exhaustion reported as corruption). Now exact (`SubstitutionError::DepthExceeded` / new `WeightExceeded`); pinned by `unit/hot/substitution_test.rs::term_bound_errors_not_misclassified`. The generator-level policy change (bound-exhausted conclusions dropped-and-counted instead of terminating the search) is ticketed separately (CEP-1050).
2. **Parked-demodulant flag loss** (`hot/search/given_clause.rs`): the demodulation parking path stored `restandardize_clause`-rebuilt literals without recomputing selection/maximality flags, silently disabling every ordering-eligible rule on the parked clause (a completeness defect). Fixed by recomputing the flags before storage.
3. **Missing checker arms** (now the certified kernel, `cold/kernel.rs`): the file header and Spec 14 claimed superposition replay, but `Superposition`, `EqualityResolution`, and `EqualityFactoring` steps fell into the reject-all catch-all (every equality proof was unverifiable). The three replay arms are implemented (superpose: both premise orders x every subterm path through the generator's `advance_path`, with the target premise renamed apart into the namespace above the equation premise's variable count exactly as the generator's standardize-apart does; equality resolution: every literal; equality factoring: every ordered pair). Two honesty notes from the Task 26 review, both closed in Phase 5 (Spec 19): the arms are sound SUPERSETS of the ordered production rules (eligibility side conditions are not re-checked - ordering restrictions are completeness-only, so accepting an ineligible instance cannot admit an unsound step), and the pre-Phase-5 Resolution/Factoring arms replayed without renaming apart (a valid proof with overlapping premise namespaces could be falsely rejected - ticket CEP-1054, closed: the kernel renames the active parent above the given parent's variables and replays it at its full literal count).

## 6. Evidence map

| Claim | Executable pin |
|---|---|
| Scheme clauses equal Spec 15's clausifications | `unit/hot/induction_test.rs::{structural,well_founded}_scheme_clauses_match_clausification`; `property/induction_property_test.rs::schemes_match_hand_clausification` |
| Imported lemmas pass the reductio check | `unit/hot/conjecture_test.rs::{refuted_candidate_imports_proof, checker_accepts_conjecture_lemma}`; `property/conjecture_property_test.rs::only_proved_lemmas_added` |
| Tampered lemmas are rejected | `unit/hot/conjecture_test.rs::checker_accepts_conjecture_lemma` (detached variant) |
| Vacuous refutations never become lemmas | `unit/hot/conjecture_test.rs::vacuous_refutation_discarded` |
| The import preserves existing clauses | `property/conjecture_property_test.rs::harvest_preserves_existing_clauses` |
| The engine corrections hold | `unit/hot/substitution_test.rs::term_bound_errors_not_misclassified`; `unit/hot/conjecture_test.rs::lemma_enters_passive_set` (the flag fix's proof path); the equality proofs checked end to end by `refuted_candidate_imports_proof` (the checker-arms fix) |
