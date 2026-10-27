# Formal Spec 19: The Certified Proof Kernel

## 1. Scope

This specification fixes the certified proof kernel (`cold/kernel/`): the single internal verifier every MAPT proof passes through before the search claims `Theorem` or the writer emits TSTP output. The kernel absorbs the replay checker that Formal Spec 14 section 6 placed in the TSTP layer: the derivation-DAG walk, the conclusion pipeline, the multiset comparison, and the per-rule replay arms live in `cold/kernel.rs`, and the TSTP module delegates to it (`check_proof` is the kernel verdict mapping; `reachable_proof_ids` delegates to the kernel's walk). The unification with the rest of the checker is total: **no other component verifies derivations**, and no component may bypass the kernel.

The kernel's contract, restated from design 18.4: *an ATP that produces an invalid proof is worse than one that produces no proof.* Verification cost is bounded and measured (CEP&CC 23); budget exhaustion is an **error**, never a rejection; every rejection names its step and reason (Law 6).

## 2. The verdict vocabulary

```
KernelVerdict ::= Valid
               |  Invalid { clause_id: u64, rejection: KernelRejection }
KernelError   ::= ReplayBudgetExhausted
```

- `Valid` — every reachable step replayed successfully.
- `Invalid { clause_id, rejection }` — one step was rejected; `clause_id` names the rejected step (or the offending parent for walk-level rejections), `rejection` names the failed check.
- `Err(ReplayBudgetExhausted)` — the verification could not finish within the injectable budget; the proof is **neither verified nor condemned** (CEP&CC 34.3: exhaustion must stay distinguishable from rejection).

The rejection vocabulary distinguishes structural corruption from replay failure:

| Rejection | Meaning |
|---|---|
| `NonMonotonicDerivation` | a parent id is not strictly below its child (Spec 14 section 2's monotonic-id contract violated) |
| `UnreadableClause` | a record or literal in the derivation could not be read |
| `DeletedRuleDerivation` | the derivation claims a deletion rule (forward/backward subsumption, subsumption resolution, tautology deletion, condensation) — deletion never derives a stored record |
| `UnrecordedRule` | a `Demodulation` derivation claiming the two-parent shape whose rule parent (derivation parent 1) is unrecorded; the pre-Phase-5 one-parent park shape fails the parent-count requirement and is rejected as `BrokenDemodulation` |
| `BrokenIntroduction` | a parentless introduction claims parents |
| `BrokenResolution` / `BrokenFactoring` / `BrokenSuperposition` / `BrokenEqualityResolution` / `BrokenEqualityFactoring` / `BrokenDemodulation` / `BrokenAvatarSplit` | no legal application of the recorded rule between the recorded parents reproduces the recorded conclusion |
| `BrokenSatLearn` | a SatLearn lemma outside the two legal shapes (Spec 18 section 5) |
| `BrokenReductio` | the ConjectureLemma reductio shape fails |
| `BrokenTheoryLemma` | a TheoryLemma record claims parents |

## 3. The walk and the budget

**Walk.** `walk_proof_dag(store, refutation)` collects the reachable clause ids in one descending pass over the id range, marking ancestors (parents are strictly older than children, so one pass is exact — Spec 14 section 2). It reports `NonMonotonicDerivation` (naming the offending parent) and `UnreadableClause` as rejections. The TSTP writer's `reachable_proof_ids` delegates here and maps the walk rejections onto `CycleDetected` / `UnreadableClause` for its existing error vocabulary.

**Budget.** `verify_refutation_with_budget(context, store, refutation, budget)` charges one unit per walked id and **one unit per replayed rule attempt**; the production budget is `kKernelReplayBudget` (1_048_576 charged actions), injectable per CEP&CC 34.3 so tests exercise exhaustion on the production path (`rejects_budget_exhaustion` verifies with budget 1 and `Err(ReplayBudgetExhausted)`, then verifies the same proof with the production budget). Charging per attempt (not per step) is what makes the bound honest: a step whose replay enumerates many candidate pairs pays for each.

`verify_clause_step(context, store, id, budget)` verifies one clause outside a whole-proof walk (the clause-learning tests' entry point); it runs the same arm, so a single-step verdict equals the step's verdict inside a full verification.

## 4. The replay arms

The arms replay the **production** rule functions — `resolve`, `superpose`, `factor`, `equality_factor`, `equality_resolve`, `demodulate`, `try_split_with` — never a parallel reimplementation, and compare the replayed conclusion to the recorded one **modulo the loop's pipeline** (restandardize to a dense namespace, then dedupe exact literal repeats — the same `restandardize_clause` + dedupe the search applies before storage, Spec 08 section 6). Multiset equality is canonical-order equality on hash-consed atom pointers and polarities.

**The standardize-apart repair (closes CEP-1054).** The generator renames the active premise into the window above the given premise's variable count before every rule call (Spec 02 section 5). The kernel replays the same rename, and — the repair — replays the renamed premise at its **full literal count**. The pre-Phase-5 checker sliced the renamed buffer at the count the rename *returns*, which is the source clause's **variable** count: a ground premise (0 variables, several literals) was truncated to an empty slice and every resolution/superposition step over it was falsely rejected. Two executable consequences, both pinned:

- `resolution_replay_renames_apart`: premises `¬p(f(f(x0))) ∨ q(x0,x0)` and `p(f(x0))` (overlapping dense namespaces); the verbatim MGU binds `x0 := f(x0)` and hits the occurs check, while the renamed replay (`x1 := f(x0)`) reproduces the recorded resolvent `q(x0,x0)`.
- The superposition arms replay **both premise orders** (into-direction: renamed active equation into the given clause; from-direction: given equation into the renamed active clause) over every literal and non-root subterm position (`advance_path`), matching the generator's two superposition phases.

**Exact demodulation (closes CEP-1036).** A `Demodulation` step's parents are `[previous, rule]` (the CEP-1036 chain records one clause per rewrite step with the demodulating rule clause's id; the pre-Phase-5 single-record park survives only as the documented corruption fallback and is rejected as `UnrecordedRule`). The arm reads the rule clause's single positive unit equation, replays `demodulate` over every literal and non-root position of the chain predecessor, and requires the restandardized rewritten clause to match the recorded conclusion exactly per step. A tampered rule id, a wrong rule, or an unrecorded step cannot pass.

**AVATAR split replay.** The arm replays the production `try_split_with` on the parent and accepts when the recorded component matches **some restandardized component multiset** of the replayed decision. The pre-Phase-5 check compared pointer-identical literals, which falsely rejected components restandardized into their own dense namespaces (the variable namespaces of split components are not dense from 0 once a component is extracted); the replay compares multisets after restandardization, so the acceptance is namespace-invariant, exactly like the production activation path. The replay gate is the **finest legal gate** (`kKernelSplitReplayGate = 1`): the splitter's variable-connectivity partition is gate-independent (a gate only refuses a whole split, it never merges or splits cells), so every production component - recorded under any injectable `min_component_size >= 1` - is exactly one cell of the finest partition, which makes the acceptance criterion gate-free: no false accept, and no gate-mismatch false reject.

**SatLearn (the executable vocabulary check).** Both shapes of Spec 18 section 5, with the trust boundary made executable: every conclusion atom must be a 0-ary predicate **whose symbol id lies inside the reserved assertion range** `[assertion_base, assertion_base + assertion_count)` carried by `KernelOptions`. The production whole-proof path (`verify_refutation_with_budget`, and therefore `check_proof`) uses the empty range - the refutation DAG cannot contain SatLearn steps under the current protocol (staged lemmas are children of the refutation, Spec 18 section 3), so any SatLearn step that appears is rejected; the clause-learning diagnostics verify staged lemmas through `verify_clause_step_with_options` with the controller's configured range. A forged parentless lemma over user-declared 0-ary predicates is rejected (`forged_sat_learn_rejected_outside_vocabulary`).

**SatLearn.** Both shapes of Spec 18 section 5: conflict lemmas are all-negative 0-ary assertion atoms over an empty anchor parent; transfers are parentless 0-ary assertion atoms. Anything else is `BrokenSatLearn`.

**ConjectureLemma (the reductio check, from Spec 17 section 4).** Unchanged in content, moved into the kernel: `parent_count == 2`; parent 0 is a `ConjectureNegation` clause with the literal-wise complement of the lemma (multiset match); parent 1 is the empty clause; parent 0 is an ancestor of parent 1 (`ancestor_of`).

**Parentless introductions.** `Input`, `NegatedConjecture`, `StructuralInduction`, `WellFoundedInduction`, `ConjectureNegation` require `parent_count == 0` (existence is checked by the walk); `TheoryLemma` likewise (rejecting with its own reason).

**Deletion rules.** `ForwardSubsumption`, `BackwardSubsumption`, `SubsumptionResolution`, `TautologyDeletion`, `Condensation` are rejected outright: deletion removes clauses, it never derives a stored record.

The match over `InferenceRule` is exhaustive over its twenty variants — a new rule cannot compile without an arm (the CEP-0 discipline applied to soundness).

## 5. What the kernel does not verify

The kernel verifies **derivations**: that each recorded clause follows from its recorded parents by a legal application of the recorded rule. It does not re-prove the metatheory (the soundness of each rule is Spec 07's theorem set; the AVATAR protocol's soundness is Spec 12; the DRAT discipline covers the SAT engine's own derivations, Formal Spec 11; the SatLearn introduction discipline is Spec 18). The composition is the standard trusted-core argument: rules with machine-checked soundness proofs + shape-complete introduction bounds + an exhaustive, production-replaying verifier over the recorded DAG.

## 6. Integration

- `cold/proof_output/tstp.rs::check_proof` = the verdict mapping: `Valid` passes; `Invalid { clause_id, .. }` maps to `TstpError::InvalidStep(clause_id)` (the TSTP error vocabulary keeps its payload contract); `Err(ReplayBudgetExhausted)` maps to the new `TstpError::BudgetExhausted`.
- `render_verified_proof` keeps the verified-then-emitted ordering.
- The property tests' corruption paths (`corrupted_proof_rejected`) run through the kernel; the former structural demodulation acceptance is now the executable rejection `checker_rejects_unrecorded_demodulation`.

## 7. Evidence map

| Property | Executable pin |
|---|---|
| End-to-end refutation (resolution + demodulation chain) verifies | `unit/cold/kernel_test.rs::accepts_loop_refutation` |
| Broken resolution rejected, step named | `unit/cold/kernel_test.rs::rejects_broken_resolution` |
| Standardize-apart replay (occurs-check fixture) | `unit/cold/kernel_test.rs::resolution_replay_renames_apart` |
| Deletion-rule derivation rejected | `unit/cold/kernel_test.rs::rejects_deletion_rule_derivation` |
| Budget exhaustion is an error; production budget verifies | `unit/cold/kernel_test.rs::rejects_budget_exhaustion` |
| Non-monotonic derivation rejected, parent named | `unit/cold/kernel_test.rs::rejects_non_monotonic_derivation` |
| TSTP wrapper mapping (InvalidStep / pass-through) | `unit/cold/kernel_test.rs::tstp_wrapper_maps_rejections` |
| Single-step verdict equals whole-proof verdict | `unit/cold/kernel_test.rs::verify_clause_step_matches_walk` |
| Unrecorded demodulation rejected (CEP-1036 inversion) | `unit/cold/tstp_test.rs::checker_rejects_unrecorded_demodulation` |
| Every loop refutation formats and checks; corruption rejected | `property/tstp_property_test.rs::{every_refutation_formats_and_checks, corrupted_proof_rejected}` |
| Staged learning lemmas verify | `unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable` |
| Forged SatLearn over user predicates rejected; range check decides | `unit/cold/kernel_test.rs::forged_sat_learn_rejected_outside_vocabulary` |
