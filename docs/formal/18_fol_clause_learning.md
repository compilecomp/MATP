# Formal Spec 18: Bidirectional FOL Clause Learning over AVATAR

## 1. Scope

This specification fixes the clause-learning feature of the AVATAR bridge (Formal Spec 12): the one-shot reservation of a bounded assertion-symbol space, the staging of first-order conflict lemmas, the transfer of abstraction-solver learnt clauses into first-order clauses, and the budgets and policy bounds that keep every path deterministic, bounded, and counted (CEP&CC 23, 22.10, Law 4). The feature is **opt-in and off by default**; every budget is a named constant in `config/limits.rs`; zero machine learning of any kind is involved — "learning" here is the standard automated-deduction term for recording logical consequences as new clauses (conflict-driven clause learning, CDCL).

The two directions:

- **FOL ← SAT (conflict lemma staging).** Each abstraction conflict round bans the component conjunction used by the refutation (Spec 12 Lemma 2). The same ban clause is *staged* in the first-order store as a `SatLearn` lemma over 0-ary assertion atoms, anchored at the round's refuting empty clause.
- **FOL ← SAT (learnt transfers).** Each abstraction solver learnt clause (a DRAT-disciplined consequence of the abstraction's problem clauses) is transferred into a first-order `SatLearn` clause over the mapped assertion atoms and enters the passive set.

There is deliberately **no SAT ← FOL direction** in this phase: the abstraction's problem clauses are exactly the split disjunctions, and the first-order search contributes consequences over the original signature, which the abstraction cannot represent. The extension is ticketed (CEP-1056).

## 2. The assertion-atom convention

The FOL copies speak only through **assertion atoms**: 0-ary predicate applications whose symbols come from the one-shot reservation

```
reserve_assertion_symbols(count) -> base
```

which declares the deterministic names `mapt_assertion_0 .. mapt_assertion_{count-1}` as 0-ary predicates back-to-back, so that **assertion atom for SAT component slot `i` is the symbol `base + i`** (the density invariant D1 below). The reservation is:

- **R1 (bounded):** `count <= kAvatarMaxAssertionSymbols`; anything larger (and `count == 0`) returns `BuilderError::AssertionBudget`.
- **R2 (one-shot):** a second reservation on the same builder returns `AssertionBudget`; the controller validates the same bound at construction (`ControllerError::InvalidOptions`).
- **R3 (collision-refusing):** if any `mapt_assertion_<i>` name is already declared with any signature, the reservation fails; `declare_symbol`'s idempotence for identical signatures would otherwise silently break density.
- **R4 (dense and deterministic):** the symbols are declared consecutively, so slot `i` maps to `base + i`; names are `mapt_assertion_<slot>` by the single builder `assertion_symbol_name`.

Interpretation (the Spec 12 reading): the assertion atom `A_i` holds in a model of the extended clause set exactly when the abstraction assigns component slot `i` true. Because the atoms are **fresh 0-ary predicates not occurring in any input clause**, adding assertion-atom clauses never changes satisfiability of the first-order clause set over the original signature (every model of the inputs extends to a model of the inputs plus any assertion-atom clause by choosing the assertion interpretation freely, and vice versa by projection). This is the soundness argument for both staging and transfer: **the extension is conservative over the input signature.**

## 3. Conflict lemma staging

`add_conflict_lemma_from_buffer(space, context, used, refutation_id)` stages the FOL copy of the ban clause currently held in the controller's conflict-slot buffer (written by `plan_conflict`, Spec 12 section 5):

- **S1 (shape):** the staged clause has `used` literals, all negative, each the assertion atom of one deduplicated used slot; the derivation is `SatLearn` with `parent_count == 1` and parent 0 = `refutation_id` (the round's refuting empty clause — the "empty anchor").
- **S2 (all-or-nothing):** if any used slot is at or above `learning_symbol_count` (unnameable), the whole staging is skipped. A partial ban clause would be unsound (it would ban less than the refutation used); staging is never truncated.
- **S3 (staged, not searched):** the record is stored but **never pushed to the passive set**. The assertion atoms are foreign to the first-order search; the lemma's role is the recorded derivation DAG (and the kernel-verifiable proof shape), not inference fuel.
- **S4 (bounded and counted):** staging requires `learning_lemmas < learning_max_lemmas` (production default `kLearningMaxFolLemmas`) and `used <= kMaxClauseLiterals`; every skip increments `stats.learning_skipped` (Law 4).

**Soundness of the staged proposition.** The SAT ban clause `¬a_{i1} ∨ ... ∨ ¬a_{ik}` is entailed by the problem clauses plus the refutation's justification (Spec 12 Lemma 2). The staged FOL clause is the same proposition over `A_{i1}..A_{ik}`; by section 2's conservativity it is sound to record, and by S3 it cannot interfere with the first-order search.

## 4. Learnt transfers

`transfer_learnts(space, context)` runs after every **unconditional** abstraction solve that returns `Satisfiable` (the initial round and each post-conflict round; assumption solves do not transfer):

- **T1 (monotone cursor):** the controller keeps `transfer_cursor`, the registry entry index one past the last considered entry. A call enumerates entries `[cursor, entry_count)`, so every registry entry is considered at most once, deterministically in registration age order.
- **T2 (policy):** an entry transfers only when it is a live learnt (`kSatClauseFlagLearnt`, not `kSatClauseFlagDeleted`, not a tombstone) with `lbd <= kLearningMaxTransferLbd` and `length <= kLearningMaxTransferLiterals` (the named quality and size bounds).
- **T3 (naming):** every literal's variable must be below `learning_symbol_count` (all-or-nothing, as S2); the FOL literal is the assertion atom `base + var` with the SAT literal's polarity.
- **T4 (shape):** the transferred clause's derivation is `SatLearn` with `parent_count == 0` (the SAT-side derivation is covered by the SAT engine's own DRAT discipline, Formal Spec 11).
- **T5 (searched):** the transferred clause **enters the passive set** (unlike S3): it is a sound recorded consequence, its atoms are fresh, and the search may consume it as it consumes any recorded clause.
- **T6 (bounded and counted):** transfers are capped by `learning_max_transfers` (production default `kLearningMaxLearntTransfers`); budget exhaustion stops the sweep **without** advancing the cursor past the deferred entries (retried on the next unconditional solve) and counts one bounded skip; every policy or naming skip advances the cursor (one-shot) and increments `stats.learning_skipped`.

## 5. The kernel's SatLearn arm

The certified kernel (Formal Spec 19) verifies a `SatLearn` step as:

| Shape | Acceptance condition |
|---|---|
| Conflict lemma (`parent_count == 1`) | every conclusion literal is a 0-ary predicate atom (the assertion-atom form), the conclusion is **all-negative**, and parent 0 is an **empty clause** (the empty anchor), strictly older than the lemma. |
| Transfer lemma (`parent_count == 0`) | every conclusion literal is a 0-ary predicate atom. |
| Anything else | rejected (`BrokenSatLearn`). |

The name-prefix discipline (`mapt_assertion_`) is enforced on the introduction side by R3/R4 (the only production path that can declare 0-ary predicates with that prefix is the reservation), and the kernel's shape check keeps every recorded lemma inside that vocabulary. The trust boundary is therefore: *introduction* is bounded and named (R1–R4, S1–S4, T1–T6); *verification* is shape-complete (the kernel arm above).

## 6. Budgets and constants

| Constant | Value | Role |
|---|---|---|
| `kAvatarMaxAssertionSymbols` | 4_096 | the reservation bound (R1) and the controller's construction check |
| `kLearningMaxFolLemmas` | 1_024 | staged conflict lemmas per run (S4) |
| `kLearningMaxLearntTransfers` | 256 | transferred learnts per run (T6) |
| `kLearningMaxTransferLiterals` | 16 | per-transfer literal bound (T2) |
| `kLearningMaxTransferLbd` | 8 | per-transfer LBD bound (T2) |

All five are pinned by the static-assertion block of `config/limits.rs`; the controller options are injectable per CEP&CC 34.3 with these as production defaults, and learning is disabled while `learning_symbol_count == 0` (the default).

## 7. Determinism

Everything in this specification is a deterministic function of the search state: the conflict-slot buffer is `plan_conflict`'s deduplicated output (index order), the staging and transfer loops iterate ascending indices, the cursor is monotone, and no clock, address, or randomness participates (CEP&CC 38.10). Two identical runs stage and transfer identical clauses in identical order, and the counters are equal.

## 8. Evidence map

| Property | Executable pin |
|---|---|
| Staging shape and kernel verification | `unit/hot/avatar_learning_test.rs::conflict_lemma_staged_and_verifiable` |
| Staging budget, skip counting | `unit/hot/avatar_learning_test.rs::conflict_lemma_budget_enforced` |
| Transfer budget and deferral | `unit/hot/avatar_learning_test.rs::transfer_budget_enforced` |
| Transfer policy (length, LBD, naming) | `unit/hot/avatar_learning_test.rs::transfer_policy_filters` |
| Transfer enters the passive set; record shape | `unit/hot/avatar_learning_test.rs::transfer_learnts_enter_passive` |
| Disabled by default | `unit/hot/avatar_learning_test.rs::learning_disabled_by_default` |
| Reservation bound, one-shot, density, collision refusal | `unit/cold/symbol_table_builder_test.rs::assertion_reservation_bounded` |
| Kernel SatLearn arm (both shapes) | `cold/kernel/kernel.rs` SatLearn arm; `unit/cold/kernel_test.rs` |
