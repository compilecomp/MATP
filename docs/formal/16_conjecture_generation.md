# Formal Spec 16: Automated Conjecture Generation (Bounded Templates and Refutation Filtering)

## 1. Scope and deliverable

This specification is normative for `hot/conjecture/` (revised build order Phase 4). The deliverable is the **harvest**: a bounded, deterministic, speculative pass that (a) collects the recent derived unit equations, (b) enumerates candidate lemmas from fixed syntactic templates, (c) filters every candidate through a bounded mini refutation of its negation, and (d) imports each **proved** lemma into the main search together with its complete reductio subproof. The feature implements the SOTA "speculative lemma" speedup (Vampire's internal theory exploration, iProver's instance generation, the IsaCoSy/Hipster bounded-synthesis school) under the CEP&CC discipline: every budget is a named constant, every enumeration order is fixed, and nothing is learned, weighted by statistics, or hidden (zero ML).

## 2. Soundness position (what the filter is for)

The current templates (section 4) generate conjectures that are semantically **implied** by their sources (symmetry and transitivity are equality consequences; constructor instances are substitution instances). The refutation filter is nevertheless **mandatory and load-bearing**, for three reasons fixed here:

1. **Proof recording.** The mini refutation IS the lemma's proof; the import carries it clause by clause into the main derivation DAG (Spec 17 section 3), so every harvested lemma ships with an independently checkable subproof — a lemma without its refutation is never added.
2. **Cost bounding of false candidates.** The filter is what makes the feature sound **independent of template quality**: a future template (or a driver-supplied one) that generates false conjectures pays exactly `kConjectureRefuteInferences` and discards (the negation is satisfiable; the mini run saturates or gives up). The soundness argument never relies on template cleverness.
3. **Search acceleration, not discovery.** The lemma enters the main passive set **now**, with its age and weight, instead of being re-derived later at a possibly much higher inference cost; the filter's budget is the price of that priority.

## 3. The harvest pipeline

### 3.1 Unit collection

The window scan walks clause ids **descending** from the store's next id and keeps a clause when it is (i) a single-literal clause, (ii) a **positive** equality atom, and (iii) derived by a genuinely inference-producing rule (the T1/T2 source filter excludes `Input`, `NegatedConjecture`, the theory schemes, `ConjectureNegation`, and `ConjectureLemma` — the last exclusion breaks the harvest cycle: a lemma's own subproof is never re-harvested). The scan stops when `kConjectureTransitivityWindow` units are collected; the window is then reversed to ascending id order. The scan is bounded by the id span; every read is bounds-checked; corrupt records stop the scan with what the window holds (the harvest's stats make the short scan visible).

### 3.2 Enumeration order (determinism)

Candidates enumerate as a pure function of the window (and, for T3, the declaration):

1. **T1 (symmetry)**, per unit ascending: the unit `(t1 = t2)` yields the candidate `(t2 = t1)`; reflexive units are skipped.
2. **T2 (transitivity)**, per ordered pair (older `A`, newer `B`): `A.right == B.left` (hash-consed pointer identity — Spec 01 section 3 makes pointer identity structural identity) yields `(A.left, B.right)`; then `B.right == A.left` yields `(B.left, A.right)`; reflexive results are skipped.
3. **T3 (constructor instances)**, only when the driver's pre-search pass supplies the induction declaration (Spec 15): every positive unit equation with at least one and at most `kConjectureInstanceVariables` distinct variables, from the input range (axioms and schemes) and the window's derived units, instantiated at the two canonical patterns — all-`zero` and all-`succ(zero)` — through one trail-disciplined substitution (bind-all, apply, unwind); ground units and reflexive instances are skipped.

Duplicates are suppressed by hash-consed atom identity, and the list is capped at `kMaxConjectureCandidates` — a deterministic prefix cut (Law 4: the harvest's stats report candidates tried).

### 3.3 The mini refutation (the filter)

For one candidate `phi` (a positive unit-equation literal):

1. A **fresh mini search space** is constructed over the **same arena** with the `MiniCapacities` budgets (injectable per CEP&CC 34.3; `MiniCapacities::production()` supplies the `kConjecture*` constants). Construction failure (arena pressure) aborts the whole harvest (`CandidateOutcome::Aborted`) — speculation never kills the search.
2. The main space's input range `[kFirstClauseId, kFirstClauseId + input_count)` is re-added **in order**, so mini input `i` maps to main id `kFirstClauseId + i` (the trivial translation the import relies on). The range is exactly the axiom set (inputs plus Spec 15 schemes; the plain saturate loop takes no AVATAR materializations between harvests).
3. The candidate's negation enters as a `ConjectureNegation` assumption premise (`add_assumption_clause`).
4. `saturate` runs under `refute_inferences` (production: `kConjectureRefuteInferences`) with harvesting disabled (`conjecture: false` — no nested speculation) and a never-stop callback (the inference budget is the only stop).
5. `Theorem` → the ancestry check and the import (below); every other outcome → `Discarded`.

### 3.4 The isolation theorem

**Theorem (failure isolation).** A discarded or aborted candidate leaves the main space byte-identical.

*Proof.* The mini space is a separate `ClauseStore`, passive set, and active set; the only shared structure is the arena (append-only) and the term store (hash-consing is idempotent). The filter reads main-store clauses and writes only to the mini space until the import; the import runs only on the `Theorem` path. Arena consumption is bounded by the named capacities times the candidate count (the static assertion in `config/limits.rs` fixes the total speculative work, including the inference bound, below `kMaxInferences`). ∎

`property/conjecture_property_test.rs::harvest_preserves_existing_clauses` verifies the theorem executably (ids, literal counts, and derivation rules of all pre-existing clauses unchanged).

### 3.5 The vacuous-refutation rejection

A mini run may refute **without using the negation** (the axioms alone are contradictory). Such a "proof" would make the lemma uncheckable (Spec 17's reductio check requires the negation in the subproof), so the import first computes the empty clause's ancestry closure and rejects the candidate when the negation is **not** contained. The main search will refute on its own from the same contradictory axioms. `unit/hot/conjecture_test.rs::vacuous_refutation_discarded` pins the rejection.

### 3.6 The import and the reductio rule

On a non-vacuous `Theorem`:

1. The reachable set (ancestry closure of the mini empty clause) is computed over the mini id range (fixed bitmap, DFS stack, both bounded by the id-table capacity).
2. The ascending walk is topological (mini ids are monotonic; Spec 14 section 2's argument), so every parent is translated before its child: mini **inputs** translate to their main originals (the order-preserving re-add); every other reachable clause is recreated in the main store through `add_proof_clause` — proof-only, never entering the main passive set (or the main loop would saturate on its own lemmas' subproofs) — with the **same rule and age** and the **translated parents**; the derivation substitution field stays `kInvalidSubstitutionOffset` everywhere (the production discipline: derivations never record trail offsets; the replay checker recomputes).
3. The lemma `phi` enters the main passive set via `add_derived_clause` with the `ConjectureLemma` rule and parents `[imported negation, imported empty clause]`.

**Theorem (soundness of the import).** The added lemma is entailed by the main space's axiom range.

*Proof.* The imported subproof derives the empty clause from the axiom range plus the negation premise `~phi`, using only the production inference rules (each replayable by the checker, Spec 14/17). By the soundness of refutational resolution, the axiom range plus `~phi` is unsatisfiable; classically, the axiom range entails `phi`. The reductio step (the `ConjectureLemma` rule) is exactly this inference, and its mechanical check (Spec 17 section 4) accepts precisely the shape this import produces. ∎

`property/conjecture_property_test.rs::only_proved_lemmas_added` verifies executably, over random problems, that every `ConjectureLemma` clause in the store passes the reductio oracle.

## 4. Schedule and budgets

| Bound | Constant | Semantics |
|---|---|---|
| Harvest interval | `kConjectureHarvestInterval` | Every N loop iterations, in-loop, when `options.conjecture` is set |
| Total in-loop harvests | `kMaxConjectureHarvests` | Guarded in the hook; the driver's pre-search pass is the +1 |
| Candidates per harvest | `kMaxConjectureCandidates` | The enumeration's deterministic prefix cut |
| T2 window | `kConjectureTransitivityWindow` | The recent-derivation front |
| T3 variable cap | `kConjectureInstanceVariables` | Instantiation eligibility |
| Mini capacities | `kConjecturePassive/Active/TreeNodes/TreeEntries/PoolWords/IdOffsets` | The mini space's memory bounds |
| Mini inference budget | `kConjectureRefuteInferences` | The per-candidate work bound |

The **total speculative work** — `(kMaxConjectureHarvests + 1) * kMaxConjectureCandidates * kConjectureRefuteInferences` — is asserted (compile time and runtime mirror) to stay within `kMaxInferences` (CEP&CC 23: the cost is named, measurable, and bounded by the main budget). The in-loop hook appends only to the passive set, which the loop reads at the next select, so the active-set consistency argument of Spec 08 is untouched.

## 5. Determinism

The window scan (fixed direction, fixed filters), the enumeration (fixed template and pair order, hash-consed identity tests), the mini run (the saturate loop's own determinism, Spec 08 section 7, under fixed options), and the import (ascending walk) are pure functions of the main space state. `unit/hot/conjecture_test.rs::enumeration_is_deterministic`, `property/conjecture_property_test.rs::harvest_deterministic_double_run`, and `fuzz/conjecture_fuzz_test.rs::random_harvests_are_deterministic` pin the discipline at all three levels.

## 6. What the feature is not

The harvest is **not** a completeness mechanism (the templates are heuristics in the classical sense — fixed, deterministic, and cheap, but not complete); it is **not** an assumption mechanism (only refutation-proved lemmas are added); and it is **not** a learning mechanism (nothing about the search is remembered between harvests beyond the lemmas themselves, which are ordinary derived clauses with complete proofs).
