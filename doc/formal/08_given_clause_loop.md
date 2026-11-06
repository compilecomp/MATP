# Formal Specification 08: The Given-Clause Loop, the Clause Database, and the Feature-Vector Filter

## Abstract

This document is the normative reference for `hot/search/{passive,active,given_clause}.rs` and `hot/index/feature_vector.rs`, cited by their `CEP:HPC-PASS-LEGALITY` fields (design 8.4, 9.3, 10.3, 15.1-15.3, 20; design 26 build order "Given-clause loop (bounded)"). It defines the passive/active clause database, the matching-based subsumption deletion, the feature-vector subsumption filter, the fairness theorem of the selection strategies, the resumable inference-generation machine, and the bounded loop contract with its outcome soundness. Inputs are the axiom clause set and injected budgets with a stop callback; outputs are the `SearchOutcome` verdicts (Theorem, Saturated, GaveUp) with `SearchStats`. References: Bachmair & Ganzinger 2001 (saturation framework); Formal Specs 03 (orderings), 07 (rules).

## Formal Definitions

### 1. The clause database

**Passive set.** A binary min-heap over (priority, clause_id) where priority is fixed at push: `age * kSelectionRatioScale / max(weight, 1)` for the default AgeWeightRatio strategy, `weight` for WeightOnly, `age` for AgeOnly (design 15.2). The clause-id tiebreak makes the order total and deterministic.

**Active set.** A dense slot array (swap-remove on deletion) plus three indexes: the atom discrimination tree (every literal of every active clause, payload = clause offset + literal index), the rule tree (left sides of positive equations, payload + unit flag), and the feature-vector index (design 8.4/9). Insertion happens when the clause is selected as given (design 15.1 step 2); deletion by backward subsumption removes the tree payloads and swaps the last slot into the hole.

**Waiting set.** AVATAR's (design 8.4) — Phase 4 (ticket CEP-1011).

### 2. Subsumption

Subsumption is the matching-based decision of Spec 07 section 8. Forward subsumption (an active clause subsumes the given clause → discard) and backward subsumption (the given clause subsumes active clauses → remove) both run at given time.

### 3. The feature-vector filter (design 9.3)

**Feature vector.** For clause C: the multiset counts of function/predicate symbol occurrences in C's atoms (variables excluded), stored as sorted (symbol, count) pairs, plus the literal count.

**Theorem (filter soundness for injective subsumption).** If C subsumes D through an injective literal mapping (each literal of Cσ matched to a DISTINCT literal of D), then |C| ≤ |D| and occ(f, C) ≤ occ(f, D) for every symbol f. Hence a violated dominance or literal-count check rejects subsumption without false negatives. *Proof.* With an injective mapping, distinct literals of C map to distinct literals of D; σ instantiates variables with terms (adding symbols, never removing them), so each symbol occurrence of C has a distinct corresponding occurrence in D, and the literal counts obey the injection. ∎ Clauses with more distinct symbols than `kFeatureVectorSlots` carry the truncated flag and pass every filter (sound degradation: truncation only removes evidence of violation).

**Collapse restriction (documented false-negative class).** The matching-based verifier of Spec 07 section 8 allows literal reuse across the target (set semantics: C = P(x) ∨ P(y) subsumes D = P(a) ∨ Q(b) with both x and y mapped to a). Under collapse the occurrence counts can violate dominance (occ(P, C) = 2 > 1 = occ(P, D)), so this filter — and the verifier's own |C| ≤ |D| guard — reject some reuse-subsumptions. This is the standard injective-subsumption restriction: it loses deletion opportunities (a completeness reduction in simplification power only, never in soundness); the filter property test verifies the ground/injective case where collapse cannot arise.

### 4. Selection fairness

**Theorem (fairness of the strategies).** AgeOnly is unconditionally fair (every clause is selected after finitely many others). AgeWeightRatio is fair under bounded weight growth: a clause's priority is fixed at birth, so only clauses born with smaller priority can precede it; weights are positive and bounded by the symbol-weight sums, so under bounded weight growth only finitely many clauses precede any given one. WeightOnly is not fair in isolation (documented: heavy clauses may starve; the inference and time budgets bound the run regardless).

**Fairness implies completeness**: with a fair strategy and the ordered calculus (Spec 07), if the empty clause is derivable the loop derives it (saturation framework, BG 2001 §4); budget exhaustion pre-empts this guarantee with an honest GaveUp.

### 5. Active-set invariants

(I1) Every live slot's clause is indexed in the atom tree with one payload per literal. (I2) Every unit-equation clause's equation literal is indexed in the rule tree with the unit flag. (I3) Every tree payload belongs to a live slot. (I4) The active array does not change during one given clause's generation (the generator's scans stay consistent; backward subsumption runs before activation).

**Retrieval superset argument.** The discrimination tree's flat-sequence retrieval matches only equal-length flattenings, so it cannot serve as a complete candidate source for unification or subsumption retrieval (a stored p(x) is invisible to the query p(f(a))). The loop therefore scans the active array with constant prefilters (head symbol, polarity) as its candidate source; the trees are maintained for their index role and future iterator work (ticket CEP-1027).

### 8. The selection weight (design 15.3)

`weight(C) = Σ_{nodes n in C's atoms} symbol_weight(n)` with variables contributing `kSelectionVariableWeight` (0). This is the *selection* weight, distinct from the cached clause weight (which counts variables at the KBO weight for ordering purposes).

## Algorithm

The given-clause loop (`hot/search/given_clause.rs::saturate<F: Fn(u64) -> bool>`):

1. Budget checks: the injected stop callback fires every `kBudgetCheckInterval` iterations (CEP-1005) → GaveUp(Timeout); the inference budget → GaveUp(InferenceBudget); the capacity family — arena or term-table exhaustion surfacing from the rules with honest kinds (CEP-1056), clause-store capacity, active-set capacity — → GaveUp(MemoryBudget), never Err: a bound firing is a legal bounded outcome, and the saturate wrapper converts the family in one place so every propagation site inside the loop is covered.
2. Pop the given clause (or continue deferred generation). Empty clause → Theorem.
3. Simplify: tautology deletion, bounded demodulation rounds. A rewritten clause is stored as a new record (records are immutable) and re-queued.
4. Forward subsumption discards; backward subsumption removes.
5. Activate; generate; conclusions (deduplicated, re-standardized, flag-computed) enter the passive set.
6. Passive empty → Saturated.

The generation machine (design 10.3):

**Phase machine.** For one given clause: Factoring (ascending pairs i < j) → EqualityRules (equality resolution singles, then equality factoring pairs i ≠ j) → Resolution (each given literal × each active literal, complementary polarity + head match) → SuperpositionInto (each subterm position of the given literals × each active positive equation, head prefilter) → SuperpositionFrom (each positive equation of the given clause × each subterm position of each active literal). The cursor (phase, literal, partner slot, partner literal, path) makes generation resumable across loop iterations.

**Budgets.** `kMaxInferencesPerClause` conclusions per given clause: buffer-full defers within the budget (the buffer drains into the passive set and the cursor resumes exactly at the interrupted pair — the advance-after-completion discipline: every cursor component — pair, partner literal, and subterm path — moves only after the candidate is fully processed; a deferral with nothing stored keeps the cursor so the resumed call re-attempts exactly that candidate, and a deferral after a stored conclusion advances first so the resumed call never re-emits it, CEP-1056); budget exhaustion ends the clause's generation with the remainder counted as dropped. Drops are counted, never silent.

**Bound-error drop policy (CEP-1050).** A conclusion whose materialization exceeds a term bound (`DepthExceeded`, `WeightExceeded`) or a shape bound (`ConclusionTooLong`, `VariableBudgetExceeded`) is dropped and counted: the rule layer unwinds the pre-unification trail on every `Err` (the `builder.rs` restore helpers), the generator advances the cursor and increments `cursor.dropped` (aggregated into `stats.dropped`), and the scan resumes — a deep or wide term can no longer abort the search with `Err`; the search reaches a legal outcome (`Saturated`, or `GaveUp` with the budget that fired). The `Err` catch-all still surfaces structural corruption loudly; `ArenaFull`/`TableFull` surface honestly and convert to `GaveUp(MemoryBudget)` (step 1).

**Outcome soundness.** Theorem ⇒ the empty clause has a derivation over sound rules (Spec 07) ⇒ the input set is unsatisfiable. Saturated ⇒ every selected clause had its budgeted inferences computed under a fair strategy ⇒ (no budget fired) no derivation of the empty clause exists among the processed closure. GaveUp ⇒ the named budget fired; nothing is claimed.

Time per iteration is the generation cost of Spec 07 plus the subsumption scans; space is the clause store plus the passive heap under the configured caps. Assumptions: strategies satisfy the fairness preconditions of section 4 when completeness is claimed; budgets are finite and the stop callback is deterministic.

## Invariants

1. Active-set index consistency: I1 through I4 of section 5 hold before and after every loop iteration (the atom and rule trees mirror the live slots; generation sees a frozen active array).
2. Filter soundness: the feature-vector filter rejects no injective subsumption (Theorem of section 3; `tests/property/discrimination_property_test.rs` complement, `tests/unit/hot/feature_vector_test.rs`).
3. Selection determinism: the passive order is total (priority, clause-id tiebreak), a pure function of the push sequence (section 1, CEP&CC 38.10).
4. Budget honesty: every GaveUp names the budget that fired; capacity exhaustion is converted to GaveUp(MemoryBudget) and never escapes as Err (loop contract step 1, CEP-1056).
5. No silent drops: generation drops are counted in the stats; every stored conclusion is emitted exactly once under the advance-after-completion discipline (section 6, CEP-1056; `tests/bug_first_negative_selection.rs`, `tests/unit/hot/given_clause_test.rs`).
6. Outcome soundness: Theorem and Saturated verdicts are logically correct; GaveUp claims nothing (Algorithm, outcome soundness; property suite `tests/property/given_clause_property_test.rs`).
7. Immutable records: simplification stores rewritten clauses as new records and re-queues them; stored clauses are never mutated in place (loop contract step 3).

## Integration Points

Depends on:

- `hot/inference/` (Specification 07) for all rule applications inside the generation machine.
- `hot/search/passive.rs` (`PassiveHeap::priority_of(&self, age: u32, weight: u32) -> u64`, `PassiveHeap::push`) and `hot/search/active.rs` (`ActiveSet::insert`, payload packing `pack_payload(offset: u32, literal_index: u16, unit: bool) -> u64`) for the database of section 1.
- `hot/index/feature_vector.rs` (`FeatureVectorIndex::may_subsume(&self, candidate: FeatureVector, target: FeatureVector) -> bool`) for the forward/backward subsumption prefilter.
- `config/limits.rs` (`kMaxInferencesPerClause`, `kBudgetCheckInterval`, `kFeatureVectorSlots`, `kSelectionRatioScale`) for the budgets and strategy constants.

Depended on by:

- `cold/portfolio/manager.rs`, which runs `saturate` under wall-clock slices in worker threads (Specification 13).
- `hot/avatar/controller.rs`, which drives the loop per split stack and re-queues components (Specification 12).
- `hot/conjecture/filter.rs`, which runs a bounded instance of the same loop as the mini refutation space (Specification 16).
- `hot/induction/` and `hot/search/given_clause.rs::saturate_probe_forward`, the probe entry used by the induction and conjecture harnesses.

## Known Limitations

- WeightOnly selection is not fair in isolation (section 4); fairness-dependent completeness claims require AgeOnly or bounded-weight AgeWeightRatio.
- Candidate retrieval scans the active array with prefilters; indexed retrieval is open under ticket CEP-1027 and the remaining index types under CEP-1029.
- Conjecture-distance and set-of-support strategies and the config/strategy.rs module of design 15.2 are not implemented (ticket CEP-1035); the three deterministic strategies of section 1 are delivered.
- Term-bound conclusions are dropped and counted (CEP-1050), so the dropped-candidate work is spent and never retried within the same given clause; a family whose members all exceed the caps silently shrinks the saturation closure (the honest accounting is in `stats.dropped`). The simplification path's demodulation materialization failure remains a loud structural error (Spec 07 Known Limitations).
