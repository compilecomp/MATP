# Formal Specification 08: The Given-Clause Loop, the Clause Database, and the Feature-Vector Filter

Version: 0.1
Status: complete for the Phase 3 scope (design 8.4, 9.3, 10.3, 15.1-15.3, 20; design 26 build order "Given-clause loop (bounded)")
Role: normative reference for `hot/search/{passive,active,given_clause}.rs` and `hot/index/feature_vector.rs`; cited by their `CEP:HPC-PASS-LEGALITY` fields.
References: design 8.4 (clause database), 9.3 (feature vectors), 10.3 (generation strategy), 15.1-15.3 (search control), 20 (budgets); Bachmair & Ganzinger 2001 (saturation framework); Formal Specs 03 (orderings), 07 (rules).

## 1. The clause database

**Passive set.** A binary min-heap over (priority, clause_id) where priority is fixed at push: `age * kSelectionRatioScale / max(weight, 1)` for the default AgeWeightRatio strategy, `weight` for WeightOnly, `age` for AgeOnly (design 15.2). The clause-id tiebreak makes the order total and deterministic.

**Active set.** A dense slot array (swap-remove on deletion) plus three indexes: the atom discrimination tree (every literal of every active clause, payload = clause offset + literal index), the rule tree (left sides of positive equations, payload + unit flag), and the feature-vector index (design 8.4/9). Insertion happens when the clause is selected as given (design 15.1 step 2); deletion by backward subsumption removes the tree payloads and swaps the last slot into the hole.

**Waiting set.** AVATAR's (design 8.4) — Phase 4 (ticket CEP-1011).

## 2. Subsumption

Subsumption is the matching-based decision of Spec 07 section 8. Forward subsumption (an active clause subsumes the given clause → discard) and backward subsumption (the given clause subsumes active clauses → remove) both run at given time.

## 3. The feature-vector filter (design 9.3)

**Feature vector.** For clause C: the multiset counts of function/predicate symbol occurrences in C's atoms (variables excluded), stored as sorted (symbol, count) pairs, plus the literal count.

**Theorem (filter soundness for injective subsumption).** If C subsumes D through an injective literal mapping (each literal of Cσ matched to a DISTINCT literal of D), then |C| ≤ |D| and occ(f, C) ≤ occ(f, D) for every symbol f. Hence a violated dominance or literal-count check rejects subsumption without false negatives. *Proof.* With an injective mapping, distinct literals of C map to distinct literals of D; σ instantiates variables with terms (adding symbols, never removing them), so each symbol occurrence of C has a distinct corresponding occurrence in D, and the literal counts obey the injection. ∎ Clauses with more distinct symbols than `kFeatureVectorSlots` carry the truncated flag and pass every filter (sound degradation: truncation only removes evidence of violation).

**Collapse restriction (documented false-negative class).** The matching-based verifier of Spec 07 section 8 allows literal reuse across the target (set semantics: C = P(x) ∨ P(y) subsumes D = P(a) ∨ Q(b) with both x and y mapped to a). Under collapse the occurrence counts can violate dominance (occ(P, C) = 2 > 1 = occ(P, D)), so this filter — and the verifier's own |C| ≤ |D| guard — reject some reuse-subsumptions. This is the standard injective-subsumption restriction: it loses deletion opportunities (a completeness reduction in simplification power only, never in soundness); the filter property test verifies the ground/injective case where collapse cannot arise.

## 4. Selection fairness

**Theorem (fairness of the strategies).** AgeOnly is unconditionally fair (every clause is selected after finitely many others). AgeWeightRatio is fair under bounded weight growth: a clause's priority is fixed at birth, so only clauses born with smaller priority can precede it; weights are positive and bounded by the symbol-weight sums, so under bounded weight growth only finitely many clauses precede any given one. WeightOnly is not fair in isolation (documented: heavy clauses may starve; the inference and time budgets bound the run regardless).

**Fairness implies completeness**: with a fair strategy and the ordered calculus (Spec 07), if the empty clause is derivable the loop derives it (saturation framework, BG 2001 §4); budget exhaustion pre-empts this guarantee with an honest GaveUp.

## 5. Active-set invariants

(I1) Every live slot's clause is indexed in the atom tree with one payload per literal. (I2) Every unit-equation clause's equation literal is indexed in the rule tree with the unit flag. (I3) Every tree payload belongs to a live slot. (I4) The active array does not change during one given clause's generation (the generator's scans stay consistent; backward subsumption runs before activation).

**Retrieval superset argument.** The discrimination tree's flat-sequence retrieval matches only equal-length flattenings, so it cannot serve as a complete candidate source for unification or subsumption retrieval (a stored p(x) is invisible to the query p(f(a))). The loop therefore scans the active array with constant prefilters (head symbol, polarity) as its candidate source; the trees are maintained for their index role and future iterator work (ticket CEP-1027).

## 6. The generation strategy (design 10.3)

**Phase machine.** For one given clause: Factoring (ascending pairs i < j) → EqualityRules (equality resolution singles, then equality factoring pairs i ≠ j) → Resolution (each given literal × each active literal, complementary polarity + head match) → SuperpositionInto (each subterm position of the given literals × each active positive equation, head prefilter) → SuperpositionFrom (each positive equation of the given clause × each subterm position of each active literal). The cursor (phase, literal, partner slot, partner literal, path) makes generation resumable across loop iterations.

**Budgets.** `kMaxInferencesPerClause` conclusions per given clause: buffer-full defers within the budget (the buffer drains into the passive set and the cursor resumes exactly at the interrupted pair — the advance-after-completion discipline: every cursor component — pair, partner literal, and subterm path — moves only after the candidate is fully processed; a deferral with nothing stored keeps the cursor so the resumed call re-attempts exactly that candidate, and a deferral after a stored conclusion advances first so the resumed call never re-emits it, CEP-1056); budget exhaustion ends the clause's generation with the remainder counted as dropped. Drops are counted, never silent.

## 7. The loop contract

1. Budget checks: the injected stop callback fires every `kBudgetCheckInterval` iterations (CEP-1005) → GaveUp(Timeout); the inference budget → GaveUp(InferenceBudget); the capacity family — arena or term-table exhaustion surfacing from the rules with honest kinds (CEP-1056), clause-store capacity, active-set capacity — → GaveUp(MemoryBudget), never Err: a bound firing is a legal bounded outcome, and the saturate wrapper converts the family in one place so every propagation site inside the loop is covered.
2. Pop the given clause (or continue deferred generation). Empty clause → Theorem.
3. Simplify: tautology deletion, bounded demodulation rounds. A rewritten clause is stored as a new record (records are immutable) and re-queued.
4. Forward subsumption discards; backward subsumption removes.
5. Activate; generate; conclusions (deduplicated, re-standardized, flag-computed) enter the passive set.
6. Passive empty → Saturated.

**Outcome soundness.** Theorem ⇒ the empty clause has a derivation over sound rules (Spec 07) ⇒ the input set is unsatisfiable. Saturated ⇒ every selected clause had its budgeted inferences computed under a fair strategy ⇒ (no budget fired) no derivation of the empty clause exists among the processed closure. GaveUp ⇒ the named budget fired; nothing is claimed.

## 8. The selection weight (design 15.3)

`weight(C) = Σ_{nodes n in C's atoms} symbol_weight(n)` with variables contributing `kSelectionVariableWeight` (0). This is the *selection* weight, distinct from the cached clause weight (which counts variables at the KBO weight for ordering purposes).
