# Formal Specification 12 — AVATAR Splitting

## 1. Scope

This document is normative for the AVATAR integration (design section 12): the splitting decision, the component interning contract, the model-guided activation protocol, the conflict-driven termination, and the degradation policy. Every `CEP:HPC-PASS-LEGALITY` comment in `hot/avatar/` cites a definition or theorem here.

References: Voronkov, CAV 2014 ("AVATAR: The Architecture for First-Order Theorem Provers"); Barbosa et al., JAR 2023 (component-based splitting in saturation).

## 2. The four rules (design 12.2)

- **Rule 1 (Split).** A clause C with variable-disjoint components C1, ..., Cn is replaced, for search purposes, by the components. Each component Ci is associated with a propositional assertion variable ai. The original clause record is retained inertly (never pushed to the passive set) as the proof-graph anchor for the components' `AvatarSplit` derivations.
- **Rule 2 (SAT solve).** The abstraction solver maintains one clause a1 ∨ ... ∨ an per split plus every conflict clause learned so far (design 12.4: no serialization - both engines share the arena; the assertion variables are dense component slots).
- **Rule 3 (Model-guided selection).** Only components whose assertion variables are true under the current model are activated (materialized as search clauses); the rest wait.
- **Rule 4 (Conflict-driven backtracking).** A first-order refutation whose component ancestry is U yields the conflict clause ¬a1 ∨ ... ∨ ¬ak over U's assertion variables; the abstraction is re-solved. An unsatisfiable abstraction closes the case as Theorem.

## 3. Splitting (the decision procedure)

**Definition 3.1 (Variable-dependency graph).** For a clause C with dense variable namespace, the graph G(C) has the variables of C as vertices and an edge between two variables whenever they occur in the same literal.

**Definition 3.2 (Components).** The components of C are the literal sets induced by the connected components of G(C). Ground literals (no variables) are singleton components.

**Definition 3.3 (Gate).** A clause splits only when it has at least two components AND every component has at least `kAvatarMinComponentSize` literals (the all-or-nothing reading of design 12.3). Failure to split is always sound: the clause stays whole.

**Lemma 1 (Splitting soundness).** If C's components partition the literal multiset and are pairwise variable-disjoint, then C is satisfiable iff every selection of one component per split has a model... more precisely, for the single-split case: C ≡ (C1 ∨ ... ∨ Cn) and any interpretation I satisfies C iff I satisfies some Ci (each component is a disjunction over disjoint variables; a model of C satisfies at least one literal, which lies in exactly one component, and that component is thereby satisfied). *Proof:* the components partition the literals (each literal in exactly one component), so satisfying any literal satisfies its component, and the disjunction C is satisfied. Conversely a model of C satisfies some literal of C, hence some component. ∎

**Theorem 1 (Abstraction soundness, Voronkov 2014 Thm 1).** If the abstraction (all split disjunctions plus all conflict clauses) is unsatisfiable, the original clause set is unsatisfiable. *Proof sketch:* every model I of the original set induces an abstraction assignment: for each split, I satisfies at least one component (Lemma 1); setting that component's assertion variable true satisfies the disjunction. Conflict clauses hold: a conflict clause ¬∧U was added only after inputs + U's components entailed ⊥; an I making all of U true would satisfy those components (ai true means I ⊨ Ci), contradicting the entailment. So I induces an abstraction model - contradicting unsatisfiability. ∎

## 4. Component interning

**Definition 4.1 (Canonical form).** A component's canonical form is its literal sequence as words (atom offset << 1 | polarity), sorted ascending, over the component's own dense variable namespace (the splitter restandardizes each component before interning).

**Lemma 2 (Interning identity).** Two components intern to the same record iff their canonical words are equal; hash-consed atoms make the word sequence an injective function of the literal multiset over the dense namespace. The assertion variable of record slot s is SatVar(s) (dense).

**Contract.** A fresh record cites the source-original clause id of the first interning; re-internings share the record (and the first source). The materialized clause carries the `AvatarSplit` derivation (parent = the source original), `split_level = slot + 1`, and per-literal component tags (design 5.2, ticket CEP-1011; the 3-bit tag is a hint, `split_level` is authoritative).

## 5. The monotone-activation protocol (Phase 4)

The Phase 4 protocol is **monotone**: a materialized component never leaves the search. Consequences:

**Theorem 2 (Soundness).** Every clause the search derives is a logical consequence of the inputs (components are consequences of their originals through the splitting equivalence; every inference rule is sound per Spec 07). A Theorem outcome is a real refutation: directly (empty ancestry), or through Theorem 1 (abstraction unsat after conflicts).

**Completeness.** Monotone activation searches a superset of the strict model-guided restriction (every clause the restricted search derives is available to the superset search), so the Phase 4 protocol is at least as complete as strict AVATAR: every refutation reachable under model-restricted exploration is reachable here.

**Protocol.** Round start: solve the abstraction; activate model-true waiting components. Run the given-clause loop (Spec 08). On Theorem: collect the component ancestry U (one descending pass over monotonic clause ids; parents precede children); U empty → direct Theorem; else add the conflict clause (Spec 12 Lemma 3 below), re-solve: unsat → Theorem (via Theorem 1); sat → activate under the new model, next round. On Saturated: if the waiting set is empty → Saturated; else rotate (section 6).

**Lemma 3 (Conflict soundness).** The conflict clause over U is entailed by the abstraction's meaning: inputs + U's components ⊨ ⊥ (the FO refutation used exactly U's components), so every original-model making all of U true is impossible - the clause ¬∧U excludes precisely those assignments. The clause is added as a permanent problem clause (never registry-reduced). A truncation of U would be UNSOUND (banning a subset); the controller fails loudly when the clause exceeds the abstraction's literal bound instead of truncating.

**Theorem 3 (Saturation terminal).** Saturated is reported when the passive set empties and every component is materialized (the waiting set is empty): the search saturated over the full monotone closure. The assertability lemma (section 6) guarantees the rotation sweep drains the waiting set while waiting components remain.

## 6. Model rotation

**Lemma 4 (Assertability).** In the monotone protocol, every waiting component's assertion variable is assertable: some abstraction model sets it true. *Proof:* conflict clauses mention only components that appear in some refutation ancestry, and every such component was materialized (monotone) - so no conflict clause mentions a waiting component's variable. Take the last adopted model M (waiting w is false in M); flipping w to true violates no clause: disjunctions still admit their satisfied literal, and no conflict clause contains w. ∎

**Protocol.** On saturation with waiting components, probe each waiting slot w by `solve_with_assumptions([aw])` (bounded by `kAvatarMaxModelRotations`, injectable): Satisfiable → adopt the model, activate, continue; UnsatUnderAssumptions → next slot. By Lemma 4 the sweep always finds an adoptable model while waiting components remain, so the sweep drains the waiting set one activation at a time; the budget is the defensive bound (GaveUp(AvatarModelBudget) when exceeded).

## 7. Degradation policy

Splitting is an optimization; its absence is always sound. The controller degrades to the unsplit clause on: single component, gate refusal, component-table record exhaustion, canonical-word blob exhaustion, or walk-budget exhaustion (each counted in stats, never silent - CEP&CC Law 6). Only input clauses split in Phase 4 (derived clauses are processed by the inner loop; derived-clause splitting is future work, documented in `docs/tickets.md`).

## 8. Proof-output mapping (design 12.4 shared proof graph)

The unified proof graph is the FO derivation DAG: component clauses cite their originals through `AvatarSplit`. The abstraction solver records no DRAT trace: conflict clauses are FO-justified lemmas (Lemma 3), not propositional consequences of the abstraction, so emitting them as plain DRAT additions would produce an unsound certificate (Spec 14 section 5 documents the TSTP presentation; external checkers must accept `avatar_split` as a black-box rule whose soundness is Lemma 1).

## 9. CEP&CC mapping

`hot/avatar/splitter.rs`, `hot/avatar/component.rs`, `hot/avatar/controller.rs` cite sections 3, 4, 5, 6, and 7 of this document in their `CEP:HPC-PASS-LEGALITY` fields. The executable evidence: `unit/hot/avatar_{splitter,component,controller}_test.rs`, `property/avatar_property_test.rs` (partition and disjointness are verified executably per Lemma 1's premises; outcome agreement pins the protocol end to end), and `fuzz/avatar_fuzz_test.rs` (totality over adversarial shapes).
