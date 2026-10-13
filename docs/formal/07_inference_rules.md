# Formal Specification 07: The Inference Rules — Resolution, Factoring, Superposition, Equality Resolution and Factoring, Demodulation, Subsumption

Version: 0.1
Status: complete for the Phase 3 scope (design 10.1/10.2; design 26 build order "Superposition + resolution + factoring")
Role: normative reference for `hot/inference/{resolution,factoring,superposition,demodulation,subsumption,selection,builder}.rs`; cited by their `CEP:HPC-PASS-LEGALITY` fields.
References: Robinson 1965; Bachmair & Ganzinger 1994/2001; Nieuwenhuis & Rubio 2001; Plotkin 1972; Formal Specs 02 (substitutions) and 03 (orderings).

## 1. Preliminaries

Clauses are multisets of literals; a clause denotes the disjunction of its literals. A substitution σ is a finite map from variables to terms (Spec 02). For a literal L = P(t̄) or ¬P(t̄) or s ≈ t, the *atom* is the underlying term. The term ordering ≻ is KBO or LPO (Spec 03), a reduction ordering; it extends to atoms directly (the equality pseudo-symbol is comparable with every predicate head, design 8.3).

The **standardize-apart discipline** (Spec 02 section 5): the substitution engine namespaces variables by dense per-clause indices below `kMaxVariablesPerClause`; two premises of one inference are renamed into one shared namespace (left keeps [0, vars(left)), right shifts by vars(left)) before unification, and every stored conclusion is re-standardized to a dense [0, n) namespace. `vars(left) + vars(right) <= kMaxVariablesPerClause` is a structural soundness precondition, enforced loudly.

## 2. Renaming (the bijorphism)

**Definition.** For offset o, the renaming ρ_o maps variable index i to i + o.

**Theorem (renaming preserves unification).** terms s, t unify iff ρ_o(s), ρ_o(t) unify; MGUs correspond by composition with ρ_o. *Proof.* Renaming is a variable-for-variable bijorphism: apply the renaming to both sides of a unifier and the result is a unifier of the renamed pair, and conversely by ρ_o⁻¹. ∎

**Theorem (renaming preserves the ordering).** s ≻ t iff ρ_o(s) ≻ ρ_o(t). *Proof.* KBO and LPO compare symbol weights, occurrence counts, and precedence; renaming changes neither (Spec 03 cases inspect variable indices only through the variable condition, which is invariant under bijorphism). ∎ Flags (selected, maximal) ride along with the renamed literals, so eligibility is preserved by the two theorems above.

## 3. Eligibility (literal selection and maximality)

**Definition (maximal).** Literal L is *maximal* in clause C iff no atom of another literal of C is strictly ≻-greater than L's atom. L is *strictly maximal* iff additionally no other literal has an equal atom.

**Definition (eligible).** L is eligible-positive iff L is selected, or nothing in C is selected and L is strictly maximal. L is eligible-negative iff L is selected, or nothing is selected and L is maximal.

**Selection override (design 10.2).** A selected literal licenses inference regardless of maximality; when any literal is selected, unselected literals are ineligible. `SelectionFunction::FirstNegative` selects the first negative literal; `None` is pure maximality.

## 4. Binary / ordered resolution

**Rule.** From C ∨ L and D ∨ M where L, M have complementary polarity over the same predicate head, σ = MGU(atom(L), atom(M)): infer (C ∪ D)σ.

**Theorem (soundness).** Every model of both premises satisfies the resolvent. *Proof.* Let I satisfy both premises and falsify the resolvent. Then I falsifies every literal of Cσ and Dσ. Since I satisfies C ∨ L, it satisfies Lσ; since it satisfies D ∨ M, it satisfies Mσ. But Lσ and Mσ are complementary — contradiction. ∎

**Restrictions.** The positive-side literal must be eligible-positive and the negative-side literal eligible-negative (section 3). These restrictions, with factoring (section 5), yield the ordered resolution calculus, refutationally complete for first-order logic without equality (Bachmair & Ganzinger 2001, theorem 4.9); the restrictions only remove inferences, never add unsound ones.

## 5. Factoring and equality factoring

**Factoring.** From C ∨ L₁ ∨ L₂ with L₁, L₂ same-polarity over the same head and σ = MGU(atom(L₁), atom(L₂)): infer (C ∨ L₁)σ, requiring L₁ eligible-positive.

**Theorem (soundness).** Every model of C ∨ L₁ ∨ L₂ satisfies (C ∨ L₁)σ. *Proof.* A model falsifying the conclusion falsifies Cσ and L₁σ, hence (L₁ ∨ L₂)σ requires it to satisfy L₂σ; but MGU makes L₁σ = L₂σ — contradiction. ∎

**Equality factoring** (Nieuwenhuis & Rubio 2001). From C ∨ (s ≈ t) ∨ (s' ≈ t') with σ = MGU(s, s'): infer (C ∨ (s ≈ t) ∨ ¬(t ≈ t'))σ, requiring (s ≈ t) eligible-positive. *Soundness:* in any model of the premises, either Cσ holds, or sσ ≈ tσ fails, or both equations hold under σ; in the last case tσ and t'σ are equal by transitivity through sσ = s'σ, so ¬(tσ ≈ t'σ) fails, making the conclusion's last disjunct false but (s ≈ t)σ true — the conclusion holds. ∎ (Full case analysis in NR01 §4.2.)

## 6. Superposition and equality resolution

**Superposition.** From C ∨ (s ≈ t) and D ∨ L[w] (L's atom contains subterm w at position p) with σ = MGU(w, s): infer (C ∪ D ∪ {Lσ[p ← tσ]})σ, provided: (s ≈ t) is positive and eligible-positive; L is eligible (positive side strictly maximal, negative side maximal); **wσ is not a variable**; and **sσ ≻ tσ** (the equation orients; design 10.2).

**Theorem (soundness).** *Proof sketch.* Suppose a model I of both premises falsifies the conclusion. Then I falsifies Cσ, Dσ, and Lσ[p ← tσ]. Two cases on L's polarity. If L is positive: I satisfies Lσ, so I satisfies wσ ≈ tσ at position p (else Lσ[p←tσ] would hold); with the premise equation sσ ≈ tσ ∈ I, congruence forces wσ = tσ, so Lσ and Lσ[p←tσ] have the same truth value — contradiction. If L is negative: I satisfies ¬Lσ, and falsifying the conclusion's rewritten literal means Lσ[p←tσ] is true in I; congruence again forces Lσ true — contradiction with ¬Lσ. The case analysis for the variable restriction excluding wσ a variable is the standard one (BG94): without it, rewriting inside a variable's binding site is not sound. ∎

**Equality resolution.** From C ∨ ¬(s ≈ t) with σ = MGU(s, t): infer Cσ, requiring ¬(s ≈ t) eligible-negative. *Soundness:* a model falsifying Cσ satisfies ¬(s ≈ t)σ, but σ unifies s and t, making the disequation false — contradiction. ∎

**Completeness context.** Superposition (both directions, i.e., into positive and negative literals), equality resolution, and equality factoring, with the eligibility restrictions of section 3, form the standard superposition calculus, refutationally complete for first-order logic with equality (NR01 theorem 4.4). The engine implements both directions (the into-direction indexed by the rule tree, the from-direction by the active scan).

## 7. Demodulation

**Rule.** Unit equation (s ≈ t) with s ≻ t (orientation), C ∨ L[w] with w a non-variable subterm of L's atom, σ the matcher of s onto w (matching, not unification — σ instantiates only the rule's variables): infer C ∨ L[w ← tσ], requiring atom(L[w←tσ]) ≺ atom(L).

**Theorem (soundness).** Rewriting by an equation preserves the clause's models: any model of the unit equation satisfies w = tσ (σ matches s onto w), so L[w] and L[w ← tσ] are equivalent under the model. ∎

**Termination.** The strict-decrease condition makes demodulation a well-founded rewrite: each rewrite strictly decreases the literal's atom in a reduction ordering, so rewrite chains terminate (a simplified clause cannot loop back).

## 8. Subsumption

**Definition.** C *subsumes* D iff there is a substitution σ with Cσ ⊆ D (literal-set inclusion). With the E-prover convention, the decision also requires |C| ≤ |D| — pairs that subsume only under duplicate collapse beyond the guard are not detected (a documented deletion incompleteness that preserves search completeness: subsumption deletion is optional for refutational completeness).

**Decision procedure.** A backtracking search assigns each candidate literal a target literal of matching polarity whose atom it matches (one-directional, Spec 02 section 5), extending one shared substitution; target-literal reuse is allowed (set semantics). **Sound and (modulo the size guard) complete** for the subsumption relation.

## 9. Tautology detection

A clause is a tautology iff it contains two literals with pointer-equal atoms and opposite polarity (hash-consing makes structural atom equality pointer equality). Unifiable-but-distinct atoms (P(x) with ¬P(f(x))) are not tautologies — x may bind to f(x)'s denotation elsewhere.

## 10. Duplicate-literal removal

Stored clauses are deduplicated at creation (design 7.2 stage 10): a disjunction with a repeated literal is logically identical, and duplicates would make the duplicated literal non-strictly-maximal (blocking both resolution on it and the factoring that would merge it). Dedup is part of clause normalization in the search layer.
