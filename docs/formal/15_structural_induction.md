# Formal Spec 15: Automated Induction (Structural and Well-Founded Schemes)

## 1. Scope and deliverable

This specification is normative for `hot/induction/` (revised build order Phase 4). Every `CEP:HPC-PASS-LEGALITY` comment in that module cites a definition or theorem here. The deliverable is the bounded, deterministic, clausal induction-scheme generator: for a **declared** freely-generated datatype shape, every occurring unary predicate receives the two-clause clausification of its induction-axiom instance (structural scheme), and when a well-order is declared additionally the two-clause clausification of its strong-induction instance (well-founded scheme).

The zero-ML rule holds absolutely: no statistics, no learned weights, no symbol-name heuristics, no hidden state. The datatype is never guessed; it is **declared** by the CEP-1 driver and validated mechanically (section 2).

## 2. The declaration contract

An `InductionDeclaration` carries:

| Field | Required shape | Validation |
|---|---|---|
| `zero` | 0-ary function symbol | `ZeroNotConstant` otherwise |
| `succ` | unary function symbol | `SuccNotUnary` otherwise |
| `skolem` | 0-ary function symbol, **absent from every input clause** | `SkolemNotConstant` / `SkolemOccursInInput` |
| `well_founded` (optional) | binary predicate symbol | `WellFoundedNotBinary` otherwise |

The skolem-absence proof is the input-signature scan (section 2.1): one walk over every input clause's atoms in clause-id order and term-child order, node-budgeted by `kInductionScanNodeBudget` (defense in depth; the structural bounds argument is in the constant's CEP:WHY). The scan is depth-bounded by `kMaxTermDepth` (the interned-term bound) and collects, in the same pass, the deduplicated set of occurring unary predicate symbol ids, sorted ascending after the scan. A declaration rejection adds **no** scheme (Law 6: no partial effects).

**Design rationale (why declaration, not detection).** E's `induction.ax` and Vampire's induction mode identify datatypes by symbol shape or name, and both document the unsoundness risk: symbols merely *named* `zero`/`succ` with axioms that contradict freeness produce scheme instances that are not valid in the intended semantics. MAPT removes the guesswork: the declaration is the trust boundary, its validation is mechanical, and the semantic obligation (the constructor family really is a freely generated datatype) rests with the declaring driver, exactly as TPTP's inductive-datatype convention rests with the problem author.

## 3. The structural scheme

### 3.1 Soundness theorem (initial-algebra convention)

**Theorem.** Let `D` be a freely generated datatype with base constructor `z : D` and step constructor `s : D -> D` (the two-constructor Peano shape; the untyped engine's only unambiguous free shape). For every formula `phi(x)` over the signature, the induction-axiom instance

  `IA(phi) = (phi(z) AND ALL y. (phi(y) -> phi(s(y)))) -> ALL x. phi(x)`

is valid in the initial (term) algebra of `D`.

*Proof.* By structural induction on the term `t` denoting `x`: the base case is the antecedent's first conjunct; the step case is the antecedent's second conjunct applied at the immediate subterm. Freeness (injectivity and distinctness of constructors, no junk beyond `z` and `s`-iterations) is what makes the initial algebra exactly the term algebra, so the induction covers every element. This is the standard initiality theorem (Birkhoff); the freeness obligation is the declaring driver's (section 2's rationale). ∎

MAPT instantiates `phi` at **goal predicates**, not arbitrary formulas — the same restriction as E's `induction.ax`: `phi(x) := p(x)` for each occurring unary predicate `p`. The instance is first-order because the predicate symbol is fixed.

### 3.2 Clausal derivation (the generator's shape)

Clausifying `IA(p)` (negate the antecedent, skolemize the existential witness of the negated inner universally quantified disjunction — one witness constant `a` for the whole instance; MAPT uses the declaration's skolem symbol, whose freshness the scan proved):

`~IA(p)` = `~p(z) OR (p(a) AND ~p(s(a))) OR ALL x. p(x)`

distributes into exactly two clauses:

- **S1** = `{ ~p(z), p(a), p(X) }`
- **S2** = `{ ~p(z), ~p(s(a)), p(X) }`

with `X` variable index 0 (the numbering is fixed by this spec; the builders in `hot/induction/scheme.rs` implement exactly these two literal sets, and `property/induction_property_test.rs::schemes_match_hand_clausification` re-derives them independently for random predicate choices).

**Pair atomicity.** S1 and S2 jointly clausify one valid formula; **neither clause alone is valid** (each is only one disjunct branch of the clausification). The installer therefore adds them as an inseparable pair: the attempts budget (`kMaxInductionAttempts`, injectable; production default in `config/limits.rs`) is checked against the **pair** (`kInductionSchemeClauses = 2`), and a budget that cannot fit a whole pair adds nothing and counts the predicate as skipped (Law 4).

## 4. The well-founded (strong) scheme

### 4.1 Soundness theorem

**Theorem.** Let `lt` be a well-founded strict order on `D` (well-foundedness is the declaring driver's semantic obligation; the standard justification — and the reason the feature exists — is that `lt` is defined recursively over the constructors, e.g. `lt(z, s(x))` and `lt(x, y) -> lt(x, s(y))`, whence well-foundedness follows by structural induction on the second argument, the standard TPTP less-than definition). For every unary predicate `p`:

  `WFI(p) = (ALL x. ((ALL y. (~lt(y, x) OR p(y))) -> p(x))) -> ALL x. p(x)`

is valid (over the well-founded structure).

*Proof.* Contrapositive: if `~p(c)` for some `c`, the antecedent's failure at `c` gives a witness `c'` with `lt(c', c)` and `~p(c')`; iterating builds an infinite descending `lt`-chain, contradicting well-foundedness. ∎

### 4.2 Clausal derivation

`~WFI(p)` = `EXISTS x. ((ALL y. (~lt(y, x) OR p(y))) AND ~p(x)) OR ALL x. p(x)`; skolemize the existential (witness `c` — the same declaration skolem, sound because each scheme instance is independently valid regardless of the constant's interpretation):

- **W1** = `{ ~lt(Y, c), p(Y), p(X) }`  (Y = variable 0, X = variable 1)
- **W2** = `{ ~p(c), p(X) }`  (X = variable 0)

## 5. Bounds

| Bound | Constant | Semantics |
|---|---|---|
| Total scheme clauses per installation | `kMaxInductionAttempts` | Pair-atomic cut; skips counted |
| Pair granularity | `kInductionSchemeClauses` = 2 | The clausification's shape |
| Scan node budget | `kInductionScanNodeBudget` | Defense-in-depth ceiling on the validation walk (injectable per CEP&CC 34.3) |
| Predicate collection bound | `kInductionMaxPredicates` | Fixed-array bound; overflow predicates skipped and counted; asserted to never bind before the attempts budget for structural-only declarations |

Static and runtime assertions (the latter mirrored in `unit/config/limits_test.rs::phase4_revised_invariants`) fix every cross-constant relation, including `kInductionMaxPredicates * kInductionSchemeClauses >= kMaxInductionAttempts`.

## 6. The worked refutation (the feature's reason to exist)

The minimal problem whose proof **requires** the scheme: inputs `p(zero)` (base), `~p(X) OR p(succ(X))` (step), `~p(a)` (negated conjecture). No first-order refutation exists (the induction axiom is second-order in `p`): the plain loop saturates honestly (`unit/hot/induction_test.rs::induction_refutes_inductive_theorem` pins both outcomes). With S1, S2 installed, the refutation path (with a precedence ranking `zero` highest and the default selection):

1. S1 `~p(z) OR p(a) OR p(X)` resolves with `p(zero)` on the maximal `~p(zero)` → `{ p(sk), p(X) }`
2. Factoring on the strictly maximal `p(sk)` → `p(sk)`
3. The step's `p(succ(X))` resolves with S2's `~p(succ(sk))` → `{ ~p(sk), ~p(zero), p(X) }`
4. `~p(zero)` with `p(zero)` → `{ ~p(sk), p(X) }`
5. `~p(sk)` with the unit `p(sk)` → `p(X)`
6. `p(X)` with `~p(a)` → the empty clause.

The same ordered restriction blocks the unbounded ground chain `p(succ^n(a))` (the step's `~p(X)` is never maximal), which is why the scheme-augmented search stays shallow and fast — the worked example is also the determinism and cost story.

## 7. Proof-recording presentation

Scheme clauses carry `InferenceRule::StructuralInduction` / `WellFoundedInduction`, parentless, and enter the passive set through the production staging path (`add_theory_clause`). The TSTP writer emits them with the `axiom` role and the source names `structural_induction` / `well_founded_induction`; the replay checker accepts them as parentless theory-axiom introductions (existence-checked by the walk), matching the published presentation of E's `induction.ax` and Vampire's introduced theory axioms: external checkers see exactly what was assumed and can audit it by name. The internal shape is pinned by the unit tests against this spec's sections 3.2/4.2.
