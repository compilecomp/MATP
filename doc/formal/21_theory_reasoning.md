# Formal Specification 21: Theory Reasoning — DPLL(T), Congruence Closure, Difference Logic, Nelson-Oppen Combination

## Abstract

This document is the normative reference for `hot/theory/` (design 13, the three theory rows of design 26 Phase 5: "DPLL(T) integration", "Congruence closure", "Nelson-Oppen combination"; ticket CEP-1069). It defines the term graph, the congruence closure for the uninterpreted-function theory, the difference-logic fragment of linear arithmetic over Q, the DPLL(T) outer loop with its theory-lemma discipline, and the Nelson-Oppen equality-propagation combination. The fourth Phase 5 row, "Higher-order extensions" (design 14), is owned by its open tickets (CEP-1033 orderings for the Phase 5 fragment, CEP-1062 the design 28.8 module set) and is not covered here. References: Nelson & Oppen 1980 (congruence closure, combination); Nieuwenhuis, Oliveras & Tinelli, JACM 2006 (DPLL(T), constraint graphs); Bacchus (hyper-binary-style theory propagation, deferred); Formal Spec 05/06 (the CDCL engine the loop drives).

## Formal Definitions

### 1. Scope and bounds

The engine works over one shared variable space (`kMaxTheoryVars`), one hash-consed term graph (`kMaxTheoryTerms`, arity `kMaxTheoryArity`), one atom registry (`kMaxTheoryAtoms`; atom i is SAT variable i of the abstraction's CDCL solver), and one conflict budget (`kMaxTheoryConflicts`, injectable). Difference-logic weights are integers scaled by 2^`kTheoryDlScaleShift` — an exact fixed-point representation of Q fragments with `|w| <= kTheoryDlMaxWeight` so every Bellman-Ford accumulation stays in i64 range (overflow is the loud `TheoryError::ArithmeticOverflow`). Every loop in the module is bounded by a named capacity; every stop is an honest status (`TheoryStatus::Unknown`, `TheoryError::*`).

### 2. Term graph and atoms

Term nodes are constants (symbol), variables (dense id), and applications (symbol, argument node ids), hash-consed so structurally identical terms share one node — the unique-node invariant the closure's signature classes require. Theory atoms are EUF equalities (t1 = t2) and difference constraints (x - y <= c). One atom id names the payload in the registry and one SAT variable in the Boolean abstraction.

### 3. Congruence closure (design 13.4)

The closure maintains union-find classes over the term graph (path halving; union by rank with ties toward the smaller id). Asserting an equality merges the classes (lazy). `check` runs the signature fixpoint: each round recomputes every application node's signature (function symbol, class-representative arguments), merges classes whose signatures coincide — with an explicit signature comparison at the hash-table probe so two different signatures that collide on one slot probe on instead of merging — and repeats until a round merges nothing.

**Theorem (closure).** After the fixpoint, two terms are in one class exactly when the asserted equalities plus the congruence rule (a = b implies f(…,a,…) = f(…,b,…)) force it. *Proof.* Asserted merges and congruence merges are exactly the Nelson-Oppen closure rules; the fixpoint applies them to saturation, and each round with a merge reduces the class count, so the round bound `kMaxTheoryTerms` is never the deciding factor. ∎ **Known bound**: the per-round recomputation is O(nodes × arity) per merge — the use-list form (O(n log n)) is the measured follow-up (CEP-1070).

### 4. Difference logic over Q (design 13.1's linear fragment)

A constraint x - y <= c is an edge y -> x of length c in the constraint graph; the asserted system is consistent iff the graph has no negative cycle, detected by Bellman-Ford from a virtual source (distances zero everywhere, `kMaxTheoryVars + 1` rounds; a further relaxation is the cycle). The negation of x - y <= c is asserted as y - x <= -c - 1 — exact over the fixed-point representation, where the one-unit epsilon is the smallest positive Q-element the representation addresses.

### 5. The DPLL(T) loop (design 13.2) and the lemma discipline

The loop (design 13.2 steps 1-5): the CDCL solver proposes a Boolean assignment over the atoms; every atom's value is asserted into its theory; the coordinator checks consistency; an inconsistent assignment produces the **theory lemma** — the negation of the full atom assignment (a literal per atom, each negating the model's value) — which the solver adds through the axiom path and the loop re-solves, until Satisfiable (a theory-consistent model), Unsatisfiable, or Unknown at the budget.

**Theorem (lemma validity and termination).** Each lemma is theory-valid (the assignment is theory-inconsistent, so its negation is entailed) and excludes exactly the current assignment (every literal is falsified by it), so the loop visits each atom assignment at most once and is complete over the finite space with the budget as the loud bound. ∎ **Trust axiom**: a theory lemma is theory-valid but not RUP against the Boolean abstraction, so it is recorded through the axiom path (justification skipped); the refutation the checker replays proves formula-plus-lemmas unsatisfiable, and theory validity of the lemmas closes the argument — the same trust structure as the kernel's `TheoryLemma` derivation source (hot/ir/clause.rs), whose producer surface is the coordinator's conflict report. **Inter-solve state**: the lemma path snapshots the atom values, returns the solver to level 0 through `return_to_root_level` (phase saving plus the batched VSIDS wave — the sanctioned backtrack), and adds the lemma at level 0; the value-aware root-level attach (Spec 06 section 8 amendment) surfaces a lemma already falsified by level-0 units as the root conflict. **Deferred**: theory-driven decisions (online propagation) are the measured follow-up (CEP-1070); the offline loop is complete without them.

### 6. The Nelson-Oppen combination (design 13.3)

The coordinator drives EUF (the closure) and difference logic over the shared variables to a fixpoint of bidirectional equality propagation: (1) per-theory consistency (the closure's fixpoint and disequality check; Bellman-Ford); (2) every EUF-merged shared pair becomes a zero-equality pair in the difference logic (edges x - y <= 0 and y - x <= 0 plus the zero-class mirror, which unions on the pair only — a single zero-weight inequality is not an equality); (3) every shared pair whose equality the difference logic **entails** is merged in EUF, where entailment is the two-orientation separation test: u = v is entailed iff both u < v and v < u (one fixed-point unit) are inconsistent with the current system — the +-0-consistency form would confuse "compatible" with "forced" and is wrong; (4) the fixpoint stabilizes when a round propagates nothing.

**Theorem (combination soundness and completeness).** The coordinator's `check` accepts an atom assignment iff a combined model of the two theories exists that realizes it. *Proof.* (⇐) the fixpoint's invariants hold in any combined model: EUF merges are realized (step 2 makes them difference-feasible), and difference-forced equalities are merged (step 3) before the disequality check, so both theories are consistent with one shared-variable arrangement. (⇒) if the fixpoint accepts: every shared pair is either merged (both theories agree on equality) or separate with the equality not entailed — a separating model exists in each theory (EUF classes are free; the difference-logic entailment test is exact for the fragment), and since EUF and difference logic over Q are stably infinite and signature-disjoint, the models combine with the propagated equalities (Nelson & Oppen 1980). ∎ Each propagation round either merges at least one shared pair or stabilizes, so `kMaxTheoryPropagationRounds` is a loud backstop, not the deciding factor.

### 7. Model reading

After a Satisfiable outcome, `atom_value` reports the model's truth value per atom; the combined theory realizes these values (section 6). Atom values are the solver's model snapshot taken before the lemma-path root-level return.

### 8. Evidence

The executable evidence: `unit/hot/theory_test.rs` (hash-consing, the four capacity vocabularies, closure and propagation, difference-logic consistency and conflict, the combination's accept and cross-theory conflict, the DPLL(T) ends, the budget's Unknown), `tests/unit/hot/sat_solver_test.rs::{falsified_clause_attachment_surfaces_conflict, unit_under_trail_attachment_propagates, return_to_root_level_keeps_root_facts}` (the solver-side contract the loop relies on), and `property/theory_property_test.rs::{euf_instances_agree_with_oracle, dl_instances_agree_with_oracle, combined_instances_agree_with_oracle}` (48 fixed seeds per family against independently implemented brute-force oracles: naive union-find with a fixpoint congruence closure and an independent Bellman-Ford).

## Invariants

1. Atom mapping: atom i is SAT variable i; the abstraction and the registry never drift (section 2; `dpll_t_satisfiable_end_to_end`).
2. Per-rewrite theory soundness: the closure realizes the congruence rules (section 3), the difference logic realizes the constraint graph (section 4), and the combination realizes Nelson-Oppen (section 6) — all pinned by the property families against independent oracles.
3. Lemma discipline: every theory lemma is theory-valid, excludes exactly the current assignment, and enters the trace through the axiom path (section 5; the trust axiom).
4. Honesty: budget stops report Unknown with the conflict count; every capacity, round, and arithmetic bound is a named constant with a loud error (section 1; the unit pins).
5. Statelessness between iterations: the coordinator resets before each assertion batch; the tentative entailment probes truncate their edges (sections 5-6).
6. Level discipline: clause additions outside solves happen at level 0 through the sanctioned return path (section 5; the three solver-side pins).

## Integration Points

Depends on:

- `hot/sat/solver.rs` (`CdclSolver` as the Boolean abstraction engine; `add_clause` for the formula and the lemmas; `return_to_root_level` for the inter-solve state; `model_value` for the atom snapshot).
- `hot/memory/arena.rs` for every backing array (no allocation outside the caller-provided arena).
- `hot/ir/clause.rs`'s `DerivationSource::TheoryLemma` and the kernel's record walk as the ATP-side surface the conflict reports feed.

Depended on by:

- The future theory-clause transfer into the ATP proof graph (the `Theory_Lemma` producers of design 13.6) and the design 13.1 theories beyond the delivered fragment (CEP-1070).
- `tests/unit/hot/theory_test.rs`, `tests/property/theory_property_test.rs`, and the cited solver pins, the executable evidence for invariants 1 through 6.

## Known Limitations

- The arithmetic fragment is difference logic over Q; unrestricted linear arithmetic (the simplex of design 13.1), non-linear arithmetic, bitvectors, arrays beyond congruence, and algebraic datatypes are not delivered (CEP-1070 owns the schedule).
- The closure recomputes signatures per merge (O(nodes × arity) per merge) instead of the use-list O(n log n); the budgets bound the work (CEP-1070).
- The loop is offline: no theory-driven decisions or propagations (design 13.2's optimization half); the lemma is the full-assignment negation, not a minimal conflict set — completeness holds, lemma quality does not (CEP-1070).
- The combination covers EUF with difference logic over Q; the Nelson-Oppen arrangement for further theory pairs follows their solvers (CEP-1070).
- The higher-order row of Phase 5 (design 14) is not covered by this module; its scope lives in CEP-1033 and CEP-1062.
