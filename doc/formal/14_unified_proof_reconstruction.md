# Formal Specification 14: Unified Proof Reconstruction

## Abstract

This document is normative for the unified proof reconstruction (`cold/proof_output/tstp.rs`; design section 18): the derivation walk, the reachability pruning, the TSTP statement grammar subset, the replay checker's contract, and the AVATAR proof presentation. Every `CEP:HPC-PASS-LEGALITY` comment in `cold/proof_output/tstp.rs` cites a definition or theorem here. Inputs are the derivation DAG of stored clauses rooted at a refutation; outputs are the pruned reachable set, the TSTP text rendering, and the checker verdicts (`InvalidStep`, `CycleDetected`, `BudgetExhausted`). References: TSTP (TPTP solution) syntax, TPTP v9.0; design 5.4 (derivation steps); design 18.4 ("an ATP that produces an invalid proof is worse than one that produces no proof").

## Formal Definitions

### 1. Scope

This document is normative for the unified proof reconstruction (design section 18): the derivation walk, the reachability pruning, the TSTP statement grammar subset, the replay checker's contract, and the AVATAR proof presentation. Every `CEP:HPC-PASS-LEGALITY` comment in `cold/proof_output/tstp.rs` cites a definition or theorem here.

### 2. The derivation walk

**Definition 2.1 (Derivation DAG).** Every stored clause carries its `DerivationStep` (rule, up to four parent clause ids, design 5.4). The DAG's vertices are clause records; an inference draws edges from each parent to the conclusion.

**Lemma 2.1 (Monotonic ids).** Clause ids are dense and monotonic from `kFirstClauseId`; parents are created before their conclusions, so every parent id is strictly below the conclusion id. *The proof walk exploits this:* one descending pass over the id range marks the ancestry of the refutation exactly (a parent marked at its own visit propagates to its parents, which are visited later in the descending scan). A parent id at or above the child id is a corrupted derivation (`CycleDetected` - the walk refuses).

**Contract.** The walk resolves ids through the clause store's id side table (the dense array indexed by id - `kClauseOffsetTableCapacity`; the 256 MiB arena holds at most ~1.76M clauses at the 152-byte minimum footprint, so the 4.19M-slot table always outlives the arena; the bound is unreachable by construction).

### 3. Pruning (design 18.2's redundant-step removal)

**Definition 3.1 (Reachable set).** The reachable set of a refutation r is {r} plus every ancestor reachable through parent edges. The pruned proof contains exactly the reachable clauses, in ascending id order (a valid topological order by Lemma 2.1).

Phase 4 scope: reachability is the subsumption-based compression; interpolation-based compression (design 18.3) remains future work.

### 4. TSTP statement grammar (the emitted subset)

```
statement  ::= "cnf(c" <id> ", " role ", " formula source ")."
role       ::= "axiom" | "negated_conjecture" | "plain"
formula    ::= literal (" | " literal)* | "$false"
literal    ::= ["~"] atom
atom       ::= variable | application | equality | sort-tag
variable   ::= "X" <index>
application::= <name> "(" term (", " term)* ")" | <name>
equality   ::= term " = " term
source     ::= ", inference(" rule ", [], [" parent-list "])"
rule       ::= "resolution" | "superposition" | "factoring" | "demodulation" | "avatar_split" | ...
```

The empty clause renders `$false` with the `plain` role. Variables render `X<n>` (the TPTP upper-case convention). Equality renders infix.

### 5. The AVATAR presentation

A Theorem-via-avatar proof presents: the input axioms; the split originals (axioms); the component clauses as `inference(avatar_split, [], [original])` steps (Spec 12 Lemma 1 is the soundness of the step); and the FO refutation DAG over the components and the remaining inputs. External checkers must accept `avatar_split` as a black-box rule - the same presentation as published AVATAR proofs. The internal checker verifies the step structurally (section 6). The abstraction-UNSAT argument that closed the case (Spec 12 Theorem 1) is a framework theorem, not a per-step check; the FO refutation itself is the checkable artifact.

### 6. The replay checker (design 18.4)

> **Phase 5 amendment (Spec 19).** The checker described in this section has moved into the certified proof kernel (`cold/kernel.rs`, Formal Spec 19) and the TSTP module delegates to it. Two checks of this section are superseded there: the AVATAR split check is the production `try_split_with` replay over restandardized component multisets at the finest replay gate (gate-free, Spec 19 section 4), and the demodulation structural-variant check is replaced by the exact per-step replay over the CEP-1036 chain (an unrecorded rule parent is rejected). The error vocabulary is unchanged: the kernel verdict maps onto `InvalidStep` / `BudgetExhausted`.

**Contract.** For every reachable derived clause, the checker independently re-runs the recorded rule between the recorded parents through the production inference functions and accepts the step only when some legal application reproduces the recorded conclusion modulo the loop's conclusion pipeline (restandardize + dedupe, Spec 08 section 6):

- **Resolution** (two parents): every pivot pair (i, j) is replayed; acceptance when some resolvent matches.
- **Factoring** (one parent): every literal pair is replayed.
- **Superposition** (two parents): every (equation, literal, path) combination is replayed through the production rule.
- **AvatarSplit** (one parent): the structural subclause check of Spec 12 Lemma 1 - every conclusion literal appears in the parent with the same polarity. (The pairwise-disjointness premise is verified at split time by the splitter and its property tests; the checker's scope is the per-step property the derivation record carries.)
- **Demodulation** (one parent): the structural variant check - same literal count and polarity multiset. This is the documented Phase 4 weakening: the Phase 3 derivation record does not carry the demodulating rule's identity (parents[1] is unused), so a full replay is impossible until the derivation records it (ticket CEP-1036).
- **Input / NegatedConjecture**: axiom steps (existence-checked by the walk).

**Theorem 6.1 (Rejection soundness).** A tampered conclusion, a redirected parent, or a corrupted derivation is rejected (`InvalidStep` with the offending id, or `CycleDetected`); the caller returns Error per design 18.4.

## Algorithm

The reconstruction pipeline of `cold/proof_output/tstp.rs`:

1. Walk: one descending pass over the clause-id range from the refutation, marking the exact ancestry (Lemma 2.1); a parent id at or above the child id aborts with `CycleDetected`.
2. Prune: emit exactly the reachable set in ascending id order (Definition 3.1), which is a topological order without a second pass.
3. Verify before formatting (section 7): replay every reachable derived step per the section 6 contract through the certified kernel (Phase 5 amendment); a failed step aborts the render with `InvalidStep` and the offending id.
4. Format: render each statement per the section 4 grammar (roles, `$false`, `X<n>` variables, infix equality, `inference(...)` sources; AVATAR originals and components per section 5).

Time is O(reachable clauses x per-step replay cost) under the kernel's replay budget; space is the reachable set plus the output buffer, sized exactly. Assumptions: clause ids are dense and monotonic; the derivation records of the phase under replay carry the parents the contract requires.

### 7. Verification ordering (design 18.4)

`render_verified_proof` verifies before formatting: a proof that fails its checker never leaves the process as valid output.

### 8. CEP&CC mapping

`cold/proof_output/tstp.rs` cites sections 2-6 of this document in its `CEP:HPC-PASS-LEGALITY` field. The executable evidence: `unit/cold/tstp_test.rs` (walk, pruning, format, and the checker's accept/reject paths) and `property/tstp_property_test.rs` (every generated refutation verifies; a corrupted proof is rejected).

## Invariants

1. Ancestry exactness: the descending walk marks exactly the ancestors of the refutation (Lemma 2.1).
2. Topological emission: the pruned proof is in ascending id order, parents before conclusions (Definition 3.1).
3. Corruption refusal: non-monotonic parentage aborts with `CycleDetected` before any output (section 2).
4. Rejection soundness: no tampered or wrongly-parented step passes the replay (Theorem 6.1).
5. Verify-before-format: a proof that fails verification is never rendered as valid output (section 7).
6. Grammar fidelity: emitted statements parse in the section 4 subset; the empty clause renders `$false` (section 4).

## Integration Points

Depends on:

- `hot/ir/clause.rs` (`ClauseStore::clause_by_id(&self, id: ClauseId) -> Result<&Clause, ClauseError>`, `DerivationStep`, the id side table) for the walk and parent resolution.
- `cold/kernel.rs` (Formal Spec 19) for the per-step replay verdicts (Phase 5 amendment).
- `hot/inference/` production rule functions, which the kernel re-runs for the replay contract.

Depended on by:

- `cold/verifier.rs` and the SAT proof pipeline (`cold/proof_output/drat_writer.rs`, Specification 11) share the derivation record discipline.
- `tests/unit/cold/tstp_test.rs` and `tests/property/tstp_property_test.rs` are the executable evidence for invariants 1 through 6.
- The golden test `tests/golden/ir_debug_print_test.rs` pins the IR rendering the same records feed.

## Known Limitations

- Interpolation-based proof compression (design 18.3) is future work; pruning is reachability only (section 3).
- The section 6 contract predates the Phase 5 kernel delegation; the authoritative per-step semantics are Specification 19 (the amendment above).
- The grammar subset covers the emitted rules only; TPTP constructs outside it (general functions, bindings in sources) are not emitted (section 4).
- The replay is budget-bounded; BudgetExhausted verdicts certify nothing beyond the processed prefix (kernel contract, Spec 19).
