# Formal Specification 11: DRAT Proof Logging and Checking

## Abstract

This document is the normative reference for `hot/sat/proof.rs` (recorder), `cold/proof_output/drat_writer.rs` (text emission), and `cold/proof_output/drat_checker.rs` (internal checker), cited by their `CEP:HPC-PASS-LEGALITY` fields (design 6.4, 11.1 S41-S43, 18). It defines the proof record layout, the five step kinds with the trace-to-formula binding, the RUP/RAT justification semantics, the empty-clause convention, the DRAT text format, and the internal checker's verdict vocabulary. Inputs are solver events (axioms, learnt clauses, deletions, assumption steps); outputs are the in-memory trace, its exactly-sized text rendering, and a `CheckOutcome` verdict from the independent replay. References: Heule, Hunt & Wetzler 2013/2014 (DRAT); Wetzler 2015 (LRAT); Formal Spec 06 (CDCL).

## Formal Definitions

### 1. The record

The recorder holds a flat step buffer (kind: Add / Delete / AssumptionAdd / AssumptionDelete / AxiomAdd; proof id; literal extent), an append-only clause-offset-to-id map (ascending offsets; binary-searched), and a concatenated literal blob. Ids are dense and 1-based (`kFirstProofId`). Capacities are named; exhaustion is a loud error surfaced as Indeterminate — never a silent truncation.

### 2. Step kinds and the trace-to-formula binding

**AxiomAdd**: a problem clause (an axiom of the run). The checker seeds its database from axiom steps and verifies their one-to-one correspondence (in order) with the caller-supplied formula — the trace is thereby bound to exactly the problem it claims to refute, and the checker's require_refutation option additionally insists on the empty-clause derivation before blessing a trace as a refutation (section 6). **Add**: a derived clause (RUP/RAT-justified). **AssumptionAdd/AssumptionDelete**: hypothesis units of an incremental call (Spec 10 section 2); the checker seeds and removes them without justification. CAVEAT: a trace containing assumption steps is an INTERNAL artifact - the hypothesis units are not RUP/RAT-justified by construction, so the text rendering of such a trace is not a standalone external DRAT refutation (external tools must be fed assumption-free traces of plain solves; section 5). **Delete** (all kinds): database-mirror updates; DRAT deletions need no justification.

### 3. Justification semantics

**RUP (reverse unit propagation).** Clause C is RUP iff assuming ¬C (all literals false) and propagating derives a conflict. Learnt clauses are RUP by construction: conflict analysis resolves the falsified clause with reason clauses (Spec 06 section 3), so the learnt clause is a resolvent chain of database clauses — replaying ¬C's propagation walks the same implication graph.

**RAT (resolution asymmetric tautology).** C is RAT on pivot p (its first literal) iff every database clause D containing ¬p yields a resolvent (C \ {p}) ∪ (D \ {¬p}) that is RUP or tautological. The checker falls back to RAT when RUP fails; over-limit scans fail closed.

**Preprocessing order.** Deduplication and strengthening additions are RUP against the database *including* the original (add-then-delete); vivification additions are RUP against the database *minus* the candidate (delete-then-add, Spec 09 section 5). The trace order mirrors exactly these disciplines, so every step is checkable as recorded.

### 4. The empty clause

A refutation ends with the empty-clause Add: RUP holds because level-0 propagation of the formula already derives a conflict (the level-0 conflict that terminated the search, or the falsified-unit root flag). For UnsatUnderAssumptions, the hypothesis units are active at the empty clause's step, so the replay propagates the assumption-forced conflict.

### 5. The text format (design 6.4)

DRAT text: DIMACS-convention 1-based signed integers (variable v renders as v+1), clauses as space-separated literals terminated "0", deletions prefixed "d ". Axioms render as ordinary clause lines (harmless for external checkers: re-adding a present clause passes RUP through the existing copy). Assumption hypotheses render as ordinary unit additions - plain DRAT has no hypothesis syntax - which is precisely why assumption-bearing text traces are internal-checker-only (section 2 caveat): externally, those units would be unjustified additions. The writer pre-computes the exact byte size (`drat_size`) so truncation is a loud, exactly-sized error.

### 6. The internal checker (S43)

The checker replays the trace against the formula: axiom steps seed (with correspondence verification), hypothesis steps seed/remove, derived steps are RUP-then-RAT verified by a from-scratch wave-propagation engine sharing no state with the solver (independence is the point of a checker), deletions mirror. Outcomes: Valid (every step verified - and, with require_refutation set, the empty-clause derivation present), Invalid (the failing step and reason: JustificationFailed, AxiomMismatch, UnknownDeletionId, MalformedStep, MissingRefutation), or BudgetExhausted (the honest prefix; the step budget and the RAT scan limit are the denial-of-service bounds - an over-limit RAT scan reports BudgetExhausted, distinct from a genuine justification failure). Verified executably: proofs of random solves verify and corrupted traces are rejected (`property/drat_property_test.rs`).

## Algorithm

Recording (`ProofRecorder`): every database mutation emits one step (kind, proof id, literal extent) appended to the flat buffer; every clause addition registers its offset in the ascending offset-to-id map. Learnt additions are emitted after conflict analysis completes, so the RUP property of section 3 holds at the recording point.

Replay (`pub fn verify` in `cold/proof_output/drat_checker.rs`):

1. Seed the checker database from AxiomAdd steps, verifying the one-to-one correspondence with the supplied formula (section 2).
2. Walk the steps in order: AssumptionAdd/AssumptionDelete seed and remove without justification; Add steps are verified RUP first, then RAT on the pivot with the bounded scan; Delete steps mirror the database.
3. Stop at the first failing step (Invalid with its `InvalidReason`), at the step budget or RAT scan limit (BudgetExhausted), or at the end (Valid; with require_refutation, the empty-clause derivation must be present).

Time is O(steps x propagation cost) with the RAT scan bounded; space is the checker's own database, independent of the solver. Assumptions: the formula is supplied exactly as during the run; budgets are finite.

Text emission (`cold/proof_output/drat_writer.rs::write_drat(recorder: &ProofRecorder<'_>, out: &mut [u8]) -> Result<usize, WriterError>`): render each step in the section 5 format into a caller buffer sized by `drat_size(recorder: &ProofRecorder<'_>) -> Result<usize, WriterError>`; a short buffer is a loud, exactly-sized error.

## Invariants

1. Dense identity: proof ids are dense and 1-based; the offset map is append-only and strictly ascending (section 1).
2. Binding: axiom steps correspond one-to-one, in order, with the caller-supplied formula (section 2; checked at replay).
3. Construction soundness: every recorded Add is RUP or RAT at its recording point, including the preprocessing trace orders (sections 3 and 4; Spec 09 sections 2 through 5).
4. Independence: the checker shares no state with the solver; a replay engine bug cannot mask a solver bug (section 6).
5. Loudness: capacity exhaustion, truncation, and over-limit scans are loud errors or BudgetExhausted, never silent truncation or an unjustified Valid (sections 1, 5, 6).
6. Refutation honesty: Valid with require_refutation implies the empty clause was derived; otherwise MissingRefutation (section 6).

## Integration Points

Depends on:

- `hot/sat/cdcl.rs` and `hot/sat/solver.rs`, which emit learning, deletion, and assumption steps at the mutation points of Specifications 06 and 10.
- `hot/memory/arena.rs` for the step buffer, offset map, and literal blob.
- `config/limits.rs` for the recorder and checker capacities (`kProofSteps`, RAT scan limit, step budget).

Depended on by:

- `cold/proof_output/drat_writer.rs` (`write_drat`, `drat_size`) renders the text form.
- `cold/proof_output/drat_checker.rs` (`verify`, `CheckOutcome`, `InvalidReason`) replays traces; `tests/property/drat_property_test.rs` and `tests/golden/drat_proof_test.rs` (golden trace `tests/golden/golden/drat_php32.txt`) are the executable evidence.
- `cold/proof_output/tstp.rs` consumes recorder ids for the SAT-side proof presentation (Specification 14).

## Known Limitations

- Assumption-bearing traces are internal artifacts only; their text rendering is not a standalone external DRAT refutation (section 2 caveat, section 5).
- LRAT text emission (hint-annotated additions) is not implemented; the recorder carries stable ids but conflict analysis does not record the hint chain (ticket CEP-1059, co-design with the analyzer when an external LRAT consumer exists).
- The checker's RAT scan is budget-bounded and fails closed; a BudgetExhausted verdict certifies nothing beyond the processed prefix (section 6).
- The abstraction solver of Specification 12 records no DRAT trace; AVATAR conflict clauses are FO-justified lemmas (Spec 12 section 8).
