# Formal Specification 11: DRAT Proof Logging and Checking

Version: 0.1
Status: complete for the Phase 3 scope (design 11.1 S41/S42/S43, 18; design 26 build order "SAT: proof logging (DRAT)")
Role: normative reference for `hot/sat/proof.rs` (recorder), `cold/proof_output/drat_writer.rs` (text emission), and `cold/proof_output/drat_checker.rs` (internal checker); cited by their `CEP:HPC-PASS-LEGALITY` fields.
References: design 6.4, 11.1 S41-S43, 18; Heule, Hunt & Wetzler 2013/2014 (DRAT); Wetzler 2015 (LRAT); Formal Spec 06 (CDCL).

## 1. The record

The recorder holds a flat step buffer (kind: Add / Delete / AssumptionAdd / AssumptionDelete / AxiomAdd; proof id; literal extent), an append-only clause-offset-to-id map (ascending offsets; binary-searched), and a concatenated literal blob. Ids are dense and 1-based (`kFirstProofId`). Capacities are named; exhaustion is a loud error surfaced as Indeterminate — never a silent truncation.

## 2. Step kinds and the trace-to-formula binding

**AxiomAdd**: a problem clause (an axiom of the run). The checker seeds its database from axiom steps and verifies their one-to-one correspondence (in order) with the caller-supplied formula — the trace is thereby bound to exactly the problem it claims to refute. **Add**: a derived clause (RUP/RAT-justified). **AssumptionAdd/AssumptionDelete**: hypothesis units of an incremental call (Spec 10 section 2); the checker seeds and removes them without justification. **Delete** (all kinds): database-mirror updates; DRAT deletions need no justification.

## 3. Justification semantics

**RUP (reverse unit propagation).** Clause C is RUP iff assuming ¬C (all literals false) and propagating derives a conflict. Learnt clauses are RUP by construction: conflict analysis resolves the falsified clause with reason clauses (Spec 06 section 3), so the learnt clause is a resolvent chain of database clauses — replaying ¬C's propagation walks the same implication graph.

**RAT (resolution asymmetric tautology).** C is RAT on pivot p (its first literal) iff every database clause D containing ¬p yields a resolvent (C \ {p}) ∪ (D \ {¬p}) that is RUP or tautological. The checker falls back to RAT when RUP fails; over-limit scans fail closed.

**Preprocessing order.** Deduplication and strengthening additions are RUP against the database *including* the original (add-then-delete); vivification additions are RUP against the database *minus* the candidate (delete-then-add, Spec 09 section 5). The trace order mirrors exactly these disciplines, so every step is checkable as recorded.

## 4. The empty clause

A refutation ends with the empty-clause Add: RUP holds because level-0 propagation of the formula already derives a conflict (the level-0 conflict that terminated the search, or the falsified-unit root flag). For UnsatUnderAssumptions, the hypothesis units are active at the empty clause's step, so the replay propagates the assumption-forced conflict.

## 5. The text format (design 6.4)

DRAT text: DIMACS-convention 1-based signed integers (variable v renders as v+1), clauses as space-separated literals terminated "0", deletions prefixed "d ". Axioms render as ordinary clause lines (harmless for external checkers: re-adding a present clause passes RUP through the existing copy). The writer pre-computes the exact byte size (`drat_size`) so truncation is a loud, exactly-sized error.

## 6. The internal checker (S43)

The checker replays the trace against the formula: axiom steps seed (with correspondence verification), hypothesis steps seed/remove, derived steps are RUP-then-RAT verified by a from-scratch wave-propagation engine sharing no state with the solver (independence is the point of a checker), deletions mirror. Outcomes: Valid (every step verified), Invalid (the failing step and reason: JustificationFailed, AxiomMismatch, UnknownDeletionId, MalformedStep), or BudgetExhausted (the honest prefix; the step budget and the RAT scan limit are the denial-of-service bounds). Verified executably: proofs of random solves verify and corrupted traces are rejected (`property/drat_property_test.rs`).
