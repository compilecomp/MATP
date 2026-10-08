# Formal Specification 05: SAT Foundations — Literals, Clauses, Trails, Watched Literals, and BCP Soundness

Version: 0.1
Status: complete for the Phase 1 subset (components S1-S6, S9-S11 of design section 11.1)
Role: normative reference for `hot/sat/*`; cited by their `CEP:EVIDENCE` fields and by the BCP property tests.
References: Moskewicz et al., DAC 2001 (Chaff); Biere, SAT 2020 (CaDiCaL); design sections 11.1-11.4.

## 1. Propositional variables and literals

Variables are dense indices `0..n`. A literal is a variable with a polarity; MAPT packs a literal into one u32 as `(var << 1) | sign` with `sign = 1` for negated literals. The encoding is injective and negation is `l xor 1`.

An assignment `A : V -> {true, false}` extends to literals by `A(not-l) = not A(l)`.

## 2. Clauses and satisfaction

A clause is a disjunction of literals; the empty clause is false under every assignment. A clause `C` is satisfied by `A` iff some `L in C` has `A(L) = true`; violated iff all literals are false; unit iff exactly one literal is non-false and unassigned.

## 3. Trails and decision levels

The trail is the sequence of assigned literals in assignment order, partitioned into decision levels: level 0 is the root (assumption-free propagation), level `k >= 1` starts with the k-th decision and continues with its propagated literals.

**Invariant T1.** A variable occurs at most once on the trail between backtracks (a variable is assigned once; backtracking removes assignments).

**Invariant T2.** Every trail entry after the first of its level is implied by unit propagation from earlier entries and the clause database (their reason clauses — recorded as such by BCP).

Backtracking `cancel_until(l)` removes all entries above level `l` and unassigns exactly their variables. Correctness follows from T1 and the trail partition.

## 4. Watched literals

For each clause of length >= 2, two of its literals are watched (positions 0 and 1 in MAPT's storage). The watch invariant:

**Invariant W1.** A clause `C` is in the watch list of exactly the literals stored at its watch positions.

**Invariant W2 (scheme invariant).** If both watches of `C` are false under `A`, then `C` is violated or was already handled (conflict reported); if exactly one watch is false, `C` has been inspected and either a new watch was found, the clause propagated its other watch, or a conflict was reported.

The amortization argument (Chaff): BCP touches a clause only when one of its two watches becomes false, so total work across a propagation cascade is bounded by the number of literal falsifications times the clause scan cost — O(1) amortized per propagation step.

## 5. Boolean constraint propagation

`BCP(A, N)` repeatedly applies unit propagation to fixpoint: while some clause `C in N` is unit with non-false literal `L`, assign `A(L) = true`; if some clause is violated, report conflict.

**Definition (propagated literal).** `L` is propagated by `C` iff `C` is unit under the current assignment and `L` is its non-false literal; then every assignment satisfying `N` minus nothing (all clauses) must set `L` true.

**Theorem (BCP soundness).** Every literal assigned by BCP is true in every model of the clause set restricted to the current partial assignment.

*Proof.* Induction over propagation steps. The base (decisions and units added at level 0) is by definition of the input problem. For a step propagating `L` by clause `C = (L or L_1 or ... or L_k)`: all `L_i` are false under the current assignment `A`; any model `M` extending `A` satisfies `C`, and since `M(L_i) = false` for all `i`, `M(L) = true`. By induction the current assignment is entailed, so `L` is entailed. ∎

**Theorem (BCP completeness at fixpoint).** If `BCP` terminates without conflict, no clause is unit-and-unassigned, and no clause is violated.

*Proof.* The loop exits only when the queue is drained; the scan of a falsified literal's watch list checks each watched clause; a clause that is unit would have enqueued its literal (making it non-unassigned), and a violated clause would have been reported. Watch invariant W1 guarantees every affected clause is reachable from the falsified literal's list. ∎

Both theorems are tested against a brute-force oracle: `tests/property/bcp_property_test.rs::propagation_is_sound` (all-models check) and `::propagation_reaches_fixpoint`.

## 6. Watch move correctness

When a watch `L` of clause `C` becomes false, BCP searches a non-false replacement `L'` among the remaining literals and swaps `L'` into the watch slot. The swap preserves the literal multiset of `C` (tested in `tests/unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents`) and re-establishes W1 by unlinking `C` from `L`'s list and linking it into `L'`'s list (tested by `tests/property/bcp_property_test.rs::watch_lists_consistent`).

## 7. Bounded resources

- Trail capacity and level count are sized by the declared variable count (sound by Invariant T1: at most one trail entry per variable, at most one level per decision plus the root).
- Clause length is bounded by `kMaxSatClauseLiterals`; learnt count by `kSatMaxLearntClauses` (deletion policy is Phase 2, ticket CEP-1003).
- Variables are bounded by `kMaxSatVariables`; literal construction rejects larger indices (security test `tests/security/literal_encoding_test.rs`).

## 8. Cost evidence

The propagation step (queue dequeue, value evaluation, watch scan, unit assignment) is measured at 44.5 cycles median on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release profile: bench CEP-BENCH-0005, artifact `benches/artifacts/sat_bcp_step.json`; disassembly in `benches/artifacts/disasm_sat.txt`.
