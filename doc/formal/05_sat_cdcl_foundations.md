# Formal Specification 05: SAT Foundations: Literals, Clauses, Trails, Watched Literals, and BCP Soundness

## Abstract

This document is the normative reference for `hot/sat/*` (literal encoding, assignment store, trail, watch lists, clause database, BCP engine), cited by their `CEP:EVIDENCE` fields and by the BCP property tests (design sections 11.1-11.4). It defines the literal packing, clause satisfaction, the decision-level trail, the two-watch scheme, and Boolean constraint propagation with its soundness and fixpoint-completeness theorems. Inputs are literal assignments and the clause database; outputs are propagated assignments, conflict reports, and watch-list state that preserves the scheme invariants. References: Moskewicz et al., DAC 2001 (Chaff); Biere, SAT 2020 (CaDiCaL).

## Formal Definitions

### 1. Propositional variables and literals

Variables are dense indices `0..n`. A literal is a variable with a polarity; MAPT packs a literal into one u32 as `(var << 1) | sign` with `sign = 1` for negated literals. The encoding is injective and negation is `l xor 1`.

An assignment `A : V -> {true, false}` extends to literals by `A(not-l) = not A(l)`.

### 2. Clauses and satisfaction

A clause is a disjunction of literals; the empty clause is false under every assignment. A clause `C` is satisfied by `A` iff some `L in C` has `A(L) = true`; violated iff all literals are false; unit iff exactly one literal is non-false and unassigned.

### 3. Trails and decision levels

The trail is the sequence of assigned literals in assignment order, partitioned into decision levels: level 0 is the root (assumption-free propagation), level `k >= 1` starts with the k-th decision and continues with its propagated literals.

**Invariant T1.** A variable occurs at most once on the trail between backtracks (a variable is assigned once; backtracking removes assignments).

**Invariant T2.** Every trail entry after the first of its level is implied by unit propagation from earlier entries and the clause database (their reason clauses — recorded as such by BCP).

Backtracking `cancel_until(l)` removes all entries above level `l` and unassigns exactly their variables. Correctness follows from T1 and the trail partition.

### 4. Watched literals

For each clause of length >= 2, two of its literals are watched (positions 0 and 1 in MAPT's storage). The watch invariant:

**Invariant W1.** A clause `C` is in the watch list of exactly the literals stored at its watch positions.

**Invariant W2 (scheme invariant).** If both watches of `C` are false under `A`, then `C` is violated or was already handled (conflict reported); if exactly one watch is false, `C` has been inspected and either a new watch was found, the clause propagated its other watch, or a conflict was reported.

The amortization argument (Chaff): BCP touches a clause only when one of its two watches becomes false, so total work across a propagation cascade is bounded by the number of literal falsifications times the clause scan cost — O(1) amortized per propagation step.

### 5. Boolean constraint propagation

`BCP(A, N)` repeatedly applies unit propagation to fixpoint: while some clause `C in N` is unit with non-false literal `L`, assign `A(L) = true`; if some clause is violated, report conflict.

**Definition (propagated literal).** `L` is propagated by `C` iff `C` is unit under the current assignment and `L` is its non-false literal; then every assignment satisfying `N` minus nothing (all clauses) must set `L` true.

**Theorem (BCP soundness).** Every literal assigned by BCP is true in every model of the clause set restricted to the current partial assignment.

*Proof.* Induction over propagation steps. The base (decisions and units added at level 0) is by definition of the input problem. For a step propagating `L` by clause `C = (L or L_1 or ... or L_k)`: all `L_i` are false under the current assignment `A`; any model `M` extending `A` satisfies `C`, and since `M(L_i) = false` for all `i`, `M(L) = true`. By induction the current assignment is entailed, so `L` is entailed. ∎

**Theorem (BCP completeness at fixpoint).** If `BCP` terminates without conflict, no clause is unit-and-unassigned, and no clause is violated.

*Proof.* The loop exits only when the queue is drained; the scan of a falsified literal's watch list checks each watched clause; a clause that is unit would have enqueued its literal (making it non-unassigned), and a violated clause would have been reported. Watch invariant W1 guarantees every affected clause is reachable from the falsified literal's list. ∎

Both theorems are tested against a brute-force oracle: `tests/property/bcp_property_test.rs::propagation_is_sound` (all-models check) and `::propagation_reaches_fixpoint`.

## Algorithm

The propagation engine (`hot/sat/bcp.rs::propagate`) drains the assignment queue:

1. Dequeue one newly assigned literal `L`.
2. Scan the watch list of `not-L`; for each watched clause, evaluate its other watch and remaining literals through the assignment store.
3. On a non-false replacement literal, swap it into the watch slot (section 6); on a unit clause, enqueue and assign the remaining literal with the clause as reason; on a violated clause, stop and report the conflict.
4. Repeat until the queue is empty (fixpoint, `PropagationOutcome`) or a conflict is found.

Time is O(1) amortized per propagation step by the Chaff argument of section 4; space is two watch entries per long clause plus one trail entry per assignment. Assumptions: the watch scheme invariants W1 and W2 hold before each call; capacities sized per section 7.

### 6. Watch move correctness

When a watch `L` of clause `C` becomes false, BCP searches a non-false replacement `L'` among the remaining literals and swaps `L'` into the watch slot. The swap preserves the literal multiset of `C` (tested in `tests/unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents`) and re-establishes W1 by unlinking `C` from `L`'s list and linking it into `L'`'s list (tested by `tests/property/bcp_property_test.rs::watch_lists_consistent`).

**Amendment (Phase 3, deleted records).** Clause deletion (the learnt-clause reduction of Spec 06 section 9 and SAT preprocessing) sets the record's deleted bit at deletion time and removes the record's watch-list links **lazily**: BCP skips any record whose deleted bit is set when the scan reaches it, so the section's watch-move swap runs only on live records and the stale links left behind by deleted clauses are inert. Watch-list consistency (W1) is therefore preserved without an eager unlink pass (tested by `tests/unit/hot/sat_registry_test.rs::bcp_skips_deleted` and the deleted-record handling of `tests/unit/hot/sat_bcp_test.rs`).

### 7. Bounded resources

- Trail capacity and level count are sized by the declared variable count (sound by Invariant T1: at most one trail entry per variable, at most one level per decision plus the root).
- Clause length is bounded by `kMaxSatClauseLiterals`; learnt count by `kSatMaxLearntClauses` (deletion policy delivered with the clause registry, Spec 06 section 9, ticket CEP-1003).
- Variables are bounded by `kMaxSatVariables`; literal construction rejects larger indices (security test `tests/security/literal_encoding_test.rs`).

### 8. Cost evidence

The propagation step (queue dequeue, value evaluation, watch scan, unit assignment) is measured at 44.5 cycles median on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release profile: bench CEP-BENCH-0005, artifact `benches/artifacts/sat_bcp_step.json`; disassembly in `benches/artifacts/disasm_sat.txt`.

## Invariants

1. Single assignment: a variable occurs at most once on the trail between backtracks (T1, section 3).
2. Propagation justification: every trail entry after the first of its level carries the reason clause that unit-propagated it (T2, section 3).
3. Watch correspondence: a clause is in the watch list of exactly its two stored watch literals (W1, section 4; `tests/property/bcp_property_test.rs::watch_lists_consistent`).
4. Scheme safety: two false watches imply violation handled; one false watch implies the clause was inspected and resolved per W2 (section 4).
5. Soundness: every propagated literal is entailed by the clause set under the current partial assignment (Theorem, section 5; `tests/property/bcp_property_test.rs::propagation_is_sound`).
6. Fixpoint completeness: quiescence without conflict leaves no unit-and-unassigned and no violated clause (Theorem, section 5; `::propagation_reaches_fixpoint`).
7. Multiset preservation: watch moves never change a clause's literal multiset (section 6; `tests/unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents`).
8. Deleted-record laziness: BCP skips records with the deleted bit set, so stale links of deleted clauses are inert (section 6 amendment; `tests/unit/hot/sat_registry_test.rs::bcp_skips_deleted`).

Violation of any invariant is a reported error or a debug assertion; BCP never returns a propagated assignment that violates invariant 5.

## Integration Points

Depends on:

- `hot/memory/arena.rs` (`Arena`) for the trail, watch lists, and clause storage.
- `config/limits.rs` (`kMaxSatVariables`, `kMaxSatClauseLiterals`, `kSatMaxLearntClauses`) for the bounds of section 7.

Depended on by:

- `hot/sat/cdcl.rs` (`ConflictAnalyzer::analyze`) consumes trails, reasons, and the database for first-UIP analysis (Specification 06).
- `hot/sat/solver.rs` (`CdclSolver::new(variables: u32, policy: RestartPolicy, reset_phases_on_restart: bool) -> Self`) drives propagation, decisions, and backtracking.
- `hot/sat/preprocess.rs` and `hot/sat/registry.rs` mutate the database and rely on the deleted-record laziness of section 6.
- `hot/avatar/` asserts and retracts assumption literals through the incremental interface (Specification 12).

## Known Limitations

- The specification covers components S1-S6, S9-S11 of design section 11.1 for the Phase 1 subset, plus the Phase 3 deleted-record amendment; conflict analysis and the solver loop are Specification 06.
- Blocking-literal caches in watch lists (MiniSat blockers, ticket CEP-1017), batched literal reads (CEP-1015), and struct-of-arrays value storage (CEP-1016) are not implemented; all three are "measure first" work items.
- Watch lists are intrusive singly linked lists; deletion of clauses leaves inert links until arena compaction (CEP-1007).
