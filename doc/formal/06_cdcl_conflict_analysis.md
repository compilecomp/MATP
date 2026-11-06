# Formal Specification 06: CDCL: Implication Graphs, First-UIP Conflict Analysis, Learning, Backjumping, VSIDS, Restarts, and Learnt-Clause Deletion

## Abstract

This document is the normative reference for `hot/sat/cdcl.rs`, `hot/sat/vsids.rs`, `hot/sat/restart.rs`, `hot/sat/solver.rs`, and `hot/sat/registry.rs`, cited by their `CEP:HPC-PASS-LEGALITY` fields and by the CDCL property and fuzz tests (design sections 11.1-11.6; section 9 is the Phase 3 amendment delivered with CEP-1003). It defines the implication graph, first-UIP conflict analysis, learnt-clause minimization, the CDCL loop with its outcome soundness, VSIDS decision heuristics with phase saving, the restart schedules, and the clause registry with learnt-clause deletion. Inputs are the clause database and the trail state of Specification 05; outputs are learnt clauses with LBD metadata, backjump levels, solve verdicts (`SolveResult`), and registry deletion decisions. References: Marques-Silva & Sakallah 1996 (GRASP); Moskewicz et al. DAC 2001 (Chaff, VSIDS); Zhang et al. 2001 (LBD-era learning); Sorensson & Biere 2009 (minimizing learned clauses); Luby, Sinclair & Zuckerman 1993 (restart schedule); Biere, Heule, van Maaren & Walsh, *Handbook of Satisfiability* 2009, ch. 4.

## Formal Definitions

### 1. Prerequisites (from Spec 05)

Trails, decision levels, watched literals, and BCP soundness are specified in Formal Spec 05 and unchanged. Phase 2 adds two per-variable arrays maintained by the core:

- `level(v)`: the decision level at which `v` was assigned (0 for root assignments and unassigned variables),
- `reason(v)`: the antecedent clause of `v` — the clause whose unit propagation assigned `v` — or "none" for decisions and for reasonless root assignments made through `assign` (the reasonless entry point used by decisions and asserting learnt units).

**Invariant R1.** Every propagated literal's reason is the clause that propagated it, recorded at assignment time by BCP and by unit-clause attachment; decisions and reasonless root assignments carry no reason. Level-0 *propagated* units do carry their unit clause as reason (the attaching clause), which is MiniSat-conformant and harmless: the analysis in section 3 never resolves a level-0 variable (its literals are excluded from learnt clauses entirely). Cancelling to a level clears both arrays for every popped variable, keeping R1 invariant across backjumps.

### 2. The implication graph

For the current assignment, the **implication graph** is the directed graph whose nodes are the assigned literals and whose edges go from each literal of a reason clause (all false) to the literal the clause propagated. Decisions and reasonless root assignments have no incoming edges; every path into a node stays within levels `<= level(node)`, and a propagated node's non-decision ancestors at the same level were assigned before it on the trail.

**Definition (conflict).** A clause is *violated* when all its literals are false. BCP reports the first violated clause it touches.

### 3. First-UIP analysis

Let `L` be the current decision level (`>= 1`; a conflict at level 0 is refutation, the loop's step 2 in the Algorithm section) and `C` the violated clause.

The analysis walks the trail backwards from the top. Variables of `C` at level `L` are *on the path*; variables of `C` at levels `1..L-1` enter the learnt clause directly (level-0 variables never do: their negation is already entailed at the root, so dropping them preserves the clause's status as a consequence of the formula). When the walk reaches a path variable `v`, it resolves `v` away against `reason(v)`: every other literal of the reason is either level 0, already accounted for, or newly put on the path (level `L`) or into the learnt clause (lower level).

**Theorem (unique first UIP).** The walk terminates with `path_count = 0` at exactly one trail entry `p`, and `p` is the unique implication point at level `L` such that every path from a level-`L` leaf of the conflict to a decision passes through `p` or a level-`< L` node.

*Proof sketch.* Each trail step either skips a non-path variable or resolves exactly one path variable; the path count decreases by one per resolution and increases only by resolving in new level-`L` variables that lie *below* the current trail index (they were assigned earlier), so the walk cannot revisit positions and the count reaches zero exactly at the last remaining level-`L` path variable — the first UIP (Marques-Silva & Sakallah 1996). ∎

**Theorem (learnt clause).** Let `D` be the set of lower-level literals accumulated by the walk and `p` the first UIP. The clause `(-p or D)` — position 0 holds the negated UIP — is a logical consequence of the clause database.

*Proof.* `(-p or D)` is the resolvent of the violated clause with the reason clauses of every resolved path variable, in reverse trail order: each resolution step eliminates a literal present in both clauses, and resolution is a sound inference. The level-0 literals dropped at seeding are entailed at the root (Spec 05 BCP soundness), so their removal preserves consequence. ∎ Verified executably: every model of the original formula satisfies every learnt clause (`tests/property/cdcl_property_test.rs::learnt_clauses_are_entailed`), and every learnt literal is false under the assignment at analysis time (same test).

**Backjump level.** After the walk, the *backjump level* is the maximum `level(q)` over `q in D` (0 when `D` is empty). The solver cancels to that level; the learnt clause is then unit with `-p` as its asserting literal, which is assigned with the learnt clause as its reason.

### 4. Learnt-clause minimization

**Definition (redundant literal).** A literal `q in D` is *redundant* iff every variable of `reason(q)`'s chain closure is either level 0, already in the learnt set (seen), or itself recursively redundant.

**Theorem (minimization preserves entailment).** Removing redundant literals from the learnt clause yields a clause still entailed by the database.

*Proof sketch.* Removing `q` is self-subsuming resolution against `reason(q)`: the resolvent of the learnt clause with `reason(q)` on `q` subsumes the original learnt clause, and iterating along a well-founded chain (reasons reference strictly earlier trail positions) terminates (Sorensson & Biere 2009). Level-0 variables are droppable by the same root-entailment argument as in section 3. ∎ The implementation checks redundancy iteratively with an explicit stack and unwinds temporary marks on failure; decision variables block removal (no reason exists).

**Quality metadata.** The LBD is the number of distinct decision levels in the final learnt clause (design 11.1 S23), recorded on the clause for the future deletion policy (Phase 3, ticket CEP-1003).

### 6. VSIDS and phase saving

**Decision rule.** Among unassigned variables, decide the one with the highest key `(activity desc, variable index asc)`; assign it the polarity saved from its last assignment, or the default `kSatDefaultPhasePositive` if never assigned.

**Activity.** Every variable newly marked during conflict analysis is bumped by the current increment; after each conflict the increment grows by `100 / kSatVsidsDecayPercent` (MiniSat-style geometric decay, design 11.1 S13). When the increment passes `kSatVsidsActivityCeiling`, all activities and the increment are multiplied by `kSatVsidsRescaleFactor` — an order-preserving positive constant — keeping every score finite and the key total, hence the decision order a pure function of the conflict history (CEP&CC 38.10 determinism).

**Heap discipline.** Assigned variables leave the heap lazily (discarded at pick time); backtracking reinserts every unassigned variable, so the heap always contains every unassigned variable (the invariant behind "pick returns None means SAT").

**Phase saving.** The solver saves each variable's polarity when unassigning (cancel) and optionally resets all saved phases on restart (design 11.1 S17, configurable at solver construction).

### 7. Restarts

**Luby schedule (default).** The k-th restart (k = 0, 1, 2, ...) occurs when `kSatRestartBaseInterval * Luby(k+1)` conflicts have accumulated since the previous restart, where `Luby` is the canonical sequence 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ... (Luby, Sinclair & Zuckerman 1993). The first sixteen values are pinned to the design's literal sequence by `tests/unit/hot/sat_restart_test.rs::luby_sequence_matches_design`.

**Geometric alternative.** The threshold grows by `kSatRestartGeometricFactorPercent / 100` per restart (design 11.5), with saturating arithmetic.

**Restart effect.** Cancelling to level 0 discards the assignment stack and keeps all learnt clauses (the learning is monotone), so restarts cannot lose information; both schedules grow without bound, so the search cannot livelock on shallow restarts.

### 9. The clause registry and learnt-clause deletion (Phase 3)

The clause registry (`hot/sat/registry.rs`, design 11.1 S4, ticket CEP-1003) is the enumerable clause database: one dense entry (clause offset, activity score, tombstone) per registered clause, appended in strictly ascending clause-offset order with the entry index as the registration age. The storage deleted bit is the single source of truth for liveness; the tombstone mirrors it.

**Reduction trigger.** After a conflict, if the live-learnt count reaches the trigger (`kSatMaxLearntClauses` in production; injectable for tests), one reduction runs: it locks, sorts, deletes, and unlocks.

**Locking (S29).** Before any victim is chosen, every clause that is the current reason of an assigned variable, plus the active conflict clause, is marked locked. Locked clauses can never be victims, so no surviving reason ever points at a deleted record and no in-flight analysis loses its conflict clause. Locks are released in the reduction epilogue.

**Victim selection (design 11.6 total order).** Live unlocked learnts are sorted best-first under the strict lexicographic key: LBD ascending, then age ascending (older clauses are better; ages are unique so the activity key is vacuous in the strict order — it is kept for the documented tie-break role only). The best `live / kSatLearntReduceDivisor` entries survive; the rest are deleted. The sort is a deterministic heapsort under this total key, so the victim set is a pure function of the database state (CEP&CC 38.10).

**Deletion effect and safety.** A deletion writes the proof-deletion step first (S41: the trace can never miss a database mutation), then sets the storage deleted bit and the registry tombstone. BCP skips deleted records (Spec 05 section 6 amendment), so lazy watch-list links left by deleted clauses are inert. Reduction runs between conflicts with a quiescent core; both first-UIP analysis (section 3) and `analyze_final` skip level-0 variables, so level-0 reason records — which reduction may legitimately leave pointing at deleted clauses — are never consulted semantically.

**Completeness.** Reduction deletes only learnt clauses; problem clauses and locked clauses always survive, and CDCL with bounded learnt deletion remains refutationally complete (Handbook of Satisfiability, ch. 4). End-to-end correctness with reduction firing is verified against the brute-force oracle in `tests/property/cdcl_property_test.rs::solve_agrees_with_brute_force` (trigger injected small so reduction runs during the tested searches) and the policy mechanics in `tests/unit/hot/sat_registry_test.rs::{reduction_keeps_best_half, locked_clauses_survive, reduction_trigger_enforced, reduction_marks_deleted, bcp_skips_deleted, reduction_records_proof_deletions}`.

## Algorithm

The CDCL loop (`hot/sat/solver.rs`, `CdclSolver`):

1. Propagate to fixpoint (Specification 05).
2. On conflict: if the level is 0, return **Unsatisfiable** (the empty resolvent is entailed). Otherwise analyze (sections 3-4), learn the clause, backjump to the backjump level, and assert the negated UIP.
3. On quiescence: if the restart condition holds (section 7), cancel to level 0 and continue; else decide (section 6). If no unassigned variable remains, return **Satisfiable** with the current assignment as the model.

**Theorem (soundness of outcomes).** Satisfiable implies the returned assignment satisfies every clause (the trail only holds BCP-consistent assignments, and quiescence plus full assignment means no clause is violated — Spec 05 fixpoint completeness). Unsatisfiable implies the formula has no model: the level-0 conflict's resolvent chain reaches the empty clause, and resolution is sound, so the empty clause is entailed by the formula.

*Proof.* Standard (Handbook of Satisfiability, ch. 4). ∎ Both directions are verified against a brute-force oracle on random formulas (`tests/property/cdcl_property_test.rs::solve_agrees_with_brute_force`, `models_satisfy_formulas`; fuzz-level in `tests/fuzz/cdcl_fuzz_test.rs`).

**Termination.** Without clause deletion the learnt set grows monotonically and each learnt clause excludes at least the current assignment prefix; with finitely many assignments the search cannot cycle. The conflict budget `kSatMaxConflicts` bounds adversarial workloads explicitly (design 20.1/20.2): exhaustion returns Indeterminate, never a wrong answer.

Time per conflict is dominated by the backward trail walk (O(trail length) with O(1) amortized watch scans of Specification 05); space is O(learnt clauses x clause length) under the registry caps. Assumptions: invariants R1, T1, T2, W1, W2 hold; reduction runs only between conflicts (section 9).

### 8. Cost evidence

Measured medians on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release, 2026-10-10 (bench CEP-BENCH-0009):

- Conflict analysis (fixed level-2 graph, 3-literal learnt with one minimized literal): 697.42 cycles (`benches/artifacts/cdcl_analyze.json`).
- Decision cycle (bump + pick + reinsert over a 256-variable heap): 420.41 cycles (`benches/artifacts/cdcl_decide.json`).
- End-to-end PHP(3,4) refutation: 5372.33 cycles per conflict (`benches/artifacts/cdcl_solve_per_conflict.json`).
- Propagation step including reason and level recording: 54.90 cycles (bench CEP-BENCH-0005, re-baselined from the 44.53 Phase 1 figure with the two added per-assignment stores).

Disassembly evidence: `benches/artifacts/disasm_cdcl.txt`.

## Invariants

1. Reason fidelity: every propagated literal's reason is the clause that propagated it; decisions and reasonless root assignments carry none (R1, section 1).
2. Entailment of learning: every learnt clause is a logical consequence of the database (Theorems of sections 3 and 4; `tests/property/cdcl_property_test.rs::learnt_clauses_are_entailed`).
3. Asserting learning: every learnt literal is false under the assignment at analysis time (section 3, same test).
4. Heap completeness: the VSIDS heap contains exactly the unassigned variables; "pick returns None" coincides with a full assignment (section 6).
5. Decision determinism: the decision order is a pure function of the conflict history (total key with order-preserving rescale, CEP&CC 38.10; section 6).
6. Restart monotonicity: restarts keep all learnt clauses and both schedules grow without bound (section 7).
7. Reason safety under deletion: locked clauses (reasons and the conflict clause) are never deletion victims (section 9; `tests/unit/hot/sat_registry_test.rs::locked_clauses_survive`).
8. Deterministic reduction: the victim set is a pure function of the database state under the LBD/age key (section 9; `::reduction_keeps_best_half`).
9. Outcome soundness: Satisfiable answers carry satisfying assignments; Unsatisfiable answers are refutations; budget exhaustion is Indeterminate (Theorem of the Algorithm section; `::solve_agrees_with_brute_force`).

## Integration Points

Depends on:

- `hot/sat/database.rs` (`SatCore::assign_with_reason(&self, literal: SatLiteral, reason: u32) -> Result<(), SatCoreError>`, `SatCore::value_of_literal(&self, literal: SatLiteral) -> SatValue`) for assignments, levels, and reasons.
- `hot/sat/bcp.rs` (`propagate(&self) -> Result<PropagationOutcome, SatCoreError>`) for propagation to fixpoint.
- `hot/sat/vsids.rs` (`VsidsHeap::bump(&self, variable: u32)`, `VsidsHeap::decay(&self)`) and `hot/sat/restart.rs` (`RestartScheduler::should_restart(&self) -> bool`) for heuristics.
- `hot/sat/registry.rs` (`ClauseRegistry::delete(&self, storage: &ClauseStorage<'_>, offset: u32) -> Result<(), RegistryError>`) for learnt deletion.
- `config/limits.rs` (`kSatMaxConflicts`, `kSatMaxLearntClauses`, `kSatVsidsDecayPercent`, `kSatRestartBaseInterval`) for every policy constant.

Depended on by:

- `hot/sat/solver.rs` exposes `SolveResult` and the incremental assumption interface consumed by Specification 10.
- `hot/avatar/controller.rs` runs assumption-based solves per split stack and consumes failed cores (Specification 12).
- `hot/sat/proof.rs` records the learning and deletion steps consumed by the DRAT trace (Specification 11).
- `hot/conjecture/filter.rs` runs bounded mini CDCL refutations (Specification 16).

## Known Limitations

- Conflict budget exhaustion returns Indeterminate by design (bounded failure, design 20.1/20.2); the solver is not an any-time prover.
- The VSIDS heap is a binary heap; the two-level bucket heap (E-prover style, ticket CEP-1030) and watched-binaries fast path in analysis (CEP-1031) are not implemented.
- Solver-loop micro-optimizations (batched trail reads, copy-free learnt handoff, ticket CEP-1032) are "measure first" work items.
- Reduction is triggered by the learnt count only; an activity-driven trigger is not provided (the activity key is documented as vacuous in the victim order, section 9).
