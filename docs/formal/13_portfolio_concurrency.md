# Formal Specification 13 — Portfolio Concurrency

## 1. Scope

This document is normative for the Phase 4 concurrency layer (design section 19): the bounded MPMC clause-sharing pool, the Chase-Lev work-stealing deque, the portable clause codec, and the portfolio manager's worker protocol. Every `CEP:HPC-PASS-LEGALITY` comment in `hot/concurrency/` and `cold/portfolio/` cites a definition or theorem here.

References: Chase and Lev, SPAA 2005 ("Dynamic Circular Work-Stealing Deque"); Vyukov, bounded MPMC queue (algorithm description, 1024cores.net); design 19.5 (determinism).

## 2. The sharing pool (design 19.2)

**Definition 2.1 (Cell protocol).** The pool is an array of cells, one sequence number per cell (initialized to the cell index), a monotonic produce cursor, and a monotonic consume cursor. Enqueue at position p claims cell p mod n by CAS on the produce cursor (Relaxed - the claim is exclusive but unordered), writes the record words (Relaxed - the cell is the claimant's until publication), and publishes by storing seq = p + 1 (Release - pairs with every consumer's Acquire seq load). Dequeue at position q claims by CAS on the consume cursor when seq = q + 1 (Acquire), reads the words (Relaxed - visibility carried by the Acquire), and recycles by storing seq = q + n (Release), freeing the cell exactly for the produce position one full turn ahead.

**Theorem 2.1 (Exactly-once delivery).** Every successfully enqueued record is delivered to exactly one successful dequeue, uncorrupted. *Proof sketch:* claims are exclusive (the cursors are CAS-advanced and monotonic); a record is published exactly once (the sequence store); a consumer reads only published cells (the seq = q+1 check) and claims exclusively; recycling defers reuse by a full turn, so a producer never overwrites an unread cell (the Release/Acquire pair on the recycle orders the consumer's reads before the overwrite).

**ABA.** Cursors are monotonic and cell reuse requires the full-turn sequence handshake: a stale claimant's CAS compares full cursor values, which never repeat.

**Bounds.** Full at capacity (`PoolError::Full` - the exporter counts and skips, design 19.2's bounded queue); retry budget per call bounds spinning (CEP&CC 22.10).

## 3. The work-stealing deque (design 19.3)

**Definition 3.1 (Protocol).** Owner push at bottom b: slot store (Relaxed - owner-exclusive until publication) then `bottom.fetch_add(1)` (Release - publication). Owner pop: `bottom.fetch_sub(1)` (SeqCst) reserves slot b-1; top load (Acquire); three cases - t < b-1 (owner-exclusive take), t > b-1 (empty; restore), t = b-1 (the last element: the top CAS t → t+1 with SeqCst success decides the winner against thieves). Thief steal: top load (Acquire), bottom load (Acquire, ordered after top for the conservative emptiness check), slot read (Relaxed - visibility carried by the Acquire chain), top CAS t → t+1 (SeqCst) claims.

**Theorem 3.1 (Linearization).** The last-element race linearizes at the top CAS: exactly one of {owner pop, thief steal} wins, and the winner is the sole deliverer. The SeqCst order between the owner's `fetch_sub` and the thieves' CAS is the standard Chase-Lev requirement that prevents both sides taking the same element.

**ABA.** Top and bottom are monotonic; the CAS compares full cursor values. Ring-slot reuse after a full turn carries a different cursor value, so a stale claim never matches.

**Role in the portfolio (Spec 13 section 5).** The pool is the primary sharing bus; each worker's deque is the overflow backlog: pool-full exports spill into the owner's deque as deferred frames (length word, then the record words, in push order), and the steal side - the oldest end - reads frames in order for any thief, including the owner thread. This is design 19.3's work-stealing load balancing applied to the sharing backlog.

## 4. The portable clause codec

**Definition 4.1 (Record layout).** Word 0: [total words:16][literal count:16][reserved:32]. Per literal: one polarity word (0 or 1), then the atom's node words in prefix order (parent first, children left to right). Node word: [tag:3][symbol or variable id:32][child count:10]. Tags follow `TermTag`; Lambda is rejected (Phase 5 scope).

**Lemma 4.1 (Tree encoding).** The prefix node-word sequence determines the term tree exactly (the child counts guide the rebuild), so decode(encode(c)) = c over interned stores with the same symbol-id table. *The symbol-table contract:* every worker rebuilds its table from the same declaration list in the same order (the ids are assignment-order-dense), so the codec's symbol ids agree across arenas.

**Contract.** The record is fixed-budget (`kSharedClauseMaxWords`); over-budget clauses are not exported (counted - design 19.2 degradation). The decoder validates every header, tag, child count, symbol id, and variable id before interning (untrusted-record discipline).

## 5. The worker protocol (design 19.1)

**Definition 5.1 (Slice loop).** Each worker: (1) boundary checks (stop flag; cancellation); (2) import phase - steal deferred frames from every deque (own included), then dequeue the pool, decoding and adding each record as an Input-role clause; (3) search phase - one wall-clock slice of the given-clause loop (or the AVATAR protocol), the slice deadline injected through the clock-free CEP-1005 callback; (4) export phase - an incremental id scan of the worker's new clauses, filtered by design 19.2's quality list (weight below `kSharedClauseMaxWeight`, LBD below `kSharedClauseMaxLbd`, rule in {resolution, superposition, factoring}) and the codec budget, enqueued to the pool with deque spill.

**Theorem 5.1 (Import soundness).** An imported clause is a logical consequence of the shared problem: the exporter derived it from the same inputs (the export filter admits only derived rules), so adding it as an Input-role clause preserves the search's invariant that every clause is a consequence of the inputs. Soundness is therefore independent of interleaving.

**Theorem 5.2 (First-to-finish linearization).** The winner CAS on the shared slot (SeqCst) linearizes the race: exactly one winner; the stop flag (SeqCst - nothing rides on its order, only visibility) cancels the other workers at their next boundary. A loser that finished inside the same slice window also reports Theorem - both outcomes are legitimate; the manager reports the CAS winner.

## 6. Determinism (design 19.5)

A single worker without imports is exactly the Phase 3 loop (deterministic). Multi-worker delivery order is scheduling-dependent by design; every delivered record is exactly-once and uncorrupted (Theorems 2.1, 3.1), and the winner's proof is independently checkable (Spec 14). The determinism gate runs single-worker workloads.

## 7. Resource bounds (design 19.4, 20.1)

Threads are created once, before the search, and joined before returning (graceful shutdown by construction). Worker count bounded by `kPortfolioMaxWorkers`; pool and deque storage bounded by their capacities; the export scan bounded per slice (`kPortfolioExportPerSlice`); worker arenas are process-lifetime (the fixture discipline; pooling is ticket CEP-1038); thread pinning and NUMA-aware placement are deferred (ticket CEP-1037) rather than half-implemented through unsafe OS-affinity calls.

## 8. CEP&CC mapping

`hot/concurrency/{mpmc_pool,chase_lev,clause_codec}.rs` and `cold/portfolio/manager.rs` cite sections 2-5 of this document in their `CEP:HPC-PASS-LEGALITY` fields. The executable evidence: `unit/hot/{mpmc_pool,chase_lev,clause_codec}_test.rs`, `unit/cold/portfolio_test.rs`, and `property/concurrency_property_test.rs` (exactly-once and conservation under real interleaving; the codec roundtrip property; the portfolio soundness property). The CI `tsan` job runs the concurrency suites under ThreadSanitizer (ticket CEP-1008's closure condition).
