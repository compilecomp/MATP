# Formal Specification 03: Term Orderings — KBO and LPO

Version: 0.1
Status: complete for the Phase 2 scope (design 8.3, ticket CEP-1013)
Role: normative reference for `hot/ordering/`; cited by their `CEP:HPC-PASS-LEGALITY` and `CEP:EVIDENCE` fields and by the ordering property tests.
References: Knuth & Bendix 1970; Kamin & Lévy 1980 (LPO as presented by Kamin and Redy 1994 and Baader & Nipkow, *Term Rewriting and All That*, ch. 5); design sections 8.3 and 10.2.

## 1. Precedence

A **precedence** is a strict total order on term heads: all symbol IDs of the frozen symbol table plus one pseudo-head for equality atoms (they carry no symbol ID; the dedicated slot prevents aliasing with symbol zero). MAPT stores it as a flat u32 rank array (`hot/ordering/precedence.rs`); the default policy is rank(symbol i) = i with the equality head maximal, and strategy-supplied ranks are validated to be a permutation at the trust boundary before the hot path can depend on totality.

The precedence is a parameter of both orderings below; nothing in this specification depends on which total order is chosen.

## 2. Knuth-Bendix Ordering (KBO)

Fix a weight function `w` with `w(f) >= 1` for every symbol (validated at symbol-table freeze) and `w(x) = 1` for variables (`kKboVariableWeight`). The weight extends homomorphically: `w(f(t_1..t_n)) = w(f) + w(t_1) + ... + w(t_n)`; MAPT caches it on the term header at intern time.

For terms `s, t` with `s != t` (pointer inequality, which is structural inequality by hash-consing):

**Definition (KBO).** `s >_kbo t` iff
1. `w(s) > w(t)` and `#x(s) >= #x(t)` for every variable `x`, or
2. `w(s) = w(t)`, `#x(s) >= #x(t)` for every variable `x`, and either
   - `s = f(s_1..s_n)`, `t = g(t_1..t_m)` with distinct heads and `f > g` in the precedence, or
   - `s = f(s_1..s_n)`, `t = f(t_1..t_n)` share the head and there is `i` with `s_j = t_j` for all `j < i` and `s_i >_kbo t_i`.

Here `#x(u)` is the number of occurrences of `x` in `u`. Variables relate to nothing: `x >_kbo t` requires `w(x) > w(t)` (impossible for `w(t) >= 1`) or the compound cases (impossible for a variable `s`), and distinct variables of equal weight are incomparable.

**Theorem 2.1 (strictness).** `>_kbo` is irreflexive and antisymmetric.

*Proof.* `s >_kbo s` is excluded by the `s != t` premise; case 1 and case 2 are asymmetric in `s, t` (weight, precedence, or the first differing child flips the direction), so `s >_kbo t` and `t >_kbo s` cannot both hold. ∎

**Theorem 2.2 (transitivity).** `>_kbo` is transitive (on ground terms, and on all terms when the variable condition holds along the chain).

*Proof sketch.* Standard (Baader & Nipkow, Lemma 5.4.4): weight comparisons and lexicographic comparisons are transitive, and the variable-occurrence condition `#x(s) >= #x(t)` composes along chains by transitivity of `>=` on counts. ∎ Verified executably by `tests/property/ordering_property_test.rs::ordering_transitive_ground`.

**Theorem 2.3 (subterm property).** If `t` is a proper subterm of `s` then `s >_kbo t`.

*Proof.* All symbol weights are at least one, so `w(s) >= w(t) + w(head(s)) > w(t)`, and every variable of `t` occurs in `s`, so `#x(s) >= #x(t)`; case 1 applies. This is where `w(f) >= 1` is essential — with zero-weight unary symbols the classic admissibility exception would be required. ∎ Verified by `tests/property/ordering_property_test.rs::subterm_property_both_orderings`.

**Theorem 2.4 (ground totality).** For ground terms `s, t` under a total precedence, exactly one of `s >_kbo t`, `t >_kbo s`, `s = t` holds.

*Proof sketch.* On ground terms the variable condition is vacuous; weight equality reduces the comparison to precedence (distinct heads, decided by totality) or to the lexicographic descent on children, which terminates on the well-founded term structure. ∎ Verified by `tests/property/ordering_property_test.rs::ordering_total_on_ground`.

**Theorem 2.5 (stability under substitution).** If `s >_kbo t` then `s*sigma >_kbo t*sigma` for every substitution `sigma` over the shared variable namespace.

*Proof sketch.* Standard KBO property (Baader & Nipkow, Lemma 5.4.6): the variable condition guarantees weight dominance is preserved because every variable of `t` occurs at least as often in `s`, and substitution replaces equal numbers of variable occurrences on both sides. ∎ Verified by `tests/property/ordering_property_test.rs::kbo_stable_under_substitution`.

**Implementation contract.** `compare_kbo` (`hot/ordering/kbo.rs`) returns Greater / Less / Equal / Incomparable; the variable condition is verified lazily in the structurally winning direction (sound because both directions cannot hold when occurrence counts differ, and both hold trivially when they are equal); work is bounded by `kMaxOrderingSteps`.

## 3. Lexicographic Path Ordering (LPO)

**Definition (LPO, strict).** `s >_lpo t` iff
1. `t` is a variable occurring in `s` (and `s != t`), or
2. `s = f(s_1..s_n)` and `t = g(t_1..t_m)` and
   a. `s_i >=_lpo t` for some `i` (where `>=` is `>` or equality), or
   b. `f > g` and `s >_lpo t_j` for all `j`, or
   c. `f = g`, `n = m`, and there is `i` with `s_j = t_j` for all `j < i` and `s_i >_lpo t_i`.

**Theorem 3.1 (strictness) / 3.2 (transitivity).** As for KBO (Baader & Nipkow, Thm 5.4.8 and exercises); verified by the same property tests.

**Theorem 3.3 (subterm property).** Case 2a with `s_i = t` gives the subterm property directly. ∎

**Theorem 3.4 (ground totality).** For ground terms under a total precedence, LPO is total: on differing terms either case 2b (distinct heads) or case 2c (same head) decides, recursively; case 2a never applies to ground pairs except through the recursion. ∎ Verified by `ordering_total_on_ground`.

**Simplification order.** Both `>_kbo` and `>_lpo` are simplification orders (strict, with the subterm property, stable under substitution and closed under contexts); this is the side-condition class that superposition and ordered resolution require for refutational completeness (Bachmair & Ganzinger 2001).

**Implementation contract.** `compare_lpo` (`hot/ordering/lpo.rs`) evaluates both directions of the strict predicate; the recursion is bounded by `kMaxOrderingSteps` and by the intern-time depth cap; Application and Lambda heads are rejected as `UnsupportedHead` (higher-order orderings are Phase 5, ticket CEP-1033).

## 4. Cost evidence

Measured medians on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release, 2026-10-10 (bench CEP-BENCH-0007):

- KBO weight-dominance fast path: 111.00 cycles (`benches/artifacts/ordering_kbo_weight.json`).
- KBO equal-weight lexicographic path: 238.18 cycles (`benches/artifacts/ordering_kbo_lex.json`).
- LPO nested ground comparison: 22.22 cycles (`benches/artifacts/ordering_lpo.json`).

Disassembly evidence: `benches/artifacts/disasm_ordering.txt`.
