# Formal Specification 02: Substitutions and Unification (Phase 1: Substitutions)

Version: 0.1
Status: complete; the unification, matching, and composition algorithms were delivered with Phase 2 (`hot/unification/unify.rs`, ticket CEP-1002 closed) against the definitions fixed here in Phase 1.
Role: normative reference for `hot/unification/substitution.rs` and `hot/unification/unify.rs`; cited by their `CEP:EVIDENCE` fields and by design sections 5.5 and 8.2.

## 1. Substitutions

A substitution is a finite map `sigma : V -> T(Sigma, V)` from variables to terms. In MAPT it is stored as a flat array indexed by dense variable ID (`hot/unification/substitution.rs`), bounded by `kMaxVariablesPerClause`.

The domain of `sigma` is `dom(sigma) = { x : sigma(x) != x }` (stored bindings; unbound slots are the identity implicitly).

## 2. Application

Application extends `sigma` to a homomorphism `hat-sigma : T -> T`:

- `hat-sigma(x) = hat-sigma(sigma(x))` if `x in dom(sigma)`, else `x`,
- `hat-sigma(f(t_1..t_n)) = f(hat-sigma(t_1), ..., hat-sigma(t_n))`, and analogously for the other tags.

The implementation applies lazily along the stored representation and re-interns rebuilt nodes, so the result is canonical by Specification 01, section 3. For cyclic `sigma` (which a well-formed unifier never produces), application is non-terminating; MAPT bounds the recursion by `kMaxUnificationDepth` and fails with `DepthExceeded` (`tests/unit/hot/substitution_test.rs::cyclic_binding_rejected`). This is a deliberate deviation from the mathematical partiality in favor of the bounded-failure contract (design section 8.2).

## 3. Composition

For substitutions `sigma, tau`, the composition `sigma tau` (apply `tau` first, then `sigma`) is defined by `x (sigma tau) = hat-sigma(x tau)` on the union of domains. Phase 1 stores compositions materialized in the arena (record format `SubstitutionRecord`); explicit composition construction arrives with Phase 2 unification.

## 4. Trail discipline (backtracking)

Bindings are recorded on a trail in application order. `undo_to(d)` restores the state to trail depth `d`. Invariants:

1. A variable is bound at most once between undos (enforced: double bind is an error).
2. After `undo_to(d)`, `dom` equals the domain before depth `d` was reached.
3. Trail depth never exceeds `kMaxSubstitutionTrailDepth` (explicit `TrailFull` error).

These invariants are exercised by `tests/unit/hot/substitution_test.rs::trail_undo_restores_state` and by the property tests.

## 5. Unification and matching (Phase 2 definitions, fixed now)

**Definition (unifier).** `sigma` unifies `s` and `t` iff `hat-sigma(s) = hat-sigma(t)`.

**Definition (most general unifier, MGU).** `sigma` is an MGU of `s, t` iff for every unifier `tau` of `s, t` there is `rho` with `tau = rho sigma`.

**Theorem (Robinson).** Unifiable terms have an MGU, computed by the Robinson algorithm with occurs check (Martelli & Montanari 1982 formulate it as the standard transformation rules). The occurs check is mandatory: without it, `x` and `f(x)` would produce a "unifier" violating well-foundedness of terms, i.e., an unsound inference (design section 8.2).

**Matching (Phase 2).** `sigma` matches pattern `p` onto subject `t` iff `hat-sigma(p) = t` and `dom(sigma) subset of vars(p)`; one-directional, no occurs check needed.

Phase 2 requirements fixed by this document: the algorithm must (a) use the flat-array substitution of this module, (b) bound work by `kMaxUnificationDepth`, (c) record bindings on the trail for backtracking, (d) return the MGU materialized in the arena for proof records, and (e) cite this section in its `CEP:HPC-PASS-LEGALITY` comment.

The delivered implementation (`hot/unification/unify.rs`, Phase 2) satisfies (a)-(e): failures unwind to the entry trail depth (section 4), matching verifies its result with one application pass as a soundness witness for the shared variable namespace, and composition (section 3) materializes records through `Substitution::write_record`; the property tests (`tests/property/unify_property_test.rs`) verify the unifier and idempotency theorems and the occurs-check agreement with a naive scan.

## 6. Complexity bounds

- `lookup`, `bind`, `is_bound`: O(1).
- `apply`: O(|t|) with one intern per rebuilt node (O(|t|) expected each, Specification 01 section 3).
- `materialize` / `read_record`: O(|dom(sigma)|).

Measured costs are recorded in `benches/artifacts/substitution_lookup.json` and `substitution_apply_small.json` (bench CEP-BENCH-0004).
