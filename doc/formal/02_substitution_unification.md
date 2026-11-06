# Formal Specification 02: Substitutions and Unification (Phase 1: Substitutions)

## Abstract

This document is the normative reference for `hot/unification/substitution.rs` and `hot/unification/unify.rs`, cited by their `CEP:EVIDENCE` fields and by design sections 5.5 and 8.2. It defines the substitution algebra (flat-array storage, application as a homomorphism, composition, trail-based backtracking) and the unification, matching, and composition algorithms with their complexity bounds. Inputs are dense variable identifiers, term pointers from the Specification 01 store, and binding requests; outputs are canonical applied terms, materialized `SubstitutionRecord` structures, and the most general unifier or match witness of term pairs.

## Formal Definitions

### 1. Substitutions

A substitution is a finite map `sigma : V -> T(Sigma, V)` from variables to terms. In MAPT it is stored as a flat array indexed by dense variable ID (`hot/unification/substitution.rs`), bounded by `kMaxVariablesPerClause`.

The domain of `sigma` is `dom(sigma) = { x : sigma(x) != x }` (stored bindings; unbound slots are the identity implicitly).

### 2. Application

Application extends `sigma` to a homomorphism `hat-sigma : T -> T`:

- `hat-sigma(x) = hat-sigma(sigma(x))` if `x in dom(sigma)`, else `x`,
- `hat-sigma(f(t_1..t_n)) = f(hat-sigma(t_1), ..., hat-sigma(t_n))`, and analogously for the other tags.

The implementation applies lazily along the stored representation and re-interns rebuilt nodes, so the result is canonical by Specification 01, section 3. For cyclic `sigma` (which a well-formed unifier never produces), application is non-terminating; MAPT bounds the recursion by `kMaxUnificationDepth` and fails with `DepthExceeded` (`tests/unit/hot/substitution_test.rs::cyclic_binding_rejected`). This is a deliberate deviation from the mathematical partiality in favor of the bounded-failure contract (design section 8.2).

### 3. Composition

For substitutions `sigma, tau`, the composition `sigma tau` (apply `tau` first, then `sigma`) is defined by `x (sigma tau) = hat-sigma(x tau)` on the union of domains. Phase 1 stores compositions materialized in the arena (record format `SubstitutionRecord`); explicit composition construction arrives with Phase 2 unification.

### 5. Unification and matching (Phase 2 definitions, fixed now)

**Definition (unifier).** `sigma` unifies `s` and `t` iff `hat-sigma(s) = hat-sigma(t)`.

**Definition (most general unifier, MGU).** `sigma` is an MGU of `s, t` iff for every unifier `tau` of `s, t` there is `rho` with `tau = rho sigma`.

**Theorem (Robinson).** Unifiable terms have an MGU, computed by the Robinson algorithm with occurs check (Martelli & Montanari 1982 formulate it as the standard transformation rules). The occurs check is mandatory: without it, `x` and `f(x)` would produce a "unifier" violating well-foundedness of terms, i.e., an unsound inference (design section 8.2).

**Matching (Phase 2).** `sigma` matches pattern `p` onto subject `t` iff `hat-sigma(p) = t` and `dom(sigma) subset of vars(p)`; one-directional, no occurs check needed.

Phase 2 requirements fixed by this document: the algorithm must (a) use the flat-array substitution of this module, (b) bound work by `kMaxUnificationDepth`, (c) record bindings on the trail for backtracking, (d) return the MGU materialized in the arena for proof records, and (e) cite this section in its `CEP:HPC-PASS-LEGALITY` comment.

The delivered implementation (`hot/unification/unify.rs`, Phase 2) satisfies (a)-(e): failures unwind to the entry trail depth (section 4), matching verifies its result with one application pass as a soundness witness for the shared variable namespace, and composition (section 3) materializes records through `Substitution::write_record`; the property tests (`tests/property/unify_property_test.rs`) verify the unifier and idempotency theorems and the occurs-check agreement with a naive scan.

## Algorithm

The unification algorithm (`unify`) is the Robinson procedure with occurs check over the shared flat-array substitution:

1. Maintain a worklist of term pairs to equate; pop one pair.
2. Dereference both sides through the substitution; identical offsets succeed.
3. If one side is a variable, run the occurs check over the other side; on absence bind the variable at the current trail depth (double binds are a `SubstitutionError`), otherwise fail.
4. If both sides are compound, require equal tags and arities, equate the symbols, and push the child pairs.
5. On any failure, unwind the trail to the entry depth before returning; on success, return the MGU materialized in the arena (`Substitution::materialize`).

`match_terms` is the one-directional restriction of the same procedure (no occurs check, domain confined to pattern variables), and `compose` realizes section 3 on materialized records. Work is bounded by `kMaxUnificationDepth`.

### 6. Complexity bounds

- `lookup`, `bind`, `is_bound`: O(1).
- `apply`: O(|t|) with one intern per rebuilt node (O(|t|) expected each, Specification 01 section 3).
- `materialize` / `read_record`: O(|dom(sigma)|).

Measured costs are recorded in `benches/artifacts/substitution_lookup.json` and `substitution_apply_small.json` (bench CEP-BENCH-0004).

### 4. Trail discipline (backtracking)

Bindings are recorded on a trail in application order. `undo_to(d)` restores the state to trail depth `d`. Invariants:

1. A variable is bound at most once between undos (enforced: double bind is an error).
2. After `undo_to(d)`, `dom` equals the domain before depth `d` was reached.
3. Trail depth never exceeds `kMaxSubstitutionTrailDepth` (explicit `TrailFull` error).

These invariants are exercised by `tests/unit/hot/substitution_test.rs::trail_undo_restores_state` and by the property tests.

## Invariants

1. Single binding: a variable is bound at most once between undos; a second `bind` is a `SubstitutionError` (section 4, invariant 1).
2. Trail restore: after `undo_to(d)`, the domain equals the domain before depth `d` was reached (section 4, invariant 2; `tests/unit/hot/substitution_test.rs::trail_undo_restores_state`).
3. Bounded trail: trail depth never exceeds `kMaxSubstitutionTrailDepth`; overflow is the explicit `TrailFull` error (section 4, invariant 3).
4. Bounded application: application recursion is bounded by `kMaxUnificationDepth`; cyclic bindings fail with `DepthExceeded` instead of diverging (section 2; `tests/unit/hot/substitution_test.rs::cyclic_binding_rejected`).
5. Canonical results: every applied term is re-interned through the Specification 01 store, so the result is canonical (section 2).
6. Match soundness witness: a successful `match_terms` verifies its result with one application pass (`hat-sigma(p) = t`) before returning (section 5).
7. MGU correctness: for every unifier `tau` of `s, t`, the returned `sigma` satisfies `tau = rho sigma` for some `rho`; property-tested in `tests/property/unify_property_test.rs` together with idempotency and occurs-check agreement with a naive scan.

Violation of any invariant is a returned error or a debug assertion, never a silent success.

## Integration Points

Depends on:

- `hot/ir/term.rs` (`TermStore::intern_fun(&self, symbols: &SymbolTable, symbol_id: u32, children: &[TermPtr]) -> Result<TermPtr, TermError>`) for canonical term construction during application.
- `hot/memory/arena.rs` (`Arena`) for the flat substitution array, the trail, and materialized records.
- `config/limits.rs` (`kMaxVariablesPerClause`, `kMaxUnificationDepth`, `kMaxSubstitutionTrailDepth`) for every bound named above.

Depended on by:

- `hot/inference/` (resolution, factoring, superposition builders) and `hot/search/generate.rs`, which unify and match clause atoms per Specification 07 and cite this section in their `CEP:HPC-PASS-LEGALITY` comments.
- `hot/induction/` and `hot/conjecture/filter.rs`, which build and apply substitutions in mini refutation spaces.
- `cold/` proof records, which consume materialized `SubstitutionRecord` structures through `Substitution::write_record(&self, pairs: &[(u32, u32)]) -> Result<u32, SubstitutionError>` and `Substitution::read_record`.

## Known Limitations

- Cyclic substitutions are rejected by bounded failure (`DepthExceeded`), not detected structurally; a well-formed unifier never produces them (section 2, design section 8.2).
- The unifier assumes the renamed-apart discipline for cross-clause variable namespaces: the variable bound stays at `kMaxVariablesPerClause` and keeping clauses variable-disjoint is the callers' contract (Spec 02 section 5; ticket CEP-1002, closed).
- Composition of open (non-materialized) substitutions is not provided; `compose` operates on materialized records (section 3).
