# Formal Specification 01: First-Order Term Syntax and Semantics

Version: 0.1 (IR version 1)
Status: complete for the Phase 1 subset
Role: normative reference for the term and clause IR (design sections 5.1-5.4, 5.7); cited by `CEP:EVIDENCE` fields in `hot/ir/term.rs`, `hot/ir/clause.rs`, and by the verifier.

## 1. Signature

A signature is a tuple `Sigma = (S, F, P)` where:

- `S` is a finite set of sort symbols. MAPT reserves the Boolean sort `$o` (builder constant `kBooleanSortName`).
- `F` is a finite set of function symbols, each with an arity `ar(f) in [0, kMaxSymbolArity]` and a sort signature `arg_1 x ... x ar(f) -> r`.
- `P` is a finite set of predicate symbols, each with an arity and argument sorts, returning `$o`.

Symbols are identified by dense u32 IDs assigned in first-declaration order (deterministic for deterministic input). The map from names to symbols is injective: redeclaration with a different signature is refused (`BuilderError::DuplicateName`).

## 2. Terms

Given a set `V` of variables with dense indices in `[0, kMaxVariablesPerClause)`, the term set `T(Sigma, V)` is the smallest set with:

- `x in V` is a term (tag Variable),
- `f(t_1, ..., t_n)` for `f in F`, `ar(f) = n`, `t_i` terms (tag Function),
- `p(t_1, ..., t_n)` for `p in P` (tag Predicate; atoms of literals),
- `=(s, t)` for terms `s, t` (tag Equality; the equality symbol is built in and reserved, design section 5.1),
- `@(s, t)` (tag Application; lambda-free higher-order fragment, design section 14.1),
- `sort_i` (tag Sort; sort annotation).

Well-formedness condition (verified by `cold/verifier.rs`): the child count of an `f`- or `p`-node equals the symbol arity; Equality and Application nodes have exactly two children; Variable, Sort nodes have zero children.

## 3. Hash-consing canonical form

Every term is stored once. The store maintains the invariant:

**Definition (canonicality).** For all terms `s, t` constructed through the store: `s = t` (structural equality) if and only if `store(s) = store(t)` (identical offsets).

**Theorem (canonicality of the store).** The interning procedure of `hot/ir/term.rs` establishes canonicality.

*Proof sketch.* Interning computes a deterministic key `k(t) = (tag, symbol, sorted-children-offsets)`; two structurally equal terms have equal keys; the table lookup returns the existing record for an equal key, so the second construction yields the first one's offset. Conversely, the record comparison in `records_equal` verifies tag, symbol, depth, and every child offset, so a returned offset belongs to a structurally equal term. Induction over term structure, using that child offsets are themselves canonical (children are interned first). ∎

**Corollary.** Term equality is offset comparison (design section 5.7 carve-out). The property is tested by `tests/property/term_property_test.rs::interning_is_canonical`.

## 4. Position, depth, weight, groundness

- `depth(x) = depth(sort) = 0`; `depth(f(t_1..t_n)) = 1 + max_i depth(t_i)`. Bounded by `kMaxTermDepth`.
- `weight(t)`: for Function/Predicate nodes, `w(symbol) + sum weight(children)`; for Variable, `kKboVariableWeight`; for Equality/Application, `kDefaultSymbolWeight + sum weight(children)`; for Sort, `kDefaultSymbolWeight`. Bounded by `kMaxTermWeight`. These caches are recomputed and compared by the verifier (`VerificationError::WrongDepth`, `WrongWeight`).
- `ground(t)`: true iff no Variable occurs in `t`; cached on the record; verifier-checked (`WrongGroundFlag`).

## 5. Literals and clauses

A literal is `A` or `not-A` for an atom `A` (Predicate or Equality term). Complementarity: `L` and `M` are complementary iff same atom and opposite polarity (`Literal::is_complementary`).

A clause is a finite multiset of literals, stored in canonical order:

**Definition (canonical literal order).** Literals are sorted ascending by the key `(!polarity, atom offset)`; the sort is stable.

The canonical order is total (offsets are distinct for distinct atoms by hash-consing) and deterministic across runs (offsets depend only on the allocation sequence, `tests/property/term_property_test.rs::hash_is_determinism`). Clause weight is the sum of atom weights; the verifier recomputes it.

## 6. Semantics

Standard many-sorted first-order semantics with equality. An interpretation `I` satisfies a clause set `N` iff every clause has a literal true under `I`. This document does not yet fix the inference rules (they arrive with Phase 2-3 and their own specifications); Phase 1 fixes only the data structures and their invariants, which every future rule must preserve.

## 7. IR contract mapping (CEP&CC 38.17)

| Requirement | Satisfaction |
|---|---|
| Printable | `cold/debug_printer.rs`, golden test `tests/golden/ir_debug_print_test.rs` |
| Hashable deterministically | FNV-1a over the canonical key, no seed, no addresses |
| Versioned | `kIrVersion = 1` |
| Verifiable | `cold/verifier.rs`, full invariant re-derivation |
| Canonicalizable | Canonical literal order; hash-consed terms |
| No pointer identity for semantics | Offset identity equals structural identity by the canonicality theorem |
| Stable IDs | Monotonic u64 clause IDs; dense u32 symbol IDs |
| No hidden target assumptions | All sizes from `config/`; layout pinned by static assertions |
