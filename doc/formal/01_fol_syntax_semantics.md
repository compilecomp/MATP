# Formal Specification 01: First-Order Term Syntax and Semantics

## Abstract

This document is the normative reference for the term and clause intermediate representation (IR version 1) of the `hot` crate: it defines the signature, the term algebra over dense symbol and variable identifiers, the hash-consing canonical form, the derived measures (depth, weight, groundness), literals and clauses in canonical order, and the many-sorted first-order semantics with equality that every inference rule of the engine must preserve. Inputs are symbol declarations frozen into a symbol table and term constructions through the term store; outputs are canonical term, literal, and clause records whose invariants the verifier re-derives. The document is cited by the `CEP:EVIDENCE` fields of `hot/ir/term.rs`, `hot/ir/clause.rs`, and the verifier, and by design sections 5.1-5.4, 5.7.

## Formal Definitions

### 1. Signature

A signature is a tuple `Sigma = (S, F, P)` where:

- `S` is a finite set of sort symbols. MAPT reserves the Boolean sort `$o` (builder constant `kBooleanSortName`).
- `F` is a finite set of function symbols, each with an arity `ar(f) in [0, kMaxSymbolArity]` and a sort signature `arg_1 x ... x ar(f) -> r`.
- `P` is a finite set of predicate symbols, each with an arity and argument sorts, returning `$o`.

Symbols are identified by dense u32 IDs assigned in first-declaration order (deterministic for deterministic input). The map from names to symbols is injective: redeclaration with a different signature is refused (`BuilderError::DuplicateName`).

### 2. Terms

Given a set `V` of variables with dense indices in `[0, kMaxVariablesPerClause)`, the term set `T(Sigma, V)` is the smallest set with:

- `x in V` is a term (tag Variable),
- `f(t_1, ..., t_n)` for `f in F`, `ar(f) = n`, `t_i` terms (tag Function),
- `p(t_1, ..., t_n)` for `p in P` (tag Predicate; atoms of literals),
- `=(s, t)` for terms `s, t` (tag Equality; the equality symbol is built in and reserved, design section 5.1),
- `@(s, t)` (tag Application; lambda-free higher-order fragment, design section 14.1),
- `sort_i` (tag Sort; sort annotation).

Well-formedness condition (verified by `cold/verifier.rs`): the child count of an `f`- or `p`-node equals the symbol arity; Equality and Application nodes have exactly two children; Variable, Sort nodes have zero children.

### 3. Hash-consing canonical form

Every term is stored once. The store maintains the invariant:

**Definition (canonicality).** For all terms `s, t` constructed through the store: `s = t` (structural equality) if and only if `store(s) = store(t)` (identical offsets).

**Theorem (canonicality of the store).** The interning procedure of `hot/ir/term.rs` establishes canonicality.

*Proof sketch.* Interning computes a deterministic key `k(t) = (tag, symbol, sorted-children-offsets)`; two structurally equal terms have equal keys; the table lookup returns the existing record for an equal key, so the second construction yields the first one's offset. Conversely, the record comparison in `records_equal` verifies tag, symbol, depth, and every child offset, so a returned offset belongs to a structurally equal term. Induction over term structure, using that child offsets are themselves canonical (children are interned first). ∎

**Corollary.** Term equality is offset comparison (design section 5.7 carve-out). The property is tested by `tests/property/term_property_test.rs::interning_is_canonical`.

### 4. Position, depth, weight, groundness

- `depth(x) = depth(sort) = 0`; `depth(f(t_1..t_n)) = 1 + max_i depth(t_i)`. Bounded by `kMaxTermDepth`.
- `weight(t)`: for Function/Predicate nodes, `w(symbol) + sum weight(children)`; for Variable, `kKboVariableWeight`; for Equality/Application, `kDefaultSymbolWeight + sum weight(children)`; for Sort, `kDefaultSymbolWeight`. Bounded by `kMaxTermWeight`. These caches are recomputed and compared by the verifier (`VerificationError::WrongDepth`, `WrongWeight`).
- `ground(t)`: true iff no Variable occurs in `t`; cached on the record; verifier-checked (`WrongGroundFlag`).

### 5. Literals and clauses

A literal is `A` or `not-A` for an atom `A` (Predicate or Equality term). Complementarity: `L` and `M` are complementary iff same atom and opposite polarity (`Literal::is_complementary`).

A clause is a finite multiset of literals, stored in canonical order:

**Definition (canonical literal order).** Literals are sorted ascending by the key `(!polarity, atom offset)`; the sort is stable.

The canonical order is total (offsets are distinct for distinct atoms by hash-consing) and deterministic across runs (offsets depend only on the allocation sequence, `tests/property/term_property_test.rs::hash_is_determinism`). Clause weight is the sum of atom weights; the verifier recomputes it.

### 6. Semantics

Standard many-sorted first-order semantics with equality. An interpretation `I` satisfies a clause set `N` iff every clause has a literal true under `I`. Phase 1 fixes only the data structures and their invariants, which every future rule must preserve; the inference rules arrive with their own specifications (Specifications 02, 03, 07).

## Algorithm

The primary algorithm is term interning (`TermStore`):

1. Compute the deterministic key `k(t) = (tag, symbol, sorted-children-offsets)` of the node to construct; children are interned first, so their offsets are canonical.
2. Probe the open-addressing hash table (FNV-1a over the key, no seed, no addresses) under the configured load-factor bound.
3. On a hit, run `records_equal` (tag, symbol, depth, every child offset); on equality return the stored offset; on a spurious probe continue.
4. On a miss, write the record (tag, symbol, cached depth, cached weight, cached groundness, children), append the key to the table, and return the new offset.

Expected time is O(1) per intern under the load-factor bound and O(|t|) per construction of depth-bounded terms, with space of one record per distinct term (`benches/artifacts/term_intern_binary_hit.json`, `benches/artifacts/disasm_term.txt`). Bounded failure follows the module contract: construction beyond `kMaxTermDepth` or `kMaxTermWeight`, or a table at capacity, returns a `TermError` instead of growing without bound. Canonical clause materialization applies a stable sort of the literal multiset by the key of section 5 above.

## Invariants

1. Canonicality: for all terms `s, t` constructed through the store, `s` and `t` are structurally equal iff their offsets are identical (`tests/property/term_property_test.rs::interning_is_canonical`).
2. Well-formedness: child counts match symbol arities; Equality and Application nodes have exactly two children; Variable and Sort nodes have zero children (`cold/verifier.rs::verify_term_store`).
3. Cache correctness: the record's depth, weight, and groundness equal the recomputed values of sections 4 (`VerificationError::WrongDepth`, `WrongWeight`, `WrongGroundFlag`).
4. Canonical literal order: every clause's literals are ascending in `(!polarity, atom offset)`, the order is total and run-deterministic.
5. Clause weight: equals the sum of atom weights; recomputed by the verifier.
6. Hash determinism: the FNV-1a key depends only on the canonical key, never on addresses, time, or environment (`tests/property/term_property_test.rs::hash_is_determinism`).

## Integration Points

Depends on:

- `hot/memory/arena.rs` (`Arena::new`, `Arena::alloc_bytes`) for all record storage; the store holds no heap allocation of its own.
- `hot/ir/symbol_table.rs` (`SymbolTable::info`, `SymbolTable::sort_signature`, `SymbolTable::symbol_weight`) for arities, sorts, and weights.
- `config/limits.rs` (`kMaxTermDepth`, `kMaxTermWeight`, `kMaxSymbolArity`, `kMaxVariablesPerClause`) for every bound named above.

Depended on by:

- `hot/ir/literal.rs` (`Literal::new(atom: TermPtr, polarity: bool) -> Literal`, `Literal::is_complementary(&self, other: &Literal) -> bool`) and `hot/ir/clause.rs` (`ClauseStore::clause_by_id(&self, id: ClauseId) -> Result<&Clause, ClauseError>`).
- `hot/unification/`, `hot/ordering/`, and every inference module; term identity is offset identity by the corollary of section 3.
- `cold/verifier.rs` (`verify_term_store(arena: &Arena, terms: &TermStore, symbols: &SymbolTable) -> Vec<VerificationError>`) re-derives invariants 1 through 5.
- `cold/debug_printer.rs` (`print_term`, `print_clause`) provides the printable contract; golden test `tests/golden/ir_debug_print_test.rs`.

### 7. IR contract mapping (CEP&CC 38.17)

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

## Known Limitations

- The specification is complete for the Phase 1 subset; the inference rules are fixed by Specifications 02, 03, and 07, not here.
- The Application tag fixes a lambda-free higher-order fragment (design section 14.1); no beta-reduction or lambda syntax exists at this layer.
- Sort annotations are carried but not yet enforced by a type discipline beyond the symbol table's sort signatures.
