# Formal Specification 04: Term Indexing — The Discrimination Tree

Version: 0.1
Status: complete for the Phase 2 scope (design 9.2, the build-order index of Phase 2)
Role: normative reference for `hot/index/discrimination_tree.rs`; cited by its `CEP:HPC-PASS-LEGALITY` field and by the index property tests.
References: Graf 1995 (substitution trees and discrimination trees); McCune (path indexing as used in Otter); design sections 9.1-9.5.

## 1. Flat preorder sequences

Every term `t` has a **flat preorder sequence** `flat(t)`: the symbol of `t`, followed by the concatenation of the flat sequences of its children in order. Variables contribute one symbol (their index); equality atoms contribute the reserved pseudo-symbol `kIndexEqualitySymbol` (they carry no symbol-table ID); all other nodes contribute their symbol ID and tag.

Example: `flat(h(x, g(a))) = [h, x, g, a]` (four symbols).

Sequences are bounded by `kIndexTermCapacity` for both indexed and query terms; longer terms are rejected loudly (`IndexError::TermTooLarge`).

## 2. The tree

The discrimination tree is a trie over flat preorder sequences:

- The root represents the empty prefix; nodes are allocated contiguously in the arena with child links as offsets (design 9.2).
- Each edge is labelled **symbol** (tag + symbol ID) or **variable**; a term is inserted by walking or creating one node per symbol of its flat sequence, and its payload (a caller-defined u64, typically a clause ID) is prepended to the leaf's payload list.
- Child lists are prepend-ordered: retrieval order is deterministic (most recently inserted matching path first), a pure function of the operation sequence (CEP&CC 38.10).
- Insertion allocates at most one node per new path edge and one payload entry; both are capped (`kDiscriminationTreeNodes`, `kDiscriminationTreeEntries`) and the caps fail loudly.

## 3. The matching rule and retrieval

**Definition (edge match).** A stored edge `e` matches a query symbol `q` iff
- `e` is a variable edge, or
- `q` is a variable, or
- `e` and `q` carry the same tag and symbol ID.

**Definition (retrieval).** A stored term `s` is retrieved by query `q` iff `|flat(s)| = |flat(q)|` and the edges along `s`'s path match `q`'s symbols position-wise.

This is exactly design 9.2's rule — "Variables in the query match any symbol" — made symmetric (stored variable edges also match any query symbol, which is what instance retrieval for rewriting needs: an indexed left-hand side `f(x)` is retrieved by the concrete query `f(a)`) and closed under the length rule (paths end together; a query variable matches exactly one symbol, not a subtree).

**Theorem (retrieval soundness as a filter).** Every retrieved term satisfies the position-wise match above. *Proof.* The walk consumes one tree edge per query symbol and only descends edges that satisfy the match rule; a payload is collected only at the node where the query sequence is exhausted, which is the end of the stored path. ∎

**Theorem (retrieval completeness as a filter).** Every stored term satisfying the match rule is retrieved. *Proof.* Induction over the query positions: at each position the walk branches over *all* children of the current node, and the match rule is exactly the descent condition; a matching path cannot be skipped. ∎

Both theorems are verified against a naive scan oracle by `tests/property/discrimination_property_test.rs::retrieval_matches_naive_scan`; the unit tests pin the individual rule cases (`exact_retrieval`, `query_variables_match_any_symbol`, `variable_edges_match_any_query_symbol`, `length_rule_enforced`).

**Index filter discipline.** The retrieval set is a *filter*: it over- and under-approximates nothing under its own rule, but the rule itself is weaker than subsumption (a query variable matches one symbol, not a subtree). Callers post-verify candidates with the matching or unification engine (design 9.3's two-level discipline: cheap filter, exact check). This is the standard use of discrimination trees in saturation provers.

## 4. Operations and costs

- **Insert:** walk or build the path, prepend the payload. O(term size).
- **Delete:** walk the path exactly (no creation), unlink the payload entry. O(term size + list length). Entries and nodes are unlinked, never freed — reclamation is arena compaction (Phase 3, ticket CEP-1007).
- **Retrieve:** depth-first walk consuming one edge per query symbol, branching at query variables and stored variable edges; payloads collected at path ends. O(query size × branching factor).

Measured medians on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release, 2026-10-10 (bench CEP-BENCH-0008): 1496.32 cycles per fresh-path insert and 1632.91 per exact-hit retrieval over a 128-term chain vocabulary (`benches/artifacts/index_insert.json`, `index_retrieve.json`). Disassembly evidence: `benches/artifacts/disasm_index.txt`.

## 5. Out of scope (tracked)

Feature-vector filtering (design 9.3), substitution trees, perfect hash, and the inverted index (design 9.1) are later phases (tickets CEP-1028, CEP-1029); the index multiplexer (design 9.4) follows when more than one index exists. Prefix (subterm) retrieval — collecting payloads at internal nodes — is a Phase 3 extension for subsumption on subterms (ticket CEP-1027 note).
