# MAPT — Full System Design

---

## 1. Identity

**Name:** MAPT
**Standard:** CEP&CC 0.1 (Psychopathic Tier), already in repo
**Primary language:** Rust (`core::` in hot paths, hand-rolled concurrency)
**Companion language:** C++26 (FFI to external solvers, target-specific intrinsics, legacy kernel validation)
**Tooling language:** Python (CEP-2, deterministic)
**Input formats:** TPTP (FOF/CNF/TFF/THF), SMT-LIB 2.x, DIMACS CNF
**Output formats:** TSTP proof, SMT-LIB model, DRAT/LRAT certificate, API result struct
**Target classes:** CEP-0/HPC-0 for all engines; CEP-1 for preprocessing, proof output, configuration; CEP-2 for benchmarking and tooling

---

## 2. What MAPT Is

MAPT is a first-order automated theorem prover with an integrated CDCL SAT solver, AVATAR-style clause splitting, theory reasoning, portfolio concurrency, and certified proof production. It competes with Vampire, E, Zipperposition, and iProver on TPTP/CASC benchmarks.

MAPT is **not** a wrapper around an external SAT solver. It owns both the ATP engine and the SAT engine. Both share a single arena allocator, a single clause representation, and a single proof graph. There is no FFI boundary between them.

### 2.1 What MAPT proves

- First-order logic with equality (FOF)
- Typed first-order logic (TFF)
- Higher-order logic, lambda-free fragment (THF subset)
- Propositional logic (CNF) via the internal SAT solver
- Theory-laden problems (LIA, LRA, bitvectors, arrays, uninterpreted functions) via SMT integration

### 2.2 What MAPT returns

| Result | Meaning |
|---|---|
| `Theorem` | Conjecture entailed. Proof produced. |
| `CounterSatisfiable` | Negation satisfiable. Model produced. |
| `Saturated` | Clause set saturated. No proof or model found. |
| `Timeout` | Time budget exhausted. |
| `MemoryExhausted` | Clause database budget exhausted. |
| `InferenceLimit` | Inference count budget exhausted. |
| `GaveUp` | Preprocessing or search aborted. |
| `Error` | Input malformed or internal fault. |

Every result except `Theorem` and `CounterSatisfiable` is a valid answer. MAPT never hangs, never crashes, never returns an unsound result.

### 2.3 Correctness contract

Within documented resource bounds, MAPT returns a sound result or an explicit failure. It never produces an unsound inference. It never silently exceeds a resource budget. It never produces nondeterministic output for identical input.

An unsound inference is Severity 0 per §38.5.

---

## 3. Language and Toolchain Decisions

| Decision | Choice | Rationale |
|---|---|---|
| Primary engine language | Rust | Compile-time safety proofs for hand-rolled concurrency; ownership/lifetime system encodes arena invariants; `core::` gives C-level control without `std` runtime |
| Hot-path concurrency | Hand-rolled in Rust | §25.3 bans `Arc`, `Mutex`, `RwLock`, channels, `dyn`, `async`. All concurrency primitives are custom-built with explicit memory ordering |
| FFI companion | C++26 | Interfacing with external SAT/SMT solvers, target-specific SIMD intrinsics, legacy unification kernel validation |
| Tooling | Python | CEP-2 only. Benchmark orchestration, code generation, TPTP regression harness. Deterministic (§28.3) |
| Build system | Cargo + CMake | Cargo for Rust; CMake for C++26 FFI modules. Both produce deterministic builds (§6.5) |
| Rust compiler | Pinned `rustc` version | §22.12: toolchain is part of trusted computing base |
| C++ compiler | Pinned GCC/Clang version | §6.1 |
| Sanitizers | ASan, UBSan, TSan, MSan in CI | §6.6 |
| Lint | `cep_lint` (§50) | Mechanical enforcement. Self-lint gate before every commit |

### 3.1 Rust CEP-0 constraints (summary)

Banned in hot-path Rust: `std` runtime, `Box`, `Vec`, `String`, `format!`, `println!`, `panic!`, `unwrap()`, `expect()`, `Rc`, `Arc`, `Mutex`, `RwLock`, channels, thread spawning, `dyn Trait`, `async` runtime, global allocator dependence.

Required: `core::` primitives, fixed-size slices, explicit lifetimes, explicit integer types, explicit error enums, `#[repr(C)]` for FFI types, arena allocators initialized before hot path, hand-rolled atomics with explicit memory ordering.

---

## 4. Repository Structure

```
mapt/
├── hot/
│   ├── ir/
│   ├── inference/
│   ├── indexing/
│   ├── search/
│   ├── sat/
│   ├── ordering/
│   ├── unification/
│   ├── simplification/
│   ├── theory/
│   ├── concurrency/
│   └── memory/
│
├── cold/
│   ├── parsing/
│   ├── preprocessing/
│   ├── proof_output/
│   ├── configuration/
│   └── diagnostics/
│
├── ffi/
│   ├── cpp/
│   ├── c/
│   └── rust/
│
├── target/
│   ├── arm64/
│   ├── x86_64/
│   ├── riscv64/
│   └── generic/
│
├── generated/
├── tests/
│   ├── unit/
│   ├── property/
│   ├── contract/
│   ├── fuzz/
│   ├── security/
│   └── golden/
├── benches/
│   ├── hot/
│   ├── target/
│   └── artifacts/
├── tools/
├── config/
│   ├── target_arm64.rs
│   ├── target_x86_64.rs
│   ├── limits.rs
│   ├── feature_gates.rs
│   └── security_policy.rs
├── security/
│   ├── threat_model.md
│   ├── trust_boundaries.md
│   └── ffi_security.md
├── docs/
│   └── formal/
│       ├── 01_fol_syntax_semantics.md
│       ├── 02_substitution_unification.md
│       ├── ...
│       └── 23_benchmark_suite.md
├── third_party/
├── quarantine/
├── scripts/
└── .cep/
    ├── cep_lint.json
    ├── waivers/
    └── exterminations/
```

### 4.1 Structural rules

- `hot/` contains only CEP-0 code. No logging, no allocation, no I/O, no `dyn`, no `std` runtime.
- `cold/` may call into `hot/` but never the reverse.
- `ffi/` is thin: validate → convert → call internal API → convert result → return. No business logic.
- `target/` isolates all ISA-specific code. No target checks in generic hot code (§38.30).
- `generated/` files have golden tests and generator identity headers (§32.7).
- `quarantine/` is excluded from builds. Every quarantined item has a manifest with deadline (§32.13).

---

## 5. Unified Internal Representation

This is the single most important design decision. Every component operates on this format. Under §38.17, this is the IR contract.

### 5.1 Term representation

Terms are hash-consed and stored in a shared arena. Two structurally identical terms share the same pointer.

**Term kinds:**

| Kind | Description |
|---|---|
| `Var(id)` | Variable, identified by `u32` index into variable environment |
| `Fun(symbol_id, children)` | Function symbol applied to child terms |
| `Eq(left, right)` | Equality atom (special-cased for superposition) |
| `Pred(symbol_id, children)` | Predicate symbol applied to child terms |
| `App(func, arg)` | Function application (higher-order) |
| `Lam(var, body)` | Lambda abstraction (higher-order) |
| `Sort(sort_id)` | Sort/type annotation |

**Term layout in memory:**

- Each term is a fixed-size header: tag byte + symbol ID (`u32`) + child count (`u16`) + flags (`u16`). Followed by child pointers.
- All terms live in the arena allocator. No per-term heap allocation.
- Hash-consing uses a perfect hash table built at initialization. Lookup is O(1) amortized.
- Term identity is pointer identity (guaranteed by hash-consing). Semantic equality is pointer comparison.
- Terms are immutable once created. This makes them safe to share across threads without synchronization.

**Design rationale:**

Hash-consing eliminates duplicate terms. In a typical ATP search, the same subterms appear thousands of times across different clauses. Without sharing, memory usage grows linearly with clause count. With sharing, it grows with the number of distinct subterms, which is much smaller. This is critical for memory bandwidth and comparison speed.

The fixed-size header means term traversal is cache-friendly: read the header, know the child count, iterate children contiguously. No pointer chasing through variable-size headers.

**Hash-consing table design:**

- Open-addressing hash table with linear probing.
- Key: (symbol_id, child_pointer_array_hash).
- Value: pointer to the canonical term in the arena.
- Table is built in sorted symbol order at initialization for determinism (§38.10).
- Table size is a named constant (`config/limits.rs`: `kTermHashTableCapacity`).
- Load factor target: 0.65. If exceeded during initialization, return `MemoryExhausted`.
- No resizing after initialization. If the table fills during search, return `MemoryExhausted`.

**Term depth bound:**

Maximum term depth is a named constant (`kMaxTermDepth`). Enforced during term construction. If exceeded, return `TermDepthExceeded` error. This prevents stack overflow during recursive traversal and bounds unification cost.

### 5.2 Literal representation

A literal is a polarity flag plus an atom plus metadata.

| Field | Type | Description |
|---|---|---|
| `polarity` | `bool` | `true` = positive, `false` = negative |
| `atom` | `TermPtr` | Pointer to the underlying atom (predicate or equality) |
| `selected` | `bool` | Whether this literal is selected by the selection function |
| `maximal` | `bool` | Whether this literal is maximal under the term ordering |
| `flags` | `u8` | Theory tag, AVATAR component membership, etc. |

**Design rationale:**

The `selected` and `maximal` flags are computed lazily when a clause enters the active set, not at clause creation time. This avoids redundant ordering comparisons during inference generation. The flags are cached on the literal so repeated access is O(1).

### 5.3 Clause representation

| Field | Type | Description |
|---|---|---|
| `id` | `u64` | Stable, deterministic, monotonic counter. Not hash-based. |
| `literal_count` | `u16` | Number of literals |
| `literals` | `&[Literal]` | Arena-allocated slice. Inline for count ≤ 8; overflow pointer for larger |
| `weight` | `u32` | Clause weight for selection heuristic |
| `age` | `u32` | Step number when clause was derived |
| `flags` | `u16` | Bitfield: active/passive, split component, theory tag, locked, etc. |
| `source` | `DerivationStep` | Proof tracking: inference rule + parent clause IDs |
| `split_level` | `u16` | AVATAR component ID (0 if not split) |
| `theory_tag` | `u8` | Theory-specific metadata (0 if pure FOL) |
| `lbd` | `u8` | Literal Block Distance (SAT engine only) |

**Clause layout:**

- Clauses are stored contiguously in the arena.
- The literal array is inline (no pointer indirection) for clauses up to 8 literals. This covers >95% of clauses in typical ATP search.
- Larger clauses use an arena-allocated overflow array.
- Clause ID is a monotonic counter, ensuring deterministic ordering (§38.10).
- Clause size is bounded by `kMaxClauseLiterals` (named constant). If exceeded during inference, the inference is skipped and logged.

**Design rationale:**

Inline literals for small clauses eliminate one level of pointer indirection on the hot path. Since most clauses have ≤ 8 literals, this gives a significant cache benefit. The overflow path for larger clauses keeps the representation general without penalizing the common case.

### 5.4 Derivation step (proof tracking)

| Field | Type | Description |
|---|---|---|
| `rule` | `InferenceRule` | Enum: `Resolution`, `Superposition`, `Factoring`, `Demodulation`, `Subsumption`, `AVATAR_Split`, `SAT_Learn`, `Theory_Lemma`, `Input`, `NegatedConjecture`, etc. |
| `parent_count` | `u8` | Number of parent clauses (bounded, max 4) |
| `parents` | `[ClauseId; 4]` | Parent clause IDs |
| `substitution` | `SubstitutionPtr` | The MGU or matching substitution used (if applicable) |

Every derived clause carries its derivation step. This builds the proof DAG incrementally. No separate proof reconstruction pass is needed for basic proofs.

### 5.5 Substitution representation

A substitution maps variable IDs to terms.

| Design choice | Description |
|---|---|
| Storage | Flat array indexed by variable ID. No hash map. |
| Size | Bounded by `kMaxVariablesPerClause` (named constant). |
| Composition | Explicit. Allocates into the arena. |
| Lifetime | Tied to the arena generation in which it was created. |
| Sharing | Substitutions are not hash-consed (too many unique instances). |

**Design rationale:**

Variable IDs are dense integers (0, 1, 2, ...) within a clause. A flat array indexed by variable ID gives O(1) lookup with no hashing overhead. This is critical because unification and matching access substitutions millions of times per second.

### 5.6 Symbol table

| Field | Type | Description |
|---|---|---|
| `symbol_id` | `u32` | Dense integer ID |
| `name` | `&str` | Symbol name (cold storage) |
| `kind` | `SymbolKind` | `Function`, `Predicate`, `Sort`, `Variable` |
| `arity` | `u16` | Number of arguments |
| `sort_signature` | `[SortId]` | Argument sorts and return sort |
| `flags` | `u8` | Built-in, theory-specific, etc. |

The symbol table is built during parsing (CEP-1) and frozen before search begins. Symbol IDs are dense and stable. All hot-path code uses symbol IDs, never string names.

### 5.7 IR contract checklist (§38.17)

| Requirement | How MAPT satisfies it |
|---|---|
| Printable | TPTP, SMT-LIB, internal debug format writers in `cold/proof_output/` |
| Hashable deterministically | Hash-consing table built in sorted order; clause IDs monotonic |
| Versioned | IR version constant in `config/`; serialized IR includes version |
| Verifiable | Internal IR verifier checks term well-formedness, clause invariants, sort correctness |
| Canonicalizable | Literals sorted by (polarity, atom pointer); clauses sorted by ID |
| Target-aware but not contaminated | No target-specific data in IR; target hooks are separate |
| No pointer identity for semantic equality | Except hash-consed terms (where pointer identity IS semantic equality by construction) |
| No hidden target assumptions | All sizes, alignments from `config/target.rs` |
| No hidden pass ordering dependence | IR is self-contained; no pass-order assumptions |

---

## 6. Input Layer (CEP-1)

### 6.1 Supported input formats

| Format | Parser location | Purpose |
|---|---|---|
| TPTP (FOF, CNF, TFF, THF) | `cold/parsing/tptp_parser.rs` | Primary ATP input. 20,000+ benchmarks. |
| SMT-LIB 2.x | `cold/parsing/smtlib_parser.rs` | Theory-laden problems. Secondary input. |
| DIMACS CNF | `cold/parsing/dimacs_parser.rs` | Pure SAT benchmarks. Tertiary input. |
| API / Library call | `ffi/` | Programmatic interface for embedding. |

### 6.2 Parser design

Each parser follows the same structure:

1. **Lexing:** Convert byte stream to token stream. Bounded token buffer. No allocation per token.
2. **Parsing:** Recursive descent with bounded recursion depth (`kMaxParseDepth`). Produces AST.
3. **Validation:** Check sort correctness, arity, symbol declarations. Reject malformed input.
4. **IR construction:** Convert AST to unified IR. Hash-cons terms. Assign clause IDs.
5. **Return:** `ParseResult` enum: `Success(ClauseSet)`, `Error(ParseError)`.

### 6.3 Input validation (§22.5)

All input is untrusted. The parser enforces:

| Bound | Named constant | Purpose |
|---|---|---|
| Maximum input file size | `kMaxInputBytes` | Prevent memory exhaustion |
| Maximum formula size | `kMaxFormulaNodes` | Prevent CPU exhaustion |
| Maximum term depth | `kMaxTermDepth` | Prevent stack overflow |
| Maximum number of symbols | `kMaxSymbolCount` | Prevent symbol table overflow |
| Maximum quantifier nesting | `kMaxQuantifierDepth` | Prevent exponential blowup |
| Maximum include depth | `kMaxIncludeDepth` | Prevent infinite include loops |
| Maximum include file count | `kMaxIncludeCount` | Prevent resource exhaustion |

Failure: return `ParseError` enum. No allocation. No panic. No exception.

### 6.4 Output formats

| Format | Writer location | Purpose |
|---|---|---|
| TSTP proof | `cold/proof_output/tstp_writer.rs` | Standard proof output |
| SMT-LIB model | `cold/proof_output/smtlib_model_writer.rs` | Model output for theory problems |
| DRAT/LRAT proof | `cold/proof_output/drat_writer.rs` | SAT proof certificate |
| Internal debug dump | `cold/diagnostics/` | Debugging only |

---

## 7. Preprocessing Pipeline (CEP-0 / HPC-0)

Preprocessing transforms the parsed formula into a clause set ready for search. Each step is a certified HPC-0 pass (§38.21).

### 7.1 Pipeline stages

| # | Stage | Input | Output | HPC-PASS name |
|---|---|---|---|---|
| 1 | Negation of conjecture | FOF formula | FOF formula (refutation form) | `negate_conjecture` |
| 2 | NNF conversion | FOF | NNF formula | `nnf_conversion` |
| 3 | Miniscoping | NNF | NNF (reduced quantifier scope) | `miniscoping` |
| 4 | Flattening | NNF | Flattened NNF | `flattening` |
| 5 | Definitional CNF (Tseitin) | NNF | CNF clause set | `cnf_conversion` |
| 6 | Skolemization | CNF | CNF (no existential quantifiers) | `skolemization` |
| 7 | Variable standardization | CNF | CNF (fresh variables per clause) | `variable_renaming` |
| 8 | Predicate elimination | CNF | CNF (reduced symbol set) | `predicate_elimination` |
| 9 | SinE / relevance filtering | CNF + axioms | CNF (pruned axioms) | `relevance_filtering` |
| 10 | Simplification | CNF | CNF (tautology, dup-literal, blocked clause removed) | `simplification` |
| 11 | Pre-search subsumption | CNF | CNF (subsumed clauses removed) | `pre_subsumption` |

### 7.2 Stage details

**Stage 1: Negation of conjecture.**
The conjecture is negated and added to the axiom set. The problem becomes: show that axioms ∪ {¬conjecture} is unsatisfiable. If the conjecture is already negated (input format convention), this step is a no-op.

**Stage 2: NNF conversion.**
Push negations inward using De Morgan's laws. Eliminate implications (`A → B` becomes `¬A ∨ B`). Eliminate equivalences (`A ↔ B` becomes `(A ∧ B) ∨ (¬A ∧ ¬B)`). Result: formula contains only `∧`, `∨`, `¬` (applied only to atoms), `∀`, `∃`.

**Stage 3: Miniscoping.**
Reduce quantifier scope by moving quantifiers inward where possible. `∀x.(P(x) ∧ Q)` becomes `(∀x.P(x)) ∧ Q` if `x` is not free in `Q`. This reduces the number of variables in scope during CNF conversion, which reduces Skolem function arity.

**Stage 4: Flattening.**
Remove nested function applications where possible. `f(g(x))` may be flattened to `f(y) ∧ y = g(x)` with fresh variable `y`. This is optional and controlled by a configuration flag.

**Stage 5: Definitional CNF (Tseitin encoding).**
Convert NNF to CNF using definitional encoding (Tseitin 1968). Each subformula gets a fresh propositional variable. The result is equisatisfiable with the original formula but may be exponentially smaller than structural CNF. Blowup is polynomial in formula size.

Blowup bound: `kMaxCnfExpansionRatio`. If exceeded, abort preprocessing and proceed with original clauses.

**Stage 6: Skolemization.**
Replace existentially quantified variables with Skolem functions. `∃x.∀y.P(x,y)` becomes `P(f(y), y)` where `f` is a fresh Skolem function. Preserves satisfiability (not logical equivalence). Skolem function arity equals the number of universally quantified variables in scope.

**Stage 7: Variable standardization.**
Rename variables so that each clause has its own fresh variable set. This prevents accidental variable capture during resolution and unification.

**Stage 8: Predicate elimination.**
Remove predicates that are defined in terms of other predicates. If `P(x) ↔ Q(x) ∧ R(x)`, replace all occurrences of `P` with `Q ∧ R` and remove the definition. Reduces symbol count and search space.

**Stage 9: SinE / relevance filtering.**
Prune axioms that are irrelevant to the conjecture. Uses symbol occurrence analysis: if an axiom shares no symbols with the conjecture (transitively), it is likely irrelevant. Controlled by depth and relevance threshold (named constants). Reference: Hoder & Voronkov, CADE 2012.

**Stage 10: Simplification.**
Remove tautologies (`P ∨ ¬P`), duplicate literals (`P ∨ P` becomes `P`), and blocked clauses. Bounded rewrite passes (`kMaxSimplifyRounds`).

**Stage 11: Pre-search subsumption.**
Remove clauses that are subsumed by other clauses. Uses the clause indexing infrastructure (Section 9). Bounded by index size.

### 7.3 Bounded preprocessing

Each stage has its own resource budget. If any stage exceeds its budget:
1. Abort that stage and proceed with current state (documented fallback), or
2. Return `GaveUp` with reason `preprocessing_timeout`.

Never silently continue with partial preprocessing that changes semantics.

### 7.4 HPC-PASS certification

Every preprocessing stage carries the full §38.49 comment block with `CEP:HPC-PASS`, `CEP:HPC-PASS-LEGALITY`, `CEP:HPC-PASS-PRESERVES`, `CEP:HPC-PASS-COST`, `CEP:HPC-PASS-FAILURE`, `CEP:HPC-PASS-EVIDENCE`.

---

## 8. Core Data Structures (CEP-0 / OPT-0)

### 8.1 Arena allocator

The arena is the foundation of all memory management.

**Design:**

| Property | Description |
|---|---|
| Allocation strategy | Bump pointer. O(1) per allocation. |
| Deallocation | No individual deallocation. Bulk reset when a search branch is pruned. |
| Generation counters | For epoch-based reclamation. Each generation has a monotonic ID. |
| Thread safety | Thread-local arenas for portfolio workers. Shared arena for single-threaded search. |
| Alignment | All allocations aligned to `config/target.rs`: `kCacheLineBytes` (§11.2). |
| Capacity | Named constant `kArenaCapacityBytes`. No resizing. |
| Exhaustion | Returns `MemoryExhausted` error. No panic. No UB. |

**Arena lifecycle:**

1. **Initialization:** Allocate the arena region (single large allocation). Build hash-consing table. This happens before any hot path.
2. **Search phase:** All terms, clauses, substitutions, and index nodes are allocated from the arena. No heap allocation.
3. **Branch pruning:** When AVATAR backtracks or a portfolio worker finishes, reset the arena to a saved generation checkpoint. All allocations after that checkpoint are invalidated in O(1).
4. **Shutdown:** Free the arena region.

**Fragmentation behavior:**

Bump-pointer allocation has zero fragmentation within a generation. Fragmentation only occurs across generations if some objects from older generations are still live. MAPT uses generation counters to track this. If fragmentation exceeds `kMaxArenaFragmentationRatio`, the arena is compacted (cold operation, CEP-1).

### 8.2 Substitution engine

**Design:**

| Property | Description |
|---|---|
| Storage | Flat array indexed by variable ID. No hash map. |
| Lookup | O(1): `subst[var_id]` |
| Composition | Explicit. Allocates into the arena. |
| MGU computation | Robinson's algorithm with occurs check (Martelli & Montanari 1982). |
| Matching | One-directional. Only the pattern's variables are substituted. |
| Binding trail | For backtracking during unification. Bounded by `kMaxUnificationDepth`. |

**Unification algorithm:**

Robinson's unification with occurs check. The occurs check prevents infinite terms (`x = f(x)`). The algorithm is O(n) where n is the size of the terms being unified.

The binding trail records each binding made during unification. If unification fails, the trail is unwound to restore the previous state. This is critical for backtracking in the search loop.

**OPT-0 requirement:** Unification is called millions of times per second. It must be OPT-0. The flat-array substitution lookup and the binding trail must generate minimal instructions. No allocation. No indirect calls. No branches on the hot path except the occurs check and the unification case analysis.

### 8.3 Term ordering

Two orderings are implemented:

| Ordering | Use case | Reference |
|---|---|---|
| KBO (Knuth-Bendix Ordering) | Default for superposition | Knuth & Bendix 1970 |
| LPO (Lexicographic Path Ordering) | Alternative, configurable | Kamin & Reddy 1994 |

**KBO design:**

Each function symbol has a weight `w(f) ≥ 1`. Variables have weight 1. A precedence `>` is defined on symbols. `s ≻_{KBO} t` iff:
1. `w(s) > w(t)`, or
2. `w(s) = w(t)` and lexicographic conditions on precedence hold.

Weight computation is cached on the term header (computed once during hash-consing). This makes ordering comparison O(depth) instead of O(size).

**LPO design:**

`s = f(s₁, ..., sₘ) ≻_{LPO} t` iff one of:
1. `t = g(t₁, ..., tₙ)` and `f > g` and `s ≻_{LPO} tⱼ` for all j.
2. `t = f(t₁, ..., tₙ)` and `(s₁, ..., sₘ) >_{lex} (t₁, ..., tₙ)` under `≻_{LPO}`.
3. `sᵢ ⪰_{LPO} t` for some i.

**OPT-0 requirement:** Ordering comparison is on the hot path (called during every superposition and resolution inference). Must be OPT-0. Cache-friendly: compare term headers first (symbol ID, weight), recurse only on tie.

**Configuration:**

The ordering is selected at startup via `config/strategy.rs`. The weight function and precedence are named constants or loaded from a strategy file. No hard-coded weights (§11.3).

### 8.4 Clause database

The clause database manages active, passive, and waiting clause sets.

| Set | Purpose | Data structure |
|---|---|---|
| Active (Usable) | Clauses already processed by the given-clause loop | Indexed for subsumption checking (discrimination tree + feature-vector index) |
| Passive (Unprocessed) | Clauses waiting to be selected | Priority queue ordered by (age, weight, id) |
| Waiting | Clauses deferred by AVATAR (inactive components) | Flat array, activated/deactivated by AVATAR truth assignments |

**Passive set design:**

The passive set is a binary heap (priority queue). The ordering key is `(age, weight, clause_id)`. Ties are broken by clause ID (monotonic counter), ensuring deterministic selection (§38.10).

The heap is implemented as a flat array in the arena. No allocation per insertion. Insertion is O(log n). Extraction is O(log n).

**Active set design:**

The active set is indexed for fast subsumption and rewriting queries. The index is a discrimination tree (Section 9). Clauses are inserted into the index when they move from passive to active.

**Waiting set design:**

The waiting set is a flat array of clause pointers. AVATAR activates/deactivates clauses by setting/clearing a flag. No allocation. No reordering.

---

## 9. Term and Clause Indexing (CEP-0 / OPT-0)

Indexing is critical for performance. Without it, subsumption and rewriting are O(n²).

### 9.1 Index types

| Index | Purpose | Lookup complexity | Build complexity |
|---|---|---|---|
| Discrimination tree (path index) | Forward subsumption, backward subsumption, rewriting | O(term depth) | O(n × depth) |
| Feature-vector index | Fast subsumption filtering | O(feature vector size) | O(n × feature count) |
| Substitution tree index | Generalization/subsumption queries | O(term depth) | O(n × depth) |
| Perfect hash index | Ground term lookup | O(1) | O(n) |
| Inverted index (symbol-based) | Quick filtering by symbol | O(occurrences) | O(n × symbols per clause) |

### 9.2 Discrimination tree

The discrimination tree is the primary index for subsumption and rewriting.

**Structure:**

- Root node represents the empty term.
- Each edge represents a symbol or variable.
- Leaf nodes store clause/literal references.
- Internal nodes branch on the next symbol in the term path.

**Operations:**

- **Insert:** Walk the tree, creating nodes as needed. O(depth).
- **Retrieve (subsumption):** Walk the tree, matching symbols. Variables in the query match any symbol. O(depth × branching factor).
- **Retrieve (rewriting):** Walk the tree, matching the left-hand side of rewrite rules. O(depth).
- **Delete:** Remove clause references from leaf nodes. O(depth).

**Design rationale:**

The discrimination tree is chosen over substitution trees because it has better cache behavior for the common case (subsumption queries). Substitution trees are more general but have worse constant factors.

The tree is stored in the arena. Nodes are allocated contiguously. Child pointers are offsets, not absolute pointers, to reduce memory traffic.

### 9.3 Feature-vector index

The feature-vector index is a secondary filter for subsumption.

**Design:**

Each clause is represented as a feature vector: counts of each symbol, polarity, and arity. Subsumption queries first filter by feature vector (cheap, O(feature count)), then verify with the discrimination tree (expensive, O(depth)).

This two-level approach reduces the number of discrimination tree lookups by 10-100x on typical benchmarks.

### 9.4 Index multiplexer

A single query dispatcher selects the appropriate index based on query type:

| Query type | Index used |
|---|---|
| Subsumption query | Feature-vector filter → discrimination tree |
| Rewriting query | Discrimination tree |
| Ground term lookup | Perfect hash |
| Symbol occurrence query | Inverted index |

The multiplexer is a tagged enum dispatch (no `dyn Trait`, no virtual dispatch). The dispatch is a `match` on the query type, which compiles to a jump table.

### 9.5 Index maintenance

Indexes are updated incrementally:
- When a clause enters the active set: insert into all indexes.
- When a clause is removed (subsumed, deleted): remove from all indexes.
- When the arena is reset (branch pruning): rebuild indexes from scratch (cold operation).

Index rebuild cost is bounded and documented. If rebuild exceeds `kMaxIndexRebuildTime`, the system returns `GaveUp`.

---

## 10. Inference Engine — ATP (CEP-0 / HPC-0 / OPT-0)

### 10.1 Inference rules

| Rule | HPC-PASS | OPT-0? | Reference |
|---|---|---|---|
| Binary resolution | `binary_resolution` | Yes | Robinson 1965, Bachmair & Ganzinger 2001 |
| Ordered resolution | `ordered_resolution` | Yes | Bachmair & Ganzinger 2001 |
| Superposition | `superposition` | Yes | Bachmair & Ganzinger 1994 |
| Factoring | `factoring` | Yes | Bachmair & Ganzinger 1994 |
| Equality factoring | `equality_factoring` | No (initially) | Nieuwenhuis & Rubio 2001 |
| Demodulation (rewriting) | `demodulation` | Yes | Bachmair & Ganzinger 1994 |
| Forward subsumption | `forward_subsumption` | No (initially) | Plotkin 1972 |
| Backward subsumption | `backward_subsumption` | No (initially) | Plotkin 1972 |
| Subsumption resolution | `subsumption_resolution` | No | Riazanov 2003 |
| Tautology deletion | `tautology_deletion` | No | Standard |
| Condensation | `condensation` | No | Standard |
| Equality resolution | `equality_resolution` | No | Nieuwenhuis & Rubio 2001 |
| AVATAR split | `avatar_splitting` | No | Voronkov 2014, Barbosa et al. 2023 |
| Literal selection | `literal_selection` | No | Bachmair & Ganzinger 2001 |

### 10.2 Side conditions (legality)

Every inference rule has side conditions. These are the `CEP:HPC-PASS-LEGALITY` conditions.

**Superposition:**

| Condition | Description |
|---|---|
| Unification | The superposition term must unify with the target subterm. MGU must exist. |
| Variable restriction | The target subterm must not be a variable. |
| Maximality | The resulting literal must be maximal or selected. |
| Ordering | The equation must be oriented: `sσ ≻ tσ`. |
| Selection | If the literal is selected, superposition is allowed regardless of maximality. |

**Resolution:**

| Condition | Description |
|---|---|
| Complementarity | The resolved literals must be complementary (one positive, one negative). |
| Unification | The MGU of the resolved atoms must exist. |
| Maximality/Selection | The resolved literals must be maximal or selected. |

**Factoring:**

| Condition | Description |
|---|---|
| Unification | The factored literals must be unifiable. |
| Maximality | The resulting literal must be maximal. |

**Demodulation:**

| Condition | Description |
|---|---|
| Orientation | The rewrite rule must be oriented: `s ≻ t`. |
| Matching | The target subterm must match the left-hand side. |
| Variable restriction | The target subterm must not be a variable. |

### 10.3 Inference generation strategy

Inferences are generated lazily. When a clause is selected as the given clause, all inferences between it and the active set are computed. This is the standard given-clause algorithm.

**Generation order:**

1. Simplify the given clause using the active set (demodulation, subsumption).
2. If the simplified clause is redundant, discard it.
3. Generate all inferences between the given clause and the active set.
4. Add resulting clauses to the passive set.

**Inference limit:**

The number of inferences generated per given clause is bounded by `kMaxInferencesPerClause`. If exceeded, excess inferences are deferred to the next iteration. This prevents a single clause from flooding the passive set.

### 10.4 Redundancy criterion

A clause C is redundant w.r.t. a set N if every ground instance Cσ is entailed by ground instances of clauses in N that are strictly smaller than Cσ under the term ordering.

In practice, redundancy is checked via:
- Subsumption (if a smaller clause subsumes C, C is redundant).
- Tautology (if C contains both P and ¬P, C is redundant).
- Simplification (if C can be simplified to a smaller clause, the original is redundant).

---

## 11. SAT Engine — CDCL (CEP-0 / HPC-0 / OPT-0)

### 11.1 Component inventory (47 components)

**Core data structures (8):**

| # | Component | Description |
|---|---|---|
| S1 | Boolean variable representation | Dense integer IDs, 0-indexed |
| S2 | Literal representation | Variable ID + polarity bit. Packed into a single `u32`. |
| S3 | Clause representation (watched literal scheme) | Arena-allocated. Two watched literals per clause. |
| S4 | Clause database | Arena-backed, generation-tagged. |
| S5 | Trail (assignment stack) | Flat array of assigned literals with decision level markers. |
| S6 | Watch lists | Per-literal list of clause pointers. Stored contiguously in arena. |
| S7 | Variable activity scores (VSIDS heap) | Binary heap in arena. Activity scores as `f64`. |
| S8 | Phase / polarity saving table | Flat array indexed by variable ID. Stores last assigned polarity. |

**Boolean Constraint Propagation (3):**

| # | Component | Description |
|---|---|---|
| S9 | Unit propagation engine (BCP) | **OPT-0, hottest path.** Processes the trail, propagates unit implications. |
| S10 | Watch literal maintenance | **OPT-0.** Updates watch lists when a watched literal becomes false. |
| S11 | Propagation queue management | Trail-driven. Bounded by trail capacity. |

**Decision & Search (6):**

| # | Component | Description |
|---|---|---|
| S12 | Decision heuristic (VSIDS) | Selects unassigned variable with highest activity score. |
| S13 | Activity decay / update | On conflict, bump variables in learnt clause. Periodically decay all scores. |
| S14 | Phase selection | Use saved phase (phase saving) or constant phase. |
| S15 | Decision level tracking | Flat array of decision levels. |
| S16 | Restart strategy | Luby sequence (Luby et al. 1993) or geometric. Configurable. |
| S17 | Phase saving and reset | Save polarity on assignment. Reset on restart (configurable). |

**Conflict Analysis & Learning (7):**

| # | Component | Description |
|---|---|---|
| S18 | Conflict detection | BCP detects a clause where all literals are false. |
| S19 | First UIP computation | **OPT-0.** Traverse implication graph backwards to find the first Unique Implication Point. |
| S20 | Learnt clause minimization | Self-subsuming resolution to remove redundant literals from learnt clause. |
| S21 | Learnt clause addition | Add learnt clause to database. Update watch lists. |
| S22 | Backjump | Non-chronological backtracking to the second-highest decision level in the learnt clause. |
| S23 | Clause activity / quality tracking (LBD) | Literal Block Distance: number of distinct decision levels in the clause. Lower LBD = higher quality. |
| S24 | Clause bumping / activity update | Update clause activity scores on conflict. |

**Clause Database Management (5):**

| # | Component | Description |
|---|---|---|
| S25 | Clause deletion / garbage collection | Remove learnt clauses that exceed quality threshold. |
| S26 | Clause reduction policy | LBD-based, age-based. Configurable thresholds. |
| S27 | Clause compaction / defragmentation | Compact arena when fragmentation exceeds threshold. Cold operation. |
| S28 | Binary/ternary clause special storage | Store binary and ternary clauses in dedicated arrays for cache efficiency. |
| S29 | Clause locking | Protect clauses from deletion during conflict analysis. |

**Preprocessing (8):**

| # | Component | Description |
|---|---|---|
| S30 | Subsumption (self-subsuming resolution) | Remove subsumed clauses. |
| S31 | Blocked clause elimination (BCE) | Remove blocked clauses. |
| S32 | Bounded variable elimination (BVE) | Eliminate variables by resolution. |
| S33 | Tautology removal | Remove tautological clauses. |
| S34 | Duplicate literal / clause removal | Remove duplicates. |
| S35 | Failed literal probing | Probe literals to detect unit implications. |
| S36 | Vivification | Strengthen clauses by removing literals. |
| S37 | Hyper-binary resolution | Optional preprocessing. |

**Incremental Solving (3):**

| # | Component | Description |
|---|---|---|
| S38 | Assumption-based solving | Activation literals for AVATAR integration. |
| S39 | Incremental solve interface | Multi-call solving without rebuilding state. |
| S40 | Model extraction | Return satisfying assignment. |

**Proof Logging (3):**

| # | Component | Description |
|---|---|---|
| S41 | DRAT / LRAT proof emission | Emit proof steps as clauses are added/deleted. |
| S42 | Proof step recording | Flat buffer of proof steps. Bounded by `kMaxProofSteps`. |
| S43 | Proof verification | Internal DRAT checker. Validates proof after solve. |

**Integration with ATP (4):**

| # | Component | Description |
|---|---|---|
| S44 | AVATAR component registration | ATP registers split components with the SAT solver. |
| S45 | SAT → ATP clause learning callback | SAT solver exports learnt clauses to ATP. |
| S46 | Shared clause database bridge | Zero-copy clause sharing via shared arena. |
| S47 | SAT model → ATP component truth assignment | SAT solver returns truth assignment for AVATAR components. |

### 11.2 The three hottest paths (OPT-0 mandatory)

| Path | Component | Why OPT-0 |
|---|---|---|
| Unit propagation (BCP) | S9, S10 | Called millions of times per second. 2 loads + 1 branch per watch check. |
| Conflict analysis (First UIP) | S19 | Called once per conflict. Millions of conflicts per solve. |
| Decision variable selection (VSIDS) | S12 | Called once per decision. Heap extract-max + re-insert. |

### 11.3 Watched literal scheme

Per Moskewicz et al. (Chaff, DAC 2001) and Biere (CaDiCaL, SAT 2020):

- Each clause of length ≥ 2 selects two watched literals.
- BCP only inspects a clause when one of its watched literals becomes false.
- Invariant: if both watched literals are not false, the clause is satisfied or not yet unit.
- This gives O(1) amortized cost per propagation step.

**Watch list layout:**

Watch lists are stored contiguously in the arena. Each literal has a list of clause pointers. When a watched literal becomes false, the solver iterates the watch list, looking for a new watch literal or detecting unit propagation.

The watch list is a linked list threaded through the clause structures themselves (no separate allocation). Each clause has two "next watch" pointers, one for each watched literal. This eliminates pointer chasing and keeps watch list traversal cache-friendly.

### 11.4 CDCL correctness

- Every learnt clause is a logical consequence of the original formula (proven by resolution over the implication graph).
- CDCL terminates and correctly decides SAT/UNSAT.
- Proof logging (DRAT/LRAT) provides an independently checkable certificate.

### 11.5 Restart strategy

MAPT uses the Luby sequence (Luby, Sinclair & Zuckerman 1993) by default. The restart interval grows as 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...

The base interval is a named constant (`kSatRestartBaseInterval`). The multiplier is configurable. Geometric restarts are available as an alternative.

### 11.6 Clause deletion policy

Learnt clauses are deleted when the database exceeds `kSatMaxLearntClauses`. Deletion priority is based on:
1. LBD (higher LBD = lower quality = deleted first).
2. Age (older clauses deleted first among same LBD).
3. Activity (lower activity = deleted first among same LBD and age).

Clauses currently involved in conflict analysis are locked and not deleted.

---

## 12. AVATAR Integration (ATP ↔ SAT)

### 12.1 Architecture

```
┌─────────────────────────────────────────────────────────┐
│              ATP Search Loop                             │
│         (Given-Clause Algorithm)                        │
│                                                         │
│  ┌──────────────────────────────────────────────┐       │
│  │ Inference Engine                              │       │
│  │ (Superposition, Resolution, Factoring)        │       │
│  └────────────────────┬─────────────────────────┘       │
│                       │                                 │
│                       ▼                                 │
│  ┌──────────────────────────────────────────────┐       │
│  │ AVATAR Splitter                               │       │
│  │ Splits clause into components                 │       │
│  │ Each component → propositional variable       │       │
│  └────────────────────┬─────────────────────────┘       │
│                       │                                 │
│                       ▼                                 │
│  ┌──────────────────────────────────────────────┐       │
│  │ SAT Solver (CDCL)                             │       │
│  │ Solves propositional abstraction              │       │
│  │ Returns model or conflict                     │       │
│  └────────────────────┬─────────────────────────┘       │
│                       │                                 │
│            ┌──────────┴──────────┐                      │
│            ▼                     ▼                      │
│  ┌──────────────┐    ┌──────────────────┐              │
│  │ Model-guided │    │ Conflict-driven  │              │
│  │ selection    │    │ backtracking     │              │
│  │ (activate    │    │ (add conflict    │              │
│  │  components) │    │  clause to SAT)  │              │
│  └──────────────┘    └──────────────────┘              │
└─────────────────────────────────────────────────────────┘
```

### 12.2 AVATAR rules

Per Voronkov (CAV 2014) and Barbosa et al. (JAR 2023):

1. **Split:** A clause C with variable-disjoint components C₁ ∨ ... ∨ Cₙ is split. Each component Cᵢ is associated with a propositional variable aᵢ. The clause is replaced by the components, each guarded by its propositional variable.

2. **SAT solve:** The SAT solver finds a satisfying assignment for the propositional abstraction. The abstraction contains the propositional variables aᵢ and any conflict clauses learned so far.

3. **Model-guided selection:** Only components whose propositional variables are true under the SAT model are activated for first-order search. Inactive components are moved to the waiting set.

4. **Conflict-driven backtracking:** If first-order search finds a contradiction under the current assignment, a conflict clause is added to the SAT solver. The SAT solver then backtracks and finds a new assignment.

### 12.3 Splitting criterion

A clause is splittable if its variable dependency graph has multiple connected components. The variable dependency graph has an edge between two variables if they appear in the same literal.

Splitting is beneficial when:
- The clause has multiple disconnected components.
- The components are large enough that searching them independently is cheaper than searching them together.

Splitting is controlled by `kAvatarMinComponentSize` (named constant). Components smaller than this threshold are not split.

### 12.4 Integration rules

- **No serialization.** Clauses move between ATP and SAT by pointer into the shared arena. Zero copy.
- **No locks.** The SAT solver runs on the same thread as the AVATAR controller, or uses the lock-free work-stealing deque for portfolio mode.
- **No FFI.** Both engines are in the same language (Rust). No `extern "C"` boundary between them.
- **Shared proof graph.** Every SAT learnt clause and every ATP inference go into the same derivation DAG. Proof reconstruction covers both.
- **Shared resource budgets.** SAT solver gets its own inference count limit, time slice, and memory budget from `config/limits.rs`.

### 12.5 Soundness

AVATAR is refutationally complete if splitting is exhaustive (Voronkov 2014, Theorem 1). The legality proof is documented in `CEP:HPC-PASS-LEGALITY` for the `avatar_splitting` pass.

---

## 13. Theory Reasoning / SMT (CEP-0 / HPC-0)

### 13.1 Supported theories

| Theory | Solver approach | Reference |
|---|---|---|
| Linear integer arithmetic (LIA) | Simplex + branch-and-bound | Nieuwenhuis et al. 2006 |
| Linear real arithmetic (LRA) | Simplex | Nieuwenhuis et al. 2006 |
| Non-linear arithmetic (NIA) | Bounded, heuristic | Barrett et al. 2009 |
| Bitvectors | Bit-blasting + SAT | Barrett et al. 2009 |
| Arrays | Congruence closure + extensionality | Nelson & Oppen 1980 |
| Algebraic datatypes | Structural reasoning | Barrett et al. 2009 |
| Uninterpreted functions | Congruence closure | Nelson & Oppen 1980 |

### 13.2 DPLL(T) architecture

Per Nieuwenhuis, Oliveras & Tinelli (JACM 2006):

1. The SAT solver proposes a Boolean assignment.
2. The theory solver checks consistency of theory literals under that assignment.
3. If inconsistent, the theory solver generates a theory lemma (conflict clause over theory atoms).
4. The SAT solver adds the theory lemma and continues.
5. Repeat until SAT or UNSAT.

### 13.3 Nelson-Oppen theory combination

For stably infinite, signature-disjoint theories: propagate equalities over shared variables. Each theory solver checks its own consistency. If all theory solvers report consistent, the combined assignment is satisfiable.

### 13.4 Congruence closure

Per Nelson & Oppen (JACM 1980):

Maintain a union-find data structure over ground terms. When an equality `a = b` is asserted, union the equivalence classes of `a` and `b`. Propagate congruence: if `a ≡ b`, then `f(..., a, ...) ≡ f(..., b, ...)`.

The congruence closure algorithm is O(n log n) where n is the number of ground terms. It is used for uninterpreted functions and as a component of array reasoning.

### 13.5 Theory-aware simplification

Theory solvers can simplify clauses:
- Arithmetic simplification: `x + 0 = x`, `x * 1 = x`, etc.
- Congruence closure simplification: if `a ≡ b` is known, replace `a` with `b` in clauses.
- Theory-specific tautology detection: `x < x` is always false.

### 13.6 Theory lemma generation

When the theory solver detects an inconsistency, it generates a theory lemma. The lemma is a clause over theory atoms that is valid in the theory. The SAT solver adds the lemma and continues searching.

Theory lemmas are recorded in the proof graph with rule `Theory_Lemma`.

---

## 14. Higher-Order Extensions (CEP-0 / HPC-0)

### 14.1 Lambda-free HOL

MAPT supports the lambda-free fragment of higher-order logic. This means:
- Function application is supported (`f(x)`, `f(g(x))`).
- Lambda abstraction is not supported in the hot path.
- Higher-order unification is not used. Instead, higher-order terms are compiled to first-order terms via applicative encoding.

Reference: Vukmirović et al., "Superposition for Full Higher-Order Logic," CADE 2021.

### 14.2 Boolean reasoning extensions

Boolean terms are treated as first-class citizens. Boolean simplification rules are applied:
- `¬¬A → A`
- `A ∧ A → A`
- `A ∨ A → A`
- `A ∧ ¬A → false`
- `A ∨ ¬A → true`

### 14.3 Extensionality handling

Extensionality axioms are added for function and predicate symbols:
- `∀f g. (∀x. f(x) = g(x)) → f = g` (function extensionality)
- `∀P Q. (∀x. P(x) ↔ Q(x)) → P = Q` (predicate extensionality)

These axioms are added lazily, only when needed.

---

## 15. Search Control (CEP-0 / HPC-0)

### 15.1 Given-clause algorithm

The given-clause algorithm is the main saturation loop. It maintains two sets: passive (unprocessed) and active (processed).

**Loop:**
1. Select a clause from the passive set using the selection strategy.
2. Move it to the active set.
3. Simplify it using the active set.
4. If redundant, discard.
5. Generate all inferences between it and the active set.
6. Add results to the passive set.
7. If the empty clause is derived, return `Theorem`.
8. If the passive set is empty, return `Saturated`.

**Fairness:** Every clause selected for processing eventually has all its inferences computed. Fairness implies completeness.

### 15.2 Selection strategies

| Strategy | Description |
|---|---|
| Age-weight ratio | Select clause with minimum `age / weight` ratio. Balances breadth-first and depth-first search. |
| Conjecture distance | Select clause closest to the conjecture in symbol overlap. |
| Weight-only | Select clause with minimum weight. |
| Age-only | Select clause with minimum age (breadth-first). |
| SOS (Set of Support) | Only select clauses derived from the conjecture or its descendants. |

The selection strategy is configurable via `config/strategy.rs`. Multiple strategies can be run in parallel (portfolio mode).

### 15.3 Clause weight function

Clause weight is a measure of clause complexity. MAPT uses a weighted sum:

`weight = Σ (symbol_weight(s) × occurrence_count(s))` for all symbols s in the clause.

Symbol weights are configurable. Default: function symbols weight 1, predicate symbols weight 1, variables weight 0.

### 15.4 Time-slice scheduling

In portfolio mode, each strategy gets a time slice. The time slice is a named constant (`kPortfolioTimeSliceMs`). Strategies that have not found a proof within their time slice are paused and the next strategy runs.

### 15.5 Adaptive strategy switching

MAPT monitors the inference rate. If the inference rate drops below `kMinInferenceRate`, the current strategy is switched to an alternative. This prevents a single strategy from dominating when it is not making progress.

---

## 16. Advanced Redundancy Elimination (CEP-0)

| Technique | Description |
|---|---|
| Global subsumption | Check all clauses in the active set for subsumption. |
| Subsumption demodulation | Use subsumption to simplify clauses. |
| Contextual literal cut | Remove literals that are entailed by the context. |
| Clause coloring | Track which axioms each clause depends on. Remove clauses that depend on irrelevant axioms. |
| Interpolation-based redundancy | Use interpolation to identify redundant clauses. |
| Redundant literal elimination | Remove literals that are entailed by other literals in the clause. |
| Equality blocking | Block superposition inferences that are redundant due to equality reasoning. |
| Global redundancy criterion | Enforce the formal redundancy criterion from Bachmair & Ganzinger 2001. |

---

## 17. Model Building (CEP-0 / CEP-1)

### 17.1 Finite model building

When the clause set is saturated without finding a proof, MAPT attempts to construct a finite model. This provides a counterexample to the conjecture.

| Component | Description |
|---|---|
| Term algebra model | Construct a model from the Herbrand universe. |
| SAT-based model finding | Use the SAT solver to find a model for the propositional abstraction. |
| Counterexample generation | Extract a concrete counterexample from the model. |
| Model-guided search | Use the model to guide further search. |

### 17.2 Model output

Models are output in SMT-LIB format or TPTP model format. The model includes:
- Domain elements.
- Function interpretations.
- Predicate interpretations.

---

## 18. Proof Production (CEP-1 / HPC-1)

### 18.1 Proof recording

Every derived clause carries its derivation step (Section 5.4). The proof is a DAG where nodes are clauses and edges are inference steps.

### 18.2 Proof reconstruction

After finding a proof, MAPT reconstructs a clean TSTP proof. This involves:
1. Traversing the proof DAG from the empty clause back to the axioms.
2. Removing redundant steps.
3. Formatting as TSTP.

### 18.3 Proof compression

Proof compression removes redundant inference steps. Techniques:
- Subsumption-based compression: remove steps that are subsumed by later steps.
- Interpolation-based compression: use interpolation to shorten proof chains.

### 18.4 Proof verification

MAPT includes an internal proof checker. The checker verifies every inference step independently. If the checker finds an invalid step, the proof is rejected and MAPT returns `Error`.

This is critical for soundness certification. An ATP that produces an invalid proof is worse than one that produces no proof.

### 18.5 DRAT/LRAT proof output

For the SAT engine, MAPT emits DRAT or LRAT proofs. These are independently checkable by external tools (drat-trim, lrat-check). Reference: Wetzler et al. 2014, Cruz-Filipe et al. 2017.

---

## 19. Concurrency / Portfolio (CEP-0, hand-rolled)

### 19.1 Architecture

MAPT uses a portfolio approach: multiple search strategies run in parallel. The first strategy to find a proof wins.

| Component | Description |
|---|---|
| Portfolio manager | Orchestrates multiple search strategies. |
| Clause sharing pool | Lock-free pool for sharing useful learnt clauses between workers. |
| Work-stealing deque | Chase-Lev deque for load balancing. |
| Thread pinning / topology | Pin threads to cores. Discover NUMA topology. |
| Resource budgeter | Enforce time/memory/inference limits per worker. |
| Result aggregation | First-to-finish. Cancel other workers on proof found. |
| Graceful shutdown | Cancel workers cleanly on timeout or proof found. |
| NUMA-aware memory placement | Place arenas on the NUMA node closest to the worker thread. |

### 19.2 Clause sharing

Workers share useful learnt clauses through a lock-free pool. A clause is shared if:
- Its weight is below `kSharedClauseMaxWeight`.
- Its LBD is below `kSharedClauseMaxLBD`.
- It was derived by a high-quality inference (superposition, resolution).

The sharing pool is a bounded MPMC (multi-producer, multi-consumer) queue. Implemented with atomics and explicit memory ordering (§8.43). No locks.

### 19.3 Work-stealing

Each worker has a local deque of clauses to process. When a worker's deque is empty, it steals from other workers' deques. The Chase-Lev deque provides O(1) push/pop from the owner and O(1) amortized steal from thieves.

### 19.4 Thread management

Threads are created at initialization (before hot path). Thread count is a named constant (`kPortfolioThreadCount`). Threads are pinned to cores using OS-specific APIs (isolated in `target/` directory).

No threads are created or destroyed during search. No locks. No condition variables. All coordination is via atomics and lock-free data structures.

### 19.5 Determinism

Portfolio mode is inherently nondeterministic at the system level (thread scheduling). However, each individual strategy must be deterministic (§38.10). Given the same input and the same strategy, a single worker produces the same result.

The portfolio result may vary across runs due to scheduling, but the proof itself is always valid.

---

## 20. Resource Management

### 20.1 Named limits

All resource limits are named constants in `config/limits.rs`:

| Limit | Description |
|---|---|
| `kMaxSearchTimeSeconds` | Maximum wall-clock time for search. |
| `kMaxInferences` | Maximum number of inference steps. |
| `kMaxClauses` | Maximum number of clauses in the database. |
| `kMaxTermDepth` | Maximum term depth. |
| `kMaxClauseLiterals` | Maximum literals per clause. |
| `kArenaCapacityBytes` | Arena size. |
| `kMaxInputBytes` | Maximum input file size. |
| `kMaxVariablesPerClause` | Maximum variables per clause. |
| `kMaxUnificationDepth` | Maximum unification depth. |
| `kSatMaxLearntClauses` | Maximum learnt clauses in SAT solver. |
| `kSatRestartBaseInterval` | Base restart interval for SAT solver. |
| `kPortfolioThreadCount` | Number of portfolio workers. |
| `kPortfolioTimeSliceMs` | Time slice per strategy. |

### 20.2 Budget enforcement

Every limit is checked at the appropriate point:
- Time: checked every `kBudgetCheckInterval` iterations (named constant). Not every iteration (too expensive).
- Inference count: checked every iteration.
- Clause count: checked when adding a clause to the database.
- Memory: checked when allocating from the arena.

When a limit is exceeded, MAPT returns the appropriate failure result (`Timeout`, `MemoryExhausted`, `InferenceLimit`). No panic. No UB. No silent continuation.

### 20.3 Safe-state transition

When a budget is exhausted, MAPT transitions to a safe state:
1. Stop generating inferences.
2. Flush any pending proof output.
3. Return the failure result.
4. Free all resources.

The transition must complete within `kSafeStateTransitionMs` (named constant). If it cannot, MAPT aborts with a diagnostic.

---

## 21. Configuration and Strategy

### 21.1 Strategy definition

A strategy is a named configuration that specifies:
- Inference rules to use.
- Selection heuristic.
- Weight function.
- Simplification level.
- AVATAR on/off.
- Theory reasoning on/off.
- Restart strategy.
- Time slice.

Strategies are defined in `config/strategy.rs` or loaded from a strategy file.

### 21.2 Schedule generation

MAPT can generate a schedule of strategies to run. The schedule is a sequence of (strategy, time_slice) pairs. The schedule is deterministic.

### 21.3 Feature-based strategy selection

MAPT extracts features from the input problem (number of clauses, symbols, equality density, Horn fraction, etc.) and selects a strategy based on the feature vector. The feature-to-strategy mapping is a lookup table in `config/`.

### 21.4 Adaptive parameter tuning

MAPT monitors search progress and adjusts parameters:
- If the inference rate drops, increase the age-weight ratio (favor older clauses).
- If the clause database grows too fast, increase the simplification level.
- If no progress after N inferences, switch strategy.

---

## 22. Memory Architecture

### 22.1 Arena layout

The arena is divided into regions:

| Region | Purpose | Lifetime |
|---|---|---|
| Term region | Hash-consed terms | Entire search |
| Clause region | Clauses and literals | Entire search or generation-scoped |
| Substitution region | Substitutions | Generation-scoped |
| Index region | Discrimination trees, feature vectors | Entire search |
| Trail region | SAT trail and watch lists | Entire search |
| Proof region | Derivation steps | Entire search |
| Scratch region | Temporary buffers | Per-inference |

### 22.2 Generation management

Each AVATAR split creates a new generation. When AVATAR backtracks, the arena is reset to the previous generation. All allocations after that generation are invalidated in O(1).

### 22.3 Cache optimization

- Clauses are stored contiguously. Literal arrays are inline for small clauses.
- Terms are hash-consed. Identical subterms share the same pointer.
- Index nodes are stored contiguously. Child pointers are offsets, not absolute pointers.
- Watch lists are threaded through clause structures. No separate allocation.
- The VSIDS heap is a flat array. No pointer chasing.

---

## 23. Formal Specification Layer

### 23.1 Document structure

The `docs/formal/` directory contains 23 specification documents. Each document defines:
1. Formal syntax (BNF or set-theoretic definition).
2. Formal semantics (model-theoretic or proof-theoretic).
3. Inference rules (as formal derivation rules with side conditions).
4. Soundness theorem (with proof sketch or citation).
5. Completeness theorem (with proof sketch or citation).
6. Complexity bounds (where known).
7. CEP&CC mapping (which `CEP:HPC-PASS-LEGALITY` fields cite this document).

### 23.2 Paper collection

The 43 foundational papers are listed in Section 5 of the previous response. Every `CEP:HPC-PASS-LEGALITY` comment in the code points to a specific definition or theorem number in these documents.

### 23.3 The rule

If an implementation cannot point to a specific definition, theorem, or lemma in `docs/formal/` that justifies its behavior, it is not HPC-0 compliant. It is quarantined or exterminated per §34.1.

---

## 24. Benchmark and Certification

### 24.1 TPTP benchmark suite

MAPT is benchmarked against the TPTP problem library (Sutcliffe 2017). The benchmark harness runs MAPT on all problems in a given category (FOF, CNF, TFF, THF) and records:
- Number of problems solved.
- Average time per problem.
- Proof correctness (verified by internal checker).
- Resource usage (time, memory, inferences).

### 24.2 CASC competition

MAPT should be entered in the CASC (CADE ATP System Competition) to validate performance against Vampire, E, Zipperposition, and iProver.

### 24.3 SAT competition benchmarks

The SAT engine is benchmarked on SATLIB and SAT competition instances.

### 24.4 Regression gates

CI fails if:
- CEP-0 benchmark regresses beyond allowed threshold.
- Disassembly changes unexpectedly.
- Branch count changes unexpectedly.
- Allocation appears in hot code.
- Proof correctness fails on any benchmark.

### 24.5 Fuzz testing

MAPT is fuzzed with adversarial TPTP, SMT-LIB, and DIMACS inputs. The fuzzer checks for:
- Crashes.
- Hangs.
- Memory safety violations.
- Unsound inferences.
- Resource exhaustion.

---

## 25. Security Model

### 25.1 Threat model

| Threat | Mitigation |
|---|---|
| Malicious TPTP input causing exponential blowup | All resource budgets enforced. Bounded preprocessing. |
| Malicious input causing stack overflow | Bounded term depth, bounded recursion. |
| Malicious input causing memory exhaustion | Arena capacity bounded. Allocation checked. |
| FFI boundary exploitation | All FFI inputs validated. `#[repr(C)]` for all FFI types. |
| Supply chain attack | Pinned dependencies. Vendored third-party code. |
| Toolchain compromise | Pinned compiler version. Reproducible builds. |

### 25.2 Trust boundaries

| Boundary | Trust level |
|---|---|
| TPTP/SMT-LIB/DIMACS input | Untrusted |
| Strategy configuration file | Trusted (repository file) |
| FFI from external solvers | Untrusted |
| Internal IR | Trusted (constructed by MAPT) |
| Proof output | Trusted (verified by internal checker) |

### 25.3 Resource limits as security

All resource limits serve double duty as security mitigations. They prevent denial-of-service via resource exhaustion (§22.10).

---

## 26. Build Order and Dependencies

### Phase 1: Foundations (months 1–3)

| Component | Dependencies |
|---|---|
| Arena allocator | None |
| Term representation + hash consing | Arena |
| Clause representation | Arena, term representation |
| Symbol table | None |
| Substitution engine | Arena |
| SAT: literal, variable, trail, watch lists | Arena |
| SAT: BCP engine (OPT-0) | Watch lists, trail |

### Phase 2: Core Engines (months 3–6)

| Component | Dependencies |
|---|---|
| Unification, matching | Substitution engine |
| Term ordering (LPO, KBO) | Term representation |
| Clause indexing (discrimination tree) | Term representation, clause representation |
| SAT: CDCL (conflict analysis, learning, backjump) | BCP |
| SAT: decision heuristic (VSIDS) | Trail |
| SAT: restart strategy | CDCL |

### Phase 3: Search Loops (months 6–9)

| Component | Dependencies |
|---|---|
| Given-clause loop (bounded) | Clause database, indexing, inference |
| Superposition + resolution + factoring | Unification, ordering |
| SAT: preprocessing (subsumption, vivification) | CDCL |
| SAT: incremental solving + assumptions | CDCL |
| SAT: proof logging (DRAT) | CDCL |

### Phase 4: Integration (months 9–12)

| Component | Dependencies |
|---|---|
| AVATAR splitter | Given-clause loop, SAT solver |
| SAT ↔ ATP clause bridge | AVATAR, shared arena |
| Model-guided search | AVATAR, SAT solver |
| Portfolio concurrency | Given-clause loop, work-stealing |
| Proof reconstruction (unified) | Proof recording, TSTP writer |

### Phase 5: Theory and Extensions (months 12–15)

| Component | Dependencies |
|---|---|
| DPLL(T) integration | SAT solver, theory solvers |
| Congruence closure | Union-find, term representation |
| Nelson-Oppen combination | Theory solvers |
| Higher-order extensions | Term representation, superposition |

### Phase 6: Certification (months 15–18)

| Component | Dependencies |
|---|---|
| TPTP benchmark suite | All engines |
| SAT competition benchmarks | SAT engine |
| Fuzz testing (adversarial TPTP + CNF) | All parsers |
| Full HPC-0 certification pass | All components |
| Extermination pipeline validation | `cep_lint`, CI |

---

## 27. Component Count Summary

| Category | Components |
|---|---|
| Input layer | 11 |
| Preprocessing pipeline | 16 |
| Core data structures | 14 |
| Term and clause indexing | 7 |
| Inference engine (ATP) | 16 |
| Theory reasoning / SMT | 13 |
| Higher-order extensions | 6 |
| Search control | 12 |
| Advanced redundancy | 8 |
| Model building | 4 |
| Proof production | 7 |
| Concurrency / portfolio | 8 |
| Configuration / strategy | 6 |
| Infrastructure | 10 |
| SAT solver | 47 |
| Integration bridge | 6 |
| **Total** | **~191** |

Roughly 110 are CEP-0 hot-path, requiring full measurement, disassembly, and OPT-0 certification.

---

This is MAPT. 191 certified modules. Two engines. One arena. One proof graph. Zero tolerance for unsound inference. Every component formally specified, measured, and mechanically enforced.