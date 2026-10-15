# MAPT

MAPT is a first-order automated theorem prover with an integrated CDCL SAT solver, AVATAR-style clause splitting, theory reasoning, portfolio concurrency, and certified proof production (see `DESIGN.md`). This repository currently contains **Phases 1-4: Foundations, Core Engines, Search Loops, and Integration** (design section 26), built to the letter of the **CEP&CC 0.1** coding standard (`standard.md`).

## Phase 4 contents (design section 26)

| Component | Status | Location |
|---|---|---|
| AVATAR splitter (variable-dependency components, min-size gate, node budget) | complete | `hot/avatar/splitter.rs` |
| AVATAR component table (hash-consing, dense assertion variables) | complete | `hot/avatar/component.rs` |
| AVATAR controller (model-guided activation, conflict clauses, rotation; monotone protocol) | complete | `hot/avatar/controller.rs` |
| Chase-Lev work-stealing deque (owner LIFO, thief FIFO, last-element CAS race) | complete | `hot/concurrency/chase_lev.rs` |
| Bounded MPMC clause-sharing pool (Vyukov cells, exactly-once) | complete | `hot/concurrency/mpmc_pool.rs` |
| Portable clause codec (fixed-budget word records, validated decode) | complete | `hot/concurrency/clause_codec.rs` |
| Portfolio manager (scoped threads, wall-clock slices, first-to-finish, graceful shutdown, sharing) | complete | `cold/portfolio/manager.rs` |
| Unified proof reconstruction (walk, pruning, TSTP writer, replay checker) | complete | `cold/proof_output/tstp.rs` |
| Clause-id side table (proof walks, ancestry, export scans) | complete | `hot/ir/clause.rs` |
| Formal specs 12-14 (AVATAR, concurrency, proof reconstruction) | complete | `docs/formal/` |

## Phase 3 contents (design section 26)

| Component | Status | Location |
|---|---|---|
| Given-clause loop (bounded, budget-injected) | complete | `hot/search/given_clause.rs` |
| Passive set (age/weight ratio, weight, age strategies) | complete | `hot/search/passive.rs` |
| Active set (atom tree, rule tree, feature-vector filter) | complete | `hot/search/active.rs`, `hot/index/feature_vector.rs` |
| Superposition + resolution + factoring (+ equality resolution/factoring, demodulation, subsumption) | complete | `hot/inference/` |
| Bounded inference generator (deferrable cursor) | complete | `hot/search/generate.rs` |
| SAT: clause registry + learnt deletion (LBD/age policy) | complete | `hot/sat/registry.rs` |
| SAT: preprocessing (subsumption, self-subsumption, tautology, duplicates, vivification) | complete | `hot/sat/preprocess.rs` |
| SAT: incremental solving + assumptions with failed cores | complete | `hot/sat/solver.rs`, `hot/sat/cdcl.rs` |
| SAT: DRAT proof recording, writer, internal RUP/RAT checker | complete | `hot/sat/proof.rs`, `cold/proof_output/` |
| Formal specs 07-11 (rules, loop, preprocessing, assumptions, DRAT) | complete | `docs/formal/` |

## Phase 1-2 contents (design section 26)

| Component | Status | Location |
|---|---|---|
| Arena allocator (bump, generations, exhaustion) | complete | `hot/memory/arena.rs` |
| Term representation + hash-consing (FNV-1a, open addressing, load-factor bound) | complete | `hot/ir/term.rs` |
| Clause representation (inline literals, overflow, monotonic IDs, derivation steps) | complete | `hot/ir/clause.rs`, `hot/ir/literal.rs` |
| Symbol table (frozen, CEP-1 builder) | complete | `hot/ir/symbol_table.rs`, `cold/symbol_table_builder.rs` |
| Substitution engine (flat array, trail, application, records) | complete | `hot/unification/substitution.rs` |
| SAT: literals, assignment store, trail, watch lists, clause database | complete | `hot/sat/` |
| SAT: BCP engine (OPT-0, watched literals, amortized O(1)) | complete | `hot/sat/bcp.rs` |
| CEP-1: arena host, IR verifier, debug printer | complete | `cold/` |
| Target hooks: cycle counters (x86-64, arm64, riscv64, generic) | complete | `target/` |
| Named limits and target configuration | complete | `config/` |
| `cep_lint` mechanical enforcement (C++26, 18 rules, self-test) | complete | `tools/cep_lint/`, `.cep/cep_lint.json` |

## Gates (all must pass before merge)

```sh
# Lint: build, self-test, self-lint, repo lint (severity 0 and 1 must be zero)
./tools/cep_lint/build.sh
./tools/cep_lint/build/cep_lint --self-test
./tools/cep_lint/build/cep_lint tools/cep_lint/src
./tools/cep_lint/build/cep_lint hot cold config target src tests benches scripts

# Rust: format, clippy, tests (debug + release incl. expensive), determinism
cargo fmt --all -- --check
cargo clippy --all-targets -- -D warnings
cargo test
cargo test --release -- --ignored
python3 scripts/check_determinism.py

# Benchmarks: measure, gate against baselines, extract disassembly evidence
cargo bench
python3 scripts/bench_gate.py
cargo rustc -p mapt-hot --release -- --emit asm
python3 scripts/extract_disasm.py
```

CI runs all of these on every push (`.github/workflows/ci.yml`), plus AddressSanitizer and UBSan builds (CEP&CC 6.6)
