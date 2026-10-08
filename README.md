# MAPT

MAPT is a first-order automated theorem prover with an integrated CDCL SAT solver, AVATAR-style clause splitting, theory reasoning, portfolio concurrency, and certified proof production (see `DESIGN.md`). This repository currently contains **Phase 1: Foundations** (design section 26), built to the letter of the **CEP&CC 0.1** coding standard (`standard.md`).

## Phase 1 contents (design section 26)

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

CI runs all of these on every push (`.github/workflows/ci.yml`), plus AddressSanitizer and UBSan builds (CEP&CC 6.6).

## Repository layout (design section 4; CEP&CC 32)

- `hot/` — CEP-0/HPC-0 hot-path engine code (`no_std`, zero dependencies, allocation-free after initialization)
- `cold/` — CEP-1 deterministic runtime code (arena host, symbol builder, verifier, printer)
- `config/` — named limits and target constants (CEP&CC 11, 32.11)
- `target/` — ISA-specific code, isolated (CEP&CC 32.5)
- `tests/` — unit, property, contract, fuzz, security, golden suites (133 tests)
- `benches/` — deterministic benchmark harness and committed evidence artifacts
- `tools/cep_lint/` — the mechanical enforcement tool of standard section 50
- `.cep/` — lint configuration (data-driven rules)
- `security/` — threat model, trust boundaries, FFI policy
- `docs/formal/` — normative specifications cited by `CEP:HPC-PASS-LEGALITY` fields
- `scripts/` — CEP-2 deterministic tooling (bench gate, determinism gate, disassembly extraction)
- `quarantine/`, `generated/`, `third_party/` — policy READMEs; all empty in Phase 1

## Standard compliance summary

- Every first-party source file carries a full CEP header; every nontrivial function carries a full CEP comment block with measured `CEP:COST` and `CEP:EVIDENCE` (bench artifacts committed under `benches/artifacts/`).
- Hot code is `no_std`, allocation-free after init, panic-free, lock-free, `dyn`-free; every banned-token class of CEP&CC 25.3 is mechanically enforced by `CEP-LINT-HOT-BANNED`.
- All limits are named constants with static cross-checks (`config/limits.rs`).
- All layouts are pinned by static assertions and golden tests.
- Determinism: monotonic IDs, seedless hashing, sorted iteration; proven by the determinism gate.
- Measurement: 8 benchmark artifacts with cycles-per-operation medians and disassembly extracts for every `CEP:OPTIMAL` claim.

## Next phases

Phases 2-6 (design section 26) are queued in `docs/tickets.md`: unification and ordering (Phase 2), search loops and CDCL (Phase 3), AVATAR and portfolio (Phase 4), theories (Phase 5), certification (Phase 6).
