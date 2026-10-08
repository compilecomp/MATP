# MAPT Threat Model

Version: 0.1
Scope: Phase 1 (Foundations): arena allocator, IR (terms, clauses, symbol table), substitution engine, SAT core (literals, trail, watch lists, clause database, BCP), CEP-1 host/builder/verifier/printer, benchmark and lint tooling.

## 1. Assets

- None. MAPT processes no secrets, no credentials, and no private user data (see `config/security_policy.rs`, `kProcessesSecrets = false`). The only assets are correctness (soundness of results) and availability (bounded resource use).

## 2. Untrusted inputs (CEP&CC 22.5)

| Input | Trust level | Entry point | Validation |
|---|---|---|---|
| TPTP / SMT-LIB / DIMACS problem files | Untrusted | Phase 3 parsers (not yet built) | Named bounds in `config/limits.rs` (`kMaxInputBytes`, `kMaxFormulaNodes`, `kMaxTermDepth`, `kMaxSymbolCount`, `kMaxInputSymbolCount`, `kMaxSymbolNameBytes`, `kMaxParseDepth`, `kMaxIncludeDepth`, `kMaxIncludeCount`) |
| Symbol declarations reaching the builder | Untrusted until validated | `cold/symbol_table_builder.rs` | Name length, arity, count, weight, and signature validation at declaration; full structural validation at freeze |
| Benchmark and lint configuration | Repository-trusted | `.cep/cep_lint.json`, bench harness | JSON schema validation with bootstrap error codes; depth-bounded parsing |

Phase 1 has no parser; the only untrusted-facing surface is the symbol table builder, which is exercised adversarially by `tests/security/symbol_bounds_test.rs` and `tests/unit/cold/symbol_table_builder_test.rs`.

## 3. Trust boundaries

See `trust_boundaries.md` for the full map. The Phase 1 boundaries are:

1. Untrusted declarations -> builder validation -> frozen symbol table (the freeze is the trust transition; every entry is revalidated there).
2. Arena backing region: CEP-1 host allocates; CEP-0 arena trusts the region after `Arena::new` validates alignment and capacity.
3. Bench and lint tooling read repository files only; no network, no environment-dependent output.

## 4. Threats considered

| Threat | Mitigation | Evidence |
|---|---|---|
| Memory exhaustion via huge inputs | `kArenaCapacityBytes`, `kMaxInputBytes`, explicit `MemoryExhausted`/`ArenaFull` errors, never growth | `tests/contract/arena_contract_test.rs`, `tests/unit/hot/arena_test.rs` |
| Stack overflow via deep terms | `kMaxTermDepth` enforced at construction; substitution recursion bounded by `kMaxUnificationDepth` | `tests/contract/term_contract_test.rs::deep_term_rejected`, `tests/unit/hot/substitution_test.rs::cyclic_binding_rejected` |
| Integer overflow in offset/size math | Checked arithmetic throughout; static assertions on constant relations in `config/limits.rs` | `tests/unit/config/limits_test.rs` |
| Out-of-bounds reads from forged offsets | Every arena access bounds-checks; handle constructors are crate-private where possible; forged handles fail loudly | `tests/fuzz/term_fuzz_test.rs`, `tests/fuzz/arena_fuzz_test.rs`, `tests/fuzz/sat_fuzz_test.rs` |
| Hash-table probing denial (adversarial collisions) | Seedless FNV-1a (no seed to attack), load-factor bound 0.65, explicit `TableFull` error | `tests/unit/hot/term_test.rs::table_full_after_load_factor_bound` |
| Symbol flooding | Input-side bound `kMaxInputSymbolCount` below the global `kMaxSymbolCount` | `tests/security/symbol_bounds_test.rs` |
| Watch-list corruption breaking BCP soundness | Per-clause watch-slot verification in BCP; property tests verify list integrity after random propagation | `tests/property/bcp_property_test.rs` |
| Supply chain | Zero third-party dependencies in all crates and the linter; pinned toolchain | `Cargo.toml`, `rust-toolchain.toml`, `tools/cep_lint` (in-house JSON) |
| Toolchain drift | Pinned `rustc 1.99.0`, deterministic build profile (LTO, one codegen unit, abort on panic) | `rust-toolchain.toml`, `Cargo.toml` |

## 5. Acceptable failure modes

Under attack, MAPT may refuse work (explicit errors: `ArenaFull`, `TableFull`, `Timeout`, `MemoryExhausted`) or terminate with a diagnostic. Forbidden under attack: undefined behavior, out-of-bounds access, silent corruption, unbounded resource use, unsound inference. No code path may convert an untrusted input into an unsound `Theorem` result; Phase 1 establishes this by construction (no inference rules yet) and by the verifier, which detects corrupted IR (`tests/unit/cold/verifier_test.rs`).

## 6. Side channels

MAPT performs no cryptography and processes no secrets; timing and cache side channels are accepted and documented (`kConstantTimeRequired = false`). No secret-dependent branches exist because no secrets exist.

## 7. Review cadence

This document is versioned with the repository. Any change to a trust boundary, a limit constant, or the input surface requires a security review note in the change description (CEP&CC 22.15).
