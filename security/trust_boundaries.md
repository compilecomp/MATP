# MAPT Trust Boundaries

Version: 0.1
Scope: Phase 1. Reference: CEP&CC 22.3, design section 25.2.

## Boundary map

```
Untrusted                       Validated                     Trusted
----------                      ----------                    --------
TPTP/SMT-LIB/DIMACS  --->  parsers (Phase 3)  --->  unified IR in arena
        |                         |                         |
        |                  symbol declarations             |
        |                         |                         |
        v                         v                         v
[kMaxInputBytes etc.]   builder validation + freeze   hot stores (terms,
                        (cold/symbol_table_builder)   clauses, SAT core)
                                                      |
                                                      v
                                              verifier (cold) re-checks
                                                      |
                                                      v
                                              proof output (Phase 3)
```

## Phase 1 boundaries

| # | Boundary | Crossing data | Validation at the boundary | Owner |
|---|---|---|---|---|
| 1 | Problem files -> parsers | Raw bytes | Size, depth, count bounds (`config/limits.rs`) | Phase 3 parsers (not yet present) |
| 2 | Declarations -> builder | Names, arities, weights, signatures | `BuilderError` set; per-declaration checks | `cold/symbol_table_builder.rs` |
| 3 | Builder -> frozen table | Entry and pool arrays | Full structural validation in `SymbolTable::freeze` | `hot/ir/symbol_table.rs` |
| 4 | Host -> arena | Backing region | Alignment and capacity validation in `Arena::new` | `hot/memory/arena.rs`, `cold/arena_host.rs` |
| 5 | Arena -> hot stores | Byte ranges | Bounds, alignment, and divisibility checks on every typed access | `hot/memory/arena.rs` |
| 6 | IR -> verifier | Term/clause records | Full re-derivation of cached invariants | `cold/verifier.rs` |
| 7 | Repository -> tooling | Config and manifest JSON | Schema validation, depth-bounded parse, regex validation | `tools/cep_lint` |

## Rules

1. Raw pointers never cross a boundary unvalidated: the only raw pointer entry is the arena region, validated in `Arena::new` before any hot code runs.
2. Lengths and counts are validated before any array access at every boundary crossing (CEP&CC 22.3).
3. The hot path trusts only the frozen table and the arena; both were validated at their own boundaries, which is why hot-path checks are bounds checks rather than structural revalidation.
4. Tooling (CEP-2) is repository-trusted and produces no artifacts consumed by the hot path except measurement evidence (JSON) and lint findings (text).

## FFI boundary (Phase 4 preview)

No FFI exists in Phase 1. The future boundary (design section 29) will require: `#[repr(C)]` types, entry validation of pointers, lengths, alignments, and enum ranges, no unwinding across the boundary, and documented ownership. See `ffi_security.md`.
