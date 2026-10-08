# MAPT FFI Security

Version: 0.1
Status: Phase 1 contains no FFI. This document fixes the policy the future boundary must satisfy and tracks the plan.

## Current state

- No `extern` functions, no `#[repr(C)]` public types, no C/C++ compilation units exist in the repository.
- The C++26 code in `tools/cep_lint` is a standalone offline tool, not a linked boundary.
- Therefore no FFI attack surface exists in Phase 1. This is verified by the repository layout and by the absence of `ffi/` sources.

## Planned boundary (design sections 3, 26, 29; Phases 4-5)

The design assigns C++26 the role of FFI companion (external solvers, target intrinsics, legacy kernel validation). When that boundary is built, the following requirements are binding (CEP&CC 22.8, 25.8, 29):

1. Every FFI type has `#[repr(C)]` or `#[repr(transparent)]` with a layout test.
2. Every FFI function is `extern "C"`, never unwinds, and returns explicit error codes.
3. Every FFI input pointer is null-checked; every length is bounds-checked; every alignment is verified; every enum is range-checked before conversion.
4. Ownership (who allocates, who frees, lifetime, threading, reentrancy, signal-safety) is documented per function.
5. FFI lives in `ffi/` only; no business logic crosses the boundary (validate -> convert -> call -> convert -> return).
6. Every FFI boundary has layout tests and adversarial validation tests (`tests/unit/ffi/`).

## Change control

Adding any FFI file without a matching update to this document and to `trust_boundaries.md` is a Severity 1 violation (CEP&CC 22.8).
