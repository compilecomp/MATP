# Benchmarks

- `hot/` — the five Phase 1 benches (arena, term, clause, substitution, SAT) using the shared harness (`harness.rs`): serialized-rdtsc cycle counter, median of 15 repeats, black-boxed sinks.
- `artifacts/` — committed evidence: per-bench JSON (cycles median/min, iterations, toolchain, target, date) and disassembly extracts (`disasm_*.txt`) cited by CEP:COST and CEP:OPTPROOF fields.
- Gates: `scripts/bench_gate.py` enforces regression thresholds; `scripts/extract_disasm.py` refreshes disassembly evidence.
