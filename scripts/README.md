# MAPT scripts

CEP-2 tooling for the MAPT gates. Each script is a CI gate; all are deterministic.

| Script | Gate | Purpose |
|---|---|---|
| `bench_gate.py` | bench (13.4) | Two-tier benchmark gate. Recording-host tier (default): fresh medians must stay within +25% of the baseline medians recorded on the machine that produced `benches/artifacts/*.json` — run this locally before pushing. Shared-runner tier (`--headroom-percent 400`, used in CI): GitHub fleet medians for throughput-bound micro-ops swing up to 2.3x across runner CPU models, so CI enforces a catastrophic bound of 5x the baseline instead; a dedicated-host or per-op-normalized tier is tracked as ticket CEP-1019. |
| `check_determinism.py` | determinism | Runs the test suite twice and requires byte-identical output (28.3). |
| `check_evidence.py` | lint | Verifies every `CEP:EVIDENCE` pointer in `hot/`, `cold/`, `config/`, `target/`, `src/`, `benches/`, and `tools/` against real files and real test functions (exact file-and-name match, no global-name fallback); enforces Law 4 mechanically. |
| `extract_disasm.py` | bench (23.4) | Extracts the hot functions from compiler-emitted assembly into `benches/artifacts/disasm_*.txt` evidence files; selects files deterministically by path. |

All scripts run from the repository root and exit nonzero on failure.
