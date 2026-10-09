# MAPT scripts

CEP-2 tooling for the MAPT gates. Each script is a CI gate; all are deterministic.

| Script | Gate | Purpose |
|---|---|---|
| `bench_gate.py` | bench (13.4) | Compares fresh benchmark medians against the committed cycle evidence in `benches/artifacts/*.json`; fails when a median exceeds the recorded artifact by more than the documented tolerance. |
| `check_determinism.py` | determinism | Runs the test suite twice and requires byte-identical output (28.3). |
| `check_evidence.py` | lint | Verifies every `CEP:EVIDENCE` pointer in `hot/`, `cold/`, `config/`, `target/`, `src/`, `benches/`, and `tools/` against real files and real test functions (exact file-and-name match, no global-name fallback); enforces Law 4 mechanically. |
| `extract_disasm.py` | bench (23.4) | Extracts the hot functions from compiler-emitted assembly into `benches/artifacts/disasm_*.txt` evidence files; selects files deterministically by path. |

All scripts run from the repository root and exit nonzero on failure.
