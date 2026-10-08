# CEP:FILE: scripts/bench_gate.py
# CEP:WHAT: Benchmark gate: reads the committed bench artifacts and enforces per-bench cycle thresholds so CEP-0 cost regressions fail CI (CEP&CC 13.4, 38.48).
# CEP:WHY: CEP&CC Law 4 makes performance a correctness requirement; a gate script keeps the thresholds in one auditable place and deterministic (sorted input, fixed comparisons).
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: Exits 1 when an artifact is missing, malformed, or exceeds its threshold; exits 0 when all benches pass.
# CEP:ASSUMES: Artifacts live in benches/artifacts/*.json in the documented schema; thresholds are medians in cycles per operation.
# CEP:COST: offline tool; runtime cost irrelevant.
# CEP:EVIDENCE: CI job bench-gate runs this script after cargo bench.
# CEP:SECURITY: repository-trusted inputs only; no network; sorted traversal.

import glob
import json
import os
import sys

# CEP:WHAT: Allowed regression headroom over the recorded baseline, in percent.
# CEP:WHY: A named threshold documents how much variance the gate tolerates (CEP&CC 11.3).
CEP_GATE_HEADROOM_PERCENT = 25.0

# CEP:WHAT: Baseline medians (cycles per operation) recorded 2026-10-08 on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release.
# CEP:WHY: The gate compares fresh measurements against these numbers; update them only with a benchmark evidence note (CEP&CC 13.1).
CEP_BASELINES = {
    "arena_alloc_bytes": 9.99,
    "clause_new_3lit": 20.36,
    "sat_bcp_step": 44.53,
    "sat_literal_negate": 1.03,
    "substitution_apply_small": 174.53,
    "substitution_lookup": 1.96,
    "term_intern_binary_hit": 37.90,
    "term_symbol_lookup": 2.95,
}


# CEP:WHAT: Loads one artifact and returns its name and median.
# CEP:WHY: Single parse point with schema validation.
# CEP:STATUS: complete
# CEP:FAILURE: returns None on missing keys or bad numbers.
# CEP:ASSUMES: the documented schema.
# CEP:COST: constant.
# CEP:EVIDENCE: gate checks.
# CEP:SECURITY: none.
def load_artifact(path):
    with open(path) as handle:
        data = json.load(handle)
    if "name" not in data or "cycles_median" not in data:
        return None
    return data["name"], float(data["cycles_median"])


# CEP:WHAT: Entry point: gate every baseline against the artifacts.
# CEP:WHY: See file header.
# CEP:STATUS: complete
# CEP:FAILURE: exit 1 on any miss or regression.
# CEP:ASSUMES: run from the repository root.
# CEP:COST: O(artifacts).
# CEP:EVIDENCE: CI bench-gate job.
# CEP:SECURITY: none.
def main():
    artifacts = {}
    for path in sorted(glob.glob(os.path.join("benches", "artifacts", "*.json"))):
        loaded = load_artifact(path)
        if loaded is not None:
            artifacts[loaded[0]] = loaded[1]
    failures = []
    for name, baseline in sorted(CEP_BASELINES.items()):
        if name not in artifacts:
            failures.append("missing artifact for {}".format(name))
            continue
        limit = baseline * (1.0 + CEP_GATE_HEADROOM_PERCENT / 100.0)
        measured = artifacts[name]
        if measured > limit:
            failures.append(
                "{}: {:.2f} cycles exceeds gate {:.2f} (baseline {:.2f} + {}%)".format(
                    name, measured, limit, baseline, CEP_GATE_HEADROOM_PERCENT
                )
            )
        else:
            print("PASS {} {:.2f} <= {:.2f}".format(name, measured, limit))
    if failures:
        for failure in failures:
            print("FAIL {}".format(failure))
        return 1
    print("bench gate: all benches within thresholds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
