# CEP:FILE: scripts/bench_gate.py
# CEP:WHAT: Benchmark gate: reads the bench artifacts produced by the current run and enforces per-bench cycle thresholds so CEP-0 cost regressions fail CI (CEP&CC 13.4, 38.48); supports two tiers via --headroom-percent.
# CEP:WHY: CEP&CC Law 4 makes performance a correctness requirement; a gate script keeps the thresholds in one auditable place and deterministic (sorted input, fixed comparisons). Two tiers are required because absolute cycle counts are host-specific: the recording-host tier (default 25 percent) runs on the machine that recorded the baselines, while the shared-runner tier (CI, 400 percent) only bounds catastrophic regressions - GitHub fleet medians for throughput-bound micro-ops swing up to 2.3x across runner models (observed runs 37963490245 vs 37964196220), so a tight absolute gate on shared runners would flake, not detect.
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: Exits 1 when an artifact is missing, malformed, or exceeds its threshold; exits 2 on usage errors; exits 0 when all benches pass.
# CEP:ASSUMES: Artifacts live in benches/artifacts/*.json in the documented schema; thresholds are medians in cycles per operation; the fine-grained tier is the pre-push responsibility of the recording host.
# CEP:COST: offline tool; runtime cost irrelevant.
# CEP:EVIDENCE: CI job bench runs this script after cargo bench with --headroom-percent 400; local runs use the default.
# CEP:SECURITY: repository-trusted inputs only; no network; sorted traversal.

import glob
import json
import os
import sys

# CEP:WHAT: Allowed regression headroom over the recorded baseline, in percent.
# CEP:WHY: A named threshold documents how much variance the gate tolerates (CEP&CC 11.3).
CEP_GATE_HEADROOM_PERCENT = 25.0

# CEP:WHAT: Baseline medians (cycles per operation) recorded 2026-10-08 (Phase 1) and 2026-10-10 (Phase 2 additions) on x86-64 (Intel Xeon, virtualized), rustc 1.99.0, release.
# CEP:WHY: The gate compares fresh measurements against these numbers; update them only with a benchmark evidence note (CEP&CC 13.1).
# CEP:NOTE: sat_bcp_step was re-baselined 2026-10-10 from 44.53 to 54.90 cycles: Phase 2 conflict analysis requires per-assignment reason and level recording (SatCore::assign_with_reason adds two stores per propagation), an honest, measured cost of the implication-graph tracking (design 11.1 S18/S19).
CEP_BASELINES = {
    "arena_alloc_bytes": 9.99,
    "clause_new_3lit": 20.36,
    "sat_bcp_step": 54.90,
    "sat_literal_negate": 1.03,
    "substitution_apply_small": 174.53,
    "substitution_lookup": 1.96,
    "term_intern_binary_hit": 37.90,
    "term_symbol_lookup": 2.95,
    "unify_ground_identical": 14.40,
    "unify_bind_pair": 101.88,
    "unify_occurs_reject": 42.35,
    "match_witness_success": 118.27,
    "ordering_kbo_weight": 111.00,
    "ordering_kbo_lex": 238.18,
    "ordering_lpo": 22.22,
    "index_insert": 1496.32,
    "index_retrieve": 1632.91,
    "cdcl_analyze": 697.42,
    "cdcl_decide": 420.41,
    "cdcl_solve_per_conflict": 5372.33,
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


# CEP:WHAT: Entry point: gate every baseline against the artifacts at the given headroom tier.
# CEP:WHY: See file header.
# CEP:STATUS: complete
# CEP:FAILURE: exit 1 on any miss or regression, exit 2 on a usage error.
# CEP:ASSUMES: run from the repository root.
# CEP:COST: O(artifacts).
# CEP:EVIDENCE: CI bench job; local pre-push runs.
# CEP:SECURITY: none.
def main():
    headroom = CEP_GATE_HEADROOM_PERCENT
    args = sys.argv[1:]
    if len(args) == 2 and args[0] == "--headroom-percent":
        try:
            headroom = float(args[1])
        except ValueError:
            print("usage: bench_gate.py [--headroom-percent N]")
            return 2
        if headroom <= 0:
            print("headroom must be positive")
            return 2
    elif args:
        print("usage: bench_gate.py [--headroom-percent N]")
        return 2
    print("bench gate tier: +{:.0f}% headroom".format(headroom))
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
        limit = baseline * (1.0 + headroom / 100.0)
        measured = artifacts[name]
        if measured > limit:
            failures.append(
                "{}: {:.2f} cycles exceeds gate {:.2f} (baseline {:.2f} + {:.0f}%)".format(
                    name, measured, limit, baseline, headroom
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
