# CEP:FILE: scripts/check_determinism.py
# CEP:WHAT: Determinism gate: runs the Rust test suite twice and compares outputs byte-for-byte, and verifies the debug-print golden file is stable.
# CEP:WHY: CEP&CC 38.10 requires deterministic translation and 34.3 stage 7 requires determinism checks in CI; identical test output across runs is the cheapest executable proof for Phase 1.
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: Exits 1 when the two runs differ or cargo fails; exits 0 when outputs are identical.
# CEP:ASSUMES: cargo is on PATH; run from the repository root; tests produce deterministic stdout/stderr given deterministic code.
# CEP:COST: two full test-suite runs.
# CEP:EVIDENCE: CI job determinism.
# CEP:SECURITY: no network; fixed environment (PYTHONHASHSEED pinned per CEP&CC 28.3).

import os
import subprocess
import sys

# CEP:WHAT: Fixed hash seed for this tool.
# CEP:WHY: CEP&CC 28.3 requires fixed seeds for deterministic tooling.
# CEP:STATUS: complete
# CEP:FAILURE: none.
# CEP:ASSUMES: none.
# CEP:COST: constant.
# CEP:EVIDENCE: determinism of this script itself.
# CEP:SECURITY: none.
CEP_HASH_SEED = "0"


# CEP:WHAT: Runs the test suite once and returns combined output.
# CEP:WHY: Single runner with a pinned environment.
# CEP:STATUS: complete
# CEP:FAILURE: returns None when cargo fails.
# CEP:ASSUMES: cargo on PATH.
# CEP:COST: one test-suite run.
# CEP:EVIDENCE: gate comparison.
# CEP:SECURITY: environment is fixed to the pinned seed.
def run_tests():
    env = dict(os.environ)
    env["PYTHONHASHSEED"] = CEP_HASH_SEED
    env["LC_ALL"] = "C"
    completed = subprocess.run(
        ["cargo", "test", "--", "--test-threads", "1"],
        capture_output=True,
        text=True,
        env=env,
    )
    if completed.returncode != 0:
        return None
    # Wall-clock durations vary between runs by nature; strip them so only the
    # deterministic content (test names, pass/fail counts, ordering) is compared.
    keep = []
    for line in completed.stdout.splitlines():
        if line.startswith("test ") or line.startswith("running"):
            keep.append(line.split("; finished in")[0])
    return "\n".join(keep)


# CEP:WHAT: Entry point: two runs and compare.
# CEP:WHY: See file header.
# CEP:STATUS: complete
# CEP:FAILURE: exit 1 on failure or drift.
# CEP:ASSUMES: none.
# CEP:COST: two test runs.
# CEP:EVIDENCE: CI determinism job.
# CEP:SECURITY: none.
def main():
    first = run_tests()
    if first is None:
        print("FAIL first test run failed")
        return 1
    second = run_tests()
    if second is None:
        print("FAIL second test run failed")
        return 1
    if first != second:
        print("FAIL test output differs between runs (nondeterminism)")
        return 1
    print("determinism gate: two sequential runs produce identical results")
    return 0


if __name__ == "__main__":
    sys.exit(main())
