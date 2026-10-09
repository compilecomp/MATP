# CEP:FILE: scripts/check_evidence.py
# CEP:WHAT: Evidence-chain gate: verifies every CEP:EVIDENCE pointer in first-party sources against real files and real test functions (exact file-and-name match).
# CEP:WHY: CEP&CC Law 4 forbids fabricated claims; CEP:EVIDENCE pointers that cite nonexistent files or tests make the evidence chain unverifiable, so the check is mechanized instead of trusted (CEP&CC 34.3 gate automation).
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: exits 1 with one line per broken pointer.
# CEP:ASSUMES: test functions are defined with "fn <name>(" in files under tests/; CEP:EVIDENCE appears on a single line; source-file pointers use repository-relative paths.
# CEP:COST: linear in source lines; <1 s on this repository.
# CEP:EVIDENCE: CI lint job; scripts/README.md.
# CEP:SECURITY: reads only repository files; no untrusted input.

"""MAPT evidence-chain checker.

Test pointers  <dir>/<path>.rs::<fn>  must resolve to a file under tests/
that defines exactly that test function (exact file+fn match, no global
name fallback). Source pointers like config/limits.rs or benches/hot/harness.rs
must reference a file that exists in the repository.

Exit 0 = every pointer resolves. Exit 1 = broken pointer list on stdout.
"""

import re
import sys
from pathlib import Path

# CEP:WHAT: Matches a Rust function definition line and captures its name.
FN_DEF = re.compile(r"^\s*(?:pub\s+)?fn\s+(\w+)\s*[\(<]", re.M)


# CEP:WHAT: Builds the test index: test-file path (relative to tests/) to defined function names.
def load_test_index(repo: Path):
    """Return {test-relative-posix-path: set(fn names)} for files under tests/."""
    index = {}
    for tf in sorted((repo / "tests").rglob("*.rs")):
        # key = path relative to tests/ (the form CEP:EVIDENCE pointers use)
        rel = tf.relative_to(repo / "tests").as_posix()
        index[rel] = set(FN_DEF.findall(tf.read_text()))
    return index


# CEP:WHAT: Entry point: scan first-party sources and report every broken pointer.
def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    tests = load_test_index(repo)
    # any file in the repo (for source-file pointers)
    repo_files = {p.relative_to(repo).as_posix() for p in repo.rglob("*")
                  if p.is_file() and ".git/" not in p.as_posix()
                  and not p.as_posix().startswith("build/")}

    test_fn_files = {fn: rel for rel, fns in tests.items() for fn in fns}
    test_paths = set(tests.keys())

    # CEP:WHAT: Matches one CEP:EVIDENCE payload; pointers look like path.rs or path.rs::fn.
    evidence_re = re.compile(r"CEP:EVIDENCE:\s*(.+)$")
    pointer_re = re.compile(r"([\w/]+\.rs)(?:::(\w+))?")

    broken = []
    checked = 0
    for group in ("hot", "cold", "config", "target", "src", "benches", "tools"):
        base = repo / group
        if not base.is_dir():
            continue
        for src in sorted(base.rglob("*.rs")):
            rel = src.relative_to(repo).as_posix()
            for lineno, line in enumerate(src.read_text().splitlines(), 1):
                m = evidence_re.search(line)
                if not m:
                    continue
                payload = m.group(1)
                for path, fn in pointer_re.findall(payload):
                    if fn:
                        # function-level pointer: exact file+fn match required
                        if path in tests:
                            if fn not in tests[path]:
                                broken.append((rel, lineno, f"{path}::{fn}",
                                               "fn not defined in cited file"))
                        elif path in repo_files:
                            real = test_fn_files.get(fn)
                            if real:
                                broken.append((rel, lineno, f"{path}::{fn}",
                                               f"fn lives in {real}, not {path}"))
                            else:
                                broken.append((rel, lineno, f"{path}::{fn}",
                                               "fn not defined in any test"))
                        else:
                            broken.append((rel, lineno, f"{path}::{fn}",
                                           "cited file not found"))
                    else:
                        # file-level pointer
                        if path in test_paths or path in repo_files:
                            pass
                        else:
                            broken.append((rel, lineno, path, "cited file not found"))
                    checked += 1

    print(f"evidence pointers checked: {checked}")
    if broken:
        print(f"BROKEN: {len(broken)}")
        for rel, lineno, what, why in broken:
            print(f"  {rel}:{lineno} -> {what} [{why}]")
        return 1
    print("evidence chain: all pointers resolve")
    return 0


if __name__ == "__main__":
    sys.exit(main())
