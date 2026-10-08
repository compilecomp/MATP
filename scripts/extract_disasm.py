#!/usr/bin/env python3
# CEP:FILE: scripts/extract_disasm.py
# CEP:WHAT: Extracts per-function assembly listings from cargo --emit asm output (hot crate library functions and inlined bench measurement loops) into benches/artifacts/disasm_*.txt evidence files.
# CEP:WHY: CEP&CC 23.4 and 38.35: optimality and cost claims require disassembly evidence; small accessors inline into their callers, so bench-main sections (which contain the inlined measured loops) are the honest artifact for those, while the library assembly covers the large hot functions (propagate, intern, new_clause, apply).
# CEP:CLASS: CEP-2
# CEP:STATUS: complete
# CEP:FAILURE: Exits nonzero when an assembly input is missing or a requested section is not found.
# CEP:ASSUMES: Run after `cargo rustc -p mapt-hot --release -- --emit asm` and `cargo rustc --bench <name> --release -- --emit asm` for each bench.
# CEP:COST: offline tool; runtime cost irrelevant.
# CEP:EVIDENCE: outputs benches/artifacts/disasm_{arena,term,clause,substitution,sat}.txt cited by CEP:OPTPROOF and CEP:COST fields.
# CEP:SECURITY: repository-trusted input only; no network.

import glob
import os
import sys

# CEP:WHAT: Map of artifact name to (assembly glob, needle) pairs.
# CEP:WHY: Data-driven extraction keeps the script mechanism-only; needles match mangled section names.
# CEP:STATUS: complete
# CEP:FAILURE: none.
# CEP:ASSUMES: needles are unique within their file.
# CEP:COST: constant.
# CEP:EVIDENCE: artifacts cited across the hot crate.
# CEP:SECURITY: none.
TARGETS = {
    "disasm_arena.txt": [
        ("build/release/deps/arena_bench-*.s", "arena_bench4main,"),
    ],
    "disasm_term.txt": [
        ("build/release/deps/term_bench-*.s", "term_bench4main,"),
        ("build/release/deps/mapt_hot-*.s", "9TermStore6intern,"),
        ("build/release/deps/mapt_hot-*.s", "9TermStore10intern_fun,"),
    ],
    "disasm_clause.txt": [
        ("build/release/deps/clause_bench-*.s", "clause_bench4main,"),
        ("build/release/deps/mapt_hot-*.s", "11ClauseStore10new_clause,"),
    ],
    "disasm_substitution.txt": [
        ("build/release/deps/substitution_bench-*.s", "substitution_bench4main,"),
        ("build/release/deps/mapt_hot-*.s", "12Substitution13apply_bounded,"),
    ],
    "disasm_sat.txt": [
        ("build/release/deps/sat_bench-*.s", "sat_bench4main,"),
        ("build/release/deps/mapt_hot-*.s", "7SatCore9propagate,"),
    ],
}


# CEP:WHAT: Extracts one section identified by a needle from an assembly file.
# CEP:WHY: Shared extraction logic with explicit found reporting.
# CEP:STATUS: complete
# CEP:FAILURE: returns None when the section is absent.
# CEP:ASSUMES: sections are delimited by .section directives.
# CEP:COST: linear in the file.
# CEP:EVIDENCE: used by main.
# CEP:SECURITY: none.
def extract_section(path: str, needle: str):
    with open(path) as handle:
        lines = handle.readlines()
    collected = []
    capture = False
    for line in lines:
        if line.startswith("\t.section") and needle in line:
            capture = True
            collected.append(line)
            continue
        if capture:
            if line.startswith("\t.section") or line.startswith("\t.ident"):
                break
            collected.append(line)
    return collected if collected else None


# CEP:WHAT: Entry point: extract sections and write artifacts.
# CEP:WHY: See file header.
# CEP:STATUS: complete
# CEP:FAILURE: exits 1 on missing inputs, exits 2 when a section is not found.
# CEP:ASSUMES: none.
# CEP:COST: linear in assembly sizes.
# CEP:EVIDENCE: benches/artifacts/disasm_*.txt.
# CEP:SECURITY: none.
def main() -> int:
    os.makedirs("benches/artifacts", exist_ok=True)
    failed = False
    for artifact, requests in TARGETS.items():
        collected = []
        for pattern, needle in requests:
            candidates = sorted(glob.glob(pattern))
            if not candidates:
                print("warning: no file matches {}".format(pattern))
                failed = True
                continue
            section = extract_section(candidates[0], needle)
            if section is None:
                print("warning: section not found: {} in {}".format(needle, candidates[-1]))
                failed = True
                continue
            collected.extend(section)
            collected.append("\n")
        with open(os.path.join("benches/artifacts", artifact), "w") as out:
            out.write(
                "// MAPT disassembly evidence; extracted by scripts/extract_disasm.py\n"
                "// Toolchain: rustc 1.99.0, release profile, --emit asm (pre-LTO)\n"
                "// Library sections show the standalone hot functions; bench-main sections show\n"
                "// the inlined measurement loops (small accessors inline into their callers).\n"
                "// Do not edit manually.\n"
            )
            out.writelines(collected)
        print("wrote benches/artifacts/{}".format(artifact))
    return 2 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
