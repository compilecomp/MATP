// CEP:FILE: tests/golden/drat_proof_test.rs
// CEP:WHAT: Golden test for the DRAT certificate text: a fixed PHP(3,2) refutation's rendered proof is byte-identical to the recorded golden file.
// CEP:WHY: Design 6.4 and Spec 11 section 6: the certificate text is an external interface; a golden file pins the numbering, line order, prefixes, and termination so rendering drift is a caught regression.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any byte deviation.
// CEP:ASSUMES: the PHP(3,2) instance and the solver's deterministic search fix the proof exactly.
// CEP:COST: one solve plus one render.
// CEP:EVIDENCE: this file is the evidence cited by cold/proof_output/drat_writer.rs and hot/sat/proof.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::cold::proof_output::drat_writer::{drat_size, write_drat};
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};

// CEP:WHAT: Variables in the PHP(3,2) encoding.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 6;

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Verifies the rendered PHP(3,2) refutation certificate matches the golden file byte for byte.
// CEP:WHY: Golden pinning of the certificate interface.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any byte deviation (regenerate the golden only with a documented rendering change).
// CEP:ASSUMES: the solver's determinism (verified by the fuzz suite) fixes the trace.
// CEP:COST: one solve plus one render.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::{write_drat, drat_size}; the golden file tests/golden/golden/drat_php32.txt.
// CEP:SECURITY: none.
#[test]
fn drat_proof_text_is_stable() {
    let arena = make_arena(16_777_216);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.record_proof = true;
    options.proof_step_capacity = 8192;
    options.proof_map_capacity = 8192;
    options.proof_literal_capacity = 65536;
    let solver = CdclSolver::new_advanced(arena, options).expect("solver");
    // PHP(3,2).
    for pigeon in 0..3u32 {
        solver
            .add_clause(&[lit(pigeon * 2, true), lit(pigeon * 2 + 1, true)])
            .expect("pigeon");
    }
    for hole in 0..2u32 {
        for first in 0..3u32 {
            for second in (first + 1)..3u32 {
                solver
                    .add_clause(&[lit(first * 2 + hole, false), lit(second * 2 + hole, false)])
                    .expect("hole");
            }
        }
    }
    let outcome = solver.solve();
    assert!(matches!(
        outcome,
        mapt::hot::sat::solver::SolveResult::Unsatisfiable
    ));
    let recorder = solver.proof().expect("recorder");
    let required = drat_size(recorder).expect("size");
    let mut buffer = vec![0u8; required];
    let written = write_drat(recorder, &mut buffer).expect("write");
    let rendered = String::from_utf8(buffer[..written].to_vec()).expect("utf8");
    // The golden is a COMMITTED artifact: a missing file fails the test loudly
    // instead of being rewritten from the current rendering (a self-written
    // golden would be self-fulfilling - it could never catch a rendering
    // change); regenerate it only deliberately, with a documented change.
    let golden_path = "tests/golden/golden/drat_php32.txt";
    let golden = std::fs::read_to_string(golden_path)
        .expect("the committed golden file must exist (never regenerated in-test)");
    assert_eq!(
        rendered, golden,
        "the certificate text must match the golden file"
    );
}
