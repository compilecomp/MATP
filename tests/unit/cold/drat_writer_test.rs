// CEP:FILE: tests/unit/cold/drat_writer_test.rs
// CEP:WHAT: Unit tests for the DRAT text writer: add and delete rendering, DIMACS 1-based numbering, assumption units, the exact-size pre-check, and truncation reporting.
// CEP:WHY: Design 6.4 and Spec 11 section 6: the certificate text is the externally checkable artifact; the rendering (line order, prefixes, 0-termination, numbering) is pinned here against literal expected strings.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any rendering deviation.
// CEP:ASSUMES: fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/proof_output/drat_writer.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::make_arena;
use mapt::cold::proof_output::drat_writer::{drat_size, write_drat, WriterError};
use mapt::hot::sat::literal::{SatLiteral, SatVar};
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::sat::solver::{CdclSolver, SolverOptions};

// CEP:WHAT: Test variable count.
// CEP:WHY: Named fixture size (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kVariables: u32 = 6;

// CEP:WHAT: Builds a literal or fails.
// CEP:WHY: Readable clause construction.
// CEP:STATUS: complete
// CEP:FAILURE: panics on out-of-range variables.
// CEP:ASSUMES: variable below kVariables.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn lit(variable: u32, positive: bool) -> SatLiteral {
    SatLiteral::new(SatVar(variable), positive).expect("literal")
}

// CEP:WHAT: Builds a proof-recording solver.
// CEP:WHY: One constructor for this file.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one solver with recorder.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_solver() -> CdclSolver<'static> {
    let arena = make_arena(16_777_216);
    let mut options = SolverOptions::new(kVariables, RestartPolicy::Luby, false);
    options.record_proof = true;
    options.proof_step_capacity = 256;
    options.proof_map_capacity = 256;
    options.proof_literal_capacity = 1024;
    CdclSolver::new_advanced(arena, options).expect("solver")
}

// CEP:WHAT: Verifies axiom adds render as 0-terminated DIMACS lines.
// CEP:WHY: Spec 11 section 6.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any byte deviation.
// CEP:ASSUMES: two clauses with mixed polarities.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::{write_drat, dimacs_literal}.
// CEP:SECURITY: none.
#[test]
fn renders_adds_and_deletes() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("c1");
    let recorder = solver.proof().expect("recorder");
    let offset = solver.registry().entry(0).expect("entry").offset.get();
    use mapt::hot::sat::registry::RegistryError;
    (|| -> Result<(), RegistryError> {
        recorder
            .record_delete(offset, solver.core().clauses())
            .map_err(RegistryError::from)?;
        solver.registry().delete(solver.core().clauses(), offset)?;
        Ok(())
    })()
    .expect("delete");
    let mut buffer = [0u8; 256];
    let written = write_drat(recorder, &mut buffer).expect("write");
    let text = core::str::from_utf8(&buffer[..written]).expect("utf8");
    assert_eq!(text, "1 -2 0\nd 1 -2 0\n");
}

// CEP:WHAT: Verifies the DIMACS numbering is 1-based with sign-for-polarity.
// CEP:WHY: Spec 11 section 6: variable v renders as v+1.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on 0-based output.
// CEP:ASSUMES: variables 0 and 2.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::dimacs_literal.
// CEP:SECURITY: none.
#[test]
fn dimacs_numbering_is_one_based() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, false), lit(2, true)])
        .expect("c1");
    let recorder = solver.proof().expect("recorder");
    let mut buffer = [0u8; 128];
    let written = write_drat(recorder, &mut buffer).expect("write");
    let text = core::str::from_utf8(&buffer[..written]).expect("utf8");
    assert_eq!(text, "-1 3 0\n");
}

// CEP:WHAT: Verifies assumption units render as plain unit lines.
// CEP:WHY: Plain DRAT has no hypothesis syntax; the unit appears and later disappears via a delete line.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on special syntax.
// CEP:ASSUMES: one assumption solve with a following flush solve.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::{write_drat, push_int}.
// CEP:SECURITY: none.
#[test]
fn assumption_units_render_as_units() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, true)])
        .expect("c1");
    let _ = solver.solve_with_assumptions(&[lit(0, true)]);
    let _ = solver.solve_with_assumptions(&[]);
    let recorder = solver.proof().expect("recorder");
    let mut buffer = [0u8; 512];
    let written = write_drat(recorder, &mut buffer).expect("write");
    let text = core::str::from_utf8(&buffer[..written]).expect("utf8");
    assert!(
        text.contains("1 0\n"),
        "the assumption unit must render as a unit line: {}",
        text
    );
    assert!(
        text.contains("d 1 0\n"),
        "the deferred cleanup must render the deletion: {}",
        text
    );
}

// CEP:WHAT: Verifies drat_size reports the exact byte count.
// CEP:WHY: Callers size buffers from it; an off-by-one would truncate.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on a size mismatch.
// CEP:ASSUMES: two clauses.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::drat_size.
// CEP:SECURITY: none.
#[test]
fn required_size_is_exact() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, false)])
        .expect("c1");
    solver.add_clause(&[lit(2, true)]).expect("c2");
    let recorder = solver.proof().expect("recorder");
    let required = drat_size(recorder).expect("size");
    let mut buffer = vec![0u8; required];
    let written = write_drat(recorder, &mut buffer).expect("write");
    assert_eq!(written, required);
}

// CEP:WHAT: Verifies truncation is a loud error carrying the required size.
// CEP:WHY: A truncated certificate is invalid; the caller must be told the exact size.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the error is missing or the size is wrong.
// CEP:ASSUMES: a buffer one byte short.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/proof_output/drat_writer.rs::{write_drat, WriterError::BufferTooSmall}.
// CEP:SECURITY: none.
#[test]
fn truncation_reports_required_size() {
    let solver = make_solver();
    solver
        .add_clause(&[lit(0, true), lit(1, false), lit(2, true)])
        .expect("c1");
    let recorder = solver.proof().expect("recorder");
    let required = drat_size(recorder).expect("size");
    let mut short = vec![0u8; required - 1];
    let result = write_drat(recorder, &mut short);
    assert!(
        matches!(result, Err(WriterError::BufferTooSmall { required: size }) if size == required)
    );
}
