// CEP:FILE: cold/proof_output/drat_writer.rs
// CEP:WHAT: DRAT text writer (design 6.4, 11.1 S41): serializes the proof recorder's step buffer into plain DRAT text (DIMACS-convention integers, 0-terminated lines, "d " deletion prefix).
// CEP:WHY: Design 6.4 names cold/proof_output/drat_writer.rs as the SAT proof certificate writer; plain DRAT (Heule, Hunt & Wetzler 2013; Wetzler 2015) is the minimal independently checkable format - additions are clause lines whose justification (RUP or RAT) is verified by a checker, deletions are "d" lines that need no justification - so the writer only has to be a faithful, total rendering of the recorded steps; assumption hypothesis units and their removals render as ordinary unit add and delete lines because plain DRAT has no hypothesis syntax (the internal checker knows the step kinds; Spec 11 section 6 fixes the rendering); CAVEAT: a text trace containing AssumptionAdd steps is NOT a standalone external DRAT refutation - the hypothesis units are not RUP/RAT-justified by construction, so external tools must be fed assumption-free traces (plain solve refutations), while the internal checker consumes the full step stream with its hypothesis semantics.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns WriterError::Proof on recorder read failures (never fabricates a line); the output buffer is caller-owned and truncation is a loud error, never a silent short proof.
// CEP:ASSUMES: The recorder's step buffer is complete (the solve that produced it has returned); variable indices are below the declared variable count; the caller provides an output buffer of sufficient size (write_drat reports the required size on truncation).
// CEP:COST: O(total literals) time, one pass; no search, no propagation - the writer never validates justifications (that is the checker's job, by design).
// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{renders_adds_and_deletes, dimacs_numbering_is_one_based, assumption_units_render_as_units, truncation_reports_required_size}; tests/golden/drat_proof_test.rs.
// CEP:SECURITY: output is generated from validated recorder state; no untrusted input.
// CEP:HPC-DETERMINISM: deterministic; step order and literal order are the recorder's, the numbering is a pure function of variable indices.

use mapt_hot::sat::proof::{ProofRecorder, ProofStepKind};

/// CEP:WHAT: Byte length of the deletion prefix ("d ").
/// CEP:WHY: Named so the writer and the size pass cannot drift apart (CEP&CC 11.3).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{renders_adds_and_deletes, required_size_is_exact}.
/// CEP:SECURITY: none.
const kDeletionPrefixBytes: usize = 2;

/// CEP:WHAT: Byte length of the line terminator (" 0" plus newline).
/// CEP:WHY: Named so the writer and the size pass cannot drift apart (CEP&CC 11.3).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{renders_adds_and_deletes, required_size_is_exact}.
/// CEP:SECURITY: none.
const kLineTerminatorBytes: usize = 3;

/// CEP:WHAT: Byte length of one separating space.
/// CEP:WHY: Named so the writer and the size pass cannot drift apart (CEP&CC 11.3).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time constant.
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::required_size_is_exact.
/// CEP:SECURITY: none.
const kSeparatorBytes: usize = 1;

/// CEP:WHAT: Error cases of the DRAT writer.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; a truncated or unreadable proof must be loud, never silently shortened.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::truncation_reports_required_size.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriterError {
    /// CEP:WHAT: The output buffer is too small for the full proof text.
    /// CEP:WHY: Truncated DRAT text is an invalid certificate; the error carries the required size so the caller can retry exactly once with a right-sized buffer.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::truncation_reports_required_size.
    /// CEP:SECURITY: none.
    BufferTooSmall {
        /// CEP:WHAT: Required buffer size in bytes.
        /// CEP:WHY: Exact retry sizing.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 8 bytes.
        /// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::truncation_reports_required_size.
        /// CEP:SECURITY: none.
        required: usize,
    },
    /// CEP:WHAT: A step or literal read from the recorder failed.
    /// CEP:WHY: The writer refuses to fabricate content for unreadable steps (Law 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::renders_adds_and_deletes.
    /// CEP:SECURITY: none.
    UnreadableStep,
}

// CEP:WHAT: Renders one variable-polarity pair as a DIMACS-convention integer.
// CEP:WHY: DRAT text uses 1-based signed integers (variable + 1, negated for negative polarity); the mapping is fixed here in one place (Spec 11 section 6) so the writer and the checker's text-facing tests agree.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: variable indices fit i32 after the +1 shift (kMaxSatVariables is far below).
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::dimacs_numbering_is_one_based.
// CEP:SECURITY: none.
fn dimacs_literal(variable: u32, positive: bool) -> i32 {
    let magnitude = (variable + 1) as i32;
    if positive {
        magnitude
    } else {
        -magnitude
    }
}

// CEP:WHAT: Writes the decimal form of a signed integer into a buffer at a cursor; returns the new cursor, or None on truncation.
// CEP:WHY: std formatting is available in CEP-1, but a hand-rolled fixed-buffer writer keeps the whole render one pass with exact truncation detection (the required size must be reported truthfully).
// CEP:STATUS: complete
// CEP:FAILURE: returns None when the digits do not fit.
// CEP:ASSUMES: buffer length >= cursor.
// CEP:COST: O(digits).
// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{renders_adds_and_deletes, dimacs_numbering_is_one_based}.
// CEP:SECURITY: none.
fn push_int(buffer: &mut [u8], cursor: usize, value: i32) -> Option<usize> {
    let digits = value.unsigned_abs().to_string();
    let mut next = cursor;
    let negative = value < 0;
    let needed = digits.len() + usize::from(negative);
    if next + needed > buffer.len() {
        return None;
    }
    if negative {
        buffer[next] = b'-';
        next += 1;
    }
    for byte in digits.bytes() {
        buffer[next] = byte;
        next += 1;
    }
    Some(next)
}

// CEP:WHAT: Writes one ASCII byte at the cursor; returns the new cursor, or None on truncation.
// CEP:WHY: Shared truncation discipline for separators, prefixes, and newlines.
// CEP:STATUS: complete
// CEP:FAILURE: returns None when the byte does not fit.
// CEP:ASSUMES: buffer length >= cursor.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::renders_adds_and_deletes.
// CEP:SECURITY: none.
fn push_byte(buffer: &mut [u8], cursor: usize, byte: u8) -> Option<usize> {
    if cursor >= buffer.len() {
        return None;
    }
    buffer[cursor] = byte;
    Some(cursor + 1)
}

/// CEP:WHAT: Serializes the recorder's steps into plain DRAT text; returns the byte length written.
/// CEP:WHY: The certificate emission entry point (design 6.4); every step renders exactly once, in recording order, with deletions (clause and assumption) prefixed "d " and every line terminated "0\\n" (Spec 11 section 6).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: WriterError::BufferTooSmall carries the exact required size; WriterError::UnreadableStep for recorder failures; never writes a partial line on error return (the buffer cursor is only committed after a line completes).
/// CEP:ASSUMES: the recorder is quiescent; the caller reads the returned length, not NUL termination (no terminator is written).
/// CEP:COST: O(total literals).
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{renders_adds_and_deletes, dimacs_numbering_is_one_based, assumption_units_render_as_units, truncation_reports_required_size}; tests/golden/drat_proof_test.rs.
/// CEP:SECURITY: no untrusted input.
pub fn write_drat(recorder: &ProofRecorder<'_>, out: &mut [u8]) -> Result<usize, WriterError> {
    let required = drat_size(recorder)?;
    if out.len() < required {
        return Err(WriterError::BufferTooSmall { required });
    }
    let mut cursor: usize = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).ok_or(WriterError::UnreadableStep)?;
        let prefix = matches!(
            step.kind,
            ProofStepKind::Delete | ProofStepKind::AssumptionDelete
        );
        if prefix {
            cursor = push_byte(out, cursor, b'd').ok_or(WriterError::UnreadableStep)?;
            cursor = push_byte(out, cursor, b' ').ok_or(WriterError::UnreadableStep)?;
        }
        for slot in 0..step.literal_count {
            let literal = recorder
                .step_literal(step, slot)
                .ok_or(WriterError::UnreadableStep)?;
            if slot > 0 {
                cursor = push_byte(out, cursor, b' ').ok_or(WriterError::UnreadableStep)?;
            }
            let value = dimacs_literal(literal.variable().0, literal.is_positive());
            cursor = push_int(out, cursor, value).ok_or(WriterError::UnreadableStep)?;
        }
        cursor = push_byte(out, cursor, b' ').ok_or(WriterError::UnreadableStep)?;
        cursor = push_byte(out, cursor, b'0').ok_or(WriterError::UnreadableStep)?;
        cursor = push_byte(out, cursor, b'\n').ok_or(WriterError::UnreadableStep)?;
    }
    debug_assert_eq!(cursor, required);
    Ok(cursor)
}

/// CEP:WHAT: Returns the exact byte size the DRAT text of the recorder's steps needs.
/// CEP:WHY: Callers size their buffer once instead of probing with retries; the count is the same single pass as the writer.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: WriterError::UnreadableStep for recorder failures.
/// CEP:ASSUMES: the recorder is quiescent.
/// CEP:COST: O(total literals).
/// CEP:EVIDENCE: unit/cold/drat_writer_test.rs::{truncation_reports_required_size, required_size_is_exact}.
/// CEP:SECURITY: none.
pub fn drat_size(recorder: &ProofRecorder<'_>) -> Result<usize, WriterError> {
    let mut total: usize = 0;
    for index in 0..recorder.step_count() {
        let step = recorder.step(index).ok_or(WriterError::UnreadableStep)?;
        if matches!(
            step.kind,
            ProofStepKind::Delete | ProofStepKind::AssumptionDelete
        ) {
            total += kDeletionPrefixBytes;
        }
        for slot in 0..step.literal_count {
            let literal = recorder
                .step_literal(step, slot)
                .ok_or(WriterError::UnreadableStep)?;
            let value = dimacs_literal(literal.variable().0, literal.is_positive());
            total += value.to_string().len();
            if slot + 1 < step.literal_count {
                total += kSeparatorBytes;
            }
        }
        total += kLineTerminatorBytes;
    }
    Ok(total)
}
