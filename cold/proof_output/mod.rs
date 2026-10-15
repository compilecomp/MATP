// CEP:FILE: cold/proof_output/mod.rs
// CEP:WHAT: Proof output module (design 6.4): the DRAT text writer and the internal DRAT checker that consume the hot proof recorder's step buffer.
// CEP:WHY: Design 6.4 places proof serialization in cold/proof_output/ (CEP-1: allocation and string building are legal here and banned in hot); design 18 and 11.1 S41-S43 split proof production into recording (hot, allocation-free) and emission/verification (cold, post-solve); this module is that cold half.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: the recorder is not being written to while its steps are read.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/cold/drat_writer_test.rs; unit/cold/drat_checker_test.rs; tests/golden/drat_proof_test.rs.
// CEP:SECURITY: proof text is generated from validated recorder state only.

pub mod drat_checker;
pub mod drat_writer;
pub mod tstp;
