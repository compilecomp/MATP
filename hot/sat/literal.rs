// CEP:FILE: hot/sat/literal.rs
// CEP:WHAT: SAT Boolean variables and literals: dense u32 variable IDs and single-u32 packed literals (variable index shifted left by one, sign bit in bit 0).
// CEP:WHY: Design 11.1 S1/S2: dense 0-indexed variables and packed literals make every literal operation (negate, variable extraction, polarity test, watch-list indexing) one or two ALU ops, which the watch-list machinery (S6) and BCP (S9) execute millions of times per second.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: SatLiteral::new returns SatLiteralError::VariableOutOfRange when the variable exceeds kMaxSatVariables; accessors are total and infallible. Never panics.
// CEP:ASSUMES: Variable indices fit u32 with one bit to spare (enforced by the kMaxSatVariables static assertion in config/limits.rs); encoding 0 is the positive literal of variable 0, so there is no spare encoding.
// CEP:COST: construction is 1 compare + 1 shift + 1 or; negation is 1 xor; variable extraction is 1 shift; negation measured at 1.03 cycles median on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0005, artifact benches/artifacts/sat_literal_negate.json.
// CEP:EVIDENCE: unit/hot/sat_literal_test.rs; security/literal_encoding_test.rs; bench CEP-BENCH-0005.
// CEP:SECURITY: variable range is validated at construction; malformed encodings cannot enter the system through the public API.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; pure bit arithmetic on values.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: each operation maps to one or two machine instructions (compare+shift+or for construction, xor for negation, shift for extraction); the bench-main disassembly (artifact disasm_sat.txt) confirms no calls and no spills; measured 1.03 cycles median for negation; no cheaper encoding of (variable, polarity) in 32 bits exists.

use mapt_config::limits::kMaxSatVariables;

/// CEP:WHAT: SAT Boolean variable identifier (dense, 0-indexed).
/// CEP:WHY: Design 11.1 S1; a newtype prevents confusing SAT variables with term variables and symbol IDs.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; transparent u32 token.
/// CEP:ASSUMES: values below kMaxSatVariables.
/// CEP:COST: 4-byte copy type.
/// CEP:EVIDENCE: unit/hot/sat_literal_test.rs.
/// CEP:SECURITY: bounds validated at literal construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct SatVar(pub u32);

/// CEP:WHAT: Packed SAT literal: (variable << 1) | sign, sign 1 = negated.
/// CEP:WHY: Design 11.1 S2: one u32 carries variable and polarity so watch lists index by a single integer and negation is a XOR.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: construction validates the variable bound.
/// CEP:ASSUMES: encoding is (var << 1) | sign with sign=1 meaning negated.
/// CEP:COST: 4-byte copy type; all operations single instructions.
/// CEP:EVIDENCE: unit/hot/sat_literal_test.rs::encoding_roundtrip.
/// CEP:SECURITY: unforgeable valid literals outside construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct SatLiteral(u32);

/// CEP:WHAT: Sign bit position in the literal encoding.
/// CEP:WHY: The only magic number in the encoding, named once (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bit 0.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_literal_test.rs.
/// CEP:SECURITY: none.
pub const kSatLiteralSignBit: u32 = 1;

/// CEP:WHAT: Error cases of literal construction.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_literal_test.rs::out_of_range_variable_rejected.
/// CEP:SECURITY: the variable bound is the memory-safety boundary for watch-head indexing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatLiteralError {
    /// CEP:WHAT: The variable index is at or above kMaxSatVariables.
    VariableOutOfRange,
}

impl SatLiteral {
    // CEP:WHAT: Constructs a literal from a variable and polarity.
    // CEP:WHY: The single sanctioned constructor; validates the variable bound so watch-head indexing can never go out of range.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns VariableOutOfRange when variable >= kMaxSatVariables.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare + 1 shift + 1 or.
    // CEP:EVIDENCE: unit/hot/sat_literal_test.rs::{out_of_range_variable_rejected, encoding_roundtrip}.
    // CEP:SECURITY: bounds check retained in release (CEP&CC 23.7).
    pub fn new(variable: SatVar, positive: bool) -> Result<SatLiteral, SatLiteralError> {
        if variable.0 >= kMaxSatVariables {
            return Err(SatLiteralError::VariableOutOfRange);
        }
        let sign = if positive { 0 } else { kSatLiteralSignBit };
        Ok(SatLiteral((variable.0 << 1) | sign))
    }

    // CEP:WHAT: Returns the negated literal.
    // CEP:WHY: Complement literals share the watch-head slot pair; negation is the hottest literal operation in BCP.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 xor.
    // CEP:EVIDENCE: unit/hot/sat_literal_test.rs::negate_roundtrip.
    // CEP:SECURITY: none.
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: single XOR on the packed encoding; no cheaper negation exists.
    pub fn negate(&self) -> SatLiteral {
        SatLiteral(self.0 ^ kSatLiteralSignBit)
    }

    // CEP:WHAT: Returns the variable of the literal.
    // CEP:WHY: Assignment lookup and watch-head indexing by variable.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 shift.
    // CEP:EVIDENCE: unit/hot/sat_literal_test.rs::encoding_roundtrip.
    // CEP:SECURITY: none.
    pub fn variable(&self) -> SatVar {
        SatVar(self.0 >> 1)
    }

    // CEP:WHAT: Returns true when the literal is positive.
    // CEP:WHY: Polarity tests in value evaluation.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 test.
    // CEP:EVIDENCE: unit/hot/sat_literal_test.rs::encoding_roundtrip.
    // CEP:SECURITY: none.
    pub fn is_positive(&self) -> bool {
        self.0 & kSatLiteralSignBit == 0
    }

    // CEP:WHAT: Returns the raw encoding (watch-head index).
    // CEP:WHY: Watch lists are indexed by the packed encoding; the projection keeps the field private.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_watch_test.rs.
    // CEP:SECURITY: read-only projection.
    pub fn encoding(&self) -> u32 {
        self.0
    }

    // CEP:WHAT: Rebuilds a literal from a stored encoding (clause storage read path).
    // CEP:WHY: Clause literals are stored as packed encodings; the crate-internal constructor is safe because every stored encoding came from SatLiteral::new.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (crate-internal; stored encodings are validated at clause creation).
    // CEP:ASSUMES: the encoding was produced by SatLiteral::new and stored verbatim.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs.
    // CEP:SECURITY: crate-internal only.
    pub(crate) fn from_encoding(encoding: u32) -> SatLiteral {
        SatLiteral(encoding)
    }
}
