// CEP:FILE: hot/result.rs
// CEP:WHAT: Prover result codes (design 2.2): Theorem, CounterSatisfiable, Saturated, Timeout, MemoryExhausted, InferenceLimit, GaveUp, Error.
// CEP:WHY: Design 2.2 defines the closed result vocabulary and requires that every result except Theorem and CounterSatisfiable is a valid answer; a shared enum prevents per-component ad-hoc status types from leaking into the API and FFI.
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: none; a vocabulary type.
// CEP:ASSUMES: values are part of the future FFI contract (u8 representation).
// CEP:COST: 1-byte copy type.
// CEP:EVIDENCE: unit/config/limits_test.rs::result_codes_unique.
// CEP:SECURITY: Error must never be silently coerced to Theorem; the closed enum makes that unrepresentable.

/// CEP:WHAT: Prover result code (design 2.2 result table).
/// CEP:WHY: See file header.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; closed vocabulary.
/// CEP:ASSUMES: representation values are stable across versions.
/// CEP:COST: 1 byte.
/// CEP:EVIDENCE: unit/config/limits_test.rs::result_codes_unique.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ProverResult {
    /// CEP:WHAT: Conjecture entailed; proof produced.
    Theorem = 0,
    /// CEP:WHAT: Negation satisfiable; model produced.
    CounterSatisfiable = 1,
    /// CEP:WHAT: Clause set saturated without deriving the empty clause.
    Saturated = 2,
    /// CEP:WHAT: Time budget exhausted.
    Timeout = 3,
    /// CEP:WHAT: Clause database budget exhausted.
    MemoryExhausted = 4,
    /// CEP:WHAT: Inference count budget exhausted.
    InferenceLimit = 5,
    /// CEP:WHAT: Preprocessing or search aborted with a documented reason.
    GaveUp = 6,
    /// CEP:WHAT: Input malformed or internal fault.
    Error = 7,
}
