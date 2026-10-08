// CEP:FILE: config/security_policy.rs
// CEP:WHAT: Security policy constants and the trust-level vocabulary for MAPT components.
// CEP:WHY: CEP&CC 22 requires an explicit security policy; codifying trust levels and policy facts as named constants makes the policy mechanically referenceable by code comments and CI checks.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: none; constants only.
// CEP:ASSUMES: The threat model in security/threat_model.md is the authoritative narrative; this module is its machine-readable summary.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: security/threat_model.md, security/trust_boundaries.md.
// CEP:SECURITY: this module IS security policy; changing it requires security review.

/// CEP:WHAT: Trust level vocabulary for MAPT data flows (CEP&CC 22.14 CEP:TRUST values).
/// CEP:WHY: Trust decisions must use one shared vocabulary instead of ad-hoc strings.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a type definition.
/// CEP:ASSUMES: Exactly three levels; extensions require a threat-model update.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/trust_boundaries.md.
/// CEP:SECURITY: vocabulary for all CEP:TRUST annotations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustLevel {
    /// CEP:WHAT: Repository-controlled data that has passed review.
    Trusted,
    /// CEP:WHAT: External data that has passed validation code.
    Validated,
    /// CEP:WHAT: External data that has not been validated yet.
    Untrusted,
}

/// CEP:WHAT: True when secret material exists anywhere in MAPT.
/// CEP:WHY: CEP&CC 22.9 requires an explicit secrets policy; MAPT processes no secrets, and this constant makes that claim reviewable and testable (a secret scan finding anything contradicts it).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a policy fact.
/// CEP:ASSUMES: MAPT input files, logs, and dumps contain no credentials by design.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/threat_model.md section "Assets and secrets".
/// CEP:SECURITY: baseline for secret-leakage review.
pub const kProcessesSecrets: bool = false;

/// CEP:WHAT: True when MAPT code paths are expected to be constant-time.
/// CEP:WHY: CEP&CC 22.9 requires a side-channel policy; MAPT performs no cryptography, so non-constant-time execution is accepted and documented.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a policy fact.
/// CEP:ASSUMES: No secret-dependent branching exists because no secrets exist (kProcessesSecrets is false).
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/threat_model.md section "Side channels".
/// CEP:SECURITY: documents the accepted non-constant-time behavior.
pub const kConstantTimeRequired: bool = false;

/// CEP:WHAT: Maximum distinct symbols accepted from one untrusted input before parsing is refused (defense in depth on top of kMaxSymbolCount).
/// CEP:WHY: Symbol flooding is the cheapest parser denial-of-service vector; a tighter input-side bound than the global table capacity limits single-problem damage.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing refuses the input with ParseError::TooLarge (Phase 3 parser).
/// CEP:ASSUMES: At most kMaxSymbolCount; enforced by static assertion in limits.rs invariants.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/symbol_bounds_test.rs.
/// CEP:SECURITY: denial-of-service mitigation for untrusted TPTP/SMT-LIB input.
pub const kMaxInputSymbolCount: u32 = 16_384;

/// CEP:WHAT: Maximum name length in bytes accepted for one symbol from untrusted input.
/// CEP:WHY: Long symbol names multiply name-table memory; bounding them is a cheap denial-of-service mitigation.
/// CEP:STATUS: complete
/// CEP:FAILURE: Parsing refuses the symbol with ParseError::NameTooLong (Phase 3 parser).
/// CEP:ASSUMES: TPTP lower-word symbols are far shorter than this bound.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: security/symbol_bounds_test.rs.
/// CEP:SECURITY: denial-of-service mitigation.
pub const kMaxSymbolNameBytes: u32 = 512;
