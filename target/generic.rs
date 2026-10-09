// CEP:FILE: target/generic.rs
// CEP:WHAT: Generic fallback target: no hardware cycle counter, benches must use wall-clock and mark measurements accordingly.
// CEP:WHY: CEP&CC 32.5 requires a generic fallback in the target directory; fabricating cycle numbers without a counter would violate CEP&CC Law 4 (no unmeasured hot code), so the fallback reports inaccuracy honestly.
// CEP:CLASS: CEP-1
// CEP:TARGET: generic
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: used only on architectures without a dedicated module.
// CEP:COST: constant.
// CEP:EVIDENCE: benches/hot/harness.rs checks cycle_counter_is_accurate before recording cycle claims.
// CEP:SECURITY: none.
// CEP:PORTABILITY: any target without a dedicated counter module.

/// CEP:WHAT: Returns zero; no hardware counter exists on this target.
/// CEP:WHY: Keeps the API total; callers must consult cycle_counter_is_accurate before interpreting the value.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: bench harness gating.
/// CEP:SECURITY: none.
pub fn read_cycle_counter() -> u64 {
    0
}

/// CEP:WHAT: Reports that no accurate counter exists on this target.
/// CEP:WHY: Prevents fabricated cycle measurements (CEP&CC Law 4).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: constant.
/// CEP:EVIDENCE: bench harness gating.
/// CEP:SECURITY: none.
pub fn cycle_counter_is_accurate() -> bool {
    false
}
