// CEP:FILE: tests/unit/config/limits_test.rs
// CEP:WHAT: Unit tests for configuration limits: runtime re-validation of every static invariant and result-code uniqueness.
// CEP:WHY: CEP&CC Law 3: invariants enforced at compile time are re-proven at runtime for defense in depth; this file is the executable form of the limits contract.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: config values match the static assertions.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by config/limits.rs.
// CEP:SECURITY: none.

use mapt::config::limits::*;
use mapt::hot::result::ProverResult;

// CEP:WHAT: Opaque constant reader.
// CEP:WHY: black_box keeps the limit re-validation assertions from being constant-folded,
// preserving their role as runtime defense in depth (clippy::assertions_on_constants).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by limit_invariants.
// CEP:SECURITY: none.
fn opaque<T>(value: T) -> T {
    std::hint::black_box(value)
}

// CEP:WHAT: Re-validates the cross-constant invariants at runtime.
// CEP:WHY: Defense in depth for the compile-time assertions.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any violation.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/limits.rs static block.
// CEP:SECURITY: none.
#[test]
fn limit_invariants() {
    assert!(opaque(kArenaCapacityBytes) < opaque(kInvalidClauseOffset));
    assert!(opaque(kArenaCapacityBytes) < opaque(kInvalidTermOffset));
    assert!(opaque(kArenaCapacityBytes) < opaque(kInvalidSubstitutionOffset));
    assert!(opaque(kMaxSymbolCount) < opaque(kInvalidSymbolId));
    assert!(opaque(kFirstClauseId) > opaque(kInvalidClauseId));
    assert!(kTermHashTableCapacity.count_ones() == 1);
    assert!(opaque(kTermHashTableLoadFactorPercent) < opaque(100));
    assert!(opaque(kInlineClauseLiterals) <= opaque(kMaxClauseLiterals as usize));
    assert!(opaque(kMaxDerivationParents) == opaque(4));
    assert!(opaque(kMaxSatVariables) <= opaque(u32::MAX / 2));
    assert!(opaque(kMaxSymbolArity) <= opaque(u16::MAX));
    assert!(kMaxAlignment.count_ones() == 1);
    assert!(kBudgetCheckInterval.count_ones() == 1);
    assert!(opaque(kPortfolioThreadCount) >= opaque(1));
    assert!(opaque(kAvatarMinComponentSize) >= opaque(1));
    assert!(opaque(kMaxArenaFragmentationRatioPercent) < opaque(100));
    assert!(opaque(kDefaultSymbolWeight) >= opaque(1));
    assert!(opaque(kKboVariableWeight) >= opaque(1));
    assert!(opaque(kSatWatchListCount) == opaque(kMaxSatVariables * 2));
    assert!(opaque(kSatTrailCapacity) == opaque(kMaxSatVariables));
    assert!(opaque(kMaxTermDepth) >= opaque(1));
    assert!(opaque(kMaxTermWeight) < opaque(u32::MAX));
    assert!(opaque(kMaxSubstitutionTrailDepth) >= opaque(kMaxVariablesPerClause));
    assert!(opaque(kMaxUnificationDepth) >= opaque(kMaxTermDepth as u32));
    assert!(opaque(kSatVsidsDecayPercent) >= opaque(1));
    assert!(opaque(kSatVsidsDecayPercent) < opaque(100));
    assert!(opaque(kSatVsidsActivityCeiling) > opaque(0.0));
    assert!(opaque(kSatVsidsActivityCeiling * kSatVsidsRescaleFactor) <= opaque(1.0));
    assert!(opaque(kSatRestartGeometricFactorPercent) >= opaque(100));
    assert!(opaque(kMaxOrderingSteps) >= opaque(kMaxTermDepth as u32));
    assert!(opaque(kDiscriminationTreeNodes) < opaque(kInvalidIndexNode));
    assert!(opaque(kDiscriminationTreeEntries) < opaque(kInvalidIndexEntry));
    assert!(opaque(kIndexEqualitySymbol) > opaque(kMaxSymbolCount));
    assert!(opaque(kIndexEqualitySymbol) < opaque(kInvalidSymbolId));
    assert!(opaque(kIndexEqualitySymbol) != opaque(kInvalidIndexNode));
    assert!(opaque(kSatMaxConflicts) >= opaque(1));
}

// CEP:WHAT: Verifies result codes are distinct.
// CEP:WHY: The result vocabulary must be injective for FFI mapping.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on duplicate codes.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/result.rs.
// CEP:SECURITY: none.
#[test]
fn result_codes_unique() {
    let codes = [
        ProverResult::Theorem,
        ProverResult::CounterSatisfiable,
        ProverResult::Saturated,
        ProverResult::Timeout,
        ProverResult::MemoryExhausted,
        ProverResult::InferenceLimit,
        ProverResult::GaveUp,
        ProverResult::Error,
    ];
    for (index, code) in codes.iter().enumerate() {
        for (other_index, other) in codes.iter().enumerate() {
            if index != other_index {
                assert_ne!(*code as u8, *other as u8, "result codes must be unique");
            }
        }
    }
    assert_eq!(codes.len(), 8);
}

// CEP:WHAT: Verifies target configuration consistency for the selected target.
// CEP:WHY: The selected target module must expose the documented constants.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on missing target constants.
// CEP:ASSUMES: exactly one target feature is enabled (compile-time guarded).
// CEP:COST: constant.
// CEP:EVIDENCE: cited by config/target.rs.
// CEP:SECURITY: none.
#[test]
fn target_selection_consistent() {
    use mapt::config::target::selected;
    assert!(!selected::kTargetName.is_empty());
    assert!(selected::kCacheLineBytes.count_ones() == 1);
    assert!(opaque(selected::kPageBytes) >= opaque(4_096));
    assert_eq!(selected::kPointerBytes, 8);
    assert!(opaque(selected::kLittleEndian));
    let gates = [
        mapt::config::feature_gates::kTargetX86_64Enabled,
        mapt::config::feature_gates::kTargetArm64Enabled,
        mapt::config::feature_gates::kTargetRiscv64Enabled,
        mapt::config::feature_gates::kTargetGenericEnabled,
    ];
    let enabled = gates.iter().filter(|gate| **gate).count();
    assert_eq!(enabled, 1, "exactly one target gate must be enabled");
}
