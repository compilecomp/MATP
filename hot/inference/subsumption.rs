// CEP:FILE: hot/inference/subsumption.rs
// CEP:WHAT: Subsumption (Plotkin 1972; design 10.1): decides whether one clause subsumes another - exists sigma with C sigma a subset of D - via literal-by-literal one-directional matching over a shared, trail-disciplined substitution; subsumption resolution (Riazanov 2003; design 10.1, CEP-1034): decides whether the side premise licenses deleting one resolution literal from the main premise; and condensation (design 10.1, CEP-1034): the same decision with the clause against itself.
// CEP:WHY: Design 10.4's redundancy criterion in practice: forward subsumption (an active clause subsumes the given clause, which is then discarded) and backward subsumption (the given clause subsumes active clauses, which are then removed) both reduce the search space without losing completeness (subsumption deletion preserves refutational completeness, BG 2001); the check is matching-based (sigma instantiates only the subsumer's variables), literal reuse across the target is allowed because subset-hood is a set condition (C = P(x) v P(y) subsumes D = P(a) v Q(b): both x and y map to a and the collapsed instance {P(a)} is a subset of D), and the trail discipline (snapshot depth, unwind per literal backtrack, unwind at exit) makes the check non-destructive on the shared substitution (Spec 02 section 4). Subsumption resolution and condensation strengthen clauses beyond deletion: they are the standard "resolution + subsumption" fusion of Riazanov & Voronkov 2003 (the formal condition is Definition 2 of Coutelier, Just, Suda et al., "SAT Solving for Variants of First-Order Subsumption", arXiv:2412.16058, which restates RV03 verbatim: sigma(S') = {not m'} and sigma(S \ S') subset of M \ {m'}), and the decision procedure reuses the same matching machinery and trail discipline.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Ok(false) is the only negative answer; Err only on structural failures; never panics.
// CEP:ASSUMES: Both literal slices belong to clauses with dense variable namespaces; the caller is responsible for renaming apart when the two clauses share the namespace (the search's forward/backward checks run candidate-against-given with the candidate renamed into the given's window by the caller).
// CEP:COST: exponential backtrack in the worst case (literal assignment search), bounded in practice by the feature-vector and discrimination-tree pre-filters and structurally by kMaxClauseLiterals; measured within bench CEP-BENCH-0012, artifact benches/artifacts/atp_subsumption_verify.json.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_ground_subset, subsumption_instantiates, subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::{subsumption_agrees_with_brute_force, subsumption_filter_admits_all_true_subsumptions}.
// CEP:SECURITY: the backtrack depth is bounded by the literal count (CEP&CC 22.10 discipline).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; literals pair in index order and the trail discipline fixes the matcher.
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 2 fixes the subsumption definition (exists sigma, C sigma a subset of D as literal sets) and the matching-based decision procedure; the property test verifies the decision against a brute-force oracle over ground instances.

use crate::ir::literal::Literal;
use crate::unification::match_terms;
use mapt_config::limits::kMaxSrMatchAttempts;

use super::InferenceContext;

/// CEP:WHAT: Decides whether candidate subsumes target.
/// CEP:WHY: Spec 08 section 2: a necessary size condition (|C| <= |D|) short-circuits, then a backtracking search assigns each candidate literal a target literal of the same polarity whose atom it matches, extending one shared substitution; success means sigma exists and the candidate subsumes the target.
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(false) when no sigma exists; Err propagates structural failures; the substitution trail is unwound to the entry depth on both outcomes.
/// CEP:ASSUMES: both namespaces are dense; the caller renamed apart when needed.
/// CEP:COST: backtracking matching, worst case exponential in the literal count (bounded by the pre-filters upstream).
/// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_ground_subset, subsumption_instantiates, subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::subsumption_agrees_with_brute_force.
/// CEP:SECURITY: bounded backtrack.
pub fn subsumes(
    context: &InferenceContext<'_>,
    candidate: &[Literal],
    target: &[Literal],
) -> Result<bool, super::InferenceError> {
    if candidate.len() > target.len() {
        return Ok(false);
    }
    if candidate.is_empty() {
        // The empty clause subsumes everything (and only it subsumes the empty clause).
        return Ok(true);
    }
    let entry_depth = context.substitution.trail_depth();
    let result = assign_literal(context, candidate, 0, target);
    context.substitution.undo_to(entry_depth);
    result
}

// CEP:WHAT: Recursive literal-assignment search: tries every same-polarity target literal for candidate[position] and recurses on success.
// CEP:WHY: The backtracking heart of the subsumption check; target literals are REUSABLE across candidate positions because subset-hood is a set condition (C = P(x) v P(y) subsumes D = P(a) with x and y both mapped to a), so no used-marks exist; termination is the finite recursion depth (|candidate|) with a finite scan per level (|target|) - exponential worst case at the clause-literal bound, pruned upstream by the feature-vector filter and the discrimination tree.
// CEP:STATUS: complete
// CEP:FAILURE: Err propagates structural failures; every failed match branch unwinds its own bindings (match_terms' contract) before the next attempt.
// CEP:ASSUMES: candidate is non-empty at the top call.
// CEP:COST: O(|target|^|candidate|) worst case.
// CEP:EVIDENCE: unit/hot/inference_test.rs::{subsumption_reuses_target_literals, subsumption_rejects}; property/inference_property_test.rs::subsumption_agrees_with_brute_force.
// CEP:SECURITY: recursion depth bounded by kMaxClauseLiterals.
fn assign_literal(
    context: &InferenceContext<'_>,
    candidate: &[Literal],
    position: usize,
    target: &[Literal],
) -> Result<bool, super::InferenceError> {
    if position == candidate.len() {
        return Ok(true);
    }
    let literal = &candidate[position];
    for other in target.iter() {
        if other.is_positive() != literal.is_positive() {
            continue;
        }
        let entry_depth = context.substitution.trail_depth();
        let matched = match_terms(
            context.terms,
            context.symbols,
            context.substitution,
            literal.atom(),
            other.atom(),
        )?;
        if matched && assign_literal(context, candidate, position + 1, target)? {
            return Ok(true);
        }
        context.substitution.undo_to(entry_depth);
    }
    Ok(false)
}

/// CEP:WHAT: Ground tautology check: a clause containing two literals with pointer-equal atoms and opposite polarity.
/// CEP:WHY: Design 10.1 tautology deletion and design 10.4: hash-consing makes structural atom equality pointer equality (design 5.1), so the check is exact and allocation-free; unifiable-but-distinct atoms (P(x) v not P(y)) are NOT tautologies (x and y can differ) and the check correctly keeps them.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: atoms interned by one store.
/// CEP:COST: O(n^2) pointer comparisons.
/// CEP:EVIDENCE: unit/hot/inference_test.rs::{tautology_detected, near_tautology_kept}.
/// CEP:SECURITY: none.
pub fn is_tautology(literals: &[Literal]) -> bool {
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            if literals[i].atom() == literals[j].atom()
                && literals[i].is_positive() != literals[j].is_positive()
            {
                return true;
            }
        }
    }
    false
}

/// CEP:WHAT: Decides whether the side premise subsumption-resolves the main premise at the given resolution literal (Riazanov 2003; design 10.1, CEP-1034): exists sigma and a non-empty S' subset of side with sigma(S') = {not main[resolution]} and sigma(side \ S') subset of main \ {main[resolution]} as exact one-directional matches.
/// CEP:WHY: Spec 07 section 11 (the CEP-1034 addition) fixes the condition per Definition 2 of arXiv:2412.16058 (restating Riazanov & Voronkov 2003): the backtracking search assigns every side literal one of two roles - join S' by matching the resolution literal's atom under the OPPOSITE polarity (sigma(s) = not m' exactly), or match some other main literal of the SAME polarity with index != resolution (sigma(s) = m exactly, set semantics so target reuse is allowed); success means the search's conclusion main \ {m'} is sound: every sigma-image of side is false at any valuation falsifying main \ {m'} (S'-images equal not m', which is false there; role-B images equal exact members of main \ {m'}, also false there), so sigma(side) is false and side cannot hold - the soundness proof of Spec 07 section 11; the matches are exact (match_terms' one-directional equality), which is what makes the proof work (instance-of witnesses would not compose with the falsifying valuation).
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(false) when no sigma exists; Err propagates structural failures; the substitution trail is unwound to the entry depth on every outcome.
/// CEP:ASSUMES: both namespaces are dense; the caller renamed the side premise apart into the main's variable window when they come from different clauses (the loop's simplify path uses rename_clause_apart like forward subsumption).
/// CEP:COST: O(|main|^|side|) backtracking worst case (same shape as subsumes), bounded by kMaxClauseLiterals; the loop's simplify scan prefilters on the head-symbol set of the main premise (see given_clause.rs).
/// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs::{sr_fires_on_resolution_literal, sr_two_side_literals_map_to_resolution_literal, sr_rejects_no_opposite_polarity_match, sr_rejects_unmatched_side_literal, sr_rejects_resolution_literal_target, sr_trail_untouched_on_failure}; kernel replay arms unit/cold/kernel_test.rs.
/// CEP:SECURITY: bounded backtrack.
pub fn subsumption_resolves_onto(
    context: &InferenceContext<'_>,
    side: &[Literal],
    main: &[Literal],
    resolution: usize,
) -> Result<bool, super::InferenceError> {
    if side.is_empty() || resolution >= main.len() || side.len() > main.len() {
        return Ok(false);
    }
    let entry_depth = context.substitution.trail_depth();
    let mut s_prime_seen = false;
    // The attempt budget bounds the exponential backtracking (Law 6): exhaustion
    // aborts the attempt as Ok(false) - a documented decision incompleteness
    // that only misses a simplification, never applies an unsound one; the
    // kernel replays with the same budget, so every recorded step verifies.
    let mut budget = kMaxSrMatchAttempts;
    let result = assign_side_literal(
        context,
        side,
        0,
        main,
        resolution,
        &mut s_prime_seen,
        &mut budget,
    );
    context.substitution.undo_to(entry_depth);
    result
}

/// CEP:WHAT: Scans the main premise left to right and returns the first resolution literal the side premise subsumption-resolves (design 10.1, CEP-1034).
/// CEP:WHY: The simplification loop's entry point: the deterministic first-hit scan (index order, CEP&CC 38.10) fixes which literal the search removes, so the recorded derivation chain and the kernel's replay agree; Ok(None) means the pair does not admit subsumption resolution and the main premise stays untouched.
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(None) when no resolution literal is licensed; Err propagates structural failures; trail-disciplined per attempt.
/// CEP:ASSUMES: as subsumption_resolves_onto.
/// CEP:COST: O(|main|) attempts of the O(|main|^|side|) decision.
/// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs::{sr_fires_on_resolution_literal, sr_first_resolution_literal_wins}.
/// CEP:SECURITY: bounded backtrack.
pub fn subsumption_resolves(
    context: &InferenceContext<'_>,
    side: &[Literal],
    main: &[Literal],
) -> Result<Option<usize>, super::InferenceError> {
    if side.is_empty() || side.len() > main.len() {
        return Ok(None);
    }
    for resolution in 0..main.len() {
        if subsumption_resolves_onto(context, side, main, resolution)? {
            return Ok(Some(resolution));
        }
    }
    Ok(None)
}

/// CEP:WHAT: Scans the clause and returns the first literal condensation may delete (design 10.1, CEP-1034): condensation deletes literal m' when it is a sigma-instance of some OTHER literal of the same clause - the per-literal subsumption condensation whose canonical shape is P(x) v P(f(x)) |- P(x).
/// CEP:WHY: Spec 07 section 12 (the CEP-1034 addition): with C' = C \ {m'} and L = k sigma for some kept literal k (the kept literal is the pattern, the deleted literal its instance, polarity preserved), C' |= L holds pointwise (any model of C' satisfies every instance of its literals) and hence C' |= C, so the replacement preserves soundness (a refutation of the strengthened set refutes the original) and refutational completeness (unsat sets stay unsat); the kept pattern is RENAMED APART above the clause's variable window before the instance match (the standardize-apart discipline of Spec 02 section 5 - matching the clause against its own namespace would bind variables to themselves and corrupt the substitution trail), which is sound because renaming is a variable bijorphism (Spec 07 section 2) and preserves the instance set exactly; the instance direction is kept-matches-deleted (the reverse of subsumption resolution's direction, where the deleted main literal is matched by the side premise's complement).
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(None) when the clause does not condense; Err propagates structural failures; trail-disciplined per attempt.
/// CEP:ASSUMES: the clause's namespace is dense.
/// CEP:COST: O(|clause|^2) instance matches per scan, each bounded by the match cost of Spec 02 section 6.
/// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs::{condensation_fires, condensation_keeps_unmatched_clause, condensation_trail_untouched_on_failure}.
/// CEP:SECURITY: bounded matches.
pub fn condensation_target(
    context: &InferenceContext<'_>,
    clause: &[Literal],
) -> Result<Option<usize>, super::InferenceError> {
    if clause.is_empty() {
        return Ok(None);
    }
    for resolution in 0..clause.len() {
        if condensation_resolves_onto(context, clause, resolution)? {
            return Ok(Some(resolution));
        }
    }
    Ok(None)
}

/// CEP:WHAT: Decides whether the clause condenses at the given deletion literal: the deleted literal must be a shared-substitution instance of some other literal of the clause (CEP-1034).
/// CEP:WHY: The per-literal condensation decision the certified kernel's Condensation arm replays: each kept literal is renamed above the clause's variable window exactly once per candidate (the standardize-apart discipline keeps the match trail clean), the instance match runs with the shared substitution, and the loop's first-hit scan and the kernel's per-literal enumeration share this one decision, so a recorded step always replays.
/// CEP:STATUS: complete
/// CEP:FAILURE: Ok(false) when m' is not licensed; Err propagates structural failures; trail-disciplined.
/// CEP:ASSUMES: resolution < clause.len(); the clause's namespace is dense.
/// CEP:COST: O(|clause|) renamed instance matches.
/// CEP:EVIDENCE: unit/cold/kernel_test.rs::{condensation_replay_accepts_recorded_step, condensation_replay_rejects_tampered_step}.
/// CEP:SECURITY: bounded matches.
pub fn condensation_resolves_onto(
    context: &InferenceContext<'_>,
    clause: &[Literal],
    resolution: usize,
) -> Result<bool, super::InferenceError> {
    if clause.is_empty() || resolution >= clause.len() {
        return Ok(false);
    }
    let deleted = &clause[resolution];
    let variables = crate::inference::count_clause_variables(context.terms, clause)?;
    let entry_depth = context.substitution.trail_depth();
    let mut licensed = false;
    for (index, kept) in clause.iter().enumerate() {
        if index == resolution || kept.is_positive() != deleted.is_positive() {
            continue;
        }
        let branch_depth = context.substitution.trail_depth();
        // Rename the kept pattern above the clause's window: the matcher then
        // binds only renamed variables, never the clause's own variable terms.
        let pattern = match crate::inference::rename_apart(
            context.terms,
            context.symbols,
            kept.atom(),
            variables as u32,
            0,
        ) {
            Ok(value) => value,
            Err(error) => {
                context.substitution.undo_to(entry_depth);
                return Err(error);
            }
        };
        let matched = match_terms(
            context.terms,
            context.symbols,
            context.substitution,
            pattern,
            deleted.atom(),
        )?;
        if matched {
            licensed = true;
            break;
        }
        context.substitution.undo_to(branch_depth);
    }
    context.substitution.undo_to(entry_depth);
    Ok(licensed)
}

// CEP:WHAT: Recursive role-assignment search for subsumption resolution: side[position] either joins S' (opposite-polarity match onto the resolution literal's atom) or matches a same-polarity main literal other than the resolution literal; the shared attempt budget bounds every match.
// CEP:WHY: The backtracking heart of the SR decision (Spec 07 section 11's Algorithm): the shared substitution composes the per-literal matchers, role-B targets are reusable across positions (the definition's set-inclusion condition), the S'-non-emptiness requirement is carried by the s_prime_seen flag checked at the recursion base, every failed branch unwinds its own bindings before the next attempt (Spec 02 section 4 trail discipline), and the budget counter (kMaxSrMatchAttempts) bounds the worst-case exponential search deterministically - the same bound replays in the certified kernel, so a recorded step always re-verifies (CEP-1034).
// CEP:STATUS: complete
// CEP:FAILURE: Err propagates structural failures; every failed match branch unwinds its own bindings (match_terms' contract) before the next attempt; budget exhaustion returns Ok(false) for the attempt.
// CEP:ASSUMES: the caller snapshots the trail depth and unwinds after the top call; budget >= 1.
// CEP:COST: O(|main|^|side|) worst case, bounded by kMaxSrMatchAttempts match attempts.
// CEP:EVIDENCE: unit/hot/subsumption_resolution_test.rs; the paper's examples S4 (fires), S5 (two S' literals), S6/S7/S8 (rejected) and the budget bound are pinned there.
// CEP:SECURITY: recursion depth bounded by kMaxClauseLiterals; the CPU cost bounded by the budget.
#[allow(clippy::too_many_arguments)]
fn assign_side_literal(
    context: &InferenceContext<'_>,
    side: &[Literal],
    position: usize,
    main: &[Literal],
    resolution: usize,
    s_prime_seen: &mut bool,
    budget: &mut u32,
) -> Result<bool, super::InferenceError> {
    if position == side.len() {
        return Ok(*s_prime_seen);
    }
    if *budget == 0 {
        return Ok(false);
    }
    let literal = &side[position];
    let entry_depth = context.substitution.trail_depth();
    // Role A: join S' - the literal sigma-matches the resolution literal's atom
    // under the opposite polarity, so sigma(literal) = not m' exactly.
    if literal.is_positive() != main[resolution].is_positive() && *budget > 0 {
        *budget -= 1;
        let matched = match_terms(
            context.terms,
            context.symbols,
            context.substitution,
            literal.atom(),
            main[resolution].atom(),
        )?;
        if matched {
            let previous = *s_prime_seen;
            *s_prime_seen = true;
            if assign_side_literal(
                context,
                side,
                position + 1,
                main,
                resolution,
                s_prime_seen,
                budget,
            )? {
                return Ok(true);
            }
            *s_prime_seen = previous;
        }
    }
    context.substitution.undo_to(entry_depth);
    // Role B: sigma(literal) equals an exact member of main \ {m'} (set
    // semantics: targets are reusable across positions).
    for (index, other) in main.iter().enumerate() {
        if index == resolution || other.is_positive() != literal.is_positive() {
            continue;
        }
        if *budget == 0 {
            return Ok(false);
        }
        *budget -= 1;
        let branch_depth = context.substitution.trail_depth();
        let matched = match_terms(
            context.terms,
            context.symbols,
            context.substitution,
            literal.atom(),
            other.atom(),
        )?;
        if matched
            && assign_side_literal(
                context,
                side,
                position + 1,
                main,
                resolution,
                s_prime_seen,
                budget,
            )?
        {
            return Ok(true);
        }
        context.substitution.undo_to(branch_depth);
    }
    Ok(false)
}
