// CEP:FILE: cold/proof_output/drat_checker.rs
// CEP:WHAT: Internal DRAT checker (design 11.1 S43): replays the recorder's steps against the formula, seeds the database from axiom steps, verifies every derived addition by RUP (unit propagation to conflict) or RAT (resolvent RUP over the pivot), mirrors deletions, and reports validity, the first invalid step, or honest budget exhaustion.
// CEP:WHY: Design 18 and 11.4: a proof is an independently checkable certificate - trusting the solver's own claim of unsatisfiability violates the zero-tolerance correctness contract, so the recorded trace is verified mechanically after the solve; the checker runs cold (std, Vec-based, no arena) because it is a post-solve batch pass; axiom steps seed the database (they ARE the formula, and their one-to-one correspondence with the caller-supplied formula is verified, which binds the trace to the problem it claims to refute), assumption units are hypotheses (justification skipped, exactly as the solver treats them), derived additions carry the RUP/RAT burden, and deletions need no justification but must reference known ids.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns CheckOutcome::Invalid with the failing step index and reason, or BudgetExhausted with the steps checked; never panics; never reports Valid for a step it could not verify.
// CEP:ASSUMES: The recorder is quiescent; the formula argument is exactly the sequence of problem clauses added through solver.add_clause, in order; variable indices are dense from zero.
// CEP:COST: O(steps_checked x database_size x propagation_length) worst case - the checker re-propagates from scratch per RUP probe (no incremental watched-literal state), which is the price of a from-scratch independent verifier; the step budget bounds the pass and is reported honestly on exhaustion.
// CEP:EVIDENCE: unit/cold/drat_checker_test.rs; property/drat_property_test.rs::{proofs_of_random_solves_verify, mutated_proofs_rejected}; tests/golden/drat_proof_test.rs.
// CEP:SECURITY: the step budget and the RAT scan limit are denial-of-service bounds; malformed steps (unknown deletion ids, axiom/formula mismatch) are rejected loudly.
// CEP:HPC-DETERMINISM: deterministic; steps replay in recording order, clauses scan in database order, no clocks or randomness.

use mapt_config::limits::kDratRatScanLimit;
use mapt_hot::sat::literal::SatLiteral;
use mapt_hot::sat::proof::{ProofRecorder, ProofStepKind};

/// CEP:WHAT: Why a step failed verification.
/// CEP:WHY: CEP&CC Law 6: the failure vocabulary names the exact broken justification so a rejected certificate is diagnosable without a debugger.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{rup_failure_rejected, rat_failure_rejected, axiom_mismatch_rejected, unknown_deletion_rejected}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidReason {
    /// CEP:WHAT: A derived addition is neither RUP nor RAT under the current database.
    /// CEP:WHY: The core justification failure.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::rup_failure_rejected; property/drat_property_test.rs::mutated_proofs_rejected.
    /// CEP:SECURITY: none.
    JustificationFailed,
    /// CEP:WHAT: An axiom step's clause does not match the corresponding formula clause.
    /// CEP:WHY: The trace must refute exactly the formula it claims; a mismatch severs that binding.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::axiom_mismatch_rejected.
    /// CEP:SECURITY: rejects trace/formula substitution.
    AxiomMismatch,
    /// CEP:WHAT: A deletion referenced an id that was never added (or was already deleted).
    /// CEP:WHY: Database-mirror bookkeeping failure.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::unknown_deletion_rejected.
    /// CEP:SECURITY: none.
    UnknownDeletionId,
    /// CEP:WHAT: A step is malformed for its kind (empty axiom, assumption clause of length other than one).
    /// CEP:WHY: Structural trace validation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::malformed_steps_rejected.
    /// CEP:SECURITY: none.
    MalformedStep,
}

/// CEP:WHAT: Outcome of one verification run.
/// CEP:WHY: CEP&CC Law 6: Valid, Invalid (with the failing step and reason), and BudgetExhausted (with the honest prefix length) are three different facts; conflating budget exhaustion with validity would fabricate trust.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{refutation_proofs_verify, rup_failure_rejected, budget_enforced}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckOutcome {
    /// CEP:WHAT: Every step verified (RUP or RAT where required, deletions mirrored, axioms matched).
    /// CEP:WHY: The trusting outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the trace ends with the empty clause when it claims a refutation (the caller checks the terminal step's shape).
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify; property/drat_property_test.rs::proofs_of_random_solves_verify.
    /// CEP:SECURITY: none.
    Valid {
        /// CEP:WHAT: Number of steps verified.
        /// CEP:WHY: Extent of the trust.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 4 bytes.
        /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
        /// CEP:SECURITY: none.
        steps_checked: u32,
    },
    /// CEP:WHAT: The step at the given index failed verification for the given reason.
    /// CEP:WHY: The rejecting outcome.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: steps before the index verified.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{rup_failure_rejected, rat_failure_rejected, axiom_mismatch_rejected, unknown_deletion_rejected}.
    /// CEP:SECURITY: none.
    Invalid {
        /// CEP:WHAT: Failing step index.
        /// CEP:WHY: Locates the broken justification.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 4 bytes.
        /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::rup_failure_rejected.
        /// CEP:SECURITY: none.
        step: u32,
        /// CEP:WHAT: Failure reason.
        /// CEP:WHY: See InvalidReason.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: enum copy.
        /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::rup_failure_rejected.
        /// CEP:SECURITY: none.
        reason: InvalidReason,
    },
    /// CEP:WHAT: The step budget ran out; the prefix verified.
    /// CEP:WHY: Honest partial verification (design 20.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: steps before the budget verified.
    /// CEP:COST: none.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::budget_enforced.
    /// CEP:SECURITY: none.
    BudgetExhausted {
        /// CEP:WHAT: Number of steps verified before exhaustion.
        /// CEP:WHY: Extent of the partial trust.
        /// CEP:STATUS: complete
        /// CEP:FAILURE: none.
        /// CEP:ASSUMES: none.
        /// CEP:COST: 4 bytes.
        /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::budget_enforced.
        /// CEP:SECURITY: none.
        steps_checked: u32,
    },
}

/// CEP:WHAT: Budgets of one verification run.
/// CEP:WHY: CEP&CC 34.3: the bounds are injectable so tests exercise exhaustion at small scales on the production path; defaults are the named constants.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a configuration record.
/// CEP:ASSUMES: budgets >= 1.
/// CEP:COST: plain data.
/// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::budget_enforced.
/// CEP:SECURITY: the budgets are the denial-of-service bounds under test.
#[derive(Default)]
pub struct CheckOptions {
    /// CEP:WHAT: Maximum steps verified per run.
    /// CEP:WHY: Bounded checking (kMaxProofSteps is the semantic ceiling; the default here is a practical working budget).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: exhaustion reports the honest prefix.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub step_budget: u64,
    /// CEP:WHAT: Maximum clauses scanned per RAT pivot.
    /// CEP:WHY: kDratRatScanLimit.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: an over-limit scan reports JustificationFailed (not silently valid).
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::rat_scan_budget_enforced.
    /// CEP:SECURITY: denial-of-service bound.
    pub rat_scan_limit: u32,
}

impl CheckOptions {
    // CEP:WHAT: Production budgets from the named constants.
    // CEP:WHY: One named place documents the defaults (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    // CEP:SECURITY: none.
    pub fn new() -> CheckOptions {
        CheckOptions {
            step_budget: 1_000_000,
            rat_scan_limit: kDratRatScanLimit,
        }
    }
}

// CEP:WHAT: The checker's database mirror: proof id to live clause.
// CEP:WHY: Deletions reference ids; Vec slots with None for deleted/never-used keep the mirror dense and O(1) addressable.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: ids are dense from kFirstProofId.
// CEP:COST: 8 bytes per id plus clause storage.
// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{refutation_proofs_verify, unknown_deletion_rejected}.
// CEP:SECURITY: none.
struct Mirror {
    /// CEP:WHAT: Live clauses by proof id slot (index = id - kFirstProofId).
    /// CEP:WHY: The active database.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: dense ids.
    /// CEP:COST: Vec growth.
    /// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    /// CEP:SECURITY: none.
    clauses: Vec<Option<Vec<SatLiteral>>>,
}

impl Mirror {
    // CEP:WHAT: Inserts a clause under a proof id.
    // CEP:WHY: Mirror add.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: id is fresh.
    // CEP:COST: amortized O(1).
    // CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    // CEP:SECURITY: none.
    fn insert(&mut self, id: u32, literals: Vec<SatLiteral>) {
        let slot = (id - mapt_config::limits::kFirstProofId) as usize;
        if slot >= self.clauses.len() {
            self.clauses.resize(slot + 1, None);
        }
        self.clauses[slot] = Some(literals);
    }

    // CEP:WHAT: Removes a clause by proof id; returns whether it was live.
    // CEP:WHY: Mirror delete; unknown or double deletions are bookkeeping failures.
    // CEP:STATUS: complete
    // CEP:FAILURE: false for unknown ids.
    // CEP:ASSUMES: id >= kFirstProofId.
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/cold/drat_checker_test.rs::unknown_deletion_rejected.
    // CEP:SECURITY: none.
    fn remove(&mut self, id: u32) -> bool {
        let slot = (id - mapt_config::limits::kFirstProofId) as usize;
        if slot >= self.clauses.len() {
            return false;
        }
        let live = self.clauses[slot].take();
        live.is_some()
    }

    // CEP:WHAT: Collects the live clauses as reference slices.
    // CEP:WHY: RUP/RAT probes scan the active database.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(clauses).
    // CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    // CEP:SECURITY: none.
    fn live(&self) -> Vec<&[SatLiteral]> {
        self.clauses
            .iter()
            .filter_map(|slot| slot.as_deref())
            .collect()
    }
}

// CEP:WHAT: Unit propagation to conflict over a clause list under seed assumptions (the RUP engine).
// CEP:WHY: RUP (reverse unit propagation, Heule et al. 2013): a clause C is RUP iff assuming the negation of every C literal and propagating derives a conflict; the routine is a plain worklist propagation over a dense value array - from-scratch by design so the verifier shares no state with the solver it verifies.
// CEP:STATUS: complete
// CEP:FAILURE: none (bool answer).
// CEP:ASSUMES: seed literals are the assumed-true literals; variables are dense from zero.
// CEP:COST: O(assignments x clause scans) - from scratch per probe.
// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{refutation_proofs_verify, rup_failure_rejected}.
// CEP:SECURITY: none.
fn propagates_to_conflict(clauses: &[&[SatLiteral]], seed: &[SatLiteral]) -> bool {
    let mut variable_count: usize = 0;
    for literal in seed.iter() {
        variable_count = variable_count.max(literal.variable().0 as usize + 1);
    }
    for clause in clauses.iter() {
        for literal in clause.iter() {
            variable_count = variable_count.max(literal.variable().0 as usize + 1);
        }
    }
    // values[v]: 1 = true, -1 = false, 0 = unassigned.
    let mut values = vec![0i8; variable_count];
    let mut queue: Vec<SatLiteral> = Vec::with_capacity(seed.len());
    for literal in seed.iter() {
        let index = literal.variable().0 as usize;
        let bit: i8 = if literal.is_positive() { 1 } else { -1 };
        match values[index] {
            0 => {
                values[index] = bit;
                queue.push(*literal);
            }
            existing if existing == bit => {}
            _ => return true,
        }
    }
    // Wave propagation: each wave scans every clause once, propagating units and
    // detecting conflicts, until a wave makes no progress (from-scratch verifier
    // simplicity). Waves run even when the seed queue is empty so that database
    // units alone can derive a conflict - that is exactly the RUP shape of the
    // final empty clause (Spec 11 section 4).
    let _ = &queue;
    loop {
        let mut progressed = false;
        for clause in clauses.iter() {
            let mut unassigned: Option<SatLiteral> = None;
            let mut satisfied = false;
            for literal in clause.iter() {
                let index = literal.variable().0 as usize;
                let bit: i8 = if literal.is_positive() { 1 } else { -1 };
                match values[index] {
                    0 => {
                        if unassigned.is_some() {
                            satisfied = true; // two unassigned: not unit this wave
                            break;
                        }
                        unassigned = Some(*literal);
                    }
                    existing if existing == bit => {
                        satisfied = true;
                        break;
                    }
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            match unassigned {
                None => return true, // all literals falsified: conflict
                Some(literal) => {
                    let index = literal.variable().0 as usize;
                    let bit: i8 = if literal.is_positive() { 1 } else { -1 };
                    values[index] = bit;
                    queue.push(literal);
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    false
}

// CEP:WHAT: Reads one step's literals from the recorder into a Vec.
// CEP:WHY: The mirror and the probes own their clause copies; None means an unreadable step (surfaced by the caller as MalformedStep).
// CEP:STATUS: complete
// CEP:FAILURE: None on unreadable literals.
// CEP:ASSUMES: step came from step().
// CEP:COST: O(literals).
// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::refutation_proofs_verify.
// CEP:SECURITY: none.
fn step_literals(
    recorder: &ProofRecorder<'_>,
    step: mapt_hot::sat::proof::ProofStep,
) -> Option<Vec<SatLiteral>> {
    let mut literals = Vec::with_capacity(step.literal_count as usize);
    for slot in 0..step.literal_count {
        literals.push(recorder.step_literal(step, slot)?);
    }
    Some(literals)
}

/// CEP:WHAT: Verifies the recorder's trace against the formula: axiom steps must match the formula in order, derived additions must be RUP or RAT, deletions must reference known ids, assumption units are hypotheses.
/// CEP:WHY: The certificate-verification entry point (S43); the outcome distinguishes verified, rejected-with-cause, and honestly-budgeted prefixes so no unverified step is ever trusted.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: see CheckOutcome; never panics.
/// CEP:ASSUMES: the formula is exactly the problem clauses in add order; the recorder is quiescent.
/// CEP:COST: O(steps x database x propagation) worst case; bounded by the step budget.
/// CEP:EVIDENCE: unit/cold/drat_checker_test.rs; property/drat_property_test.rs::{proofs_of_random_solves_verify, mutated_proofs_rejected}.
/// CEP:SECURITY: budgets bound adversarial traces.
pub fn verify(
    formula: &[Vec<SatLiteral>],
    recorder: &ProofRecorder<'_>,
    options: &CheckOptions,
) -> CheckOutcome {
    let mut mirror = Mirror {
        clauses: Vec::new(),
    };
    let mut formula_cursor: usize = 0;
    let total = recorder.step_count();
    let mut checked: u32 = 0;
    for index in 0..total {
        if checked as u64 >= options.step_budget {
            return CheckOutcome::BudgetExhausted {
                steps_checked: checked,
            };
        }
        let step = match recorder.step(index) {
            Some(value) => value,
            None => {
                return CheckOutcome::Invalid {
                    step: index,
                    reason: InvalidReason::MalformedStep,
                }
            }
        };
        let literals = match step_literals(recorder, step) {
            Some(value) => value,
            None => {
                return CheckOutcome::Invalid {
                    step: index,
                    reason: InvalidReason::MalformedStep,
                }
            }
        };
        match step.kind {
            ProofStepKind::AxiomAdd => {
                if literals.is_empty() || formula_cursor >= formula.len() {
                    return CheckOutcome::Invalid {
                        step: index,
                        reason: InvalidReason::AxiomMismatch,
                    };
                }
                if literals != formula[formula_cursor] {
                    return CheckOutcome::Invalid {
                        step: index,
                        reason: InvalidReason::AxiomMismatch,
                    };
                }
                formula_cursor += 1;
                mirror.insert(step.proof_id, literals);
            }
            ProofStepKind::Add => {
                // Derived addition: RUP first, then RAT on the first literal.
                let negated: Vec<SatLiteral> =
                    literals.iter().map(|literal| literal.negate()).collect();
                let live = mirror.live();
                let rup = propagates_to_conflict(&live, &negated);
                let justified = if rup {
                    true
                } else if literals.is_empty() {
                    false
                } else {
                    rat_justified(&live, &literals, options.rat_scan_limit)
                };
                if !justified {
                    return CheckOutcome::Invalid {
                        step: index,
                        reason: InvalidReason::JustificationFailed,
                    };
                }
                mirror.insert(step.proof_id, literals);
            }
            ProofStepKind::AssumptionAdd => {
                if literals.len() != 1 {
                    return CheckOutcome::Invalid {
                        step: index,
                        reason: InvalidReason::MalformedStep,
                    };
                }
                // Hypothesis: seeds the mirror without justification (Spec 11 section 3).
                mirror.insert(step.proof_id, literals);
            }
            ProofStepKind::Delete | ProofStepKind::AssumptionDelete => {
                if !mirror.remove(step.proof_id) {
                    return CheckOutcome::Invalid {
                        step: index,
                        reason: InvalidReason::UnknownDeletionId,
                    };
                }
            }
        }
        checked += 1;
    }
    if formula_cursor != formula.len() {
        // Every formula clause must appear as an axiom step; a short axiom run means
        // the trace does not cover the stated formula.
        return CheckOutcome::Invalid {
            step: total,
            reason: InvalidReason::AxiomMismatch,
        };
    }
    CheckOutcome::Valid {
        steps_checked: checked,
    }
}

// CEP:WHAT: RAT check: the pivot is the clause's first literal; every live clause containing the negated pivot yields a resolvent that must be RUP (tautological resolvents are skipped).
// CEP:WHY: RAT (resolution asymmetric tautology, Heule et al. 2013): C is RAT on pivot p iff for every clause D containing -p, the resolvent (C \ {p}) u (D \ {-p}) is RUP or tautological; the scan limit bounds adversarial databases.
// CEP:STATUS: complete
// CEP:FAILURE: false when any required resolvent is not RUP or the scan limit is exceeded.
// CEP:ASSUMES: clause is non-empty (the caller checks).
// CEP:COST: O(scan limit x resolvent size x propagation).
// CEP:EVIDENCE: unit/cold/drat_checker_test.rs::{rat_step_verified, rat_failure_rejected, rat_scan_budget_enforced}.
// CEP:SECURITY: the scan limit is a denial-of-service bound.
fn rat_justified(live: &[&[SatLiteral]], clause: &[SatLiteral], scan_limit: u32) -> bool {
    let pivot = clause[0];
    let negated_pivot = pivot.negate();
    let mut scanned: u32 = 0;
    for candidate in live.iter() {
        if !candidate
            .iter()
            .any(|literal| literal.encoding() == negated_pivot.encoding())
        {
            continue;
        }
        scanned += 1;
        if scanned > scan_limit {
            return false;
        }
        // Resolvent: (clause \ {pivot}) u (candidate \ {negated pivot}).
        let mut resolvent: Vec<SatLiteral> = Vec::with_capacity(clause.len() + candidate.len());
        for literal in clause.iter().skip(1) {
            resolvent.push(*literal);
        }
        for literal in candidate.iter() {
            if literal.encoding() == negated_pivot.encoding() {
                continue;
            }
            resolvent.push(*literal);
        }
        // Tautological resolvents are vacuously fine.
        let mut tautology = false;
        for i in 0..resolvent.len() {
            for j in (i + 1)..resolvent.len() {
                if resolvent[i].variable().0 == resolvent[j].variable().0
                    && resolvent[i].is_positive() != resolvent[j].is_positive()
                {
                    tautology = true;
                }
            }
        }
        if tautology {
            continue;
        }
        let negated_resolvent: Vec<SatLiteral> =
            resolvent.iter().map(|literal| literal.negate()).collect();
        if !propagates_to_conflict(live, &negated_resolvent) {
            return false;
        }
    }
    true
}
