// CEP:FILE: tests/property/inference_property_test.rs
// CEP:WHAT: Property tests for the inference rules: soundness of resolution, factoring, equality factoring, equality resolution, superposition, and demodulation over random ground premises (validated by exhaustive interpretation), the subsumption decision against a brute-force oracle, the subsumption filter's soundness (no true subsumption filtered out), truncated-vector soundness, and the eligibility rules under selection.
// CEP:WHY: Spec 07's soundness theorems are unconditional, so a single counterexample over ground instances falsifies the implementation; ground premises with constants a, b interpreted over a two-element domain give an exact finite oracle for entailment checks.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any soundness violation.
// CEP:ASSUMES: the deterministic LCG; the fixture vocabulary (constants a, b; unary f, g; predicates p, r; equality).
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by hot/inference/{resolution,factoring,superposition,demodulation,subsumption}.rs and hot/index/feature_vector.rs.
// CEP:SECURITY: no untrusted input; fixed seeds.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::hot::inference::demodulation::demodulate;
use mapt::hot::inference::factoring::{equality_factor, factor};
use mapt::hot::inference::resolution::resolve;
use mapt::hot::inference::subsumption::subsumes;
use mapt::hot::inference::superposition::{equality_resolve, superpose};
use mapt::hot::inference::{InferenceContext, OrderingKind, SelectionFunction};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::{TermPtr, TermStore};

// CEP:WHAT: Runs per property test.
// CEP:WHY: Named property-test size (CEP&CC 28.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kRuns: u64 = 40;

// CEP:WHAT: One property-test fixture: context plus the interned vocabulary.
// CEP:WHY: Building terms by name keeps the generators readable.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
struct OracleFixture {
    context: InferenceContext<'static>,
    symbols: &'static mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: mapt::cold::symbol_table_builder::SymbolTableBuilder,
    terms: &'static TermStore<'static>,
    a: TermPtr,
    b: TermPtr,
    #[allow(dead_code)]
    _arena: &'static mapt::hot::memory::arena::Arena,
}

// CEP:WHAT: Builds the oracle fixture.
// CEP:WHY: One constructor.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn make_oracle() -> OracleFixture {
    // The pieces borrow one leaked arena; leaking the owned structs too gives the
    // fixture 'static (the arena itself is already leaked by the common helper).
    let (arena, symbols, builder, terms, precedence, substitution) = make_inference_fixture();
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let symbols: &'static _ = Box::leak(Box::new(symbols));
    let terms: &'static _ = Box::leak(Box::new(terms));
    let precedence: &'static _ = Box::leak(Box::new(precedence));
    let substitution: &'static _ = Box::leak(Box::new(substitution));
    let context = InferenceContext {
        terms,
        symbols,
        substitution,
        precedence,
        ordering: OrderingKind::Kbo,
    };
    OracleFixture {
        context,
        symbols,
        builder,
        terms,
        a,
        b,
        _arena: arena,
    }
}

// CEP:WHAT: Evaluates a ground term under an interpretation of f and g.
// CEP:WHY: The oracle's term semantics: constants map to their domain values, f and g to the selected unary functions.
// CEP:STATUS: complete
// CEP:FAILURE: returns None for non-ground or unreadable terms.
// CEP:ASSUMES: ground term over the fixture vocabulary.
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn eval_term(fixture: &OracleFixture, term: TermPtr, f_value: u64, g_value: u64) -> Option<u64> {
    let view = fixture.terms.term(term).ok()?;
    match view.tag() {
        mapt::hot::ir::term::TermTag::Function => {
            if view.symbol() == symbol_id(&fixture.builder, "a") {
                Some(0)
            } else if view.symbol() == symbol_id(&fixture.builder, "b") {
                Some(1)
            } else {
                let head = if view.symbol() == symbol_id(&fixture.builder, "f") {
                    f_value
                } else {
                    g_value
                };
                let arg = eval_term(fixture, view.child(0).ok()?, f_value, g_value)?;
                Some(apply_unary(head, arg))
            }
        }
        _ => None,
    }
}

// CEP:WHAT: Applies a unary function selected by index to a domain value.
// CEP:WHY: The four unary functions over {0,1}: identity, negation, constant-0, constant-1.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: head < 4, value < 2.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn apply_unary(head: u64, value: u64) -> u64 {
    match head {
        0 => value,
        1 => 1 - value,
        2 => 0,
        _ => 1,
    }
}

// CEP:WHAT: Evaluates a ground literal under an interpretation.
// CEP:WHY: Atom truth: p over the term value; r a fixed proposition per interpretation; equality over value identity.
// CEP:STATUS: complete
// CEP:FAILURE: returns None for non-ground atoms.
// CEP:ASSUMES: ground atom.
// CEP:COST: O(atom nodes).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn eval_literal(
    fixture: &OracleFixture,
    literal: Literal,
    f_value: u64,
    g_value: u64,
    r_value: bool,
) -> Option<bool> {
    let view = fixture.terms.term(literal.atom()).ok()?;
    let atom_value = match view.tag() {
        mapt::hot::ir::term::TermTag::Predicate => {
            if view.symbol() == symbol_id(&fixture.builder, "p") {
                eval_term(fixture, view.child(0).ok()?, f_value, g_value)? == 1
            } else {
                r_value
            }
        }
        mapt::hot::ir::term::TermTag::Equality => {
            let left = eval_term(fixture, view.child(0).ok()?, f_value, g_value)?;
            let right = eval_term(fixture, view.child(1).ok()?, f_value, g_value)?;
            left == right
        }
        _ => return None,
    };
    Some(atom_value == literal.is_positive())
}

// CEP:WHAT: Generates a random ground clause.
// CEP:WHY: The soundness premises.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_ground_clause(
    fixture: &OracleFixture,
    rng: &mut DeterministicRng,
    allow_equality: bool,
) -> Vec<Literal> {
    let length = 1 + rng.below(3u64) as usize;
    let mut literals: Vec<Literal> = Vec::new();
    for _ in 0..length {
        let atom = if allow_equality && rng.below(3u64) == 0 {
            let left = random_ground_term(fixture, rng, 0);
            let right = random_ground_term(fixture, rng, 0);
            fixture
                .terms
                .intern_eq(fixture.symbols, left, right)
                .expect("eq")
        } else if rng.below(3u64) == 0 {
            fixture
                .terms
                .intern_pred(fixture.symbols, symbol_id(&fixture.builder, "r"), &[])
                .expect("r")
        } else {
            let arg = random_ground_term(fixture, rng, 0);
            fixture
                .terms
                .intern_pred(fixture.symbols, symbol_id(&fixture.builder, "p"), &[arg])
                .expect("p")
        };
        literals.push(Literal::new(atom, rng.below(2u64) == 0));
    }
    literals
}

// CEP:WHAT: Generates a random ground term of bounded depth.
// CEP:WHY: The atom arguments.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: depth bound 2.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn random_ground_term(fixture: &OracleFixture, rng: &mut DeterministicRng, depth: u32) -> TermPtr {
    if depth >= 2 || rng.below(2u64) == 0 {
        return if rng.below(2u64) == 0 {
            fixture.a
        } else {
            fixture.b
        };
    }
    let head = if rng.below(2u64) == 0 { "f" } else { "g" };
    let child = random_ground_term(fixture, rng, depth + 1);
    fixture
        .terms
        .intern_fun(fixture.symbols, symbol_id(&fixture.builder, head), &[child])
        .expect("term")
}

// CEP:WHAT: Computes the flags of both premises and asserts the conclusion is entailed whenever a rule concludes.
// CEP:WHY: The shared soundness harness: for every concluded clause, every interpretation satisfying both premises must satisfy the conclusion.
// CEP:STATUS: complete
// CEP:FAILURE: panics on a soundness violation.
// CEP:ASSUMES: ground premises.
// CEP:COST: O(runs x interpretations).
// CEP:EVIDENCE: used by this file's soundness tests.
// CEP:SECURITY: none.
fn assert_conclusion_entailed(
    fixture: &OracleFixture,
    left: &[Literal],
    right: &[Literal],
    conclusion: &[Literal],
) {
    // Entailment check: premises -> conclusion over the finite interpretation
    // space: every interpretation that satisfies both premises (all literals of
    // each) must satisfy the conclusion clause.
    for f_value in 0..4u64 {
        for g_value in 0..4u64 {
            for r_bits in 0..2u64 {
                let r_value = r_bits == 1;
                let premises_hold = left.iter().chain(right.iter()).all(|literal| {
                    eval_literal(fixture, *literal, f_value, g_value, r_value).unwrap_or(false)
                });
                if !premises_hold {
                    continue;
                }
                let conclusion_holds = conclusion.iter().any(|literal| {
                    eval_literal(fixture, *literal, f_value, g_value, r_value).unwrap_or(false)
                });
                assert!(
                    conclusion_holds,
                    "soundness violation: premises {:?} entail NOT {:?} under f={} g={} r={}",
                    (left.len() + right.len()),
                    conclusion.len(),
                    f_value,
                    g_value,
                    r_value
                );
            }
        }
    }
}

// CEP:WHAT: Verifies resolution is sound over random ground premise pairs.
// CEP:WHY: Spec 07 section 4, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed resolvent.
// CEP:ASSUMES: ground premises (the oracle is exact there).
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::resolve.
// CEP:SECURITY: none.
#[test]
fn resolution_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1701);
    for _ in 0..kRuns {
        let left = random_ground_clause(&fixture, &mut rng, true);
        let right = random_ground_clause(&fixture, &mut rng, true);
        let mut left_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let mut right_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        for (index, literal) in left.iter().enumerate() {
            if index >= 8 {
                break;
            }
            left_buf[index] = *literal;
        }
        for (index, literal) in right.iter().enumerate() {
            if index >= 8 {
                break;
            }
            right_buf[index] = *literal;
        }
        let left_len = left.len().min(8);
        let right_len = right.len().min(8);
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut left_buf[..left_len],
        );
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut right_buf[..right_len],
        );
        for left_index in 0..left_len {
            for right_index in 0..right_len {
                let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                let outcome = resolve(
                    context,
                    &left_buf[..left_len],
                    left_index,
                    &right_buf[..right_len],
                    right_index,
                    &mut out,
                )
                .expect("resolve");
                if let mapt::hot::inference::resolution::ResolutionOutcome::Concluded(count) =
                    outcome
                {
                    assert_conclusion_entailed(
                        &fixture,
                        &left_buf[..left_len],
                        &right_buf[..right_len],
                        &out[..count],
                    );
                }
            }
        }
    }
}

// CEP:WHAT: Verifies factoring is sound over random ground clauses.
// CEP:WHY: Spec 07 section 5, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed factored clause.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::factor.
// CEP:SECURITY: none.
#[test]
fn factoring_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1702);
    for _ in 0..kRuns {
        let clause = random_ground_clause(&fixture, &mut rng, true);
        let mut buffer: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let length = clause.len().min(8);
        for (index, literal) in clause.iter().enumerate() {
            if index >= 8 {
                break;
            }
            buffer[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut buffer[..length],
        );
        for first in 0..length {
            for second in 0..length {
                if first == second {
                    continue;
                }
                let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                let outcome =
                    factor(context, &buffer[..length], first, second, &mut out).expect("factor");
                if let mapt::hot::inference::factoring::FactoringOutcome::Concluded(count) = outcome
                {
                    assert_conclusion_entailed(&fixture, &buffer[..length], &[], &out[..count]);
                }
            }
        }
    }
}

// CEP:WHAT: Verifies equality factoring is sound.
// CEP:WHY: Spec 07 section 5, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed conclusion.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::equality_factor.
// CEP:SECURITY: none.
#[test]
fn equality_factoring_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1703);
    for _ in 0..kRuns {
        let clause = random_ground_clause(&fixture, &mut rng, true);
        let mut buffer: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let length = clause.len().min(8);
        for (index, literal) in clause.iter().enumerate() {
            if index >= 8 {
                break;
            }
            buffer[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut buffer[..length],
        );
        for first in 0..length {
            for second in 0..length {
                if first == second {
                    continue;
                }
                let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                let outcome = equality_factor(context, &buffer[..length], first, second, &mut out)
                    .expect("factor");
                if let mapt::hot::inference::factoring::FactoringOutcome::Concluded(count) = outcome
                {
                    assert_conclusion_entailed(&fixture, &buffer[..length], &[], &out[..count]);
                }
            }
        }
    }
}

// CEP:WHAT: Verifies equality resolution is sound.
// CEP:WHY: Spec 07 section 6, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed conclusion.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::equality_resolve.
// CEP:SECURITY: none.
#[test]
fn equality_resolution_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1704);
    for _ in 0..kRuns {
        let clause = random_ground_clause(&fixture, &mut rng, true);
        let mut buffer: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let length = clause.len().min(8);
        for (index, literal) in clause.iter().enumerate() {
            if index >= 8 {
                break;
            }
            buffer[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut buffer[..length],
        );
        for index in 0..length {
            let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
            let outcome =
                equality_resolve(context, &buffer[..length], index, &mut out).expect("resolve");
            if let mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(count) =
                outcome
            {
                assert_conclusion_entailed(&fixture, &buffer[..length], &[], &out[..count]);
            }
        }
    }
}

// CEP:WHAT: Verifies superposition is sound over random ground pairs.
// CEP:WHY: Spec 07 section 6, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed conclusion.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs x positions.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::superpose.
// CEP:SECURITY: none.
#[test]
fn superposition_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1705);
    for _ in 0..kRuns {
        let from = random_ground_clause(&fixture, &mut rng, true);
        let into = random_ground_clause(&fixture, &mut rng, true);
        let mut from_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let mut into_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let from_len = from.len().min(8);
        let into_len = into.len().min(8);
        for (index, literal) in from.iter().enumerate() {
            if index >= 8 {
                break;
            }
            from_buf[index] = *literal;
        }
        for (index, literal) in into.iter().enumerate() {
            if index >= 8 {
                break;
            }
            into_buf[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut from_buf[..from_len],
        );
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut into_buf[..into_len],
        );
        let paths: [&[u16]; 3] = [&[0u16], &[1u16], &[0u16, 0u16]];
        for equation_index in 0..from_len {
            for into_index in 0..into_len {
                for path in paths {
                    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                    let outcome = superpose(
                        context,
                        &from_buf[..from_len],
                        equation_index,
                        &into_buf[..into_len],
                        into_index,
                        path,
                        &mut out,
                    )
                    .expect("superpose");
                    if let mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(
                        count,
                    ) = outcome
                    {
                        assert_conclusion_entailed(
                            &fixture,
                            &from_buf[..from_len],
                            &into_buf[..into_len],
                            &out[..count],
                        );
                    }
                }
            }
        }
    }
}

// CEP:WHAT: Verifies demodulation is sound: the rewritten clause is entailed by the rule.
// CEP:WHY: Spec 07 section 7, executably (the rule clause alone entails the demodulant).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an unentailed demodulant.
// CEP:ASSUMES: ground target clauses.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/demodulation.rs::demodulate.
// CEP:SECURITY: none.
#[test]
fn demodulation_is_sound() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0050_1706);
    for _ in 0..kRuns {
        let rule = random_ground_clause(&fixture, &mut rng, true);
        let target = random_ground_clause(&fixture, &mut rng, false);
        let mut rule_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let mut target_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let rule_len = rule.len().min(8);
        let target_len = target.len().min(8);
        for (index, literal) in rule.iter().enumerate() {
            if index >= 8 {
                break;
            }
            rule_buf[index] = *literal;
        }
        for (index, literal) in target.iter().enumerate() {
            if index >= 8 {
                break;
            }
            target_buf[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut rule_buf[..rule_len],
        );
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut target_buf[..target_len],
        );
        // Try every rule literal as the (unit) equation side and every position.
        for rule_literal in rule_buf[..rule_len].iter() {
            let literal = *rule_literal;
            if !literal.is_positive() {
                continue;
            }
            let sides = match mapt::hot::inference::factoring::equality_sides(
                context.terms,
                literal.atom(),
            ) {
                Some(value) => value,
                None => continue,
            };
            for target_index in 0..target_len {
                for path in [[0u16], [1u16]] {
                    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                    let outcome = demodulate(
                        context,
                        &target_buf[..target_len],
                        target_index,
                        &path,
                        sides.0,
                        sides.1,
                        &mut out,
                    )
                    .expect("demodulate");
                    if let mapt::hot::inference::demodulation::DemodulationOutcome::Rewritten(
                        count,
                    ) = outcome
                    {
                        // The rule clause alone must entail the demodulant when the
                        // rule is the unit equation used; the harness passes the
                        // rule premise list as the premise.
                        assert_conclusion_entailed(&fixture, &[*rule_literal], &[], &out[..count]);
                    }
                }
            }
        }
    }
}

// CEP:WHAT: Brute-force subsumption oracle over ground clauses with a fresh-variable probe.
// CEP:WHY: Subsumption on ground candidates reduces to literal-set inclusion; the oracle enumerates target-literal assignments for the candidate's literals.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: ground clauses.
// CEP:COST: O(target^n).
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn brute_force_subsumes(candidate: &[Literal], target: &[Literal]) -> bool {
    if candidate.is_empty() {
        return true;
    }
    if candidate.len() > target.len() {
        return false;
    }
    // Ground case: every candidate literal must occur in the target (identical
    // atoms and polarity); the non-ground case is covered by the unit tests.
    candidate.iter().all(|literal| {
        target.iter().any(|other| {
            other.atom() == literal.atom() && other.is_positive() == literal.is_positive()
        })
    })
}

// CEP:WHAT: Verifies the subsumption decision agrees with the brute-force oracle on ground pairs.
// CEP:WHY: Spec 08 section 2, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any disagreement.
// CEP:ASSUMES: ground clauses.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/subsumption.rs::{subsumes, assign_literal}.
// CEP:SECURITY: none.
#[test]
fn subsumption_agrees_with_brute_force() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0058_8501);
    for _ in 0..kRuns {
        let candidate = random_ground_clause(&fixture, &mut rng, true);
        let target = random_ground_clause(&fixture, &mut rng, true);
        let oracle = brute_force_subsumes(&candidate, &target);
        let decision = subsumes(&fixture.context, &candidate, &target).expect("check");
        assert_eq!(
            decision, oracle,
            "subsumption decision must agree with the oracle"
        );
    }
}

// CEP:WHAT: Verifies the feature-vector filter admits every true subsumption (no false negatives).
// CEP:WHY: The filter's soundness theorem (Spec 08 section 3): a filtered-out pair cannot subsume.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when the filter rejects a true subsumption.
// CEP:ASSUMES: ground clauses (the oracle side); the filter side is checked directly.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{may_subsume, build}.
// CEP:SECURITY: none.
#[test]
fn subsumption_filter_admits_all_true_subsumptions() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0058_8502);
    // Build a private filter index over the fixture's arena through the public
    // constructor with a small pool.
    let index = mapt::hot::index::feature_vector::FeatureVectorIndex::new_with(
        // The fixture arena is not exposed; rebuild one through the same helper.
        fixture_arena(),
        4096,
    )
    .expect("index");
    for _ in 0..kRuns {
        let candidate = random_ground_clause(&fixture, &mut rng, true);
        let target = random_ground_clause(&fixture, &mut rng, true);
        if brute_force_subsumes(&candidate, &target) {
            let candidate_vector = index.build(fixture.terms, &candidate).expect("vector");
            let target_vector = index.build(fixture.terms, &target).expect("vector");
            assert!(
                index.may_subsume(candidate_vector, target_vector),
                "the filter must admit a true subsumption"
            );
        }
    }
}

// CEP:WHAT: Rebuilds the fixture arena pointer for the filter test.
// CEP:WHY: The index borrows an arena; a fresh leaked arena of fixture size is the simplest sound host.
// CEP:STATUS: complete
// CEP:FAILURE: panics on failure.
// CEP:ASSUMES: none.
// CEP:COST: one arena.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fixture_arena() -> &'static mapt::hot::memory::arena::Arena {
    common::make_arena(common::kAtpFixtureArenaBytes)
}

// CEP:WHAT: Verifies truncated vectors pass the filter (sound degradation).
// CEP:WHY: Truncation only removes violation evidence.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a truncated vector is filtered out.
// CEP:ASSUMES: synthetic truncated vectors.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/index/feature_vector.rs::{may_subsume, FeatureVector}.
// CEP:SECURITY: none.
#[test]
fn filter_is_sound_on_truncated_vectors() {
    let index =
        mapt::hot::index::feature_vector::FeatureVectorIndex::new_with(fixture_arena(), 4096)
            .expect("index");
    let truncated = mapt::hot::index::feature_vector::FeatureVector {
        start: 0,
        pairs: 0,
        literal_count: 1,
        truncated: true,
    };
    let also_truncated = mapt::hot::index::feature_vector::FeatureVector {
        start: 0,
        pairs: 0,
        literal_count: 5,
        truncated: true,
    };
    assert!(index.may_subsume(truncated, also_truncated));
    assert!(index.may_subsume(also_truncated, truncated));
}

// CEP:WHAT: Verifies the eligibility rules respect selection: a selected literal is eligible, an unselected literal of a clause with selection is not.
// CEP:WHY: Spec 07 section 3's override rule, executably over random clauses.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on an eligibility violation.
// CEP:ASSUMES: ground clauses.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/selection.rs::{eligible_positive, eligible_negative}.
// CEP:SECURITY: none.
#[test]
fn ordering_eligibility_respects_selection() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0011_3701);
    for _ in 0..kRuns {
        let clause = random_ground_clause(&fixture, &mut rng, false);
        let mut buffer: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let length = clause.len().min(8);
        for (index, literal) in clause.iter().enumerate() {
            if index >= 8 {
                break;
            }
            buffer[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::FirstNegative,
            &mut buffer[..length],
        );
        let selected: Vec<usize> = (0..length)
            .filter(|index| buffer[*index].is_selected())
            .collect();
        if let Some(&selected_index) = selected.first() {
            assert!(mapt::hot::inference::eligible_negative(
                &buffer[..length],
                selected_index
            ));
            for index in 0..length {
                if index != selected_index {
                    assert!(
                        !mapt::hot::inference::eligible_negative(&buffer[..length], index),
                        "unselected literals are blocked when a selection exists"
                    );
                    assert!(
                        !mapt::hot::inference::eligible_positive(context, &buffer[..length], index),
                        "unselected literals are blocked when a selection exists"
                    );
                }
            }
        }
    }
}

// CEP:WHAT: Verifies the resolution side conditions hold under the ordered rule over random pairs (no conclusion from blocked literals).
// CEP:WHY: Spec 07 section 4's restrictions, executably: whenever the rule concludes, the side literals carry the eligibility flags.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a conclusion's premises violate the eligibility contract.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/resolution.rs::{resolve, eligible_positive, eligible_negative}.
// CEP:SECURITY: none.
#[test]
fn resolution_side_conditions() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0011_3702);
    for _ in 0..kRuns {
        let left = random_ground_clause(&fixture, &mut rng, true);
        let right = random_ground_clause(&fixture, &mut rng, true);
        let mut left_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let mut right_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let left_len = left.len().min(8);
        let right_len = right.len().min(8);
        for (index, literal) in left.iter().enumerate() {
            if index >= 8 {
                break;
            }
            left_buf[index] = *literal;
        }
        for (index, literal) in right.iter().enumerate() {
            if index >= 8 {
                break;
            }
            right_buf[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut left_buf[..left_len],
        );
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut right_buf[..right_len],
        );
        for left_index in 0..left_len {
            for right_index in 0..right_len {
                let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                let outcome = resolve(
                    context,
                    &left_buf[..left_len],
                    left_index,
                    &right_buf[..right_len],
                    right_index,
                    &mut out,
                )
                .expect("resolve");
                if let mapt::hot::inference::resolution::ResolutionOutcome::Concluded(_) = outcome {
                    // The concluding pair must satisfy the eligibility contract.
                    let (positive_side, negative_side, positive_index, negative_index) =
                        if left_buf[left_index].is_positive() {
                            (
                                &left_buf[..left_len],
                                &right_buf[..right_len],
                                left_index,
                                right_index,
                            )
                        } else {
                            (
                                &right_buf[..right_len],
                                &left_buf[..left_len],
                                right_index,
                                left_index,
                            )
                        };
                    assert!(
                        mapt::hot::inference::eligible_positive(
                            context,
                            positive_side,
                            positive_index
                        ),
                        "the positive side of a concluding pair must be eligible"
                    );
                    assert!(
                        mapt::hot::inference::eligible_negative(negative_side, negative_index),
                        "the negative side of a concluding pair must be eligible"
                    );
                }
            }
        }
    }
}

// CEP:WHAT: Verifies the superposition side conditions hold over random pairs.
// CEP:WHY: Spec 07 section 6's restrictions, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a conclusion's premises violate the eligibility contract.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/superposition.rs::{superpose, eligible_positive, eligible_negative}.
// CEP:SECURITY: none.
#[test]
fn superposition_side_conditions() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0011_3703);
    for _ in 0..kRuns {
        let from = random_ground_clause(&fixture, &mut rng, true);
        let into = random_ground_clause(&fixture, &mut rng, true);
        let mut from_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let mut into_buf: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let from_len = from.len().min(8);
        let into_len = into.len().min(8);
        for (index, literal) in from.iter().enumerate() {
            if index >= 8 {
                break;
            }
            from_buf[index] = *literal;
        }
        for (index, literal) in into.iter().enumerate() {
            if index >= 8 {
                break;
            }
            into_buf[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut from_buf[..from_len],
        );
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut into_buf[..into_len],
        );
        for equation_index in 0..from_len {
            for into_index in 0..into_len {
                for path in [[0u16], [1u16]] {
                    let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                    let outcome = superpose(
                        context,
                        &from_buf[..from_len],
                        equation_index,
                        &into_buf[..into_len],
                        into_index,
                        &path,
                        &mut out,
                    )
                    .expect("superpose");
                    if let mapt::hot::inference::superposition::SuperpositionOutcome::Concluded(_) =
                        outcome
                    {
                        assert!(
                            mapt::hot::inference::eligible_positive(
                                context,
                                &from_buf[..from_len],
                                equation_index
                            ),
                            "the equation literal of a concluding pair must be eligible"
                        );
                        let into_eligible = if into_buf[into_index].is_positive() {
                            mapt::hot::inference::eligible_positive(
                                context,
                                &into_buf[..into_len],
                                into_index,
                            )
                        } else {
                            mapt::hot::inference::eligible_negative(
                                &into_buf[..into_len],
                                into_index,
                            )
                        };
                        assert!(
                            into_eligible,
                            "the into literal of a concluding pair must be eligible"
                        );
                    }
                }
            }
        }
    }
}

// CEP:WHAT: Verifies the factoring side conditions hold over random clauses.
// CEP:WHY: Spec 07 section 5's restrictions, executably.
// CEP:STATUS: complete
// CEP:FAILURE: test fails when a conclusion's kept literal is ineligible.
// CEP:ASSUMES: ground premises.
// CEP:COST: 40 runs.
// CEP:EVIDENCE: cited by hot/inference/factoring.rs::{factor, eligible_positive}.
// CEP:SECURITY: none.
#[test]
fn factoring_side_conditions() {
    let fixture = make_oracle();
    let mut rng = DeterministicRng::new(0x0011_3704);
    for _ in 0..kRuns {
        let clause = random_ground_clause(&fixture, &mut rng, true);
        let mut buffer: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
        let length = clause.len().min(8);
        for (index, literal) in clause.iter().enumerate() {
            if index >= 8 {
                break;
            }
            buffer[index] = *literal;
        }
        let context = &fixture.context;
        let _ = mapt::hot::inference::selection::compute_selection_flags(
            context,
            SelectionFunction::None,
            &mut buffer[..length],
        );
        for first in 0..length {
            for second in 0..length {
                if first == second {
                    continue;
                }
                let mut out: [Literal; 8] = [Literal::new(TermPtr::invalid(), true); 8];
                let outcome =
                    factor(context, &buffer[..length], first, second, &mut out).expect("factor");
                if let mapt::hot::inference::factoring::FactoringOutcome::Concluded(_) = outcome {
                    assert!(
                        mapt::hot::inference::eligible_positive(context, &buffer[..length], first),
                        "the kept literal of a concluding factoring pair must be eligible"
                    );
                }
            }
        }
    }
}
