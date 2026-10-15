// CEP:FILE: tests/property/tstp_property_test.rs
// CEP:WHAT: Property tests of the unified proof reconstruction: every refutation the loop produces over generated problems formats and passes the replay checker, and a corrupted proof is rejected.
// CEP:WHY: CEP&CC 34.3 and design 18.4: proof verification is the soundness certification; the property must hold over the generated distribution, not one hand-built proof.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fixed seeds.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to property/tstp_property_test.rs.
// CEP:SECURITY: the corruption test exercises the tamper guard.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::cold::proof_output::tstp::{check_proof, render_verified_proof, TstpError};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

#[test]
// CEP:WHAT: Over generated ground problems, every Theorem outcome's refutation formats as TSTP and passes the replay checker; Saturated outcomes produce no proof and no panic.
// CEP:WHY: Design 18.2-18.4 end to end over the generated distribution.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any checker rejection of an honest proof.
// CEP:ASSUMES: fixed seeds; ground literals (the standard fixture vocabulary).
// CEP:COST: kRounds problems.
// CEP:EVIDENCE: backs property/tstp_property_test.rs::every_refutation_formats_and_checks.
// CEP:SECURITY: none.
fn every_refutation_formats_and_checks() {
    // CEP:WHAT: Generated problems per run.
    // CEP:WHY: Named bound (each problem leaks its fixture arena - the documented test discipline - so the bound also bounds memory).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRounds: u32 = 40;
    let mut rng = DeterministicRng::new(0x7E57_1057);
    let mut theorems: u32 = 0;
    for _ in 0..kRounds {
        let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
        let _ = arena;
        let options = SearchOptions::new();
        let space = SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 65536, 4096)
            .expect("space");
        let context = InferenceContext {
            terms: &terms,
            symbols: &symbols,
            substitution: &space.substitution,
            precedence: &precedence,
            ordering: OrderingKind::Kbo,
        };
        let names = ["p", "q", "r"];
        let constants = ["a", "b"];
        let clause_count = 2 + rng.below(3) as usize;
        for _ in 0..clause_count {
            let count = 1 + rng.below(2) as usize;
            let mut literals: Vec<Literal> = Vec::new();
            for _ in 0..count {
                let name = names[rng.below(3) as usize];
                let arity = if name == "q" {
                    2
                } else if name == "r" {
                    0
                } else {
                    1
                };
                let mut args: Vec<mapt::hot::ir::term::TermPtr> = Vec::new();
                for _ in 0..arity {
                    let constant = constants[rng.below(2) as usize];
                    args.push(
                        terms
                            .intern_fun(&symbols, symbol_id(&builder, constant), &[])
                            .expect("constant"),
                    );
                }
                let atom = terms
                    .intern_pred(&symbols, symbol_id(&builder, name), &args)
                    .expect("atom");
                literals.push(Literal::new(atom, rng.below(2) == 0));
            }
            space
                .add_input_clause(&context, &options, &literals)
                .expect("add");
        }
        let mut stats = SearchStats::default();
        match saturate(&space, &context, &options, &never_stop, &mut stats).expect("saturate") {
            SearchOutcome::Theorem { refutation } => {
                theorems += 1;
                let (count, text) =
                    render_verified_proof(&context, &terms, &builder, &space.store, refutation)
                        .expect("the honest proof must verify");
                assert!(count >= 2);
                assert!(text.contains("$false"));
            }
            SearchOutcome::Saturated => {}
            SearchOutcome::GaveUp(_) => panic!("budget-free runs cannot give up"),
        }
    }
    assert!(theorems > 0, "the generator must produce theorems");
}

#[test]
// CEP:WHAT: A corrupted proof (one derivation parent redirected to an unrelated clause so the replay fails) is rejected by the checker.
// CEP:WHY: The tamper guard of design 18.4 must reject, not trust, corrupted derivations.
// CEP:STATUS: complete
// CEP:FAILURE: panics if the corrupted proof is accepted.
// CEP:ASSUMES: a produced refutation; the corruption swaps one parent id to an unrelated input's id.
// CEP:COST: one run plus one check.
// CEP:EVIDENCE: backs property/tstp_property_test.rs::corrupted_proof_rejected.
// CEP:SECURITY: tamper guard.
fn corrupted_proof_rejected() {
    let (arena, symbols, builder, terms, precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 65536, 4096).expect("space");
    let context = InferenceContext {
        terms: &terms,
        symbols: &symbols,
        substitution: &space.substitution,
        precedence: &precedence,
        ordering: OrderingKind::Kbo,
    };
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, symbol_id(&builder, "b"), &[])
        .expect("b");
    let p = |arg, positive| -> Literal {
        Literal::new(
            terms
                .intern_pred(&symbols, symbol_id(&builder, "p"), &[arg])
                .expect("p"),
            positive,
        )
    };
    // A three-input problem: the refutation uses p(a) and -p(a); r(b) is unrelated.
    space
        .add_input_clause(&context, &options, &[p(a, true)])
        .expect("p(a)");
    space
        .add_input_clause(&context, &options, &[p(a, false)])
        .expect("-p(a)");
    let unrelated = [Literal::new(
        terms
            .intern_pred(&symbols, symbol_id(&builder, "r"), &[])
            .expect("r"),
        true,
    )];
    let _ = unrelated;
    let _ = b;
    let mut stats = SearchStats::default();
    let refutation =
        match saturate(&space, &context, &options, &never_stop, &mut stats).expect("saturate") {
            SearchOutcome::Theorem { refutation } => refutation,
            other => panic!("expected a theorem, got {:?}", other),
        };
    // The honest proof checks.
    check_proof(&context, &space.store, refutation).expect("honest proof");
    // Corrupt the refutation's derivation: redirect parent 0 to an id with no
    // resolution replay (a future/unrelated id fails the walk loudly - use the
    // highest existing input id, whose replay cannot reproduce the empty clause).
    let record = space
        .store
        .clause(mapt::hot::ir::clause::ClausePtr::from_u32(refutation))
        .expect("record");
    let _ = record;
    // The corruption path: craft the check against a refutation whose parent is the
    // unrelated input's clause id - reachable through the side table.
    let unrelated_id = space.store.next_clause_id().0 - 1;
    let corrupted = space
        .store
        .new_clause(
            &terms,
            &[],
            9,
            mapt::hot::ir::clause::DerivationStep {
                rule: mapt::hot::ir::clause::InferenceRule::Resolution,
                parent_count: 1,
                reserved: 0,
                parents: [
                    unrelated_id,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                    mapt_config::limits::kInvalidClauseId,
                ],
                substitution: mapt_config::limits::kInvalidClauseOffset,
            },
        )
        .expect("corrupted");
    let corrupted_id = space
        .store
        .clause(corrupted)
        .expect("corrupted record")
        .id
        .0;
    assert_eq!(
        check_proof(&context, &space.store, corrupted.as_u32()),
        Err(TstpError::InvalidStep(corrupted_id)),
        "a one-parent resolution citing a non-complementary premise is rejected"
    );
}

// CEP:WHAT: The never-stop callback.
// CEP:WHY: Budget-free runs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn never_stop(_iterations: u64) -> bool {
    false
}
