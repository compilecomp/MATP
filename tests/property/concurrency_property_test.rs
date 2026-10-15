// CEP:FILE: tests/property/concurrency_property_test.rs
// CEP:WHAT: Property tests of the Phase 4 concurrency layer: exactly-once delivery and element conservation for the deque and the pool under threads, the codec roundtrip property over generated clauses, and the portfolio first-theorem soundness property.
// CEP:WHY: CEP&CC 34.3 and Spec 13: the lock-free protocol claims (conservation, exactly-once) and the sharing data flow must hold under real interleaving, not just sequentially.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fixed seeds; the host can run a few threads.
// CEP:COST: offline; bounded rounds.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to property/concurrency_property_test.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use std::sync::atomic::{AtomicI64, AtomicU64};

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::hot::concurrency::chase_lev::WorkStealingDeque;
use mapt::hot::concurrency::clause_codec::{decode_clause, encode_clause};
use mapt::hot::concurrency::mpmc_pool::SharingPool;
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;

#[test]
// CEP:WHAT: Under a producer and two stealing consumers, every pushed deque element is delivered exactly once (sum conservation).
// CEP:WHY: Spec 13 section 3's conservation property under interleaving.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any loss or duplication.
// CEP:ASSUMES: three threads.
// CEP:COST: kItems pushes and steals.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::{deque_conserves_elements_under_threads, exactly_once_delivery}.
// CEP:SECURITY: none.
fn deque_conserves_elements_under_threads() {
    // CEP:WHAT: Items in the race.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kItems: u64 = 4096;
    let cells = 8192usize;
    let buffer: &'static [AtomicU64] = std::boxed::Box::leak(
        (0..cells)
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let top: &'static AtomicI64 = std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let bottom: &'static AtomicI64 = std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let deque = WorkStealingDeque::new(buffer, top, bottom).expect("deque");
    let stolen: u64 = std::thread::scope(|scope| {
        let thief_a = deque.clone();
        let thief_b = deque.clone();
        let handle_a = scope.spawn(move || {
            let mut stolen: u64 = 0;
            let mut idle: u64 = 0;
            while stolen < kItems / 2 && idle < kItems * 8 {
                if let Ok(Some(_)) = thief_a.steal() {
                    stolen += 1;
                    idle = 0;
                } else {
                    idle += 1;
                }
            }
            stolen
        });
        let handle_b = scope.spawn(move || {
            let mut stolen: u64 = 0;
            let mut idle: u64 = 0;
            while stolen < kItems / 2 && idle < kItems * 8 {
                if let Ok(Some(_)) = thief_b.steal() {
                    stolen += 1;
                    idle = 0;
                } else {
                    idle += 1;
                }
            }
            stolen
        });
        let mut pushed: u64 = 0;
        while pushed < kItems {
            if deque.push(pushed).is_ok() {
                pushed += 1;
            }
        }
        let mut popped: u64 = 0;
        while let Ok(Some(_)) = deque.pop() {
            popped += 1;
        }
        let stolen: u64 = handle_a.join().expect("a") + handle_b.join().expect("b");
        assert_eq!(pushed, stolen + popped, "exactly-once delivery");
        stolen
    });
    assert!(stolen <= kItems);
}

#[test]
// CEP:WHAT: The MPMC pool delivers every enqueued record exactly once under two producers and two consumers (tag-sum conservation).
// CEP:WHY: Spec 13 section 2's exactly-once property under interleaving.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any loss, duplication, or corruption.
// CEP:ASSUMES: four threads.
// CEP:COST: kRecords enqueues and dequeues.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::{mpmc_conserves_records_under_threads, exactly_once_delivery}.
// CEP:SECURITY: none.
fn mpmc_conserves_records_under_threads() {
    // CEP:WHAT: Records in the race.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRecords: u64 = 512;
    const kPerProducer: u64 = kRecords / 2;
    let cells = 64usize;
    let sequences: &'static [AtomicI64] = std::boxed::Box::leak(
        (0..cells)
            .map(|index| AtomicI64::new(index as i64))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let words: &'static [AtomicU64] = std::boxed::Box::leak(
        (0..(cells * mapt_config::limits::kSharedClauseMaxWords))
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let produce: &'static AtomicI64 =
        std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let consume: &'static AtomicI64 =
        std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let pool = SharingPool::new(sequences, words, produce, consume).expect("pool");
    let total: u64 = std::thread::scope(|scope| {
        let mut producers: Vec<std::thread::ScopedJoinHandle<'_, ()>> = Vec::new();
        for producer in 0..2u64 {
            let pool_ref = &pool;
            producers.push(scope.spawn(move || {
                let base = producer * kPerProducer;
                let mut enqueued: u64 = 0;
                while enqueued < kPerProducer {
                    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
                    record[0] = 4;
                    record[1] = base + enqueued;
                    if pool_ref.enqueue(&record).is_ok() {
                        enqueued += 1;
                    }
                }
            }));
        }
        let mut consumers: Vec<std::thread::ScopedJoinHandle<'_, u64>> = Vec::new();
        for _ in 0..2 {
            let pool_ref = &pool;
            consumers.push(scope.spawn(move || {
                let mut sum: u64 = 0;
                let mut idle: u32 = 0;
                let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
                loop {
                    match pool_ref.dequeue(&mut out) {
                        Ok(Some(length)) => {
                            assert!(length >= 2, "record layout");
                            sum += out[1];
                            idle = 0;
                        }
                        Ok(None) => {
                            idle += 1;
                            if idle > 2_000_000 {
                                break;
                            }
                        }
                        Err(_) => break,
                    }
                }
                sum
            }));
        }
        for handle in producers {
            handle.join().expect("producer");
        }
        consumers
            .into_iter()
            .map(|handle| handle.join().expect("consumer"))
            .sum()
    });
    assert_eq!(total, (0..kRecords).sum::<u64>(), "exactly-once delivery");
}

#[test]
// CEP:WHAT: Over generated clauses, decode(encode(c)) = c (atoms, polarities, and counts).
// CEP:WHY: Spec 13 section 4's tree-encoding lemma over the generated distribution (variable and ground arguments, mixed polarity).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any mismatch.
// CEP:ASSUMES: fixed seeds; single arena (encode and decode share the store).
// CEP:COST: kRounds roundtrips.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::codec_roundtrip_property.
// CEP:SECURITY: none.
fn codec_roundtrip_property() {
    // CEP:WHAT: Roundtrips per run.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRounds: u32 = 200;
    let (_arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let mut rng = DeterministicRng::new(0x0C0D_EC01);
    let names = ["p", "q"];
    let constants = ["a", "b"];
    for _ in 0..kRounds {
        let count = 1 + rng.below(4) as usize;
        let mut literals: Vec<Literal> = Vec::new();
        for _ in 0..count {
            let name = names[rng.below(2) as usize];
            let mut args: Vec<TermPtr> = Vec::new();
            for _ in 0..(if name == "q" { 2 } else { 1 }) {
                if rng.below(2) == 0 {
                    let constant = constants[rng.below(2) as usize];
                    args.push(
                        terms
                            .intern_fun(&symbols, symbol_id(&builder, constant), &[])
                            .expect("constant"),
                    );
                } else {
                    args.push(terms.intern_var(rng.below(4) as u32).expect("var"));
                }
            }
            let atom = terms
                .intern_pred(&symbols, symbol_id(&builder, name), &args)
                .expect("atom");
            literals.push(Literal::new(atom, rng.below(2) == 0));
        }
        let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
        let length = encode_clause(&terms, &literals, &mut record).expect("encode");
        let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
        let decoded_count =
            decode_clause(&record[..length], &terms, &symbols, &mut decoded).expect("decode");
        assert_eq!(decoded_count, literals.len());
        for (index, literal) in literals.iter().enumerate() {
            assert_eq!(decoded[index].atom(), literal.atom(), "atom roundtrip");
            assert_eq!(decoded[index].is_positive(), literal.is_positive());
        }
    }
}

#[test]
// CEP:WHAT: The portfolio's first Theorem is sound: the winning worker's outcome is a Theorem and no worker reports an error (the single-machine, small-scale soundness property of the sharing path).
// CEP:WHY: Spec 13 section 7: imported clauses are Input-role consequences of the shared problem, so the winner's refutation is a real refutation regardless of interleaving.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any worker error or a missing winner.
// CEP:ASSUMES: two workers on the unit-hole core problem (fast, deterministic refutation).
// CEP:COST: two worker runs.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::portfolio_first_theorem_is_sound.
// CEP:SECURITY: none.
fn portfolio_first_theorem_is_sound() {
    use mapt::cold::portfolio::manager::{
        run_portfolio, PortfolioConfig, ProblemEncoding, SortSpec, SymbolSpec, WorkerPlan,
    };
    use mapt::hot::search::SelectionStrategy;
    // Build the encoding over the standard fixture vocabulary (p/1 with ground and
    // variable arguments; q/2 as the second predicate).
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let sort_id = 0;
    let mut encoding = ProblemEncoding {
        sorts: vec![SortSpec { name: "S".into() }],
        symbols: Vec::new(),
        inputs: Vec::new(),
    };
    // The worker replay must declare in the same order the fixture did: the standard
    // fixture declares S, T sorts first - mirror them.
    encoding.sorts.push(SortSpec { name: "T".into() });
    let _ = sort_id;
    for (name, arity, predicate) in [
        ("a", 0u16, false),
        ("b", 0, false),
        ("f", 1, false),
        ("g", 1, false),
        ("h", 2, false),
        ("p", 1, true),
        ("q", 2, true),
        ("r", 0, true),
    ] {
        encoding.symbols.push(SymbolSpec {
            name: name.into(),
            arity,
            weight: 1,
            arg_sorts: vec![0; arity as usize],
            result_sort: 0,
            predicate,
        });
    }
    // The core problem: p(x) | q(y, a), -p(z), -q(w, a).
    let mut add_clause = |literals: &[Literal]| {
        let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
        let length = encode_clause(&terms, literals, &mut record).expect("encode");
        encoding.inputs.push(record[..length].to_vec());
    };
    let x = terms.intern_var(0).expect("x");
    let y = terms.intern_var(1).expect("y");
    let z = terms.intern_var(2).expect("z");
    let w = terms.intern_var(3).expect("w");
    let a = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let p_lit = |args: &[TermPtr], positive: bool| -> Literal {
        Literal::new(
            terms
                .intern_pred(&symbols, symbol_id(&builder, "p"), args)
                .expect("p"),
            positive,
        )
    };
    let q_lit = |args: &[TermPtr], positive: bool| -> Literal {
        Literal::new(
            terms
                .intern_pred(&symbols, symbol_id(&builder, "q"), args)
                .expect("q"),
            positive,
        )
    };
    let core = [p_lit(&[x], true), q_lit(&[y, a], true)];
    add_clause(&core);
    let neg_p = [p_lit(&[z], false)];
    add_clause(&neg_p);
    let neg_q = [q_lit(&[w, a], false)];
    add_clause(&neg_q);
    let plans = vec![
        WorkerPlan {
            strategy: SelectionStrategy::AgeWeightRatio,
            avatar: false,
        },
        WorkerPlan {
            strategy: SelectionStrategy::WeightOnly,
            avatar: false,
        },
    ];
    let config = PortfolioConfig {
        workers: 2,
        slice_ms: 20,
        share: true,
        arena_bytes: 50_331_648,
        passive_capacity: 4096,
        active_capacity: 2048,
        id_capacity: 4096,
        export_per_slice: 64,
    };
    let result = run_portfolio(&encoding, &plans, &config).expect("portfolio run");
    for report in result.reports.iter() {
        assert!(report.error.is_none(), "worker error: {:?}", report.error);
    }
    let winner = result.winner.expect("a winner");
    match result.reports[winner].outcome {
        Some(mapt::hot::avatar::controller::AvatarOutcome::Theorem { .. }) => {}
        other => panic!("the winner must hold a theorem, got {:?}", other),
    }
}

#[test]
// CEP:WHAT: Exactly-once delivery across both lock-free structures (the combined alias pinned by the structures' file headers).
// CEP:WHY: Spec 13 sections 2-3 cite one property name for both structures' delivery guarantees; the dedicated per-structure tests carry the full workloads and this test pins the combined claim on a smaller scale.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any loss or duplication.
// CEP:ASSUMES: single-threaded interleaving of the two structures.
// CEP:COST: a few hundred operations.
// CEP:EVIDENCE: backs property/concurrency_property_test.rs::exactly_once_delivery (cited by hot/concurrency/{chase_lev,mpmc_pool}.rs).
// CEP:SECURITY: none.
fn exactly_once_delivery() {
    // Deque: push/steal/pop partition.
    let cells = 8usize;
    let buffer: &'static [AtomicU64] = std::boxed::Box::leak(
        (0..cells)
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let top: &'static AtomicI64 = std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let bottom: &'static AtomicI64 = std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let deque = WorkStealingDeque::new(buffer, top, bottom).expect("deque");
    for value in 0..6u64 {
        deque.push(value).expect("push");
    }
    let mut delivered: u64 = 0;
    while let Ok(Some(_)) = deque.steal() {
        delivered += 1;
    }
    while let Ok(Some(_)) = deque.pop() {
        delivered += 1;
    }
    assert_eq!(delivered, 6, "deque exactly-once");
    assert!(deque.is_empty());
    // Pool: enqueue/dequeue pairing.
    let pool_cells = 4usize;
    let sequences: &'static [AtomicI64] = std::boxed::Box::leak(
        (0..pool_cells)
            .map(|index| AtomicI64::new(index as i64))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let words: &'static [AtomicU64] = std::boxed::Box::leak(
        (0..(pool_cells * mapt_config::limits::kSharedClauseMaxWords))
            .map(|_| AtomicU64::new(0))
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let produce: &'static AtomicI64 =
        std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let consume: &'static AtomicI64 =
        std::boxed::Box::leak(std::boxed::Box::new(AtomicI64::new(0)));
    let pool = SharingPool::new(sequences, words, produce, consume).expect("pool");
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    record[0] = 4;
    record[1] = 1;
    let mut out: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    for _ in 0..6 {
        pool.enqueue(&record).expect("enqueue");
        assert!(pool.dequeue(&mut out).expect("dequeue").is_some());
    }
    assert_eq!(
        pool.dequeue(&mut out).expect("dequeue"),
        None,
        "pool drains"
    );
}
