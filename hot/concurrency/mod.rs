// CEP:FILE: hot/concurrency/mod.rs
// CEP:WHAT: The concurrency module (design 19): the Chase-Lev work-stealing deque, the bounded MPMC clause-sharing pool, and the portable clause codec - all storage-agnostic algorithms over caller-supplied atomic storage.
// CEP:WHY: Design 26 Phase 4 and CEP&CC 25.3.1: the hot crate is no_std and allocation-free, so the lock-free structures (design 19.4: no locks, no condition variables, atomics with explicit memory ordering per CEP&CC 8.43) carry only the protocols while the CEP-1 portfolio manager owns the storage; this split keeps the hand-rolled concurrency inside the audited CEP-0 boundary and the allocation inside CEP-1 where it belongs.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: storage is caller-supplied, outlives every handle, and is zero/sequence-initialized per structure contract.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/chase_lev_test.rs; unit/hot/mpmc_pool_test.rs; unit/hot/clause_codec_test.rs; property/concurrency_property_test.rs.
// CEP:SECURITY: no interior mutability beyond the supplied atomics; every capacity named.
// CEP:UNSAFE: none; the module is safe Rust.
// CEP:HPC-DETERMINISM: single-threaded use is deterministic; cross-thread delivery order is scheduling-dependent by design (design 19.5) with exactly-once delivery.
// CEP:HPC-PASS-LEGALITY: Formal Spec 13 (13_portfolio_concurrency.md) fixes the pool and deque protocols, the memory-ordering tables, the linearization points, and the ABA arguments; every legality comment in this module cites it.

pub mod chase_lev;
pub mod clause_codec;
pub mod mpmc_pool;

pub use chase_lev::{DequeError, WorkStealingDeque};
pub use clause_codec::{decode_clause, encode_clause, CodecError};
pub use mpmc_pool::{PoolError, SharingPool};
