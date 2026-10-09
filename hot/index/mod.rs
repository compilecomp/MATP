// CEP:FILE: hot/index/mod.rs
// CEP:WHAT: Term and clause indexing module: the discrimination tree (path index) of design 9.2.
// CEP:WHY: Design section 9 places indexing under hot/ as CEP-0/OPT-0; Phase 2 delivers the discrimination tree named in the build order; the feature-vector filter, substitution tree, perfect hash, and inverted index of design 9.1 are later phases (tickets CEP-1028, CEP-1029) and the index multiplexer of design 9.4 is deferred with them.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: none; module wiring only.
// CEP:ASSUMES: one arena, one term store per index.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs; property/discrimination_property_test.rs; bench CEP-BENCH-0008.
// CEP:SECURITY: node, entry, and query capacities are named and enforced.
// CEP:HPC-DETERMINISM: deterministic; tree shape is a pure function of the operation sequence.

pub mod discrimination_tree;

pub use discrimination_tree::{DiscriminationTree, IndexEntry, IndexError, IndexNode};
