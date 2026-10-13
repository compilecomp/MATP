// CEP:FILE: hot/index/mod.rs
// CEP:WHAT: Term and clause indexing module: the discrimination tree (path index) of design 9.2 and the feature-vector filter of design 9.3.
// CEP:WHY: Design section 9 places indexing under hot/ as CEP-0/OPT-0; Phase 2 delivered the discrimination tree named in the build order and Phase 3 adds the feature-vector subsumption pre-filter (CEP-1028, design 26 Phase 3 given-clause dependencies); the substitution tree, perfect hash, and inverted index of design 9.1 and the index multiplexer of design 9.4 remain ticketed (CEP-1029, narrowed to the types with consumers).
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
pub mod feature_vector;

pub use discrimination_tree::{DiscriminationTree, IndexEntry, IndexError, IndexNode};
pub use feature_vector::{FeatureError, FeatureVector, FeatureVectorIndex};
