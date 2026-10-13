// CEP:FILE: hot/index/feature_vector.rs
// CEP:WHAT: Feature-vector index (design 9.3, CEP-1028): per-clause sparse (symbol, occurrence-count) vectors in a shared arena pool plus a sound subsumption pre-filter (literal count and per-symbol occurrence dominance).
// CEP:WHY: Design 9.3: subsumption queries first filter by feature vector (cheap, O(feature count)) and then verify with the discrimination tree and matching (expensive), reducing tree lookups 10-100x on typical benchmarks; the filter is SOUND, never complete: if C subsumes D (exists sigma with C sigma a subset of D), then every symbol occurrence of C has a corresponding occurrence in C sigma and hence in D (sigma only instantiates variables, never removes symbols), so occ(f, C) <= occ(f, D) for every f and |C| <= |D| - a violated dominance or literal-count check therefore rejects subsumption without false negatives; variables are excluded from the vectors (they are the wildcard side of matching) and clauses with more distinct symbols than kFeatureVectorSlots are unfilterable (truncated vectors pass every filter - a sound degradation documented at the constant).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns FeatureError (pool exhausted, slot capacity exceeded by the caller's slice contract); never panics; a truncated vector is reported, not an error.
// CEP:ASSUMES: Single-threaded use; the pool is never compacted on slot release (active-set deletion drops the reference; pool garbage is reclaimed only by arena reset, bounded by the pool capacity - co-designed with CEP-1007); vectors are sorted by symbol id ascending (build enforces it, filter relies on it).
// CEP:COST: build is O(symbols in the clause) with an insertion sort bounded by kFeatureVectorSlots; the dominance filter is O(|C| + |D|) two-pointer; measured in bench CEP-BENCH-0012, artifact benches/artifacts/atp_subsumption_filter.json.
// CEP:EVIDENCE: unit/hot/feature_vector_test.rs; property/inference_property_test.rs::{subsumption_filter_admits_all_true_subsumptions, filter_is_sound_on_truncated_vectors}; bench CEP-BENCH-0012.
// CEP:SECURITY: pool capacity is a memory-exhaustion bound; all reads are bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; vectors are symbol-id sorted, scans are index-ordered (CEP&CC 38.10).
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 3 fixes the filter's soundness theorem (occurrence dominance is necessary for subsumption) and the two-pointer dominance check; the property test verifies executably that no true subsumption is filtered out.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: the pool never reuses freed words (active-set deletion leaks until arena reset); compaction is deferred to the arena-level policy of ticket CEP-1007.

use crate::ir::literal::Literal;
use crate::ir::term::{TermStore, TermTag};
use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::{kFeatureVectorPoolWords, kFeatureVectorSlots};

/// CEP:WHAT: Error cases of the feature-vector index.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the index never panics and never silently drops a vector.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, pool_capacity_enforced}.
/// CEP:SECURITY: the pool bound is the memory-exhaustion boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeatureError {
    /// CEP:WHAT: The word pool is exhausted.
    /// CEP:WHY: Bounded pool memory; loud failure at the capacity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced.
    /// CEP:SECURITY: memory bound.
    PoolFull,
}

// CEP:WHAT: One (symbol, count) pair of a feature vector, packed into one u32 word each.
// CEP:WHY: Sparse vectors keep the memory per clause proportional to the distinct symbols (the average clause has few), and packing pairs as two consecutive u32 pool words avoids per-pair struct padding; symbol ids are bounded by kMaxSymbolCount and counts by the clause-literal bound, so u32 is exact.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: 8 bytes per pair.
// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
// CEP:SECURITY: none.
const kWordsPerPair: u32 = 2;

/// CEP:WHAT: A clause's feature vector handle: pool extent plus the literal count and the truncated flag.
/// CEP:WHY: The active set stores one handle per clause; the filter needs the literal count (subsumption necessary condition) and callers need the truncated flag to know the vector passed every dominance check by construction.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: handles come from FeatureVectorIndex::build.
/// CEP:COST: 12 bytes.
/// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, filter_is_sound_on_truncated_vectors}.
/// CEP:SECURITY: pool offsets are bounds-checked on every read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeatureVector {
    /// CEP:WHAT: First pool word of the vector.
    /// CEP:WHY: Extent start.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: valid pool offset.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    /// CEP:SECURITY: bounds-checked reads.
    pub start: u32,
    /// CEP:WHAT: Number of (symbol, count) pairs.
    /// CEP:WHY: Extent length.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kFeatureVectorSlots.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    /// CEP:SECURITY: none.
    pub pairs: u32,
    /// CEP:WHAT: Literal count of the clause.
    /// CEP:WHY: The |C| <= |D| necessary condition of subsumption.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: exact.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::dominance_filter_sound.
    /// CEP:SECURITY: none.
    pub literal_count: u32,
    /// CEP:WHAT: Whether the vector was truncated at kFeatureVectorSlots (unfilterable).
    /// CEP:WHY: A truncated vector passed every dominance check by construction, not by evidence; the caller must know to fall through to full verification.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: set by build.
    /// CEP:COST: 4 bytes (bool plus padding).
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::filter_is_sound_on_truncated_vectors.
    /// CEP:SECURITY: none.
    pub truncated: bool,
}

/// CEP:WHAT: The feature-vector index: a monotonic word pool plus the append cursor.
/// CEP:WHY: Design 9.3; owning the pool and cursor in one type makes the invariants (words appended in pairs, vectors sorted by symbol, pool garbage bounded) local and testable; there is no per-clause side array - the caller holds the handles - so active-set swap-remove is a handle drop, not an index mutation.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see FeatureError.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/feature_vector_test.rs; property/inference_property_test.rs::subsumption_filter_admits_all_true_subsumptions.
/// CEP:SECURITY: pool capacity bounded.
pub struct FeatureVectorIndex<'a> {
    /// CEP:WHAT: Word pool (symbol, count pairs concatenated).
    /// CEP:WHY: Shared storage for all vectors.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: appends error at the capacity.
    /// CEP:ASSUMES: never compacted.
    /// CEP:COST: 4 bytes per word.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, pool_capacity_enforced}.
    /// CEP:SECURITY: capacity bound.
    pool: &'a [Cell<u32>],
    /// CEP:WHAT: Number of words appended.
    /// CEP:WHY: The append cursor.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= pool.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced.
    /// CEP:SECURITY: bounds checks on every read.
    used: Cell<u32>,
}

// CEP:WHAT: Mutable accumulator of one feature-vector build: the (symbol, count) pairs, the pair count, and the degradation flags.
// CEP:WHY: Bundling the collect recursion's out-parameters keeps the walk's signature within the argument discipline (CEP&CC Law 5) and makes the build's state one auditable object.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: one instance per build call.
// CEP:COST: about 2 KiB on the stack.
// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, counts_are_per_symbol}.
// CEP:SECURITY: none.
struct CollectState {
    /// CEP:WHAT: The (symbol, count) pairs.
    /// CEP:WHY: The vector under construction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: pairs beyond pair_count are zero.
    /// CEP:COST: kFeatureVectorSlots x 8 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    /// CEP:SECURITY: none.
    symbols: [(u32, u32); kFeatureVectorSlots as usize],
    /// CEP:WHAT: Number of live pairs.
    /// CEP:WHY: Fill level.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= symbols.len().
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    /// CEP:SECURITY: none.
    pair_count: usize,
    /// CEP:WHAT: Pair-capacity overflow flag.
    /// CEP:WHY: Sound degradation marker.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::filter_is_sound_on_truncated_vectors.
    /// CEP:SECURITY: none.
    truncated: bool,
    /// CEP:WHAT: Depth-overflow flag.
    /// CEP:WHY: Unreachable for store-interned terms; kept for the guard's honesty.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::deep_terms_count_all_levels.
    /// CEP:SECURITY: none.
    depth_overflow: bool,
}

impl Default for CollectState {
    // CEP:WHAT: Zeroed initial state.
    // CEP:WHY: Arrays beyond 32 elements have no derived Default (CEP&CC 22.6 discipline); the manual impl is the explicit zeroing.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    // CEP:SECURITY: none.
    fn default() -> Self {
        CollectState {
            symbols: [(0, 0); kFeatureVectorSlots as usize],
            pair_count: 0,
            truncated: false,
            depth_overflow: false,
        }
    }
}

impl<'a> FeatureVectorIndex<'a> {
    // CEP:WHAT: Constructs the index with the default pool capacity.
    // CEP:WHY: Production entry point.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns PoolFull when the array does not fit the arena.
    // CEP:ASSUMES: arena has room for kFeatureVectorPoolWords words.
    // CEP:COST: O(capacity) one-time allocation.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    // CEP:SECURITY: capacity validated before allocation.
    pub fn new(arena: &'a Arena) -> Result<FeatureVectorIndex<'a>, FeatureError> {
        FeatureVectorIndex::new_with(arena, kFeatureVectorPoolWords)
    }

    // CEP:WHAT: Constructs the index with an explicit pool capacity.
    // CEP:WHY: CEP&CC 34.3: capacity tests run at small scales on the production code path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns PoolFull when the array does not fit; rejects zero capacity.
    // CEP:ASSUMES: capacity >= 1.
    // CEP:COST: O(capacity) one-time.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced; security/phase3_bounds_test.rs::feature_pool_capacity_enforced.
    // CEP:SECURITY: bounds validated before allocation.
    pub fn new_with(
        arena: &'a Arena,
        capacity: u32,
    ) -> Result<FeatureVectorIndex<'a>, FeatureError> {
        if capacity == 0 {
            return Err(FeatureError::PoolFull);
        }
        let range = arena
            .alloc_array::<Cell<u32>>(capacity)
            .map_err(|_| FeatureError::PoolFull)?;
        let pool = arena
            .array::<Cell<u32>>(range)
            .map_err(|_| FeatureError::PoolFull)?;
        Ok(FeatureVectorIndex {
            pool,
            used: Cell::new(0),
        })
    }

    // CEP:WHAT: Builds the feature vector of one clause: walks every literal's atom, counts function and predicate symbol occurrences (variables excluded), sorts by symbol id, and appends the pairs to the pool.
    // CEP:WHY: Design 9.3's per-clause feature vector; the walk is depth-guarded recursion over interned terms (same discipline as the discrimination-tree flatten); equality atoms contribute their two argument-side symbols but no equality pseudo-entry (the pseudo-symbol is an index-space sentinel, not a term symbol).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns PoolFull when the pairs do not fit; unreadable atoms surface as empty vectors with truncated = true (the filter then passes them - sound, documented) only when the term store rejects reads, which cannot happen for store-interned atoms (law 3: construction validated them).
    // CEP:ASSUMES: literals' atoms were interned by the given term store.
    // CEP:COST: O(total term nodes) with an insertion sort bounded by kFeatureVectorSlots.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{vectors_store_counts, counts_are_per_symbol, equality_atoms_contribute_arguments}; property/inference_property_test.rs::subsumption_filter_admits_all_true_subsumptions.
    // CEP:SECURITY: depth-bounded recursion (CEP&CC 22.10).
    pub fn build(
        &self,
        terms: &TermStore<'_>,
        literals: &[Literal],
    ) -> Result<FeatureVector, FeatureError> {
        let mut state = CollectState::default();
        for literal in literals.iter() {
            self.collect(terms, literal.atom(), &mut state, 0);
        }
        // Insertion sort by symbol id (stable, allocation-free).
        for i in 1..state.pair_count {
            let mut j = i;
            while j > 0 && state.symbols[j].0 < state.symbols[j - 1].0 {
                state.symbols.swap(j, j - 1);
                j -= 1;
            }
        }
        let start = self.used.get();
        let words_needed = (state.pair_count as u32) * kWordsPerPair;
        if start + words_needed > self.pool.len() as u32 {
            return Err(FeatureError::PoolFull);
        }
        for (index, pair) in state.symbols[..state.pair_count].iter().enumerate() {
            self.pool[start as usize + index * 2].set(pair.0);
            self.pool[start as usize + index * 2 + 1].set(pair.1);
        }
        self.used.set(start + words_needed);
        Ok(FeatureVector {
            start,
            pairs: state.pair_count as u32,
            literal_count: literals.len() as u32,
            truncated: state.truncated || state.depth_overflow,
        })
    }

    // CEP:WHAT: Recursively counts symbol occurrences of one term into the pair array.
    // CEP:WHY: Shared by atoms of every tag; variables are skipped (wildcards), function and predicate symbols counted, children recursed in order; the depth guard mirrors the intern-time bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: sets the truncated flag when the pair array fills (the rest of the walk still terminates via the depth bound and pair cap).
    // CEP:ASSUMES: atom was interned by the store.
    // CEP:COST: O(term nodes).
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{counts_are_per_symbol, deep_terms_count_all_levels}.
    // CEP:SECURITY: depth-bounded.
    fn collect(
        &self,
        terms: &TermStore<'_>,
        term: crate::ir::term::TermPtr,
        state: &mut CollectState,
        depth: u32,
    ) {
        if depth > mapt_config::limits::kMaxTermDepth as u32 {
            state.depth_overflow = true;
            return;
        }
        let view = match terms.term(term) {
            Ok(value) => value,
            Err(_) => {
                state.depth_overflow = true;
                return;
            }
        };
        match view.tag() {
            TermTag::Variable => {}
            TermTag::Function | TermTag::Predicate => {
                let symbol = view.symbol();
                let mut found = false;
                for entry in state.symbols[..state.pair_count].iter_mut() {
                    if entry.0 == symbol {
                        entry.1 += 1;
                        found = true;
                        break;
                    }
                }
                if !found {
                    if state.pair_count < state.symbols.len() {
                        state.symbols[state.pair_count] = (symbol, 1);
                        state.pair_count += 1;
                    } else {
                        state.truncated = true;
                    }
                }
                for child in view.children() {
                    self.collect(terms, child, state, depth + 1);
                }
            }
            TermTag::Equality => {
                // Equality atoms have exactly two children and no symbol-table entry
                // (tag-fixed term); count the arguments' symbols only.
                for child in view.children() {
                    self.collect(terms, child, state, depth + 1);
                }
            }
            TermTag::Application | TermTag::Lambda | TermTag::Sort => {
                // Higher-order and sort tags are Phase 5; their symbols are counted
                // like function symbols so the filter stays sound if they appear.
                let symbol = view.symbol();
                let mut found = false;
                for entry in state.symbols[..state.pair_count].iter_mut() {
                    if entry.0 == symbol {
                        entry.1 += 1;
                        found = true;
                        break;
                    }
                }
                if !found {
                    if state.pair_count < state.symbols.len() {
                        state.symbols[state.pair_count] = (symbol, 1);
                        state.pair_count += 1;
                    } else {
                        state.truncated = true;
                    }
                }
                for child in view.children() {
                    self.collect(terms, child, state, depth + 1);
                }
            }
        }
    }

    // CEP:WHAT: Reads one (symbol, count) pair of a vector.
    // CEP:WHY: The filter and tests read vectors pair-wise; bounds-checked so forged handles fail loudly.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-extent indices.
    // CEP:ASSUMES: vector came from build.
    // CEP:COST: 2 loads.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::vectors_store_counts.
    // CEP:SECURITY: bounds-checked.
    pub fn pair(&self, vector: FeatureVector, index: u32) -> Option<(u32, u32)> {
        if index >= vector.pairs {
            return None;
        }
        let slot = vector.start as usize + index as usize * 2;
        if slot + 1 >= self.pool.len() {
            return None;
        }
        Some((self.pool[slot].get(), self.pool[slot + 1].get()))
    }

    // CEP:WHAT: Sound subsumption pre-filter: true when candidate might subsume the target (no necessary condition violated), false when subsumption is impossible.
    // CEP:WHY: Design 9.3 and Spec 08 section 3: C subsumes D implies |C| <= |D| and occ(f, C) <= occ(f, D) for every symbol f (sigma only instantiates); the two-pointer scan over symbol-sorted vectors checks exactly these conditions; truncated vectors (either side) pass - sound because truncation only removes evidence of violation.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (bool answer; the filter never claims subsumption, only possibility).
    // CEP:ASSUMES: both vectors came from build (symbol-sorted).
    // CEP:COST: O(|C| + |D|) two-pointer.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::{dominance_filter_sound, dominance_filter_rejects, literal_count_filter_rejects}; property/inference_property_test.rs::subsumption_filter_admits_all_true_subsumptions.
    // CEP:SECURITY: none.
    pub fn may_subsume(&self, candidate: FeatureVector, target: FeatureVector) -> bool {
        if candidate.truncated || target.truncated {
            return true;
        }
        if candidate.literal_count > target.literal_count {
            return false;
        }
        let mut i: u32 = 0;
        let mut j: u32 = 0;
        while i < candidate.pairs && j < target.pairs {
            let (candidate_symbol, candidate_count) = match self.pair(candidate, i) {
                Some(value) => value,
                None => return true,
            };
            let (target_symbol, target_count) = match self.pair(target, j) {
                Some(value) => value,
                None => return true,
            };
            if candidate_symbol == target_symbol {
                if candidate_count > target_count {
                    return false;
                }
                i += 1;
                j += 1;
            } else if candidate_symbol > target_symbol {
                // The candidate needs a symbol the target does not carry past this
                // point: occurrence dominance is violated.
                j += 1;
            } else {
                return false;
            }
        }
        true
    }

    // CEP:WHAT: Returns the number of pool words in use.
    // CEP:WHY: Capacity introspection for tests and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced.
    // CEP:SECURITY: none.
    pub fn used_words(&self) -> u32 {
        self.used.get()
    }
}
