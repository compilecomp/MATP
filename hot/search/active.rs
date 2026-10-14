// CEP:FILE: hot/search/active.rs
// CEP:WHAT: The active set (design 8.4/9): a dense slot array of processed clauses, the atom discrimination tree (every literal of every active clause, payload = clause offset + literal index), the rule discrimination tree (left sides of positive equations, payload additionally carrying the unit flag for demodulation), and the feature-vector filter (CEP-1028).
// CEP:WHY: Design 8.4: clauses are indexed for fast subsumption and rewriting when they move from passive to active; design 9.1-9.4: the discrimination tree answers unification-mode retrieval (a sound SUPERSET for both subsumption directions - query variables may match stored symbols and stored variables may match query symbols only widen the candidate set, never shrink it, so no true candidate is lost and the verifier discards the false positives), the rule tree answers rewriting queries by left-hand-side, and the feature-vector filter is the cheap first tier (design 9.3's two-level approach); deletion is swap-remove on the slot array plus tree deletes, and feature-pool garbage is accepted until arena reset (bounded, co-designed with CEP-1007); the waiting set of design 8.4 is AVATAR's (Phase 4) and is not built here (ticket CEP-1011).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns ActiveError (slot capacity, tree capacities, pool capacity, structural); never panics.
// CEP:ASSUMES: Single-threaded; one active set per search; clause records are immutable once stored (tree deletes re-read the literals through the store); tree payloads pack (clause offset, literal index, unit flag) into u64.
// CEP:COST: insert is O(literals x depth) tree walks plus the feature build; delete is O(literals x depth); retrieval is the tree's cost; measured within bench CEP-BENCH-0012, artifact benches/artifacts/atp_subsumption_filter.json.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_trees_updated, rule_tree_indexes_units}; unit/hot/feature_vector_test.rs; unit/hot/given_clause_test.rs::{backward_subsumption_removes, forward_subsumption_discards}.
// CEP:SECURITY: all capacities are named and enforced; tree walks are bounded by kIndexTermCapacity.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; slot order is insertion order modulo swap-remove, tree shapes are pure functions of the operation sequence.
// CEP:HPC-PASS-LEGALITY: Formal Spec 08 section 5 fixes the active-set invariants (every live slot's clause is indexed in the atom tree with one payload per literal, unit equations additionally in the rule tree, and every tree payload belongs to a live slot) and the retrieval-superset argument; the property tests verify executably that every true subsumption partner is among the retrieved candidates.

use crate::index::discrimination_tree::DiscriminationTree;
use crate::index::feature_vector::{FeatureError, FeatureVector, FeatureVectorIndex};
use crate::index::IndexError;
use crate::ir::clause::{ClauseError, ClauseStore};
use crate::ir::literal::Literal;
use crate::ir::term::{TermStore, TermTag};
use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::{
    kActiveSetCapacity, kDiscriminationTreeEntries, kDiscriminationTreeNodes,
    kFeatureVectorPoolWords,
};

/// CEP:WHAT: Error cases of the active set.
/// CEP:WHY: CEP&CC Law 6 vocabulary; the set never panics.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_capacity_enforced}.
/// CEP:SECURITY: capacity errors are the memory boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActiveError {
    /// CEP:WHAT: The slot capacity is exhausted.
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_capacity_enforced.
    /// CEP:SECURITY: memory bound.
    SlotsFull,
    /// CEP:WHAT: A tree capacity is exhausted.
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated.
    /// CEP:SECURITY: memory bound.
    Tree(IndexError),
    /// CEP:WHAT: The feature-vector pool is exhausted.
    /// CEP:WHY: Loud bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced.
    /// CEP:SECURITY: memory bound.
    Features(FeatureError),
    /// CEP:WHAT: The slot index is out of range (no such slot was ever inserted).
    /// CEP:WHY: An out-of-range removal is a caller bug, not a capacity fact; the honest kind names it instead of masquerading as SlotsFull.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    /// CEP:SECURITY: bounds-checked API.
    InvalidSlot,
    /// CEP:WHAT: A clause record read failed during an active-set operation.
    /// CEP:WHY: Tree deletes re-read the clause's literals through the store; an unreadable record is a storage failure and is reported as one, not as a tree failure.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the record was readable at insertion.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated.
    /// CEP:SECURITY: none.
    Store(ClauseError),
}

impl From<IndexError> for ActiveError {
    // CEP:WHAT: Converts tree errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated.
    // CEP:SECURITY: none.
    fn from(error: IndexError) -> ActiveError {
        ActiveError::Tree(error)
    }
}

impl From<FeatureError> for ActiveError {
    // CEP:WHAT: Converts feature-pool errors.
    // CEP:WHY: CEP&CC 33.18 translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/feature_vector_test.rs::pool_capacity_enforced.
    // CEP:SECURITY: none.
    fn from(error: FeatureError) -> ActiveError {
        ActiveError::Features(error)
    }
}

// CEP:WHAT: Bit shift of the literal index inside a packed tree payload.
// CEP:WHY: The payload layout (offset in the low 32 bits, literal index in bits 32..48, unit flag in bit 48) must be named at every pack/unpack site so the two sides cannot drift apart (CEP&CC 11.3 auditability).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: clause offsets fit 32 bits (arena capacity).
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_trees_updated, rule_tree_indexes_units}.
// CEP:SECURITY: none.
const kPayloadLiteralShift: u32 = 32;

// CEP:WHAT: Bit shift of the unit-equation flag inside a packed tree payload.
// CEP:WHY: The flag occupies bit 48, directly above the 16-bit literal index.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: literal indices fit 16 bits (kMaxClauseLiterals).
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::rule_tree_indexes_units.
// CEP:SECURITY: none.
const kPayloadUnitShift: u32 = 48;

// CEP:WHAT: Mask extracting the clause offset (the low word) of a packed payload.
// CEP:WHY: The unpacking side of the named layout.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: offsets occupy the low 32 bits.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/inference_test.rs::resolution_candidates_retrieved.
// CEP:SECURITY: none.
const kPayloadOffsetMask: u64 = 0xFFFF_FFFF;

// CEP:WHAT: Mask extracting the 16-bit literal index of a packed payload.
// CEP:WHY: The unpacking side of the named layout.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: literal indices occupy bits 32..48.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/inference_test.rs::resolution_candidates_retrieved.
// CEP:SECURITY: none.
const kPayloadLiteralMask: u64 = 0xFFFF;

// CEP:WHAT: Packs a clause offset, a literal index, and the unit-equation flag into one u64 tree payload.
// CEP:WHY: The discrimination tree's payload is a bare u64; the packing (offset in the low 32 bits, literal index in bits 32..48, unit flag in bit 48) keeps one tree for all literals without a side table, and the helpers make the layout explicit and auditable (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: offsets below 2^32 (arena capacity), literal indices below 2^16 (kMaxClauseLiterals).
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_trees_updated, rule_tree_indexes_units}; unit/hot/inference_test.rs::resolution_candidates_retrieved.
// CEP:SECURITY: none.
pub fn pack_payload(offset: u32, literal_index: u16, unit: bool) -> u64 {
    (offset as u64)
        | ((literal_index as u64) << kPayloadLiteralShift)
        | (u64::from(unit) << kPayloadUnitShift)
}

// CEP:WHAT: Unpacks a tree payload.
// CEP:WHY: The generator and subsumption checks decode candidates.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: payload came from pack_payload.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/inference_test.rs::resolution_candidates_retrieved.
// CEP:SECURITY: none.
pub fn unpack_payload(payload: u64) -> (u32, u16, bool) {
    (
        (payload & kPayloadOffsetMask) as u32,
        ((payload >> kPayloadLiteralShift) & kPayloadLiteralMask) as u16,
        (payload >> kPayloadUnitShift) & 1 == 1,
    )
}

/// CEP:WHAT: One active-set slot: the clause offset and its feature vector.
/// CEP:WHY: The dense array keeps iteration (superposition-from scans, backward subsumption) cache-friendly; the feature vector rides along for the subsumption pre-filter; Copy keeps swap-remove trivial.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: features built for exactly this clause.
/// CEP:COST: 16 bytes.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, forward_subsumption_uses_filter}.
/// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub struct ActiveSlot {
    /// CEP:WHAT: Clause record offset.
    /// CEP:WHY: The clause identity in the active set.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: store-produced.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    /// CEP:SECURITY: bounds-checked on use.
    pub offset: u32,
    /// CEP:WHAT: The clause's feature vector.
    /// CEP:WHY: The subsumption pre-filter input.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: built at insertion.
    /// CEP:COST: 12 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
    /// CEP:SECURITY: none.
    pub features: FeatureVector,
}

/// CEP:WHAT: The active set: slot array, atom tree, rule tree, and feature-vector pool.
/// CEP:WHY: Design 8.4 and 9; see the file header.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ActiveError.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/search_db_test.rs; unit/hot/given_clause_test.rs.
/// CEP:SECURITY: capacities bounded.
pub struct ActiveSet<'a> {
    /// CEP:WHAT: Dense slot array.
    /// CEP:WHY: Iteration and swap-remove storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: insert errors at the capacity.
    /// CEP:ASSUMES: slots[..count] are live.
    /// CEP:COST: 16 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_capacity_enforced}.
    /// CEP:SECURITY: capacity bound.
    slots: &'a [Cell<ActiveSlot>],
    /// CEP:WHAT: Number of live slots.
    /// CEP:WHY: Extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= slots.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    /// CEP:SECURITY: bounds checks.
    count: Cell<u32>,
    /// CEP:WHAT: The atom tree (every literal of every active clause).
    /// CEP:WHY: Resolution and subsumption candidate retrieval.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: insert/delete propagate tree errors.
    /// CEP:ASSUMES: one payload per (clause, literal).
    /// CEP:COST: see DiscriminationTree.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::active_trees_updated; unit/hot/inference_test.rs::resolution_candidates_retrieved.
    /// CEP:SECURITY: capacities bounded.
    atom_tree: DiscriminationTree<'a>,
    /// CEP:WHAT: The rule tree (left sides of positive equations; unit flag in the payload).
    /// CEP:WHY: Demodulation and superposition-from retrieval by left-hand side.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: insert/delete propagate tree errors.
    /// CEP:ASSUMES: one payload per positive equation literal.
    /// CEP:COST: see DiscriminationTree.
    /// CEP:EVIDENCE: unit/hot/search_db_test.rs::rule_tree_indexes_units.
    /// CEP:SECURITY: capacities bounded.
    rule_tree: DiscriminationTree<'a>,
    /// CEP:WHAT: The feature-vector pool.
    /// CEP:WHY: The subsumption pre-filter (design 9.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: build errors at the pool capacity.
    /// CEP:ASSUMES: never compacted.
    /// CEP:COST: see FeatureVectorIndex.
    /// CEP:EVIDENCE: unit/hot/feature_vector_test.rs; unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
    /// CEP:SECURITY: capacity bound.
    features: FeatureVectorIndex<'a>,
}

impl<'a> ActiveSet<'a> {
    // CEP:WHAT: Constructs the active set with the default capacities.
    // CEP:WHY: Production entry point.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns capacity errors when the arrays do not fit the arena.
    // CEP:ASSUMES: arena has room for the slot array, two trees, and the pool (about 120 MiB at the maximum caps; tests size arenas accordingly).
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    // CEP:SECURITY: capacities validated before allocation.
    pub fn new(arena: &'a Arena) -> Result<ActiveSet<'a>, ActiveError> {
        ActiveSet::new_with(
            arena,
            kActiveSetCapacity,
            kDiscriminationTreeNodes,
            kDiscriminationTreeEntries,
            kFeatureVectorPoolWords,
        )
    }

    // CEP:WHAT: Constructs the active set with explicit capacities.
    // CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns capacity errors on exhaustion; rejects zero capacities.
    // CEP:ASSUMES: all capacities >= 1; tree caps >= 1 node (the root).
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_capacity_enforced, active_trees_updated}; security/phase3_bounds_test.rs::active_capacity_enforced.
    // CEP:SECURITY: bounds validated.
    pub fn new_with(
        arena: &'a Arena,
        slot_capacity: u32,
        tree_nodes: u32,
        tree_entries: u32,
        pool_words: u32,
    ) -> Result<ActiveSet<'a>, ActiveError> {
        if slot_capacity == 0 {
            return Err(ActiveError::SlotsFull);
        }
        let slot_range = arena
            .alloc_array::<Cell<ActiveSlot>>(slot_capacity)
            .map_err(|_| ActiveError::SlotsFull)?;
        let slots = arena
            .array::<Cell<ActiveSlot>>(slot_range)
            .map_err(|_| ActiveError::SlotsFull)?;
        let atom_tree = DiscriminationTree::new_with_caps(arena, tree_nodes, tree_entries)?;
        let rule_tree = DiscriminationTree::new_with_caps(arena, tree_nodes, tree_entries)?;
        let features = FeatureVectorIndex::new_with(arena, pool_words)?;
        Ok(ActiveSet {
            slots,
            count: Cell::new(0),
            atom_tree,
            rule_tree,
            features,
        })
    }

    // CEP:WHAT: Inserts a clause into the active set: builds the feature vector, indexes every literal into the atom tree, indexes positive equations' left sides into the rule tree, and appends the slot; returns the slot index.
    // CEP:WHY: Design 8.4: insertion into all indexes happens exactly when the clause moves from passive to active (design 9.5), so every later query sees a consistent index set.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates ActiveError at any capacity.
    // CEP:ASSUMES: the clause is live in the store with at least one literal (the empty clause never becomes active).
    // CEP:COST: O(literals x depth) plus the feature build.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_trees_updated, rule_tree_indexes_units}.
    // CEP:SECURITY: capacities enforced.
    pub fn insert(
        &self,
        terms: &TermStore<'_>,
        offset: u32,
        literals: &[Literal],
    ) -> Result<u32, ActiveError> {
        let next = self.count.get() as usize;
        if next >= self.slots.len() {
            return Err(ActiveError::SlotsFull);
        }
        let features = self.features.build(terms, literals)?;
        let unit = literals.len() == 1;
        for (index, literal) in literals.iter().enumerate() {
            self.atom_tree.insert(
                terms,
                literal.atom(),
                pack_payload(offset, index as u16, false),
            )?;
            if literal.is_positive() {
                if let Ok(view) = terms.term(literal.atom()) {
                    if view.tag() == TermTag::Equality {
                        if let Ok(left) = view.child(0) {
                            self.rule_tree.insert(
                                terms,
                                left,
                                pack_payload(offset, index as u16, unit),
                            )?;
                        }
                    }
                }
            }
        }
        self.slots[next].set(ActiveSlot { offset, features });
        self.count.set(self.count.get() + 1);
        Ok(next as u32)
    }

    // CEP:WHAT: Removes a clause from the active set by slot index: deletes every tree payload, then swap-removes the slot.
    // CEP:WHY: Backward subsumption and later given-clause processing remove clauses; the tree deletes re-read the literals through the store so the caller passes no clause copy; swap-remove keeps the array dense.
    // CEP:STATUS: complete
    // CEP:FAILURE: InvalidSlot for out-of-range slot indices; Store for unreadable clause records; Tree propagates tree-delete failures.
    // CEP:ASSUMES: the slot is live; the clause record is readable.
    // CEP:COST: O(literals x depth).
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, active_trees_updated}; unit/hot/given_clause_test.rs::backward_subsumption_removes.
    // CEP:SECURITY: none.
    pub fn remove(
        &self,
        terms: &TermStore<'_>,
        store: &ClauseStore<'_>,
        slot: u32,
    ) -> Result<(), ActiveError> {
        let index = slot as usize;
        let count = self.count.get() as usize;
        if index >= count {
            return Err(ActiveError::InvalidSlot);
        }
        let record = self.slots[index].get();
        let clause = store
            .clause(crate::ir::clause::ClausePtr::from_u32(record.offset))
            .map_err(ActiveError::Store)?;
        let unit = clause.literal_count == 1;
        for position in 0..clause.literal_count {
            let literal = store
                .literal(clause, position)
                .map_err(ActiveError::Store)?;
            self.atom_tree.delete(
                terms,
                literal.atom(),
                pack_payload(record.offset, position, false),
            )?;
            if literal.is_positive() {
                if let Ok(view) = terms.term(literal.atom()) {
                    if view.tag() == TermTag::Equality {
                        if let Ok(left) = view.child(0) {
                            self.rule_tree.delete(
                                terms,
                                left,
                                pack_payload(record.offset, position, unit),
                            )?;
                        }
                    }
                }
            }
        }
        // Swap-remove: the last slot moves into the hole.
        let last = count - 1;
        if index != last {
            self.slots[index].set(self.slots[last].get());
        }
        self.count.set(last as u32);
        Ok(())
    }

    // CEP:WHAT: Returns the live slot record at an index.
    // CEP:WHY: Scans (superposition-from, backward subsumption) and tests read slots.
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) for out-of-range indices.
    // CEP:ASSUMES: index < count.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::{active_insert_delete, forward_subsumption_uses_filter}.
    // CEP:SECURITY: bounds-checked.
    pub fn slot(&self, index: u32) -> Option<ActiveSlot> {
        let slot = index as usize;
        if slot >= self.count.get() as usize {
            return None;
        }
        Some(self.slots[slot].get())
    }

    // CEP:WHAT: Returns the number of live slots.
    // CEP:WHY: Scan bounds and diagnostics.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    // CEP:SECURITY: none.
    pub fn len(&self) -> u32 {
        self.count.get()
    }

    // CEP:WHAT: Returns whether the active set holds no clauses.
    // CEP:WHY: The len/is_empty pair discipline (CEP&CC lint); the loop's saturation path and the tests read it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::active_insert_delete.
    // CEP:SECURITY: none.
    pub fn is_empty(&self) -> bool {
        self.count.get() == 0
    }

    // CEP:WHAT: Returns the atom tree for candidate retrieval.
    // CEP:WHY: The generator and subsumption checks query it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: read-only use.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/inference_test.rs::resolution_candidates_retrieved; unit/hot/given_clause_test.rs::{forward_subsumption_discards, backward_subsumption_removes}.
    // CEP:SECURITY: none.
    pub fn atom_tree(&self) -> &DiscriminationTree<'a> {
        &self.atom_tree
    }

    // CEP:WHAT: Returns the rule tree for rewriting retrieval.
    // CEP:WHY: The demodulation scan of simplify_given queries it with subterms of the given clause's literal atoms (the inter-clause inference phases scan the active array directly; ticket CEP-1027 tracks indexed retrieval).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: read-only use.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/given_clause_test.rs::demodulation_simplifies.
    // CEP:SECURITY: none.
    pub fn rule_tree(&self) -> &DiscriminationTree<'a> {
        &self.rule_tree
    }

    // CEP:WHAT: Returns the feature-vector pool.
    // CEP:WHY: The subsumption pre-filter reads vectors through it.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: read-only use.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/search_db_test.rs::forward_subsumption_uses_filter.
    // CEP:SECURITY: none.
    pub fn features(&self) -> &FeatureVectorIndex<'a> {
        &self.features
    }
}
