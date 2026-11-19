// CEP:FILE: hot/theory/congruence.rs
// CEP:WHAT: The congruence closure over the theory term graph (design 13.4, Nelson & Oppen 1980): union-find with path halving over ground terms, asserted-equality merging, and a signature-fixpoint that merges application nodes whose (function, class-representative arguments) signatures coincide.
// CEP:WHY: Design 13.4 defines the closure as the EUF theory's engine and the base of array reasoning: when an equality a = b is asserted the classes of a and b merge, and congruence propagates f(...,a,...) = f(...,b,...); the signature-fixpoint form recomputes every application node's signature per round, which is O(nodes) per merge instead of the use-list O(n log n) — the use-list version is the measured follow-up (ticket CEP-1070) and the node bound keeps the quadratic form honest (CEP&CC 22.10).
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns TheoryError on storage failures or past the fixpoint round bound (PropagationRounds); never panics.
// CEP:ASSUMES: single-threaded; the graph's unique-node invariant holds (hash-consing); reset() is called between checks.
// CEP:COST: assert_equal is O(alpha) amortized; one check round is O(nodes x arity); the fixpoint is O(merges x nodes x arity) bounded by the node capacity.
// CEP:EVIDENCE: unit/hot/theory_test.rs::{congruence_closes, congruence_propagates_through_arguments}.
// CEP:SECURITY: every loop is bounded by the node capacity; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; nodes are visited in id order and unions resolve by rank then node id (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;
use crate::sat::database::SatCoreError;
use mapt_config::limits::kMaxTheoryTerms;

use super::term_graph::{TermGraph, TermNode};
use super::TheoryError;

/// CEP:WHAT: The congruence closure: union-find over the term graph plus the signature-fixpoint merger.
/// CEP:WHY: Design 13.4; the closure is the EUF consistency engine and the only place that interprets the term graph's structure.
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError.
/// CEP:ASSUMES: one closure per graph; no node is created after the first check of a reset cycle.
/// CEP:COST: one union-find cell triple per node plus one signature scratch row.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
/// CEP:SECURITY: bounds-checked reads throughout.
pub struct CongruenceClosure<'a> {
    /// CEP:WHAT: Union-find parent per node (self until merged).
    /// CEP:WHY: The equivalence classes of design 13.4.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryTerms; reset before each check cycle.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounds-checked reads.
    parent: &'a [Cell<u32>],
    /// CEP:WHAT: Union rank per node.
    /// CEP:WHY: Union by rank keeps the find paths short; ties break toward the smaller node id for determinism.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryTerms.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounds-checked reads.
    rank: &'a [Cell<u32>],
    /// CEP:WHAT: The signature hash table: one representative node per occupied slot.
    /// CEP:WHY: The fixpoint's per-round collision detection; cleared at each round.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryTerms * 2.
    /// CEP:COST: 4 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounded probes.
    sig_table: &'a [Cell<u32>],
}

// CEP:WHAT: The empty signature-table slot sentinel.
// CEP:WHY: A named constant instead of a bare u32::MAX (CEP&CC 11.3); never a valid node id.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kMaxTheoryTerms < u32::MAX.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
// CEP:SECURITY: none.
const kEmptySlot: u32 = u32::MAX;

impl<'a> CongruenceClosure<'a> {
    /// CEP:WHAT: Constructs the closure over the graph.
    /// CEP:WHY: Design 4.1: every structure is fully built before use.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    /// CEP:ASSUMES: the arena has room for the union-find and signature arrays.
    /// CEP:COST: O(kMaxTheoryTerms) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<CongruenceClosure<'a>, TheoryError> {
        let parent = Self::alloc(arena, kMaxTheoryTerms)?;
        let rank = Self::alloc(arena, kMaxTheoryTerms)?;
        let sig_table = Self::alloc(arena, kMaxTheoryTerms * 2)?;
        let closure = CongruenceClosure {
            parent,
            rank,
            sig_table,
        };
        // Design 4.1: the structure is fully built before use - the arena arrays
        // are zeroed memory, so every class starts as a singleton.
        closure.reset();
        Ok(closure)
    }

    // CEP:WHAT: Allocates one u32 arena array.
    // CEP:WHY: One translation point for the arena error (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    // CEP:SECURITY: none.
    fn alloc(arena: &'a Arena, count: u32) -> Result<&'a [Cell<u32>], TheoryError> {
        let range = arena.alloc_array::<Cell<u32>>(count).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<u32>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: Resets every class to a singleton.
    /// CEP:WHY: The DPLL(T) loop re-asserts the full atom assignment per conflict cycle; one reset point keeps the state machine honest.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before each assertion batch.
    /// CEP:COST: O(kMaxTheoryTerms).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: none.
    pub fn reset(&self) {
        for node in 0..kMaxTheoryTerms as usize {
            self.parent[node].set(node as u32);
            self.rank[node].set(0);
        }
    }

    /// CEP:WHAT: Returns the class representative of a node (path halving).
    /// CEP:WHY: The read side of design 13.4's equivalence classes.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on an out-of-range node.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(alpha) amortized.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn find(&self, node: TermNode) -> Result<TermNode, TheoryError> {
        if node.0 >= kMaxTheoryTerms {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        let mut current = node.0;
        while self.parent[current as usize].get() != current {
            let grandparent = self.parent[self.parent[current as usize].get() as usize].get();
            self.parent[current as usize].set(grandparent);
            current = grandparent;
        }
        Ok(TermNode(current))
    }

    /// CEP:WHAT: Asserts an equality: merges the two nodes' classes (union by rank, ties toward the smaller id).
    /// CEP:WHY: Design 13.4: "when an equality a = b is asserted, union the equivalence classes of a and b"; the merge is lazy here and the congruence propagation happens in check.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on out-of-range nodes.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(alpha) amortized.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_closes.
    /// CEP:SECURITY: bounds-checked writes.
    pub fn assert_equal(&self, left: TermNode, right: TermNode) -> Result<(), TheoryError> {
        let a = self.find(left)?;
        let b = self.find(right)?;
        if a.0 == b.0 {
            return Ok(());
        }
        let (child, root) = if self.rank[a.0 as usize].get() > self.rank[b.0 as usize].get()
            || (self.rank[a.0 as usize].get() == self.rank[b.0 as usize].get() && a.0 < b.0)
        {
            (b, a)
        } else {
            (a, b)
        };
        self.parent[child.0 as usize].set(root.0);
        if self.rank[a.0 as usize].get() == self.rank[b.0 as usize].get() {
            self.rank[root.0 as usize].set(self.rank[root.0 as usize].get() + 1);
        }
        Ok(())
    }

    /// CEP:WHAT: Runs the congruence fixpoint: repeatedly recomputes every application node's signature (function symbol, class-representative arguments) and merges colliding classes, until a round merges nothing.
    /// CEP:WHY: Design 13.4's propagation rule "if a = b, then f(...,a,...) = f(...,b,...)"; the fixpoint is the bounded, allocation-free form of the use-list algorithm.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::PropagationRounds past the node-bound round limit (unreachable: each round merges at least one class or terminates).
    /// CEP:ASSUMES: called after the assertion batch.
    /// CEP:COST: O(merges x nodes x arity) worst case, bounded by the node capacity.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_propagates_through_arguments.
    /// CEP:SECURITY: bounded rounds and probes.
    pub fn check(&self, graph: &TermGraph<'a>) -> Result<(), TheoryError> {
        for _ in 0..kMaxTheoryTerms {
            if !self.one_round(graph)? {
                return Ok(());
            }
        }
        Err(TheoryError::PropagationRounds)
    }

    // CEP:WHAT: One signature-fixpoint round: rebuilds the signature table over all application nodes and unions every signature collision, comparing signatures explicitly so two different signatures that hash to one slot probe on instead of merging.
    // CEP:WHY: The propagation step of the closure; returns whether anything merged.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::HashTableFull past the table load bound (unreachable while nodes are at most half the table).
    // CEP:ASSUMES: called by check only.
    // CEP:COST: O(nodes x arity).
    // CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_propagates_through_arguments.
    // CEP:SECURITY: bounded probes.
    fn one_round(&self, graph: &TermGraph<'a>) -> Result<bool, TheoryError> {
        for slot in 0..self.sig_table.len() {
            self.sig_table[slot].set(kEmptySlot);
        }
        let mut merged = false;
        let count = graph.node_count();
        for index in 0..count {
            let node = TermNode(index);
            let arity = graph.node_arity(node)?;
            if arity == 0 {
                continue;
            }
            let symbol = graph.node_symbol(node)?;
            let mut hash: u64 = 0xCBF2_9CE4_8422_2325u64;
            hash ^= symbol as u64;
            hash = hash.wrapping_mul(0x100_0000_01B3);
            for slot in 0..arity {
                let argument = graph.node_argument(node, slot)?;
                let representative = self.find(argument)?;
                hash ^= representative.0 as u64;
                hash = hash.wrapping_mul(0x100_0000_01B3);
            }
            // Linear probe over the signature table: an empty slot claims the
            // signature; an occupied slot is compared by its full signature
            // (symbol and class-representative arguments) so a hash collision
            // between different signatures probes on instead of merging.
            let capacity = self.sig_table.len() as u64;
            let mut slot = (hash % capacity) as usize;
            for _ in 0..self.sig_table.len() {
                let entry = self.sig_table[slot].get();
                if entry == kEmptySlot {
                    self.sig_table[slot].set(index);
                    break;
                }
                if self.signatures_match(graph, TermNode(entry), node)? {
                    let other = self.find(TermNode(entry))?;
                    let mine = self.find(node)?;
                    if other.0 != mine.0 {
                        self.assert_equal(mine, other)?;
                        merged = true;
                    }
                    break;
                }
                slot = (slot + 1) % self.sig_table.len();
            }
        }
        Ok(merged)
    }

    // CEP:WHAT: Returns whether two application nodes share one signature: equal function symbols and pairwise equal class-representative arguments (all compared through the current find state).
    // CEP:WHY: The probe comparison of one_round; recomputing through find keeps the comparison correct across unions that happened earlier in the same round.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates TheoryError from the node reads.
    // CEP:ASSUMES: both nodes are application nodes of equal arity (checked here).
    // CEP:COST: O(arity).
    // CEP:EVIDENCE: unit/hot/theory_test.rs::congruence_propagates_through_arguments.
    // CEP:SECURITY: bounded reads.
    fn signatures_match(
        &self,
        graph: &TermGraph<'a>,
        left: TermNode,
        right: TermNode,
    ) -> Result<bool, TheoryError> {
        let left_symbol = graph.node_symbol(left)?;
        let right_symbol = graph.node_symbol(right)?;
        if left_symbol != right_symbol {
            return Ok(false);
        }
        let arity = graph.node_arity(left)?;
        if graph.node_arity(right)? != arity {
            return Ok(false);
        }
        for slot in 0..arity {
            let left_argument = graph.node_argument(left, slot)?;
            let right_argument = graph.node_argument(right, slot)?;
            if self.find(left_argument)?.0 != self.find(right_argument)?.0 {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
