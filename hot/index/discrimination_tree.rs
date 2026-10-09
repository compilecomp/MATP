// CEP:FILE: hot/index/discrimination_tree.rs
// CEP:WHAT: Discrimination tree (path index): a trie over the flat preorder symbol sequences of terms, with variable edges, intrusive sibling links, and per-leaf payload lists, supporting insert, delete, and retrieval under the design 9.2 matching rule.
// CEP:WHY: Design 9.2: the discrimination tree is the primary index for subsumption and rewriting ("without it, subsumption and rewriting are O(n^2)"); it is chosen over substitution trees for cache behavior, its nodes are allocated contiguously in the arena with child pointers as offsets not addresses, and the retrieval semantics are fixed by the design: "Variables in the query match any symbol" -- one tree edge per query symbol, so the index is an exact filter under that rule and callers post-verify candidates with the matching engine (design 9.3 two-level discipline); Formal Spec 04 fixes the soundness and completeness statements.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns IndexError::TreeFull at the node cap, IndexError::EntryBudgetExceeded at the payload cap, IndexError::ArenaFull on arena exhaustion, IndexError::InvalidTerm for unreadable terms, IndexError::TermTooLarge past kIndexTermCapacity, IndexError::PayloadMissing when deleting an absent payload, IndexError::BufferTooSmall when the result set exceeds the caller buffer. Never panics.
// CEP:ASSUMES: One tree per index purpose; payloads are caller-defined u64 identifiers (clause IDs); nodes and payload entries are never freed (deletion unlinks; reclamation is Phase 3 arena compaction, ticket CEP-1007); child lists are prepend-ordered so retrieval order is deterministic (most recently inserted matching path first); flattened symbol sequences are bounded by kIndexTermCapacity for both indexed and query terms.
// CEP:COST: insert and delete are O(term size) edge walks; retrieval is O(query size x branching factor) with the flat-sequence walk; measured 1496.32 cycles median per fresh-path insert and 1632.91 per exact-hit retrieval over a 128-term chain vocabulary on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0008, artifacts benches/artifacts/index_insert.json and index_retrieve.json.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs; property/discrimination_property_test.rs; bench CEP-BENCH-0008.
// CEP:SECURITY: node and entry indices are bounds-checked on every access; both counts are capped by named constants (denial-of-service bound on insert floods); query flattening is capacity-bounded.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; tree shape is a pure function of the insertion sequence, child lists are prepend-ordered, and retrieval walks children in list order.
// CEP:HPC-PASS-LEGALITY: Formal Spec 04 fixes the retrieval contract: a stored term is retrieved by a query iff the two flat preorder sequences have equal length and match position-wise under the design 9.2 rule (stored variable edges match any query symbol, query variables match any stored symbol, symbol edges match identical tag and symbol); the property test verifies set equality against a naive scan over the same rule.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: child lookup is a linear sibling scan; hash-bucketed child sets would shorten wide nodes, and the walk collects payloads only at exact path ends (prefix retrieval for subterm indexing is a Phase 3 extension with the feature-vector filter); deferred pending workload measurements; tickets CEP-1027 and CEP-1028.

use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::memory::arena::Arena;
use core::cell::Cell;
use mapt_config::limits::{
    kDiscriminationTreeEntries, kDiscriminationTreeNodes, kIndexEqualitySymbol, kIndexTermCapacity,
    kInvalidIndexEntry, kInvalidIndexNode,
};

/// CEP:WHAT: Error cases of the discrimination tree.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary for the indexing component.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{term_capacity_enforced, payload_missing_rejected}; security/phase2_bounds_test.rs::{discrimination_tree_node_cap_enforced, discrimination_tree_entry_budget_enforced}.
/// CEP:SECURITY: caps are the denial-of-service boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IndexError {
    /// CEP:WHAT: The node array reached kDiscriminationTreeNodes.
    TreeFull,
    /// CEP:WHAT: The payload entry count reached kDiscriminationTreeEntries.
    EntryBudgetExceeded,
    /// CEP:WHAT: The arena is exhausted.
    ArenaFull,
    /// CEP:WHAT: A referenced term is unreadable.
    InvalidTerm,
    /// CEP:WHAT: The term's flat symbol sequence exceeds kIndexTermCapacity.
    TermTooLarge,
    /// CEP:WHAT: A delete named a payload that is not present at the term's leaf.
    PayloadMissing,
    /// CEP:WHAT: The caller-supplied result buffer is too small for the retrieved set.
    BufferTooSmall,
}

// CEP:WHAT: Edge kind discriminant: symbol edge or variable edge.
// CEP:WHY: Design 9.2: "Each edge represents a symbol or variable"; a u8 discriminant keeps the node compact and the match test a single branch (CEP&CC 11.3 named constants).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: exactly two kinds.
// CEP:COST: 1 byte.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, variable_edges_match_any_query_symbol}.
// CEP:SECURITY: none.
const kEdgeKindSymbol: u8 = 0;
/// CEP:WHAT: Variable-edge discriminant.
/// CEP:WHY: See kEdgeKindSymbol; stored variable edges match any query symbol (design 9.2 retrieval rule).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: 1 byte.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::variable_edges_match_any_query_symbol.
/// CEP:SECURITY: none.
const kEdgeKindVariable: u8 = 1;

// CEP:WHAT: Bit positions of kind and tag inside the packed edge word.
// CEP:WHY: Packing kind (byte 0) and term tag (byte 1) into one u32 keeps the node at 20 bytes; the positions are named (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kind occupies bits 0-7, tag bits 8-15.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
// CEP:SECURITY: none.
const kEdgeKindShift: u32 = 0;
/// CEP:WHAT: Tag shift inside the packed edge word.
/// CEP:WHY: See kEdgeKindShift.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
/// CEP:SECURITY: none.
const kEdgeTagShift: u32 = 8;

// CEP:WHAT: Root node index.
// CEP:WHY: The root exists from construction; naming the index documents that node 0 is reserved (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: node 0 is always the root.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
// CEP:SECURITY: none.
const kRootNodeIndex: u32 = 0;

/// CEP:WHAT: One trie node: the incoming edge label, first-child and next-sibling links, and the head of the payload list.
/// CEP:WHY: Design 9.2: nodes are contiguous arena records with offset links; the intrusive sibling list avoids per-node child arrays, and the leaf list head keeps payloads reachable in O(1) at path ends; the repr(C) layout is pinned because it is the index memory contract (CEP&CC 38.17).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: indices are validated by the store before access.
/// CEP:COST: 20 bytes per node.
/// CEP:EVIDENCE: layout pinned by static assertion; unit/hot/discrimination_tree_test.rs::node_layout.
/// CEP:SECURITY: fixed layout, no pointers.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct IndexNode {
    /// CEP:WHAT: Symbol of the incoming edge (kIndexEqualitySymbol for equality atoms).
    /// CEP:WHY: Edge label half one.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: meaningful only for symbol edges.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::equality_terms_indexed.
    /// CEP:SECURITY: none.
    pub edge_symbol: u32,
    /// CEP:WHAT: Packed edge kind (bits 0-7) and term tag (bits 8-15).
    /// CEP:WHY: One word carries both match-relevant components.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: shifts named above.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
    /// CEP:SECURITY: none.
    pub edge_kind_tag: u32,
    /// CEP:WHAT: First child node index (kInvalidIndexNode = none).
    /// CEP:WHY: First-child/next-sibling encoding of the child list.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: indices below the node cap.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::shared_prefixes_share_nodes.
    /// CEP:SECURITY: bounds-checked.
    pub first_child: u32,
    /// CEP:WHAT: Next sibling node index under the same parent (kInvalidIndexNode = none).
    /// CEP:WHY: Sibling link of the intrusive child list.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: indices below the node cap.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::shared_prefixes_share_nodes.
    /// CEP:SECURITY: bounds-checked.
    pub next_sibling: u32,
    /// CEP:WHAT: Head of the payload list at this node (kInvalidIndexEntry = none).
    /// CEP:WHY: Payload storage at path ends.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries below the entry cap.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, delete_removes_payload}.
    /// CEP:SECURITY: bounds-checked.
    pub leaf_head: u32,
}

// CEP:WHAT: Node layout pin.
// CEP:WHY: The node record is the index memory contract read by the cold verifier; drift is an IR break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<IndexNode>() == 20);

/// CEP:WHAT: One payload list entry: the caller payload and the link to the next entry.
/// CEP:WHY: Design 9.2: "Leaf nodes store clause/literal references"; a singly linked arena list makes insertion O(1), deletion an unlink, and traversal cache-linear; the repr(C) layout is pinned as part of the index contract.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: next is kInvalidIndexEntry at the list end.
/// CEP:COST: 16 bytes per entry (8 payload, 4 link, 4 padding).
/// CEP:EVIDENCE: layout pinned by static assertion; unit/hot/discrimination_tree_test.rs::node_layout.
/// CEP:SECURITY: fixed layout, no pointers.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct IndexEntry {
    /// CEP:WHAT: Caller payload (for example a clause ID).
    /// CEP:WHY: The retrieved reference design 9.2 requires.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: opaque to the index.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    /// CEP:SECURITY: none.
    pub payload: u64,
    /// CEP:WHAT: Next entry index (kInvalidIndexEntry = end).
    /// CEP:WHY: List link.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: indices below the entry cap.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, delete_removes_payload}.
    /// CEP:SECURITY: bounds-checked.
    pub next: u32,
    /// CEP:WHAT: Reserved padding to 16 bytes.
    /// CEP:WHY: Fixed power-of-two entry size; must be zero (CEP&CC 38.17 stable IR).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: verifier flags nonzero.
    /// CEP:ASSUMES: zero.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
    /// CEP:SECURITY: rejects smuggled data.
    pub reserved: u32,
}

// CEP:WHAT: Entry layout pin.
// CEP:WHY: Same reasoning as the node pin (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::node_layout.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<IndexEntry>() == 16);

/// CEP:WHAT: One flattened query/index symbol: variable flag, term tag, and symbol ID.
/// CEP:WHY: The walk consumes one tree edge per flat symbol (Spec 04); an explicit record keeps the match test branch-free on the packed fields and the buffer size named.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: symbol is kIndexEqualitySymbol for equality atoms.
/// CEP:COST: 8 bytes per symbol.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, query_variables_match_any_symbol}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy)]
pub struct FlatSymbol {
    /// CEP:WHAT: True when the symbol is a term variable.
    /// CEP:WHY: Drives the any-symbol match rule.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::query_variables_match_any_symbol.
    /// CEP:SECURITY: none.
    pub is_variable: bool,
    /// CEP:WHAT: Term tag of the node.
    /// CEP:WHY: Symbol edges match identical tag and symbol.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::equality_terms_indexed.
    /// CEP:SECURITY: none.
    pub tag: u8,
    /// CEP:WHAT: Symbol ID (variable index for variables, kIndexEqualitySymbol for equality).
    /// CEP:WHY: Symbol-edge identity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    /// CEP:SECURITY: none.
    pub symbol: u32,
}

/// CEP:WHAT: The discrimination tree: node array, entry array, and counts, all arena-backed.
/// CEP:WHY: Design 9.2: "The tree is stored in the arena. Nodes are allocated contiguously. Child pointers are offsets, not absolute pointers, to reduce memory traffic."; the two flat arrays give exactly that, with Cell interior mutability for shared-reference operation under the single-threaded discipline used throughout the hot crate.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see IndexError.
/// CEP:ASSUMES: single-threaded use; the arena outlives the tree; the caller guarantees payload uniqueness per (term, payload) pair for deletion to address the intended entry.
/// CEP:COST: see file header; measured in bench CEP-BENCH-0008.
/// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs; property/discrimination_property_test.rs; bench CEP-BENCH-0008.
/// CEP:SECURITY: caps and bounds checks on every access.
pub struct DiscriminationTree<'a> {
    /// CEP:WHAT: Node array (index 0 is the root with an unused edge).
    /// CEP:WHY: Contiguous node storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: node_count <= kDiscriminationTreeNodes.
    /// CEP:COST: 20 bytes per node.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::shared_prefixes_share_nodes.
    /// CEP:SECURITY: bounds-checked.
    nodes: &'a [Cell<IndexNode>],
    /// CEP:WHAT: Payload entry array.
    /// CEP:WHY: Contiguous entry storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entry_count <= kDiscriminationTreeEntries.
    /// CEP:COST: 16 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, delete_removes_payload}.
    /// CEP:SECURITY: bounds-checked.
    entries: &'a [Cell<IndexEntry>],
    /// CEP:WHAT: Number of allocated nodes.
    /// CEP:WHY: Allocation cursor and cap enforcement.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: insert returns TreeFull at the cap.
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase2_bounds_test.rs::discrimination_tree_node_cap_enforced.
    /// CEP:SECURITY: memory bound.
    node_count: Cell<u32>,
    /// CEP:WHAT: Number of allocated payload entries.
    /// CEP:WHY: Allocation cursor and cap enforcement.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: insert returns EntryBudgetExceeded at the cap.
    /// CEP:ASSUMES: monotonic.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: security/phase2_bounds_test.rs::discrimination_tree_entry_budget_enforced.
    /// CEP:SECURITY: memory bound.
    entry_count: Cell<u32>,
}

impl<'a> DiscriminationTree<'a> {
    // CEP:WHAT: Constructs an empty discrimination tree with the root node allocated.
    // CEP:WHY: The root must exist before any insert walks it; both arrays are pre-allocated at their named caps so the hot path never allocates and cap enforcement is a counter check (design 8.1 initialization discipline).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull when either array does not fit.
    // CEP:ASSUMES: arena has room for kDiscriminationTreeNodes nodes and kDiscriminationTreeEntries entries (about 104 MiB at the maximum caps; tests and benches size arenas accordingly).
    // CEP:COST: one-time pre-allocation.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    // CEP:SECURITY: fixed capacity, no growth path.
    pub fn new(arena: &'a Arena) -> Result<DiscriminationTree<'a>, IndexError> {
        DiscriminationTree::new_with_caps(
            arena,
            kDiscriminationTreeNodes,
            kDiscriminationTreeEntries,
        )
    }

    // CEP:WHAT: Constructs a tree with explicit node and entry caps (the production constructor delegates with the named constants).
    // CEP:WHY: Security tests must exercise cap enforcement at small, fast scales instead of allocating the full production arrays; the explicit-cap constructor keeps the enforcement code identical for both paths (CEP&CC 34.3: test the mechanism, not a copy of it).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaFull on exhaustion; caps below one node (the root) are rejected as ArenaFull.
    // CEP:ASSUMES: caps >= 1; the arena holds cap x 20 plus cap x 16 bytes.
    // CEP:COST: one-time allocation proportional to the caps.
    // CEP:EVIDENCE: security/phase2_bounds_test.rs::{discrimination_tree_node_cap_enforced, discrimination_tree_entry_budget_enforced}; unit/hot/discrimination_tree_test.rs::exact_retrieval.
    // CEP:SECURITY: fixed capacity, no growth path.
    pub fn new_with_caps(
        arena: &'a Arena,
        node_cap: u32,
        entry_cap: u32,
    ) -> Result<DiscriminationTree<'a>, IndexError> {
        if node_cap == 0 || entry_cap == 0 {
            return Err(IndexError::ArenaFull);
        }
        let node_range = arena
            .alloc_array::<Cell<IndexNode>>(node_cap)
            .map_err(|_| IndexError::ArenaFull)?;
        let nodes = arena
            .array::<Cell<IndexNode>>(node_range)
            .map_err(|_| IndexError::ArenaFull)?;
        let entry_range = arena
            .alloc_array::<Cell<IndexEntry>>(entry_cap)
            .map_err(|_| IndexError::ArenaFull)?;
        let entries = arena
            .array::<Cell<IndexEntry>>(entry_range)
            .map_err(|_| IndexError::ArenaFull)?;
        nodes[kRootNodeIndex as usize].set(IndexNode {
            edge_symbol: 0,
            edge_kind_tag: (kEdgeKindSymbol as u32) << kEdgeKindShift,
            first_child: kInvalidIndexNode,
            next_sibling: kInvalidIndexNode,
            leaf_head: kInvalidIndexEntry,
        });
        Ok(DiscriminationTree {
            nodes,
            entries,
            node_count: Cell::new(1),
            entry_count: Cell::new(0),
        })
    }

    // CEP:WHAT: Returns the number of allocated nodes.
    // CEP:WHY: Diagnostics and cap reporting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::shared_prefixes_share_nodes.
    // CEP:SECURITY: none.
    pub fn node_count(&self) -> u32 {
        self.node_count.get()
    }

    // CEP:WHAT: Returns the number of allocated payload entries.
    // CEP:WHY: Diagnostics and budget accounting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    // CEP:SECURITY: none.
    pub fn entry_count(&self) -> u32 {
        self.entry_count.get()
    }

    // CEP:WHAT: Inserts a term with a payload: flattens the term's preorder sequence, walks or builds the edge path, and prepends the payload at the final node.
    // CEP:WHY: Design 9.2 insert: "Walk the tree, creating nodes as needed. O(depth)."; the payload list at the path end is what retrieval returns.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TermTooLarge past kIndexTermCapacity, TreeFull / EntryBudgetExceeded at the caps, InvalidTerm for unreadable terms.
    // CEP:ASSUMES: the term was interned by the caller's store.
    // CEP:COST: O(term size) with one node allocation per new edge; measured in bench CEP-BENCH-0008.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, shared_prefixes_share_nodes, multiple_payloads_at_one_leaf}; bench CEP-BENCH-0008.
    // CEP:SECURITY: caps enforced before allocation.
    pub fn insert(
        &self,
        terms: &TermStore<'_>,
        term: TermPtr,
        payload: u64,
    ) -> Result<(), IndexError> {
        let mut flat = FlatBuffer::default();
        flatten(terms, term, &mut flat)?;
        let mut current = kRootNodeIndex;
        for symbol in flat.used() {
            current = self.find_or_create_child(current, *symbol)?;
        }
        let entry_index = self.allocate_entry()?;
        let old_head = self.nodes[current as usize].get().leaf_head;
        self.entries[entry_index as usize].set(IndexEntry {
            payload,
            next: old_head,
            reserved: 0,
        });
        let mut node = self.nodes[current as usize].get();
        node.leaf_head = entry_index;
        self.nodes[current as usize].set(node);
        Ok(())
    }

    // CEP:WHAT: Deletes a payload from a term's leaf list.
    // CEP:WHY: Design 9.2 delete: "Remove clause references from leaf nodes. O(depth)."; index maintenance when clauses leave the active set (design 9.5); entries are unlinked, not freed (arena reclamation is Phase 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns InvalidTerm for unreadable terms, TermTooLarge past the capacity, and PayloadMissing when the walk cannot reach a leaf or the payload is absent there.
    // CEP:ASSUMES: the term was inserted with this payload.
    // CEP:COST: O(term size) walk plus O(list length) unlink.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{delete_removes_payload, delete_keeps_other_payloads}.
    // CEP:SECURITY: bounds-checked walk.
    pub fn delete(
        &self,
        terms: &TermStore<'_>,
        term: TermPtr,
        payload: u64,
    ) -> Result<(), IndexError> {
        let mut flat = FlatBuffer::default();
        flatten(terms, term, &mut flat)?;
        let mut current = kRootNodeIndex;
        for symbol in flat.used() {
            current = match self.find_child(current, *symbol) {
                Some(child) => child,
                None => return Err(IndexError::PayloadMissing),
            };
        }
        let mut previous = kInvalidIndexEntry;
        let mut cursor = self.nodes[current as usize].get().leaf_head;
        loop {
            if cursor == kInvalidIndexEntry {
                return Err(IndexError::PayloadMissing);
            }
            let entry = self.entries[cursor as usize].get();
            if entry.payload == payload {
                if previous == kInvalidIndexEntry {
                    let mut node = self.nodes[current as usize].get();
                    node.leaf_head = entry.next;
                    self.nodes[current as usize].set(node);
                } else {
                    let mut predecessor = self.entries[previous as usize].get();
                    predecessor.next = entry.next;
                    self.entries[previous as usize].set(predecessor);
                }
                return Ok(());
            }
            previous = cursor;
            cursor = entry.next;
        }
    }

    // CEP:WHAT: Retrieves the payloads of every stored term whose flat sequence matches the query under the design 9.2 rule.
    // CEP:WHY: Design 9.2 retrieve: "Walk the tree, matching symbols. Variables in the query match any symbol."; stored variable edges match any query symbol symmetrically; paths must end together, so the walk consumes exactly one edge per query symbol and collects at the final node.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns BufferTooSmall when the result set exceeds the buffer, TermTooLarge past the capacity, InvalidTerm for unreadable queries.
    // CEP:ASSUMES: the buffer is caller-owned; retrieved order is the deterministic child-list order (most recently inserted matching path first).
    // CEP:COST: O(query size x branching factor) worst case; measured in bench CEP-BENCH-0008.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, query_variables_match_any_symbol, variable_edges_match_any_query_symbol, length_rule_enforced}; property/discrimination_property_test.rs::retrieval_matches_naive_scan.
    // CEP:SECURITY: bounds-checked traversal; output bounded by the caller buffer.
    pub fn retrieve(
        &self,
        terms: &TermStore<'_>,
        query: TermPtr,
        buffer: &mut [u64],
    ) -> Result<usize, IndexError> {
        let mut flat = FlatBuffer::default();
        flatten(terms, query, &mut flat)?;
        let mut count: usize = 0;
        self.walk(flat.used(), 0, kRootNodeIndex, buffer, &mut count)?;
        Ok(count)
    }

    // CEP:WHAT: Recursive walk: consumes the query symbol at position against the children of the node, collecting payloads when the sequence ends exactly at a child.
    // CEP:WHY: The one-edge-per-symbol alignment of Spec 04: each matching root-to-node path of length equal to the query sequence is a retrieval hit; branching arises where a query variable matches several children or stored variable edges occur.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates BufferTooSmall.
    // CEP:ASSUMES: position < symbols.len() on entry.
    // CEP:COST: one sibling scan per level; recursion bounded by the flat capacity.
    // CEP:EVIDENCE: property/discrimination_property_test.rs::retrieval_matches_naive_scan.
    // CEP:SECURITY: bounds-checked.
    fn walk(
        &self,
        symbols: &[FlatSymbol],
        position: usize,
        node_index: u32,
        buffer: &mut [u64],
        count: &mut usize,
    ) -> Result<(), IndexError> {
        let query = symbols[position];
        let last = position + 1 == symbols.len();
        let mut child = self.nodes[node_index as usize].get().first_child;
        while child != kInvalidIndexNode {
            let node = self.nodes[child as usize].get();
            if edge_matches(&node, query) {
                if last {
                    self.collect_payloads(child, buffer, count)?;
                } else {
                    self.walk(symbols, position + 1, child, buffer, count)?;
                }
            }
            child = self.nodes[child as usize].get().next_sibling;
        }
        Ok(())
    }

    // CEP:WHAT: Collects every payload of a node's leaf list into the buffer.
    // CEP:WHY: One shared collection point enforces the buffer bound once (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns BufferTooSmall when the buffer is exhausted.
    // CEP:ASSUMES: none.
    // CEP:COST: O(list length).
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, multiple_payloads_at_one_leaf}.
    // CEP:SECURITY: bounds-checked writes.
    fn collect_payloads(
        &self,
        node_index: u32,
        buffer: &mut [u64],
        count: &mut usize,
    ) -> Result<(), IndexError> {
        let mut cursor = self.nodes[node_index as usize].get().leaf_head;
        while cursor != kInvalidIndexEntry {
            let entry = self.entries[cursor as usize].get();
            if *count >= buffer.len() {
                return Err(IndexError::BufferTooSmall);
            }
            buffer[*count] = entry.payload;
            *count += 1;
            cursor = entry.next;
        }
        Ok(())
    }

    // CEP:WHAT: Finds the child edge matching a flat symbol, or creates it (prepend) when absent.
    // CEP:WHY: The insert primitive of design 9.2; creation is one arena-array slot with the link updates of the intrusive sibling list.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TreeFull at the cap.
    // CEP:ASSUMES: node_index is valid.
    // CEP:COST: O(siblings) scan plus constant creation.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, shared_prefixes_share_nodes}.
    // CEP:SECURITY: cap enforced before allocation.
    fn find_or_create_child(&self, node_index: u32, symbol: FlatSymbol) -> Result<u32, IndexError> {
        if let Some(child) = self.find_child(node_index, symbol) {
            return Ok(child);
        }
        if self.node_count.get() >= self.nodes.len() as u32 {
            return Err(IndexError::TreeFull);
        }
        let fresh = self.node_count.get();
        let kind = if symbol.is_variable {
            kEdgeKindVariable
        } else {
            kEdgeKindSymbol
        };
        let parent = self.nodes[node_index as usize].get();
        self.nodes[fresh as usize].set(IndexNode {
            edge_symbol: symbol.symbol,
            edge_kind_tag: ((kind as u32) << kEdgeKindShift)
                | ((symbol.tag as u32) << kEdgeTagShift),
            first_child: kInvalidIndexNode,
            next_sibling: parent.first_child,
            leaf_head: kInvalidIndexEntry,
        });
        let mut updated = parent;
        updated.first_child = fresh;
        self.nodes[node_index as usize].set(updated);
        self.node_count.set(fresh + 1);
        Ok(fresh)
    }

    // CEP:WHAT: Finds the child edge exactly matching a flat symbol (stored variable edges never match here because insert never stores a variable edge for a symbol).
    // CEP:WHY: The walk primitive shared by delete (exact path following) and insert (probe before create); equality with the edge fields is the symbol-edge match rule minus the query-variable case, which only applies to retrieval.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (None means absent).
    // CEP:ASSUMES: node_index is valid.
    // CEP:COST: O(siblings) scan.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, delete_removes_payload}.
    // CEP:SECURITY: none.
    fn find_child(&self, node_index: u32, symbol: FlatSymbol) -> Option<u32> {
        let mut child = self.nodes[node_index as usize].get().first_child;
        while child != kInvalidIndexNode {
            let node = self.nodes[child as usize].get();
            let kind = if symbol.is_variable {
                kEdgeKindVariable
            } else {
                kEdgeKindSymbol
            };
            let packed = (kind as u32) << kEdgeKindShift | (symbol.tag as u32) << kEdgeTagShift;
            if node.edge_kind_tag == packed && node.edge_symbol == symbol.symbol {
                return Some(child);
            }
            child = self.nodes[child as usize].get().next_sibling;
        }
        None
    }

    // CEP:WHAT: Allocates one payload entry, enforcing the entry cap.
    // CEP:WHY: The insert budget check of design 9.5 / limits discipline.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns EntryBudgetExceeded at the cap.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: security/phase2_bounds_test.rs::discrimination_tree_entry_budget_enforced.
    // CEP:SECURITY: memory bound.
    fn allocate_entry(&self) -> Result<u32, IndexError> {
        if self.entry_count.get() >= self.entries.len() as u32 {
            return Err(IndexError::EntryBudgetExceeded);
        }
        let fresh = self.entry_count.get();
        self.entry_count.set(fresh + 1);
        Ok(fresh)
    }
}

// CEP:WHAT: Edge-vs-query-symbol match rule of design 9.2.
// CEP:WHY: A stored variable edge matches any query symbol; a query variable matches any stored symbol edge; otherwise tag and symbol must be identical; single-sourcing the rule keeps insert, delete, and retrieval consistent with Spec 04.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the node carries a well-formed packed edge.
// CEP:COST: 2-3 compares.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{query_variables_match_any_symbol, variable_edges_match_any_query_symbol}.
// CEP:SECURITY: none.
fn edge_matches(node: &IndexNode, query: FlatSymbol) -> bool {
    let kind = (node.edge_kind_tag >> kEdgeKindShift) as u8;
    if kind == kEdgeKindVariable {
        return true;
    }
    if query.is_variable {
        return true;
    }
    let tag = (node.edge_kind_tag >> kEdgeTagShift) as u8;
    tag == query.tag && node.edge_symbol == query.symbol
}

// CEP:WHAT: Capacity-bounded flat symbol buffer.
// CEP:WHY: The walk and insert operate on flat preorder sequences; a fixed-capacity stack buffer keeps the hot path allocation-free with a loud TermTooLarge error at the bound (CEP&CC 22.10, Law 6).
// CEP:STATUS: complete
// CEP:FAILURE: push returns TermTooLarge at capacity.
// CEP:ASSUMES: kIndexTermCapacity covers all realistic indexed and query terms.
// CEP:COST: 8 bytes per symbol on the stack.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::term_capacity_enforced; security/phase2_bounds_test.rs::index_capacity_enforced.
// CEP:SECURITY: capacity bound.
#[derive(Clone, Copy)]
struct FlatBuffer {
    /// CEP:WHAT: Symbol slots.
    /// CEP:WHY: Fixed storage.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: length <= kIndexTermCapacity.
    /// CEP:COST: kIndexTermCapacity x 8 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: none.
    symbols: [FlatSymbol; kIndexTermCapacity as usize],
    /// CEP:WHAT: Number of used slots.
    /// CEP:WHY: Length cursor.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= symbols.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: none.
    length: usize,
}

// CEP:WHAT: FlatBuffer construction and operations.
// CEP:WHY: Keeps the buffer private and its bound checks local.
// CEP:STATUS: complete
// CEP:FAILURE: push errors at capacity.
// CEP:ASSUMES: none.
// CEP:COST: constant per push.
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::term_capacity_enforced.
// CEP:SECURITY: none.
impl FlatBuffer {
    // CEP:WHAT: Creates an empty buffer.
    // CEP:WHY: Entry point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant (slots are untyped until pushed).
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    // CEP:SECURITY: none.
    fn default() -> FlatBuffer {
        FlatBuffer {
            symbols: [FlatSymbol {
                is_variable: false,
                tag: 0,
                symbol: 0,
            }; kIndexTermCapacity as usize],
            length: 0,
        }
    }

    // CEP:WHAT: Returns the used prefix of the buffer.
    // CEP:WHY: The walk and insert iterate exactly the flattened sequence.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::exact_retrieval.
    // CEP:SECURITY: none.
    fn used(&self) -> &[FlatSymbol] {
        &self.symbols[..self.length]
    }
}

// CEP:WHAT: Flattens a term into its preorder symbol sequence.
// CEP:WHY: The discrimination tree is a trie over preorder sequences (Spec 04); the flattening walk is depth-guarded by the intern-time depth bound and capacity-guarded by kIndexTermCapacity.
// CEP:STATUS: complete
// CEP:FAILURE: Returns InvalidTerm for unreadable terms and TermTooLarge past the capacity.
// CEP:ASSUMES: the term was interned (depth already bounded by kMaxTermDepth).
// CEP:COST: O(term size).
// CEP:EVIDENCE: unit/hot/discrimination_tree_test.rs::{exact_retrieval, term_capacity_enforced}.
// CEP:SECURITY: bounded recursion and buffer.
fn flatten(
    terms: &TermStore<'_>,
    term: TermPtr,
    buffer: &mut FlatBuffer,
) -> Result<(), IndexError> {
    if buffer.length >= kIndexTermCapacity as usize {
        return Err(IndexError::TermTooLarge);
    }
    let view = terms.term(term).map_err(|_| IndexError::InvalidTerm)?;
    let is_variable = view.tag() == TermTag::Variable;
    let symbol = if is_variable {
        view.symbol()
    } else if view.tag() == TermTag::Equality {
        kIndexEqualitySymbol
    } else {
        view.symbol()
    };
    buffer.symbols[buffer.length] = FlatSymbol {
        is_variable,
        tag: view.tag() as u8,
        symbol,
    };
    buffer.length += 1;
    if is_variable {
        return Ok(());
    }
    // Recursion depth is structurally bounded by the intern-time depth cap (kMaxTermDepth,
    // enforced in term.rs) because flatten follows exactly the term's tree structure; the
    // buffer capacity above bounds the total symbol count (CEP&CC 22.10).
    for index in 0..view.child_count() {
        let child = view.child(index).map_err(|_| IndexError::InvalidTerm)?;
        flatten(terms, child, buffer)?;
    }
    Ok(())
}
