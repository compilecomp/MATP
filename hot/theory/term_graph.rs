// CEP:FILE: hot/theory/term_graph.rs
// CEP:WHAT: The theory solver's hash-consed ground term graph (design 13.4): constant, variable, and application nodes in fixed-density arena arrays with structural deduplication through a bounded open-addressing signature table.
// CEP:WHY: Design 13.4 builds congruence closure over ground terms, and congruence closure's signature classes require the unique-node invariant (two structurally identical terms are the same node), which hash-consing provides; the graph is the single term surface both theory solvers and the Nelson-Oppen coordinator read, with every allocation in the caller-provided arena (CEP&CC 25.3.1, design 4.1).
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: construction and node creation return TheoryError on capacity exhaustion (TermCapacity, HashTableFull) or an out-of-range variable id (VarCapacity); never panics.
// CEP:ASSUMES: single-threaded; the arena outlives the graph; node ids are never reused.
// CEP:COST: node creation is O(arity) hashing plus O(1) amortized table probe; reads are O(1).
// CEP:EVIDENCE: unit/hot/theory_test.rs::{term_graph_hash_consing, term_capacity_enforced}.
// CEP:SECURITY: every table probe is bounded by the table capacity; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; insertion order is the caller's node-creation order and the probe sequence is fixed (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;
use mapt_config::limits::{kMaxTheoryTerms, kMaxTheoryVars};

use super::TheoryError;

/// CEP:WHAT: One term-graph node id.
/// CEP:WHY: A typed index keeps term nodes distinct from variable ids and atom ids at the type level.
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: produced only by TermGraph.
/// CEP:COST: 4 bytes.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
/// CEP:SECURITY: none.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct TermNode(pub u32);

// CEP:WHAT: Node-kind tags of the term graph.
// CEP:WHY: A named encoding keeps kind reads single-sourced (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: distinct values.
// CEP:COST: compile-time constants.
// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
// CEP:SECURITY: none.
const kNodeKindConst: u32 = 0;
const kNodeKindVar: u32 = 1;
const kNodeKindApp: u32 = 2;

// CEP:WHAT: Argument-slot capacity of the flattened argument array, derived from the node bound.
// CEP:WHY: The argument array is one fixed arena allocation sized to the worst-case total arity; the derivation from kMaxTheoryTerms keeps the two bounds from drifting apart (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: average arity well below 4 covers the uninterpreted-function workloads of Phase 5.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
// CEP:SECURITY: memory bound on the theory state.
const kTheoryArgSlots: u32 = kMaxTheoryTerms * 4;

/// CEP:WHAT: The hash-consed ground term graph over the shared variable space.
/// CEP:WHY: Design 13.4; the unique-node invariant is what makes the congruence closure's signature classes sound (two structurally identical applications are one node, so a signature collision is a congruence, not a bookkeeping artifact).
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError.
/// CEP:ASSUMES: single-threaded; no node is ever removed.
/// CEP:COST: 16 bytes of arena per node plus 4 bytes per argument slot and one hash-table slot per node.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
/// CEP:SECURITY: bounds-checked reads throughout.
pub struct TermGraph<'a> {
    /// CEP:WHAT: Node-kind tags (0 = constant, 1 = variable, 2 = application).
    /// CEP:WHY: The kind dispatches every node read.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    kind: &'a [Cell<u32>],
    /// CEP:WHAT: Per-node symbol: the constant's symbol id, the variable's id, or the application's function symbol.
    /// CEP:WHY: One cell covers the payload of all three kinds.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    symbol: &'a [Cell<u32>],
    /// CEP:WHAT: Per-application-node start index into the flattened argument array.
    /// CEP:WHY: Variable-length argument lists without per-node allocation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count; meaningful only for application nodes.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    first_arg: &'a [Cell<u32>],
    /// CEP:WHAT: Per-node arity (0 for constants and variables).
    /// CEP:WHY: Gates the argument-slot reads.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by count.
    /// CEP:COST: 4 bytes per node.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    arity: &'a [Cell<u32>],
    /// CEP:WHAT: The flattened argument-node array.
    /// CEP:WHY: Application arguments are contiguous per node.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kTheoryArgSlots.
    /// CEP:COST: 4 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    args: &'a [Cell<u32>],
    /// CEP:WHAT: Number of live nodes.
    /// CEP:WHY: Extent of the per-node arrays.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxTheoryTerms.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: none.
    count: Cell<u32>,
    /// CEP:WHAT: Argument slots used so far.
    /// CEP:WHY: Extent of the flattened argument array.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kTheoryArgSlots.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: none.
    args_used: Cell<u32>,
    /// CEP:WHAT: The hash-consing table: one node id per occupied slot, kInvalidNode for empty slots.
    /// CEP:WHY: Structural deduplication is the unique-node invariant.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryTerms * 2 (load factor kept at or below one half).
    /// CEP:COST: 4 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounded probes.
    table: &'a [Cell<u32>],
    /// CEP:WHAT: Number of occupied hash-table slots.
    /// CEP:WHY: The full-table check bounds the probe loops.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= table.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: none.
    occupied: Cell<u32>,
    /// CEP:WHAT: The per-variable node lookup (kInvalidNode until the variable's node is created).
    /// CEP:WHY: One node per variable id keeps the Nelson-Oppen shared-variable interface name-free.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryVars.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    var_index: &'a [Cell<u32>],
}

// CEP:WHAT: The empty hash-table slot sentinel.
// CEP:WHY: A named constant instead of a bare u32::MAX (CEP&CC 11.3); never a valid node id because node ids are bounded by kMaxTheoryTerms.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: kMaxTheoryTerms < u32::MAX.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
// CEP:SECURITY: none.
const kInvalidNode: u32 = u32::MAX;

impl<'a> TermGraph<'a> {
    /// CEP:WHAT: Constructs the term graph over the arena.
    /// CEP:WHY: Design 4.1: every structure is fully built before use, from the caller-provided arena.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError on arena exhaustion.
    /// CEP:ASSUMES: the arena has room for the node, argument, table, and variable arrays.
    /// CEP:COST: O(kMaxTheoryTerms + kTheoryArgSlots + kMaxTheoryVars) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<TermGraph<'a>, TheoryError> {
        let kind = Self::alloc_u32(arena, kMaxTheoryTerms)?;
        let symbol = Self::alloc_u32(arena, kMaxTheoryTerms)?;
        let first_arg = Self::alloc_u32(arena, kMaxTheoryTerms)?;
        let arity = Self::alloc_u32(arena, kMaxTheoryTerms)?;
        let args = Self::alloc_u32(arena, kTheoryArgSlots)?;
        let table_len = kMaxTheoryTerms * 2;
        let table = Self::alloc_u32(arena, table_len)?;
        for cell in table.iter().take(table_len as usize) {
            cell.set(kInvalidNode);
        }
        let var_index = Self::alloc_u32(arena, kMaxTheoryVars)?;
        for cell in var_index.iter() {
            cell.set(kInvalidNode);
        }
        Ok(TermGraph {
            kind,
            symbol,
            first_arg,
            arity,
            args,
            count: Cell::new(0),
            args_used: Cell::new(0),
            occupied: Cell::new(0),
            table,
            var_index,
        })
    }

    // CEP:WHAT: Allocates one u32 arena array with the error translation every caller needs.
    // CEP:WHY: One translation point for the arena error (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: none.
    fn alloc_u32(arena: &'a Arena, count: u32) -> Result<&'a [Cell<u32>], TheoryError> {
        let range = arena.alloc_array::<Cell<u32>>(count).map_err(|_| {
            TheoryError::Storage(crate::sat::database::SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<u32>>(range).map_err(|_| {
            TheoryError::Storage(crate::sat::database::SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: Returns the number of live nodes.
    /// CEP:WHY: Capacity accounting for tests and the coordinator.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_capacity_enforced.
    /// CEP:SECURITY: none.
    pub fn node_count(&self) -> u32 {
        self.count.get()
    }

    /// CEP:WHAT: Creates (or finds) the constant node for a symbol id.
    /// CEP:WHY: Hash-consing: repeated constants share one node.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::TermCapacity past the node bound.
    /// CEP:ASSUMES: symbol ids are caller-managed opaque ids.
    /// CEP:COST: O(1) amortized.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounded by the node capacity.
    pub fn const_node(&self, symbol: u32) -> Result<TermNode, TheoryError> {
        let hash = Self::mix_hash(symbol, kNodeKindConst);
        if let Some(existing) = self.table_find(hash, symbol, kNodeKindConst, 0, 0)? {
            return Ok(TermNode(existing));
        }
        let node = self.append_node(kNodeKindConst, symbol, 0, 0)?;
        self.table_insert(hash, node.0)?;
        Ok(node)
    }

    /// CEP:WHAT: Creates (or finds) the variable node for a variable id.
    /// CEP:WHY: One node per variable keeps both theory solvers and the Nelson-Oppen interface on one name space (design 13.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::VarCapacity for an out-of-range id and TermCapacity past the node bound.
    /// CEP:ASSUMES: variable ids are dense from 0.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounded by the variable capacity.
    pub fn var_node(&self, variable: u32) -> Result<TermNode, TheoryError> {
        if variable >= kMaxTheoryVars {
            return Err(TheoryError::VarCapacity);
        }
        let existing = self.var_index[variable as usize].get();
        if existing != kInvalidNode {
            return Ok(TermNode(existing));
        }
        let node = self.append_node(kNodeKindVar, variable, 0, 0)?;
        self.var_index[variable as usize].set(node.0);
        Ok(node)
    }

    /// CEP:WHAT: Creates (or finds) the application node for a function symbol and argument nodes.
    /// CEP:WHY: Hash-consing on the raw structural signature keeps the unique-node invariant the congruence closure's signature classes rely on.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::TermCapacity past the node or argument-slot bounds and HashTableFull past the table's load bound.
    /// CEP:ASSUMES: argument nodes already exist.
    /// CEP:COST: O(arity) hashing plus O(1) amortized probe.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounded by the node and slot capacities.
    pub fn app_node(&self, symbol: u32, arguments: &[TermNode]) -> Result<TermNode, TheoryError> {
        if arguments.is_empty() {
            // An application with no arguments is a constant.
            return self.const_node(symbol);
        }
        if arguments.len() > mapt_config::limits::kMaxTheoryArity as usize {
            return Err(TheoryError::ArityExceeded);
        }
        let mut hash = Self::mix_hash(symbol, kNodeKindApp);
        for argument in arguments.iter() {
            self.validate_node(argument.0)?;
            hash = hash
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add(argument.0 as u64);
        }
        if let Some(existing) = self.app_table_find(hash, symbol, arguments)? {
            return Ok(TermNode(existing));
        }
        let args_used = self.args_used.get() as usize;
        if args_used + arguments.len() > kTheoryArgSlots as usize
            || self.count.get() >= kMaxTheoryTerms
        {
            return Err(TheoryError::TermCapacity);
        }
        let node = self.append_node(
            kNodeKindApp,
            symbol,
            args_used as u32,
            arguments.len() as u32,
        )?;
        for (slot, argument) in arguments.iter().enumerate() {
            self.args[args_used + slot].set(argument.0);
        }
        self.args_used.set((args_used + arguments.len()) as u32);
        self.table_insert(hash, node.0)?;
        Ok(node)
    }

    /// CEP:WHAT: Reads a node's kind tag, symbol, and arguments into the caller's buffer.
    /// CEP:WHY: One bounds-checked read path for the closure, the coordinator, and the tests.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage(InvariantViolation) on an invalid node id or a buffer shorter than the arity.
    /// CEP:ASSUMES: the buffer has room for the node's arguments.
    /// CEP:COST: O(arity).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn read_node(
        &self,
        node: TermNode,
        arguments: &mut [TermNode],
    ) -> Result<(u32, u32, u32), TheoryError> {
        self.validate_node(node.0)?;
        let index = node.0 as usize;
        let arity = self.arity[index].get();
        if arguments.len() < arity as usize {
            return Err(TheoryError::Storage(
                crate::sat::database::SatCoreError::InvariantViolation,
            ));
        }
        let base = self.first_arg[index].get() as usize;
        for (slot, cell) in arguments.iter_mut().enumerate().take(arity as usize) {
            *cell = TermNode(self.args[base + slot].get());
        }
        Ok((self.kind[index].get(), self.symbol[index].get(), arity))
    }

    /// CEP:WHAT: Returns the raw structural payload of a node for signature hashing: the symbol and the argument node ids.
    /// CEP:WHY: The congruence closure's signature recomputation and the coordinator's shared-variable scan both walk nodes through this read.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none for valid node ids.
    /// CEP:ASSUMES: the node exists.
    /// CEP:COST: O(arity).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn node_symbol(&self, node: TermNode) -> Result<u32, TheoryError> {
        self.validate_node(node.0)?;
        Ok(self.symbol[node.0 as usize].get())
    }

    /// CEP:WHAT: Returns a node's arity.
    /// CEP:WHY: The closure's signature recomputation gates its buffer reads on the arity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none for valid node ids.
    /// CEP:ASSUMES: the node exists.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn node_arity(&self, node: TermNode) -> Result<u32, TheoryError> {
        self.validate_node(node.0)?;
        Ok(self.arity[node.0 as usize].get())
    }

    /// CEP:WHAT: Returns the argument node at one slot of an application node.
    /// CEP:WHY: The closure walks arguments slot by slot without a buffer copy.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage(InvariantViolation) on an invalid node id or slot.
    /// CEP:ASSUMES: the node is an application with the slot in range.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn node_argument(&self, node: TermNode, slot: u32) -> Result<TermNode, TheoryError> {
        self.validate_node(node.0)?;
        let index = node.0 as usize;
        if slot >= self.arity[index].get() {
            return Err(TheoryError::Storage(
                crate::sat::database::SatCoreError::InvariantViolation,
            ));
        }
        Ok(TermNode(
            self.args[self.first_arg[index].get() as usize + slot as usize].get(),
        ))
    }

    /// CEP:WHAT: Appends one node with the given fields.
    /// CEP:WHY: The single append path keeps the node layout and the capacity check in one place (CEP&CC 33.18).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::TermCapacity past the node bound.
    /// CEP:ASSUMES: called by the three node constructors only.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    /// CEP:SECURITY: bounds-checked writes.
    fn append_node(
        &self,
        kind: u32,
        symbol: u32,
        first_arg: u32,
        arity: u32,
    ) -> Result<TermNode, TheoryError> {
        let count = self.count.get();
        if count >= kMaxTheoryTerms {
            return Err(TheoryError::TermCapacity);
        }
        let index = count as usize;
        self.kind[index].set(kind);
        self.symbol[index].set(symbol);
        self.first_arg[index].set(first_arg);
        self.arity[index].set(arity);
        self.count.set(count + 1);
        Ok(TermNode(count))
    }

    // CEP:WHAT: Linear-probe lookup of a constant or variable node by its mixed hash and payload.
    // CEP:WHY: Hash-consing for the arity-zero node kinds.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage(InvariantViolation) when the table is saturated (unreachable because the node bound is half the table).
    // CEP:ASSUMES: called with a kind of 0 or 1.
    // CEP:COST: O(table load).
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: bounded probes.
    fn table_find(
        &self,
        hash: u64,
        symbol: u32,
        kind: u32,
        first_arg: u32,
        arity: u32,
    ) -> Result<Option<u32>, TheoryError> {
        let capacity = self.table.len() as u64;
        let mut slot = (hash % capacity) as usize;
        for _ in 0..self.table.len() {
            let entry = self.table[slot].get();
            if entry == kInvalidNode {
                return Ok(None);
            }
            let index = entry as usize;
            if self.kind[index].get() == kind
                && self.symbol[index].get() == symbol
                && self.first_arg[index].get() == first_arg
                && self.arity[index].get() == arity
            {
                return Ok(Some(entry));
            }
            slot = (slot + 1) % self.table.len();
        }
        Err(TheoryError::Storage(
            crate::sat::database::SatCoreError::InvariantViolation,
        ))
    }

    // CEP:WHAT: Linear-probe lookup of an application node by its mixed hash, symbol, and argument node ids.
    // CEP:WHY: Hash-consing for applications compares the full structural signature.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage(InvariantViolation) when the table is saturated.
    // CEP:ASSUMES: called with the application kind.
    // CEP:COST: O(table load x arity).
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: bounded probes.
    fn app_table_find(
        &self,
        hash: u64,
        symbol: u32,
        arguments: &[TermNode],
    ) -> Result<Option<u32>, TheoryError> {
        let capacity = self.table.len() as u64;
        let mut slot = (hash % capacity) as usize;
        for _ in 0..self.table.len() {
            let entry = self.table[slot].get();
            if entry == kInvalidNode {
                return Ok(None);
            }
            let index = entry as usize;
            if self.kind[index].get() == kNodeKindApp
                && self.symbol[index].get() == symbol
                && self.arity[index].get() as usize == arguments.len()
            {
                let mut equal = true;
                for (offset, argument) in arguments.iter().enumerate() {
                    if self.args[self.first_arg[index].get() as usize + offset].get() != argument.0
                    {
                        equal = false;
                        break;
                    }
                }
                if equal {
                    return Ok(Some(entry));
                }
            }
            slot = (slot + 1) % self.table.len();
        }
        Err(TheoryError::Storage(
            crate::sat::database::SatCoreError::InvariantViolation,
        ))
    }

    // CEP:WHAT: Inserts one node id into the hash table at its probe position.
    // CEP:WHY: The write half of hash-consing; the occupied count bounds the load factor.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::HashTableFull when the table has no free slot (unreachable while the node bound is half the table).
    // CEP:ASSUMES: the node was just appended.
    // CEP:COST: O(table load).
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: bounded probes.
    fn table_insert(&self, hash: u64, node: u32) -> Result<(), TheoryError> {
        if self.occupied.get() >= self.table.len() as u32 {
            return Err(TheoryError::HashTableFull);
        }
        let capacity = self.table.len() as u64;
        let mut slot = (hash % capacity) as usize;
        loop {
            if self.table[slot].get() == kInvalidNode {
                self.table[slot].set(node);
                self.occupied.set(self.occupied.get() + 1);
                return Ok(());
            }
            slot = (slot + 1) % self.table.len();
        }
    }

    // CEP:WHAT: Validates a node id against the live count.
    // CEP:WHY: One bounds-check point for every node read (CEP&CC 23.7).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage(InvariantViolation) on an out-of-range id.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: bounds-check under test.
    fn validate_node(&self, node: u32) -> Result<(), TheoryError> {
        if node >= self.count.get() {
            return Err(TheoryError::Storage(
                crate::sat::database::SatCoreError::InvariantViolation,
            ));
        }
        Ok(())
    }

    // CEP:WHAT: The FNV-style 64-bit hash mixer for the node payloads.
    // CEP:WHY: Deterministic hashing with no clock or address dependence (CEP&CC 38.10).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::term_graph_hash_consing.
    // CEP:SECURITY: none.
    fn mix_hash(symbol: u32, kind: u32) -> u64 {
        let mut hash = 0xCBF2_9CE4_8422_2325u64;
        hash ^= symbol as u64;
        hash = hash.wrapping_mul(0x100_0000_01B3);
        hash ^= kind as u64;
        hash = hash.wrapping_mul(0x100_0000_01B3);
        hash
    }
}
