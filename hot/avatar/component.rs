// CEP:FILE: hot/avatar/component.rs
// CEP:WHAT: The AVATAR component table (design 12.2): hash-consing of split components over canonical literal-word sequences, with one dense propositional assertion variable per interned component (assertion variable = component slot) and the materialized-clause bookkeeping.
// CEP:WHY: Voronkov (CAV 2014) section 4: identical components from different splits must share one assertion variable, otherwise the abstraction grows variables for no information and component-based learning (conflict clauses over assertion literals) cannot fire across splits; Spec 12 section 4 fixes the canonical form (literals as (atom offset << 1 | polarity) words, sorted ascending) - hash-consed atoms make the word sequence an injective function of the literal multiset up to the dense variable namespace (both restandardized), so word-sequence equality is component equality; the open-addressing table with linear probing and a deterministic FNV-1a hash mirrors the term table's discipline (design 5.1) and keeps interning allocation-free after construction.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: returns AvatarError::{ComponentTableFull, WordBudgetExceeded} at the capacities; the controller falls back to adding the unsplit clause (sound degradation, Spec 12 section 7); never panics.
// CEP:ASSUMES: one table per search arena; canonical words come from the controller's restandardized component literals; the assertion variable count equals the record capacity (the solver must be constructed with at least that many variables).
// CEP:COST: O(words) hash plus O(words) compare per probe; interning measured in bench CEP-BENCH-0032, artifact benches/artifacts/avatar_intern_step.json.
// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, distinct_components_get_distinct_slots, canonical_words_sorted, capacity_enforced, word_budget_enforced, assertion_variables_dense}; property/avatar_property_test.rs::{splits_preserve_literal_multiset, disjunction_of_components_is_original}.
// CEP:SECURITY: capacity and word budgets are explicit bounds (CEP&CC 22.10); the hash is deterministic (no seed dependence, CEP&CC 38.10).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; FNV-1a is seedless, probe order is slot order, record numbering is interning order.
// CEP:HPC-PASS-LEGALITY: Formal Spec 12 section 4 fixes the canonical component form and the interning contract (identical canonical words imply the same assertion variable); the unit tests verify executably that identical literals intern once and distinct literals occupy distinct slots.

use core::cell::Cell;
use mapt_config::limits::{
    kAvatarComponentCapacity, kAvatarComponentWordCapacity, kInvalidClauseId, kInvalidClauseOffset,
    kMaxClauseLiterals,
};

use crate::ir::literal::Literal;
use crate::memory::arena::Arena;
use crate::sat::literal::SatVar;

// CEP:WHAT: FNV-1a 32-bit offset basis.
// CEP:WHY: The component hash must be deterministic and seedless (CEP&CC 38.10); FNV-1a is the same family the term table uses.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
// CEP:SECURITY: none.
const kFnvOffsetBasis: u32 = 2_166_136_261;

// CEP:WHAT: FNV-1a 32-bit prime.
// CEP:WHY: Named multiplier of the hash round (CEP&CC 11.3 no-magic-numbers).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
// CEP:SECURITY: none.
const kFnvPrime: u32 = 16_777_619;

/// CEP:WHAT: Error cases of the component table.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the table never panics and every bound has a named variant.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{capacity_enforced, word_budget_enforced}.
/// CEP:SECURITY: capacity bounds are the resource-exhaustion guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AvatarError {
    /// CEP:WHAT: The component record capacity is exhausted.
    /// CEP:WHY: kAvatarComponentCapacity bounds the assertion-variable space; interning past it fails loudly and the controller keeps the clause whole.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: the capacity argument was >= 1.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::capacity_enforced.
    /// CEP:SECURITY: resource-exhaustion boundary.
    ComponentTableFull,
    /// CEP:WHAT: The canonical-word blob budget is exhausted.
    /// CEP:WHY: The blob is a fixed arena allocation; a component whose words do not fit fails loudly instead of truncating (truncation would corrupt component identity).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: per-component word counts are <= kMaxClauseLiterals.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::word_budget_enforced.
    /// CEP:SECURITY: resource-exhaustion boundary.
    WordBudgetExceeded,
    /// CEP:WHAT: A clause-reference read failed.
    /// CEP:WHY: Bounds-checked reads are the memory-safety contract (CEP&CC Law 3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: handles were produced by the owning stores.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: forged or stale handles are rejected.
    InvalidClause,
}

/// CEP:WHAT: One interning result: the component slot and whether this call created it.
/// CEP:WHY: The controller allocates the assertion variable's clause-side state only for fresh components and reuses the variable otherwise (design 12.2 component sharing).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: slot < table capacity.
/// CEP:COST: enum copy with payload.
/// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, distinct_components_get_distinct_slots}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interned {
    /// CEP:WHAT: The component slot (its assertion variable is SatVar(slot)).
    /// CEP:WHY: Dense slot numbering doubles as the assertion-variable space (Spec 12 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::assertion_variables_dense.
    /// CEP:SECURITY: none.
    pub slot: u32,
    /// CEP:WHAT: Whether this interning call created the record.
    /// CEP:WHY: Fresh components need the abstraction clause and materialization state; shared ones do not.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
    /// CEP:SECURITY: none.
    pub fresh: bool,
}

/// CEP:WHAT: The component table: open-addressing interning over canonical literal words with dense assertion variables and materialization bookkeeping.
/// CEP:WHY: Design 12.2 rules 1-2: components hash-consed to assertion variables, the abstraction solver consumes SatVar(slot) literals, and the controller reads/writes the materialized clause offset per slot; parallel Cell arrays keep every field a fixed arena allocation (design 22.1, structure-of-arrays discipline).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see AvatarError.
/// CEP:ASSUMES: single-threaded use; arena outlives the table; the abstraction solver declares at least the record capacity variables.
/// CEP:COST: construction O(capacities); intern O(words); bench CEP-BENCH-0032.
/// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, distinct_components_get_distinct_slots, canonical_words_sorted, capacity_enforced, word_budget_enforced, assertion_variables_dense}.
/// CEP:SECURITY: all reads bounds-checked; capacities validated before allocation.
pub struct ComponentTable<'a> {
    /// CEP:WHAT: Hash slots: component slot + 1, or 0 when empty (capacity entries, power of two).
    /// CEP:WHY: Linear probing with a 0 sentinel avoids a second occupancy array; +1 packing keeps slot 0 representable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: interning past the record capacity returns ComponentTableFull before any slot wrap (the load factor stays <= 1 by construction because records are the scarcer resource).
    /// CEP:ASSUMES: capacity is a power of two (masked indexing).
    /// CEP:COST: 4 bytes per slot.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, capacity_enforced}.
    /// CEP:SECURITY: bounds-checked slot reads.
    slots: &'a [Cell<u32>],
    /// CEP:WHAT: Canonical-word blob start per record.
    /// CEP:WHY: Components store their words contiguously in one shared blob; the start offset plus count locates them.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: start + count <= blob capacity for every record.
    /// CEP:COST: 4 bytes per record.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
    /// CEP:SECURITY: bounds-checked.
    word_start: &'a [Cell<u32>],
    /// CEP:WHAT: Canonical-word count per record.
    /// CEP:WHY: The interning comparison and the identity check read the extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: 1 <= count <= kMaxClauseLiterals.
    /// CEP:COST: 2 bytes per record.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::canonical_words_sorted.
    /// CEP:SECURITY: none.
    word_count: &'a [Cell<u16>],
    /// CEP:WHAT: Materialized clause offset per record (kInvalidClauseOffset until the component becomes a search clause).
    /// CEP:WHY: The controller materializes a component clause exactly once (monotone activation, Spec 12 section 5); the offset feeds proof reconstruction and the export scans.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: written once (kInvalidClauseOffset -> offset), never reset.
    /// CEP:COST: 4 bytes per record.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    /// CEP:SECURITY: none.
    materialized: &'a [Cell<u32>],
    /// CEP:WHAT: Source-original clause id per record (the split parent the first interning cites).
    /// CEP:WHY: The materialized component's AvatarSplit derivation names the original clause of the split that first interned the component (Spec 12 section 4); later re-internings of the same component share the record and therefore the first source - sound because the component is a subclause of that original, and the proof only needs one valid parent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: written once at record creation.
    /// CEP:COST: 8 bytes per record.
    /// CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_derivations_cite_original.
    /// CEP:SECURITY: none.
    source_clause: &'a [Cell<u64>],
    /// CEP:WHAT: The canonical-word blob (one region shared by all records).
    /// CEP:WHY: A single bump region keeps per-component storage proportional to actual words, not capacity x max literals (the 128 MiB alternative is rejected in Spec 12 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: exhaustion returns WordBudgetExceeded.
    /// CEP:ASSUMES: kAvatarComponentWordCapacity words.
    /// CEP:COST: 4 bytes per word.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::word_budget_enforced.
    /// CEP:SECURITY: bounds-checked.
    words: &'a [Cell<u32>],
    /// CEP:WHAT: Number of records in use.
    /// CEP:WHY: Dense record allocation; also the next assertion variable's slot.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= record capacity.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::assertion_variables_dense.
    /// CEP:SECURITY: none.
    used_records: Cell<u32>,
    /// CEP:WHAT: Number of blob words in use.
    /// CEP:WHY: Bump cursor of the word region.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= word capacity.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::word_budget_enforced.
    /// CEP:SECURITY: none.
    used_words: Cell<u32>,
}

// CEP:WHAT: Computes the FNV-1a hash of a canonical word sequence.
// CEP:WHY: Deterministic, seedless hashing (CEP&CC 38.10); the named constants keep the function auditable.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: O(words).
// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
// CEP:SECURITY: none.
fn hash_words(words: &[u32]) -> u32 {
    let mut hash = kFnvOffsetBasis;
    for word in words.iter() {
        hash ^= *word;
        hash = hash.wrapping_mul(kFnvPrime);
    }
    hash
}

// CEP:WHAT: Builds the canonical word sequence of a literal slice into out; returns the word count.
// CEP:WHY: Spec 12 section 4: one word per literal as (atom offset << 1) | polarity, sorted ascending - hash-consed atoms make the sequence injective on literal multisets over the dense variable namespace, and sorting removes literal-order dependence so components from different splits compare equal.
// CEP:STATUS: complete
// CEP:FAILURE: none (the caller bounds out by kMaxClauseLiterals).
// CEP:ASSUMES: literals.len() <= out.len().
// CEP:COST: O(n log n) insertion sort (n <= kMaxClauseLiterals, typical <= 8).
// CEP:EVIDENCE: unit/hot/avatar_component_test.rs::canonical_words_sorted; property/avatar_property_test.rs::splits_preserve_literal_multiset.
// CEP:SECURITY: none.
pub fn canonical_component_words(literals: &[Literal], out: &mut [u32]) -> usize {
    let count = literals.len();
    for (index, literal) in literals.iter().enumerate() {
        let polarity_bit: u32 = if literal.is_positive() { 1 } else { 0 };
        out[index] = (literal.atom().as_u32() << 1) | polarity_bit;
    }
    // Insertion sort ascending (deterministic, allocation-free).
    let slice = &mut out[..count];
    for index in 1..slice.len() {
        let mut position = index;
        while position > 0 && slice[position] < slice[position - 1] {
            slice.swap(position, position - 1);
            position -= 1;
        }
    }
    count
}

impl<'a> ComponentTable<'a> {
    // CEP:WHAT: Constructs the table with production capacities.
    // CEP:WHY: Design 19.4: every structure is fully built before the hot path; the production capacities are the named constants.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns AvatarError when the arena cannot host the arrays.
    // CEP:ASSUMES: the arena has about 6 MiB free.
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::components_interned_once.
    // CEP:SECURITY: capacities validated before allocation.
    pub fn new(arena: &'a Arena) -> Result<ComponentTable<'a>, AvatarError> {
        ComponentTable::new_with(
            arena,
            kAvatarComponentCapacity,
            kAvatarComponentWordCapacity,
        )
    }

    // CEP:WHAT: Constructs the table with explicit record and word capacities.
    // CEP:WHY: CEP&CC 34.3: capacity tests at small scales on the production code path; the hash-slot count equals the record capacity (power of two validated by the limits chain at the production value, and re-validated here for injected values by rounding up to the next power of two).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns AvatarError::ComponentTableFull for zero capacity or arena exhaustion.
    // CEP:ASSUMES: capacities >= 1; word capacity >= record capacity (each record needs at least one word).
    // CEP:COST: O(capacities) one-time.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{capacity_enforced, word_budget_enforced}.
    // CEP:SECURITY: capacities validated before allocation.
    pub fn new_with(
        arena: &'a Arena,
        record_capacity: u32,
        word_capacity: u32,
    ) -> Result<ComponentTable<'a>, AvatarError> {
        // Zero capacities are invalid; a word blob smaller than the record capacity is
        // legal (the blob budget fires loudly on the later records - the bound is the
        // blob itself, not a construction-time relation between the two capacities).
        if record_capacity == 0 || word_capacity == 0 {
            return Err(AvatarError::ComponentTableFull);
        }
        // Round the slot count up to a power of two for masked probing.
        let mut slot_count: u32 = 1;
        while slot_count < record_capacity {
            slot_count = match slot_count.checked_mul(2) {
                Some(value) => value,
                None => return Err(AvatarError::ComponentTableFull),
            };
        }
        let slots_range = arena
            .alloc_array::<Cell<u32>>(slot_count)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let slots = arena
            .array::<Cell<u32>>(slots_range)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        for slot in slots.iter() {
            slot.set(0);
        }
        let word_start_range = arena
            .alloc_array::<Cell<u32>>(record_capacity)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let word_start = arena
            .array::<Cell<u32>>(word_start_range)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let word_count_range = arena
            .alloc_array::<Cell<u16>>(record_capacity)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let word_count = arena
            .array::<Cell<u16>>(word_count_range)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let materialized_range = arena
            .alloc_array::<Cell<u32>>(record_capacity)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let materialized = arena
            .array::<Cell<u32>>(materialized_range)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        for slot in materialized.iter() {
            slot.set(kInvalidClauseOffset);
        }
        let source_range = arena
            .alloc_array::<Cell<u64>>(record_capacity)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        let source_clause = arena
            .array::<Cell<u64>>(source_range)
            .map_err(|_| AvatarError::ComponentTableFull)?;
        for slot in source_clause.iter() {
            slot.set(kInvalidClauseId);
        }
        let words_range = arena
            .alloc_array::<Cell<u32>>(word_capacity)
            .map_err(|_| AvatarError::WordBudgetExceeded)?;
        let words = arena
            .array::<Cell<u32>>(words_range)
            .map_err(|_| AvatarError::WordBudgetExceeded)?;
        Ok(ComponentTable {
            slots,
            word_start,
            word_count,
            materialized,
            source_clause,
            words,
            used_records: Cell::new(0),
            used_words: Cell::new(0),
        })
    }

    // CEP:WHAT: Interns a canonical word sequence citing the source-original clause id: returns the component slot, creating a record when the sequence is new.
    // CEP:WHY: Spec 12 section 4: word-sequence equality is component equality; fresh records append to the word blob, claim the next dense slot (the assertion variable), and remember the split parent for the materialized clause's AvatarSplit derivation; shared records return the existing slot with fresh = false (the first source stays).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns ComponentTableFull when the record capacity is exhausted and WordBudgetExceeded when the blob cannot host the words.
    // CEP:ASSUMES: words is the canonical sorted form (canonical_component_words built it); 1 <= words.len() <= kMaxClauseLiterals; source is a valid clause id (only read for fresh records).
    // CEP:COST: O(words) hash plus O(words) per probe; bench CEP-BENCH-0032.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, distinct_components_get_distinct_slots, capacity_enforced, word_budget_enforced}; unit/hot/avatar_controller_test.rs::split_derivations_cite_original.
    // CEP:SECURITY: probe count bounded by the record capacity (every slot is either empty or holds a distinct record).
    pub fn intern(&self, words: &[u32], source: u64) -> Result<Interned, AvatarError> {
        if words.is_empty() || words.len() > kMaxClauseLiterals as usize {
            return Err(AvatarError::WordBudgetExceeded);
        }
        let mask = (self.slots.len() as u32 - 1) as usize;
        let mut slot_index = (hash_words(words) as usize) & mask;
        // CEP:WHAT: Probe budget: at most one probe per hash slot.
        // CEP:WHY: A full table has no empty slot to stop the linear probe, so the budget terminates the scan with ComponentTableFull instead of spinning forever (CEP&CC 22.10 unbounded-loop ban); the budget equals the slot count because every occupied slot holds a distinct record (so a full sweep has compared against every record).
        // CEP:STATUS: complete
        // CEP:FAILURE: budget exhaustion returns ComponentTableFull.
        // CEP:ASSUMES: slots are all distinct records or empty.
        // CEP:COST: at most slots.len() probes.
        // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::capacity_enforced.
        // CEP:SECURITY: denial-of-service bound on probing.
        let mut probes: usize = 0;
        loop {
            if probes >= self.slots.len() {
                return Err(AvatarError::ComponentTableFull);
            }
            probes += 1;
            let packed = self.slots[slot_index].get();
            if packed == 0 {
                // Empty: create the record here.
                let record = self.used_records.get();
                if record as usize >= self.word_start.len() {
                    return Err(AvatarError::ComponentTableFull);
                }
                let word_start = self.used_words.get();
                let word_end = match word_start.checked_add(words.len() as u32) {
                    Some(end) => end,
                    None => return Err(AvatarError::WordBudgetExceeded),
                };
                if word_end as usize > self.words.len() {
                    return Err(AvatarError::WordBudgetExceeded);
                }
                for (offset, word) in words.iter().enumerate() {
                    self.words[word_start as usize + offset].set(*word);
                }
                self.word_start[record as usize].set(word_start);
                self.word_count[record as usize].set(words.len() as u16);
                self.materialized[record as usize].set(kInvalidClauseOffset);
                self.source_clause[record as usize].set(source);
                self.used_words.set(word_end);
                self.used_records.set(record + 1);
                self.slots[slot_index].set(record + 1);
                return Ok(Interned {
                    slot: record,
                    fresh: true,
                });
            }
            // Occupied: compare against the packed record's words.
            let record = packed - 1;
            let start = self.word_start[record as usize].get() as usize;
            let count = self.word_count[record as usize].get() as usize;
            if count == words.len() {
                let mut equal = true;
                for (slot, word) in self.words[start..start + count].iter().zip(words.iter()) {
                    if slot.get() != *word {
                        equal = false;
                        break;
                    }
                }
                if equal {
                    return Ok(Interned {
                        slot: record,
                        fresh: false,
                    });
                }
            }
            slot_index = (slot_index + 1) & mask;
        }
    }

    // CEP:WHAT: Returns the number of interned components.
    // CEP:WHY: Diagnostics and the saturation/waiting accounting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::{components_interned_once, distinct_components_get_distinct_slots}.
    // CEP:SECURITY: none.
    pub fn component_count(&self) -> u32 {
        self.used_records.get()
    }

    // CEP:WHAT: Returns the assertion variable of a component slot (dense: SatVar(slot)).
    // CEP:WHY: Spec 12 section 4: the slot index doubles as the assertion variable, so the abstraction solver's variable space is exactly the record capacity.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: slot < component_count.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::assertion_variables_dense.
    // CEP:SECURITY: none.
    pub fn assertion_variable(&self, slot: u32) -> SatVar {
        SatVar(slot)
    }

    // CEP:WHAT: Returns the materialized clause offset of a slot, or None while unmaterialized.
    // CEP:WHY: The controller activates a component exactly once by materializing its clause; proof reconstruction and export scans read the offset.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-range slots (bounds-checked).
    // CEP:ASSUMES: slot came from intern.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: bounds-checked.
    pub fn materialized(&self, slot: u32) -> Option<u32> {
        let cell = self.materialized.get(slot as usize)?;
        let offset = cell.get();
        if offset == kInvalidClauseOffset {
            return None;
        }
        Some(offset)
    }

    // CEP:WHAT: Marks a slot materialized with its clause offset.
    // CEP:WHY: Monotone activation (Spec 12 section 5): the write happens once per slot; a second call is a no-op that keeps the first offset (idempotent by design, asserted by the caller).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns AvatarError::InvalidClause for out-of-range slots.
    // CEP:ASSUMES: offset != kInvalidClauseOffset.
    // CEP:COST: 1 store.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::refutes_split_pigeonhole.
    // CEP:SECURITY: bounds-checked.
    pub fn set_materialized(&self, slot: u32, offset: u32) -> Result<(), AvatarError> {
        let cell = match self.materialized.get(slot as usize) {
            Some(cell) => cell,
            None => return Err(AvatarError::InvalidClause),
        };
        if cell.get() == kInvalidClauseOffset {
            cell.set(offset);
        }
        Ok(())
    }

    // CEP:WHAT: Returns the canonical word at a blob position (identity reads for diagnostics).
    // CEP:WHY: The controller and tests read back a record's words to verify interning identity.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None out of bounds.
    // CEP:ASSUMES: position < word capacity.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::canonical_words_sorted.
    // CEP:SECURITY: bounds-checked.
    pub fn word_at(&self, position: u32) -> Option<u32> {
        Some(self.words.get(position as usize)?.get())
    }

    // CEP:WHAT: Returns the word extent of a record.
    // CEP:WHY: Diagnostics and tests locate a record's canonical words in the blob.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-range slots.
    // CEP:ASSUMES: slot < component_count.
    // CEP:COST: 2 loads.
    // CEP:EVIDENCE: unit/hot/avatar_component_test.rs::canonical_words_sorted.
    // CEP:SECURITY: bounds-checked.
    pub fn word_extent(&self, slot: u32) -> Option<(u32, u32)> {
        let start = self.word_start.get(slot as usize)?.get();
        let count = self.word_count.get(slot as usize)?.get() as u32;
        Some((start, count))
    }

    // CEP:WHAT: Returns the source-original clause id of a slot (the AvatarSplit parent).
    // CEP:WHY: The controller builds the materialized clause's derivation from it (Spec 12 section 4).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-range slots.
    // CEP:ASSUMES: slot < component_count.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::split_derivations_cite_original.
    // CEP:SECURITY: bounds-checked.
    pub fn source_clause(&self, slot: u32) -> Option<u64> {
        let cell = self.source_clause.get(slot as usize)?;
        let value = cell.get();
        if value == kInvalidClauseId {
            return None;
        }
        Some(value)
    }

    // CEP:WHAT: Returns the record capacity (the assertion-variable space).
    // CEP:WHY: The controller validates the abstraction solver's variable count against it at construction.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/avatar_controller_test.rs::controller_validates_solver_variables.
    // CEP:SECURITY: none.
    pub fn record_capacity(&self) -> u32 {
        self.word_start.len() as u32
    }
}
