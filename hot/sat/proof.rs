// CEP:FILE: hot/sat/proof.rs
// CEP:WHAT: DRAT proof recorder (design 11.1 S41/S42): a bounded flat step buffer of clause additions and deletions with stable 1-based proof ids, an append-only clause-offset-to-id map, and a concatenated literal blob, all arena-backed.
// CEP:WHY: Design 18 (proof production) and 11.1 S41-S43: proof steps must be emitted as clauses are added and deleted, recorded into a flat buffer bounded by kMaxProofSteps, and independently checkable (S43, the cold checker); keeping recording in the hot crate makes it allocation-free (one append per step) and keeps the step buffer the single source of truth that the CEP-1 DRAT/LRAT writer serializes and the CEP-1 checker replays; deletions carry their literals so plain DRAT text (deletion by clause) is emittable, while the stable ids make LRAT text (deletion by id) emittable too.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns ProofError (buffer capacity exhausted, unmapped deletion offset, storage read failure); the solver surfaces exhaustion as Indeterminate - never silent truncation (CEP&CC Law 6); never panics.
// CEP:ASSUMES: Single-threaded use; clause offsets arrive in strictly ascending order across record_add calls (arena bump allocation; the map's binary search relies on it); one record_add per clause offset (double-add of the same offset is an invariant violation); step ids are dense and 1-based.
// CEP:COST: every step kind shares one O(1) append primitive (step record plus literal blob write) measured in bench CEP-BENCH-0013, artifact benches/artifacts/sat_drat_record.json (the assumption-add step: the append path with no map interaction); record_add adds one ascending-map insert and record_delete one O(log map) search on top of that primitive, both capacity-bounded and covered by the unit tests.
// CEP:EVIDENCE: unit/hot/sat_proof_test.rs; unit/cold/drat_writer_test.rs; unit/cold/drat_checker_test.rs; property/drat_property_test.rs::proofs_of_random_solves_verify.
// CEP:SECURITY: buffer capacities are memory-exhaustion bounds; all enumeration is bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; step order is the clause-lifecycle order, ids are dense counters, no clocks or addresses (CEP&CC 38.10).
// CEP:HPC-PASS-LEGALITY: Formal Spec 11 fixes the recording contract: every added clause is recorded before any later step references it, every deleted clause is recorded with the id of its addition, and the sequence of adds and deletions is exactly the solver's clause-database lifecycle; the RUP property of each learnt addition follows from Spec 06 section 3 (the learnt clause is a resolvent chain of database clauses), and the checker verifies the recorded sequence mechanically.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: deletion steps store the clause literals for DRAT text even though LRAT needs only the id; the dual storage is a documented cost of supporting both formats from one buffer; ticket CEP-1032.

use crate::memory::arena::Arena;
use crate::sat::clause::{ClauseStorage, SatClauseError};
use crate::sat::literal::SatLiteral;
use mapt_config::limits::{
    kFirstProofId, kInvalidProofId, kSatProofLiteralCapacity, kSatProofMapCapacity,
    kSatProofStepCapacity,
};

/// CEP:WHAT: Error cases of the proof recorder.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; recording never panics and never silently truncates or reorders.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{capacity_enforced, deletion_resolves_id}.
/// CEP:SECURITY: capacity errors are the memory-exhaustion boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofError {
    /// CEP:WHAT: The step buffer capacity is exhausted.
    /// CEP:WHY: Bounded proof memory; the solver turns this into Indeterminate instead of emitting a truncated certificate.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced; security/phase3_bounds_test.rs::proof_step_budget_enforced.
    /// CEP:SECURITY: memory bound.
    StepBufferFull,
    /// CEP:WHAT: The offset-to-id map capacity is exhausted.
    /// CEP:WHY: One map entry per added clause; loud failure at the bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    MapFull,
    /// CEP:WHAT: The literal blob capacity is exhausted.
    /// CEP:WHY: Bounded proof memory; loud failure at the bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced.
    /// CEP:SECURITY: memory bound.
    LiteralBlobFull,
    /// CEP:WHAT: A deletion referenced a clause offset that was never added to the proof.
    /// CEP:WHY: Deletion steps must carry the id of the addition they undo; an unmapped offset means the solver's lifecycle bookkeeping diverged from the proof, which is surfaced loudly instead of skipped.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::unmapped_deletion_rejected.
    /// CEP:SECURITY: rejects corrupted bookkeeping.
    UnmappedOffset,
    /// CEP:WHAT: A clause record read failed while collecting deletion literals.
    /// CEP:WHY: Deletion steps store the clause's literals; unreadable offsets are surfaced, never guessed past.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
    /// CEP:SECURITY: bounds-checked reads.
    Storage(SatClauseError),
}

impl From<SatClauseError> for ProofError {
    // CEP:WHAT: Converts storage errors into the proof vocabulary.
    // CEP:WHY: CEP&CC 33.18: one explicit translation point.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
    // CEP:SECURITY: none.
    fn from(error: SatClauseError) -> ProofError {
        ProofError::Storage(error)
    }
}

/// CEP:WHAT: Kind of one proof step.
/// CEP:WHY: DRAT has exactly two step kinds (addition and deletion); a closed vocabulary forbids ad-hoc kinds.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: 1 byte.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum ProofStepKind {
    /// CEP:WHAT: A clause was added to the solver database.
    /// CEP:WHY: The RUP/RAT-justified introduction step.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    /// CEP:SECURITY: none.
    Add = 0,
    /// CEP:WHAT: A clause was deleted from the solver database.
    /// CEP:WHY: Deletions need no justification in DRAT but must be replayed by the checker's database mirror.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the id matches a prior Add of the same clause.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
    /// CEP:SECURITY: none.
    Delete = 1,
    /// CEP:WHAT: An assumption unit was added as a hypothesis for an incremental solve (S38).
    /// CEP:WHY: Assumption units are hypotheses, not consequences: RUP does not hold for them by construction, so the internal checker skips justification for this kind while the text writer emits them as ordinary unit clauses (plain DRAT has no hypothesis syntax; the paired AssumptionDelete removes them from the trace).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the literal is a unit clause.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::assumption_steps_pair_up; unit/cold/drat_checker_test.rs::assumption_hypotheses_skip_rup.
    /// CEP:SECURITY: none.
    AssumptionAdd = 2,
    /// CEP:WHAT: An assumption unit's hypothesis period ended (the incremental solve returned).
    /// CEP:WHY: The paired removal keeps the trace's active set mirroring the solver database across incremental calls.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the id matches a prior AssumptionAdd of the same literal.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::assumption_steps_pair_up.
    /// CEP:SECURITY: none.
    AssumptionDelete = 3,
    /// CEP:WHAT: A problem clause was added to the solver database (an axiom of the run, not a derivation).
    /// CEP:WHY: DRAT proof files carry only derivations - the formula is a separate input - so the internal checker must distinguish axiom seeding (justification skipped, correspondence with the caller-supplied formula verified) from derived additions (RUP/RAT verified); the text writer renders axioms as ordinary clause lines, which are harmless for standard tools (re-adding a present clause passes RUP through the existing copy).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the clause came from the input formula.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::axiom_steps_match_formula; unit/cold/drat_checker_test.rs::{axioms_seed_the_database, axiom_mismatch_rejected}.
    /// CEP:SECURITY: none.
    AxiomAdd = 4,
}

/// CEP:WHAT: One recorded proof step: kind, proof id, and the literal extent in the blob.
/// CEP:WHY: Design 11.1 S42 (flat buffer of proof steps, bounded by kMaxProofSteps); the fixed 12-byte record keeps the buffer dense and serializable without indirection.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: literal extents are within the blob; ids are dense and 1-based for adds.
/// CEP:COST: 12 bytes.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, literals_stored_verbatim}.
/// CEP:SECURITY: private mutation discipline; all writes go through the recorder.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct ProofStep {
    /// CEP:WHAT: Step kind (addition or deletion).
    /// CEP:WHY: Drives the checker's database mirror and the writer's line format.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: ProofStepKind representation.
    /// CEP:COST: 1 byte plus padding.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    /// CEP:SECURITY: none.
    pub kind: ProofStepKind,
    /// CEP:WHAT: Proof id of the clause this step adds or deletes.
    /// CEP:WHY: LRAT deletion lines and checker bookkeeping need the stable identity.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= kFirstProofId.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
    /// CEP:SECURITY: none.
    pub proof_id: u32,
    /// CEP:WHAT: First literal slot in the blob.
    /// CEP:WHY: Steps reference literals by extent, keeping the record fixed-size.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: start + count <= blob capacity.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::literals_stored_verbatim.
    /// CEP:SECURITY: bounds-checked reads.
    pub literal_start: u32,
    /// CEP:WHAT: Literal count of the step's clause.
    /// CEP:WHY: Extent length; 0 only for the final empty clause is impossible (the empty clause has 0 literals and IS representable - count 0 with a valid start is the empty-clause add).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxSatClauseLiterals.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{literals_stored_verbatim, empty_clause_step_recorded}.
    /// CEP:SECURITY: none.
    pub literal_count: u32,
}

// CEP:WHAT: Proof step layout pin.
// CEP:WHY: The step buffer is serialized by the CEP-1 writer and replayed by the CEP-1 checker; drift is an interface break (CEP&CC 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes (kind byte plus padding, three u32 words).
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<ProofStep>() == 16);

// CEP:WHAT: Halving factor of the clause-offset-to-proof-id map's binary search.
// CEP:WHY: The midpoint divisor names its base (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time constant.
// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
// CEP:SECURITY: none.
const kProofMapSearchHalving: usize = 2;

/// CEP:WHAT: One entry of the clause-offset-to-proof-id map.
/// CEP:WHY: Deletions arrive by clause offset and must leave by proof id; the append-only sorted map is binary-searched, and ascending offsets (arena bump allocation) keep it sorted by construction.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: offsets strictly ascending across appends.
/// CEP:COST: 8 bytes.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
/// CEP:SECURITY: private mutation discipline.
#[repr(C)]
pub struct ProofMapEntry {
    /// CEP:WHAT: Clause offset in the shared storage.
    /// CEP:WHY: The lookup key.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: ascending across appends.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
    /// CEP:SECURITY: none.
    pub offset: core::cell::Cell<u32>,
    /// CEP:WHAT: Proof id assigned at addition time.
    /// CEP:WHY: The lookup value.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= kFirstProofId.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::ids_are_monotonic.
    /// CEP:SECURITY: none.
    pub proof_id: core::cell::Cell<u32>,
}

/// CEP:WHAT: The DRAT proof recorder: step buffer, offset-to-id map, literal blob, and the dense id counter.
/// CEP:WHY: Design 11.1 S41/S42; owning all buffers in one type makes the invariants (ids dense and 1-based, map ascending by offset, blob extents disjoint) local and testable, and gives the cold writer and checker one read-only surface.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ProofError.
/// CEP:ASSUMES: see file header.
/// CEP:COST: see file header.
/// CEP:EVIDENCE: unit/hot/sat_proof_test.rs; unit/cold/drat_writer_test.rs; unit/cold/drat_checker_test.rs.
/// CEP:SECURITY: capacities bounded.
pub struct ProofRecorder<'a> {
    /// CEP:WHAT: Step buffer (capacity steps).
    /// CEP:WHY: S42: the flat proof record.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: appends error at the capacity.
    /// CEP:ASSUMES: dense appends.
    /// CEP:COST: 12 bytes per step.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, capacity_enforced}.
    /// CEP:SECURITY: capacity bound.
    steps: &'a [core::cell::Cell<ProofStep>],
    /// CEP:WHAT: Number of steps recorded.
    /// CEP:WHY: Enumeration bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= steps.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    /// CEP:SECURITY: bounds checks on every read.
    step_count: core::cell::Cell<u32>,
    /// CEP:WHAT: Offset-to-id map (capacity entries).
    /// CEP:WHY: Deletion resolution.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: appends error at the capacity.
    /// CEP:ASSUMES: ascending offsets.
    /// CEP:COST: 8 bytes per entry.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
    /// CEP:SECURITY: capacity bound.
    map: &'a [ProofMapEntry],
    /// CEP:WHAT: Number of map entries.
    /// CEP:WHY: Map extent and binary-search bound.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= map.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::deletion_resolves_id.
    /// CEP:SECURITY: bounds checks.
    map_count: core::cell::Cell<u32>,
    /// CEP:WHAT: Literal blob (capacity u32 encodings).
    /// CEP:WHY: Step literals live in one flat array referenced by extents.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: appends error at the capacity.
    /// CEP:ASSUMES: extents never overlap.
    /// CEP:COST: 4 bytes per literal.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::literals_stored_verbatim.
    /// CEP:SECURITY: capacity bound.
    literals: &'a [core::cell::Cell<u32>],
    /// CEP:WHAT: Number of literals appended to the blob.
    /// CEP:WHY: The append cursor.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= literals.len().
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::literals_stored_verbatim.
    /// CEP:SECURITY: bounds checks.
    literal_count: core::cell::Cell<u32>,
    /// CEP:WHAT: Next proof id to assign.
    /// CEP:WHY: Dense 1-based ids (kFirstProofId start) keep LRAT lines stable and checker bookkeeping simple.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: ids never reused.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_proof_test.rs::ids_are_monotonic.
    /// CEP:SECURITY: none.
    next_id: core::cell::Cell<u32>,
}

impl<'a> ProofRecorder<'a> {
    // CEP:WHAT: Constructs the recorder with the default capacities.
    // CEP:WHY: Production entry point; the named constants are the documented defaults.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns capacity errors when the buffers do not fit the arena.
    // CEP:ASSUMES: the arena has room for (12 x steps + 8 x map + 4 x literals) bytes.
    // CEP:COST: O(capacity) one-time allocation and clear.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    // CEP:SECURITY: capacities validated before allocation.
    pub fn new(arena: &'a Arena) -> Result<ProofRecorder<'a>, ProofError> {
        ProofRecorder::new_with(
            arena,
            kSatProofStepCapacity,
            kSatProofMapCapacity,
            kSatProofLiteralCapacity,
        )
    }

    // CEP:WHAT: Constructs the recorder with explicit capacities.
    // CEP:WHY: CEP&CC 34.3: capacity and exhaustion tests must run at small, fast scales on the production code path.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns capacity errors when the buffers do not fit; rejects zero capacities.
    // CEP:ASSUMES: all capacities >= 1.
    // CEP:COST: O(capacity) one-time.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::capacity_enforced; security/phase3_bounds_test.rs::proof_step_budget_enforced.
    // CEP:SECURITY: bounds validated before allocation.
    pub fn new_with(
        arena: &'a Arena,
        step_capacity: u32,
        map_capacity: u32,
        literal_capacity: u32,
    ) -> Result<ProofRecorder<'a>, ProofError> {
        if step_capacity == 0 || map_capacity == 0 || literal_capacity == 0 {
            return Err(ProofError::StepBufferFull);
        }
        let step_range = arena
            .alloc_array::<core::cell::Cell<ProofStep>>(step_capacity)
            .map_err(|_| ProofError::StepBufferFull)?;
        let steps = arena
            .array::<core::cell::Cell<ProofStep>>(step_range)
            .map_err(|_| ProofError::StepBufferFull)?;
        let map_range = arena
            .alloc_array::<ProofMapEntry>(map_capacity)
            .map_err(|_| ProofError::MapFull)?;
        let map = arena
            .array::<ProofMapEntry>(map_range)
            .map_err(|_| ProofError::MapFull)?;
        for entry in map.iter() {
            entry.offset.set(u32::MAX);
            entry.proof_id.set(kInvalidProofId);
        }
        let literal_range = arena
            .alloc_array::<core::cell::Cell<u32>>(literal_capacity)
            .map_err(|_| ProofError::LiteralBlobFull)?;
        let literals = arena
            .array::<core::cell::Cell<u32>>(literal_range)
            .map_err(|_| ProofError::LiteralBlobFull)?;
        Ok(ProofRecorder {
            steps,
            step_count: core::cell::Cell::new(0),
            map,
            map_count: core::cell::Cell::new(0),
            literals,
            literal_count: core::cell::Cell::new(0),
            next_id: core::cell::Cell::new(kFirstProofId),
        })
    }

    // CEP:WHAT: Records a clause addition: appends the step, the literals, and the map entry; returns the assigned proof id.
    // CEP:WHY: S41: steps are emitted as clauses are added; the id assignment is dense and 1-based so LRAT lines are stable across the whole proof.
    // CEP:STATUS: complete
    // CEP:FAILURE: capacity errors at any buffer bound; InvariantViolation-mapped StepBufferFull never occurs here - ordering violations surface as double-add of the same offset below.
    // CEP:ASSUMES: offset was never added before; offsets arrive in ascending order; the caller registers the clause with the registry separately (the recorder does not touch the registry).
    // CEP:COST: O(1) appends.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, ids_are_monotonic, capacity_enforced}.
    // CEP:SECURITY: capacity bounds.
    pub fn record_add(
        &self,
        clause_offset: u32,
        literals: &[SatLiteral],
    ) -> Result<u32, ProofError> {
        self.record_clause_add(clause_offset, literals, ProofStepKind::Add)
    }

    // CEP:WHAT: Records an axiom (problem-clause) addition: the map entry plus an AxiomAdd step.
    // CEP:WHY: The checker seeds its database from axiom steps and verifies their one-to-one correspondence with the caller-supplied formula, while derived additions carry the RUP/RAT burden (Spec 11 section 3); the writer renders axioms as ordinary clause lines.
    // CEP:STATUS: complete
    // CEP:FAILURE: as record_add.
    // CEP:ASSUMES: offset is a problem clause just added to the database.
    // CEP:COST: as record_add.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{axiom_steps_match_formula, steps_recorded_in_order}; unit/cold/drat_checker_test.rs::axioms_seed_the_database.
    // CEP:SECURITY: capacity bounds.
    pub fn record_axiom_add(
        &self,
        clause_offset: u32,
        literals: &[SatLiteral],
    ) -> Result<u32, ProofError> {
        self.record_clause_add(clause_offset, literals, ProofStepKind::AxiomAdd)
    }

    // CEP:WHAT: Shared clause-addition recording for both step kinds (one append implementation).
    // CEP:WHY: CEP&CC Law 3: the map append, literal copy, and id assignment must not be duplicated per kind.
    // CEP:STATUS: complete
    // CEP:FAILURE: as record_add.
    // CEP:ASSUMES: kind is Add or AxiomAdd.
    // CEP:COST: as record_add.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, axiom_steps_match_formula}.
    // CEP:SECURITY: capacity bounds.
    fn record_clause_add(
        &self,
        clause_offset: u32,
        literals: &[SatLiteral],
        kind: ProofStepKind,
    ) -> Result<u32, ProofError> {
        let step_index = self.step_count.get() as usize;
        if step_index >= self.steps.len() {
            return Err(ProofError::StepBufferFull);
        }
        let map_index = self.map_count.get() as usize;
        if map_index >= self.map.len() {
            return Err(ProofError::MapFull);
        }
        if map_index > 0 && self.map[map_index - 1].offset.get() >= clause_offset {
            return Err(ProofError::UnmappedOffset);
        }
        let start = self.literal_count.get();
        let extent = literals.len() as u32;
        if start + extent > self.literals.len() as u32 {
            return Err(ProofError::LiteralBlobFull);
        }
        let proof_id = self.next_id.get();
        self.steps[step_index].set(ProofStep {
            kind,
            proof_id,
            literal_start: start,
            literal_count: extent,
        });
        for (index, literal) in literals.iter().enumerate() {
            self.literals[start as usize + index].set(literal.encoding());
        }
        self.map[map_index].offset.set(clause_offset);
        self.map[map_index].proof_id.set(proof_id);
        self.step_count.set(self.step_count.get() + 1);
        self.map_count.set(self.map_count.get() + 1);
        self.literal_count.set(start + extent);
        self.next_id.set(proof_id + 1);
        Ok(proof_id)
    }

    // CEP:WHAT: Records a clause deletion: reads the clause's literals from storage, resolves its proof id, and appends the step.
    // CEP:WHY: S41: deletions are emitted as clauses are deleted; deletions need no DRAT justification but must mirror the database lifecycle for the checker; storing the literals supports plain DRAT deletion lines.
    // CEP:STATUS: complete
    // CEP:FAILURE: UnmappedOffset when the clause was never added (bookkeeping divergence, loud); Storage on unreadable records; capacity errors at the bounds.
    // CEP:ASSUMES: the offset was added through record_add and has not been deleted yet.
    // CEP:COST: O(log map) id resolution plus O(length) literal copy.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{deletion_resolves_id, unmapped_deletion_rejected, capacity_enforced}.
    // CEP:SECURITY: bounds-checked reads.
    pub fn record_delete(
        &self,
        clause_offset: u32,
        storage: &ClauseStorage<'_>,
    ) -> Result<(), ProofError> {
        let proof_id = self
            .proof_id_of(clause_offset)
            .ok_or(ProofError::UnmappedOffset)?;
        let header = storage.header(clause_offset)?;
        let length = header.length;
        let step_index = self.step_count.get() as usize;
        if step_index >= self.steps.len() {
            return Err(ProofError::StepBufferFull);
        }
        let start = self.literal_count.get();
        if start + length > self.literals.len() as u32 {
            return Err(ProofError::LiteralBlobFull);
        }
        self.steps[step_index].set(ProofStep {
            kind: ProofStepKind::Delete,
            proof_id,
            literal_start: start,
            literal_count: length,
        });
        for index in 0..length {
            let literal = storage.literal(clause_offset, index)?;
            self.literals[start as usize + index as usize].set(literal.encoding());
        }
        self.step_count.set(self.step_count.get() + 1);
        self.literal_count.set(start + length);
        Ok(())
    }

    // CEP:WHAT: Resolves the proof id of a clause offset.
    // CEP:WHY: Binary search over the ascending map; also the surface the solver uses to check recording state.
    // CEP:STATUS: complete
    // CEP:FAILURE: Ok(None) when the offset was never added.
    // CEP:ASSUMES: ascending-offset invariant.
    // CEP:COST: O(log map).
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{ids_are_monotonic, deletion_resolves_id}.
    // CEP:SECURITY: none.
    pub fn proof_id_of(&self, clause_offset: u32) -> Option<u32> {
        let count = self.map_count.get() as usize;
        let mut low: usize = 0;
        let mut high: usize = count;
        while low < high {
            let mid = low + (high - low) / kProofMapSearchHalving;
            let value = self.map[mid].offset.get();
            if value < clause_offset {
                low = mid + 1;
            } else if value > clause_offset {
                high = mid;
            } else {
                return Some(self.map[mid].proof_id.get());
            }
        }
        None
    }

    // CEP:WHAT: Records an assumption unit addition (step only, no map entry, fresh id) and returns the id.
    // CEP:WHY: solve_with_assumptions pushes assumptions as decision levels, not clauses, but a self-contained DRAT trace of an unsat-under-assumptions refutation needs the assumptions as unit clauses; the virtual step keeps the clause-offset namespace untouched (the map stays clause-only), and the returned id lets the epilogue record the matching deletion.
    // CEP:STATUS: complete
    // CEP:FAILURE: capacity errors at the bounds.
    // CEP:ASSUMES: called at assumption push time, before any step that depends on the assumption.
    // CEP:COST: O(1) append.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{assumption_steps_pair_up, steps_recorded_in_order}.
    // CEP:SECURITY: capacity bounds.
    pub fn record_assumption_add(&self, literal: SatLiteral) -> Result<u32, ProofError> {
        self.append_step(ProofStepKind::AssumptionAdd, &[literal])
    }

    // CEP:WHAT: Records the deletion of a previously recorded assumption unit (step only, by id).
    // CEP:WHY: Assumptions are per-solve: the trace must remove them before the next incremental solve's steps, mirroring the solver's own cleanup.
    // CEP:STATUS: complete
    // CEP:FAILURE: capacity errors at the bounds.
    // CEP:ASSUMES: id came from record_assumption_add of the same literal.
    // CEP:COST: O(1) append.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::assumption_steps_pair_up.
    // CEP:SECURITY: capacity bounds.
    pub fn record_assumption_delete(
        &self,
        proof_id: u32,
        literal: SatLiteral,
    ) -> Result<(), ProofError> {
        let step_index = self.step_count.get() as usize;
        if step_index >= self.steps.len() {
            return Err(ProofError::StepBufferFull);
        }
        if self.literal_count.get() + 1 > self.literals.len() as u32 {
            return Err(ProofError::LiteralBlobFull);
        }
        self.steps[step_index].set(ProofStep {
            kind: ProofStepKind::AssumptionDelete,
            proof_id,
            literal_start: self.literal_count.get(),
            literal_count: 1,
        });
        self.literals[self.literal_count.get() as usize].set(literal.encoding());
        self.step_count.set(self.step_count.get() + 1);
        self.literal_count.set(self.literal_count.get() + 1);
        Ok(())
    }

    // CEP:WHAT: Records the final empty-clause addition of a refutation and returns its id.
    // CEP:WHY: A DRAT refutation ends with the empty clause; the solver emits it when it returns Unsatisfiable (level-0 conflict, falsified unit) or UnsatUnderAssumptions (root-region conflict with assumption units in the trace); the RUP justification is verified mechanically by the checker (Spec 11 section 4).
    // CEP:STATUS: complete
    // CEP:FAILURE: capacity error at the step bound.
    // CEP:ASSUMES: called exactly once, at the refuting return.
    // CEP:COST: O(1) append.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::empty_clause_step_recorded; unit/cold/drat_checker_test.rs::refutation_proofs_verify.
    // CEP:SECURITY: capacity bound.
    pub fn record_empty_clause(&self) -> Result<u32, ProofError> {
        let proof_id = self.next_id.get();
        let step_index = self.step_count.get() as usize;
        if step_index >= self.steps.len() {
            return Err(ProofError::StepBufferFull);
        }
        self.steps[step_index].set(ProofStep {
            kind: ProofStepKind::Add,
            proof_id,
            literal_start: self.literal_count.get(),
            literal_count: 0,
        });
        self.step_count.set(self.step_count.get() + 1);
        self.next_id.set(proof_id + 1);
        Ok(proof_id)
    }

    // CEP:WHAT: Appends one step with fresh id and the given literals (internal primitive).
    // CEP:WHY: The assumption-add path shares the step-append code with record_add without touching the map (CEP&CC Law 3: one append implementation).
    // CEP:STATUS: complete
    // CEP:FAILURE: capacity errors at the bounds.
    // CEP:ASSUMES: none.
    // CEP:COST: O(1) append.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::{steps_recorded_in_order, assumption_steps_pair_up}.
    // CEP:SECURITY: capacity bounds.
    fn append_step(&self, kind: ProofStepKind, literals: &[SatLiteral]) -> Result<u32, ProofError> {
        let step_index = self.step_count.get() as usize;
        if step_index >= self.steps.len() {
            return Err(ProofError::StepBufferFull);
        }
        let start = self.literal_count.get();
        let extent = literals.len() as u32;
        if start + extent > self.literals.len() as u32 {
            return Err(ProofError::LiteralBlobFull);
        }
        let proof_id = self.next_id.get();
        self.steps[step_index].set(ProofStep {
            kind,
            proof_id,
            literal_start: start,
            literal_count: extent,
        });
        for (index, literal) in literals.iter().enumerate() {
            self.literals[start as usize + index].set(literal.encoding());
        }
        self.step_count.set(self.step_count.get() + 1);
        self.literal_count.set(start + extent);
        self.next_id.set(proof_id + 1);
        Ok(proof_id)
    }

    // CEP:WHAT: Returns the number of recorded steps.
    // CEP:WHY: Enumeration bound for the writer and checker.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    // CEP:SECURITY: none.
    pub fn step_count(&self) -> u32 {
        self.step_count.get()
    }

    // CEP:WHAT: Returns the step record at an index.
    // CEP:WHY: Read surface for the cold writer and checker; bounds-checked so forged indices fail loudly.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-range indices (a read API, not a mutation; None is the honest answer, not a panic).
    // CEP:ASSUMES: index < step_count.
    // CEP:COST: 1 bounds check.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::steps_recorded_in_order.
    // CEP:SECURITY: bounds-checked.
    pub fn step(&self, index: u32) -> Option<ProofStep> {
        let slot = index as usize;
        if slot >= self.step_count.get() as usize {
            return None;
        }
        Some(self.steps[slot].get())
    }

    // CEP:WHAT: Returns the i-th literal of a step.
    // CEP:WHY: Read surface for the writer and checker.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None for out-of-extent indices.
    // CEP:ASSUMES: step came from step(); index < step.literal_count.
    // CEP:COST: 1 bounds check.
    // CEP:EVIDENCE: unit/hot/sat_proof_test.rs::literals_stored_verbatim.
    // CEP:SECURITY: bounds-checked.
    pub fn step_literal(&self, step: ProofStep, index: u32) -> Option<SatLiteral> {
        let slot = step.literal_start as usize + index as usize;
        if index >= step.literal_count || slot >= self.literals.len() {
            return None;
        }
        Some(SatLiteral::from_encoding(self.literals[slot].get()))
    }
}
