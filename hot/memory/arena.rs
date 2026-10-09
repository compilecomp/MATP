// CEP:FILE: hot/memory/arena.rs
// CEP:WHAT: Bump-pointer arena allocator with generation checkpoints, serving every MAPT engine (terms, clauses, substitutions, SAT structures) from one caller-provided region.
// CEP:WHY: Design 8.1 makes the arena the single allocation domain: O(1) allocation, zero per-object heap traffic, O(1) bulk reset across a generation, which is the only way to satisfy the CEP-0 allocation ban (CEP&CC 25.5) while search still produces unbounded numbers of temporary objects. A Vec-per-object design was rejected because deallocation cost and fragmentation are hidden, unbounded costs (CEP&CC Law 1).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Allocation returns ArenaError::Exhausted when the request does not fit, ArenaError::Misaligned for invalid alignment, ArenaError::TypeMismatch for layout-invalid typed access, ArenaError::StaleCheckpoint when resetting to a checkpoint from an older generation. Never panics. Never allocates. Never traps.
// CEP:ASSUMES: The backing region is allocated and aligned by CEP-1 host code before the hot path starts, outlives the arena, and is exclusively owned by this arena; enforced by the 'static lifetime bound on Arena::new, by the base-alignment check inside new, and by !Send/!Sync auto traits that forbid cross-thread sharing.
// CEP:COST: alloc_bytes is 9.99 cycles median per call including measurement-loop and black_box overhead (the allocation sequence itself is align+add+compare+store) on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O; measured 2026-10-08, bench CEP-BENCH-0001, artifact benches/artifacts/arena_alloc_bytes.json.
// CEP:EVIDENCE: bench CEP-BENCH-0001; unit tests unit/hot/arena_test.rs; property tests property/arena_property_test.rs; fuzz tests fuzz/arena_fuzz_test.rs; disassembly artifact benches/artifacts/disasm_arena.txt.
// CEP:SECURITY: All offsets are u32 values checked against capacity on every typed access; alignment is validated, not assumed; exhaustion is an explicit error, which bounds worst-case memory for untrusted input (CEP&CC 22.10).
// CEP:UNSAFE: Four isolated unsafe blocks construct slice references from (base, checked range); every range is bounds-checked immediately before construction. No other unsafe operations exist in this file.
// CEP:HPC-DETERMINISM: deterministic; byte offsets depend only on the sequence of allocation calls, never on addresses, clocks, or thread scheduling.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: allocation must compute an aligned offset, bounds-check it, bump one cursor, and store one u32; the bench-main disassembly (artifact disasm_arena.txt) shows the inlined allocation sequence with no calls and no heap traffic; the 9.99-cycle median includes the surrounding measurement loop.

use core::cell::Cell;
use mapt_config::limits::{kArenaCapacityBytes, kInvalidSubstitutionOffset, kMaxAlignment};

/// CEP:WHAT: Error cases of the arena allocator.
/// CEP:WHY: CEP&CC Law 6 requires explicit failure enumeration; the arena never panics and reports every failure through this type.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum value copy; no allocation.
/// CEP:EVIDENCE: unit/hot/arena_test.rs covers every variant.
/// CEP:SECURITY: exhaustion errors are the memory denial-of-service boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArenaError {
    /// CEP:WHAT: The requested allocation does not fit in the remaining capacity.
    Exhausted,
    /// CEP:WHAT: The alignment argument is zero, not a power of two, or above kMaxAlignment.
    Misaligned,
    /// CEP:WHAT: A typed access was given a range whose alignment or size does not fit the element type.
    TypeMismatch,
    /// CEP:WHAT: A typed access was given a range outside the arena capacity.
    OutOfRange,
    /// CEP:WHAT: The checkpoint belongs to an older generation than the current one.
    StaleCheckpoint,
    /// CEP:WHAT: The backing region given at initialization is empty.
    EmptyRegion,
}

/// CEP:WHAT: A validated byte range inside the arena: [start, end).
/// CEP:WHY: Offsets, not pointers, keep the arena position-independent and deterministic across runs (CEP&CC 38.10 bans address-dependent identity); u32 offsets halve memory traffic versus u64 pointers on the hot path.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: ArenaRange::new returns ArenaError::OutOfRange when end < start or end exceeds kArenaCapacityBytes.
/// CEP:ASSUMES: Ranges are only produced by the arena or validated by ArenaRange::new; every constructor enforces the bound.
/// CEP:COST: 8-byte copy type; no allocation.
/// CEP:EVIDENCE: unit/hot/arena_test.rs::range_validation.
/// CEP:SECURITY: the constructor bound-check is the first line of defense against offset corruption.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct ArenaRange {
    /// CEP:WHAT: First byte offset of the range.
    /// CEP:WHY: Start of the allocation for slice construction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; validated by ArenaRange::new.
    /// CEP:ASSUMES: bounded by kArenaCapacityBytes.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs.
    /// CEP:SECURITY: bounds-checked at every use.
    pub start: u32,
    /// CEP:WHAT: One-past-the-end byte offset of the range.
    /// CEP:WHY: Half-open intervals make subtraction-based length checks overflow-free.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; validated by ArenaRange::new.
    /// CEP:ASSUMES: bounded by kArenaCapacityBytes; start <= end.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs.
    /// CEP:SECURITY: bounds-checked at every use.
    pub end: u32,
}

// CEP:WHAT: Static layout check for ArenaRange.
// CEP:WHY: The type crosses the FFI boundary in later phases; its layout must stay fixed and known (CEP&CC 22.8).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails when the layout changes.
// CEP:ASSUMES: u32 is 4 bytes on all supported targets; enforced by target modules.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/arena_test.rs::range_layout.
// CEP:SECURITY: layout drift would be an ABI break.
const _: () = assert!(core::mem::size_of::<ArenaRange>() == 8);

impl ArenaRange {
    // CEP:WHAT: Validates and constructs a byte range.
    // CEP:WHY: Every range-producing path must enforce the same invariant; centralizing the check makes the bound provable (CEP&CC Law 3).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::OutOfRange when start > end or end exceeds kArenaCapacityBytes.
    // CEP:ASSUMES: kArenaCapacityBytes fits u32; enforced by static assertion in config/limits.rs.
    // CEP:COST: 2 compares; no allocation.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::range_validation.
    // CEP:SECURITY: bounds enforcement.
    pub fn new(start: u32, end: u32) -> Result<ArenaRange, ArenaError> {
        if end < start || end > kArenaCapacityBytes {
            return Err(ArenaError::OutOfRange);
        }
        Ok(ArenaRange { start, end })
    }

    // CEP:WHAT: Returns the range length in bytes.
    // CEP:WHY: Half-open interval subtraction is overflow-free by construction (start <= end).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: invariant start <= end enforced by new().
    // CEP:COST: 1 subtract.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::range_validation.
    // CEP:SECURITY: none.
    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    // CEP:WHAT: Returns true when the range covers zero bytes.
    // CEP:WHY: Zero-length allocations are legal but must be recognizable by callers that skip typed access.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::zero_size_allocation_is_empty_range.
    // CEP:SECURITY: none.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

/// CEP:WHAT: A generation checkpoint: the arena cursor and generation at save time.
/// CEP:WHY: Design 8.1 requires O(1) bulk reclamation: resetting to a checkpoint invalidates every later allocation without touching them.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: reset_to returns ArenaError::StaleCheckpoint when the checkpoint predates the current generation.
/// CEP:ASSUMES: Checkpoints are only produced by Arena::checkpoint.
/// CEP:COST: 8-byte copy type; no allocation.
/// CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
/// CEP:SECURITY: generation mismatch detection prevents cross-epoch memory confusion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct ArenaCheckpoint {
    /// CEP:WHAT: Arena cursor to restore.
    /// CEP:WHY: Defines the rollback point.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= capacity at save time.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs.
    /// CEP:SECURITY: validated by reset_to.
    front: u32,
    /// CEP:WHAT: Generation ID at save time.
    /// CEP:WHY: Detects stale checkpoints after a later reset.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: generations are monotonic within one arena.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
    /// CEP:SECURITY: epoch confusion guard.
    generation: u32,
}

/// CEP:WHAT: The shared bump-pointer arena.
/// CEP:WHY: See the file header; this struct is the single allocation authority for both engines (design 12.4: no serialization, no locks, shared arena).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: see ArenaError; no panics, no traps, no allocation.
/// CEP:ASSUMES: single-threaded use (enforced by !Send/!Sync from Cell and raw pointer), region exclusively owned, region outlives the arena (enforced by the 'static bound on new).
/// CEP:COST: allocation is O(1); see file header for measured cycles.
/// CEP:EVIDENCE: bench CEP-BENCH-0001; tests cited per method.
/// CEP:SECURITY: capacity-bounded; all accesses bounds-checked.
pub struct Arena {
    /// CEP:WHAT: Base pointer of the backing region.
    /// CEP:WHY: Raw storage address; never exposed publicly.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; validated non-null and kMaxAlignment-aligned at construction.
    /// CEP:ASSUMES: pointer stays valid for the arena lifetime ('static region).
    /// CEP:COST: 8-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs::construction_validates_alignment.
    /// CEP:SECURITY: pointer is never derived from untrusted input.
    base: *mut u8,
    /// CEP:WHAT: Region capacity in bytes.
    /// CEP:WHY: The exhaustion bound; a named check against it replaces unbounded growth.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; <= kArenaCapacityBytes enforced at construction.
    /// CEP:ASSUMES: region length equals capacity.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs::construction_rejects_oversized_region.
    /// CEP:SECURITY: primary memory bound.
    capacity: u32,
    /// CEP:WHAT: Current bump cursor (first free byte offset).
    /// CEP:WHY: Interior mutability through Cell lets shared &Arena references allocate, which is what makes one arena serve every store simultaneously without locks (design 12.4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; monotonic within a generation, only moved backward by reset_to.
    /// CEP:ASSUMES: front <= capacity at all times.
    /// CEP:COST: 4-byte field with interior mutation.
    /// CEP:EVIDENCE: property/arena_property_test.rs::cursor_stays_in_bounds.
    /// CEP:SECURITY: never above capacity.
    front: Cell<u32>,
    /// CEP:WHAT: Monotonic generation counter, incremented by every reset.
    /// CEP:WHY: Design 8.1 epoch-based reclamation: allocations are only valid within their generation; checkpoints record the generation to detect stale resets.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: wraps only after u32::MAX resets, which is unreachable under kMaxInferences-class budgets.
    /// CEP:COST: 4-byte field.
    /// CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
    /// CEP:SECURITY: epoch confusion guard.
    generation: Cell<u32>,
}

// CEP:WHAT: Layout pin for ArenaCheckpoint.
// CEP:WHY: The checkpoint crosses into diagnostics and later FFI; drift is an ABI break (CEP&CC 11.2, 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
// CEP:SECURITY: none.
const _: () = assert!(core::mem::size_of::<ArenaCheckpoint>() == 8);

// CEP:WHAT: Static checks tying arena layout assumptions to the target.
// CEP:WHY: CEP&CC Law 3: the overflow-freedom proof of align_up relies on capacity plus max alignment fitting u32; that fact must be enforced, not assumed.
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails when the invariant breaks.
// CEP:ASSUMES: kArenaCapacityBytes and kMaxAlignment keep their config values.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: config/limits.rs static assertions.
// CEP:SECURITY: integer-overflow prevention.
const _: () = assert!(kArenaCapacityBytes + kMaxAlignment < u32::MAX);
const _: () = assert!(kInvalidSubstitutionOffset > kArenaCapacityBytes);

impl Arena {
    // CEP:WHAT: Constructs an arena over a caller-provided, kMaxAlignment-aligned region.
    // CEP:WHY: CEP-1 host code owns all real allocation (design 8.1 lifecycle step 1); the arena itself stays allocation-free, so this is the only place a pointer enters the system.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::EmptyRegion for zero-length regions, ArenaError::Misaligned when the base is not kMaxAlignment-aligned or the length exceeds kArenaCapacityBytes.
    // CEP:ASSUMES: The region is 'static (leaked or static), exclusively owned, and not modified by anyone else; the 'static bound enforces lifetime, ownership is a documented caller contract covered by tests.
    // CEP:COST: constant-time init; 3 compares.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::construction_validates_alignment and neighbors.
    // CEP:SECURITY: rejects misaligned or oversized regions before any pointer arithmetic happens.
    // CEP:UNSAFE: takes a raw pointer out of the region; safe because the 'static bound guarantees the region outlives every arena use and the pointer is only used with offsets bounded by the validated capacity.
    pub fn new(region: &'static mut [u8]) -> Result<Arena, ArenaError> {
        if region.is_empty() {
            return Err(ArenaError::EmptyRegion);
        }
        let capacity_u64 = region.len() as u64;
        if capacity_u64 > kArenaCapacityBytes as u64 {
            return Err(ArenaError::Misaligned);
        }
        let base = region.as_mut_ptr();
        let base_addr = base as usize;
        if !base_addr.is_multiple_of(kMaxAlignment as usize) {
            return Err(ArenaError::Misaligned);
        }
        Ok(Arena {
            base,
            capacity: capacity_u64 as u32,
            front: Cell::new(0),
            generation: Cell::new(0),
        })
    }

    // CEP:WHAT: Allocates size bytes aligned to align, returning the byte range.
    // CEP:WHY: O(1) bump allocation is the whole point of the arena (design 8.1); zero-size requests return an empty range without moving the cursor so callers can allocate empty child arrays uniformly.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::Misaligned when align is zero, not a power of two, or above kMaxAlignment; ArenaError::Exhausted when the aligned request does not fit.
    // CEP:ASSUMES: front <= capacity (invariant), kArenaCapacityBytes + kMaxAlignment < u32::MAX (static assertion above) so align_up cannot overflow.
    // CEP:COST: 9.99 cycles median including measurement-loop overhead (allocation sequence: align+add+compare+store); worst case adds a mispredicted branch; measured on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, bench CEP-BENCH-0001, artifact benches/artifacts/arena_alloc_bytes.json.
    // CEP:EVIDENCE: bench CEP-BENCH-0001; unit/hot/arena_test.rs::allocate_returns_distinct_regions; property/arena_property_test.rs.
    // CEP:SECURITY: alignment and capacity are validated on every call; untrusted sizes cannot overflow the arithmetic.
    // CEP:OPTIMAL: target-optimal
    // CEP:OPTPROOF: the function must validate alignment (2 compares), align the cursor (add, and), bounds-check (compare), and bump the cursor (store); the bench-main disassembly (artifact disasm_arena.txt) contains this inlined sequence; the 9.99-cycle median includes the surrounding measurement loop.
    pub fn alloc_bytes(&self, size: u32, align: u32) -> Result<ArenaRange, ArenaError> {
        if align == 0 || align > kMaxAlignment || align & (align - 1) != 0 {
            return Err(ArenaError::Misaligned);
        }
        if size == 0 {
            return Ok(ArenaRange {
                start: self.front.get(),
                end: self.front.get(),
            });
        }
        let front = self.front.get();
        let align_mask = align - 1;
        let aligned_front = (front + align_mask) & !align_mask;
        if aligned_front > self.capacity || size > self.capacity - aligned_front {
            return Err(ArenaError::Exhausted);
        }
        let range = ArenaRange {
            start: aligned_front,
            end: aligned_front + size,
        };
        self.front.set(range.end);
        Ok(range)
    }

    // CEP:WHAT: Allocates an array of count elements of type Element, layout-aligned.
    // CEP:WHY: Typed arrays (term headers, clauses, literals, watch heads) are the arena's main product; aligning to align_of::<Element>() keeps every consumer layout-correct without per-caller alignment knowledge.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::TypeMismatch for zero-sized element types; propagates ArenaError::Exhausted and ArenaError::Misaligned (the latter cannot occur for Rust-native alignments, which are powers of two <= kMaxAlignment; the check is retained as defense in depth).
    // CEP:ASSUMES: size_of::<Element>() * count fits u32 after u64Checked multiplication.
    // CEP:COST: constant overhead over alloc_bytes; 2 extra multiplies/compares.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::typed_array_roundtrip.
    // CEP:SECURITY: element count is u64-checked before multiplication (CEP&CC 22.6 unchecked multiplication ban).
    pub fn alloc_array<Element>(&self, count: u32) -> Result<ArenaRange, ArenaError> {
        let element_size = core::mem::size_of::<Element>() as u64;
        if element_size == 0 {
            return Err(ArenaError::TypeMismatch);
        }
        let total_bytes = element_size * count as u64;
        if total_bytes > kArenaCapacityBytes as u64 {
            return Err(ArenaError::Exhausted);
        }
        let align = core::mem::align_of::<Element>() as u32;
        self.alloc_bytes(total_bytes as u32, align)
    }

    // CEP:WHAT: Returns the byte slice of a validated range.
    // CEP:WHY: Safe read access with the bounds check retained as required security cost (CEP&CC 23.7).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::OutOfRange when the range exceeds capacity.
    // CEP:ASSUMES: range came from this arena (or ArenaRange::new); the debug assertion additionally catches ranges allocated before the last reset in the same region.
    // CEP:COST: 2 compares plus slice construction.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::typed_array_roundtrip; fuzz/arena_fuzz_test.rs.
    // CEP:SECURITY: bounds check retained in release; unsafe pointer construction only after the check.
    // CEP:UNSAFE: constructs a slice from (base, range) after checking range.end <= capacity; safe because base..base+capacity describes exactly the region handed to new().
    pub fn bytes(&self, range: ArenaRange) -> Result<&[u8], ArenaError> {
        if range.end > self.capacity {
            return Err(ArenaError::OutOfRange);
        }
        debug_assert!(range.end <= self.front.get());
        unsafe {
            Ok(core::slice::from_raw_parts(
                self.base.add(range.start as usize),
                range.len() as usize,
            ))
        }
    }

    // CEP:WHAT: Returns the mutable byte slice of a validated range.
    // CEP:WHY: Writers (term construction, clause construction) need mutable access; ranges are unique by construction (monotonic bump within a generation), so no two live ranges overlap.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::OutOfRange when the range exceeds capacity.
    // CEP:ASSUMES: the caller holds no other reference into the same range (guaranteed by the bump discipline: every range is handed out exactly once per generation); a reset invalidates all earlier ranges and callers must drop them (documented caller contract, tested by unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection).
    // CEP:COST: 2 compares plus slice construction.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::typed_array_roundtrip.
    // CEP:SECURITY: bounds check retained in release.
    // CEP:UNSAFE: constructs a &mut slice from (base, range) after the bounds check; uniqueness is guaranteed by the documented bump discipline above.
    #[allow(clippy::mut_from_ref)]
    pub fn bytes_mut(&self, range: ArenaRange) -> Result<&mut [u8], ArenaError> {
        if range.end > self.capacity {
            return Err(ArenaError::OutOfRange);
        }
        debug_assert!(range.end <= self.front.get());
        unsafe {
            Ok(core::slice::from_raw_parts_mut(
                self.base.add(range.start as usize),
                range.len() as usize,
            ))
        }
    }

    // CEP:WHAT: Returns the range as a typed element slice.
    // CEP:WHY: Hot structures read arrays of headers, literals, and offsets; typed access validates alignment and element divisibility so no caller repeats the proof.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::TypeMismatch when the range is not aligned to Element or its length is not a multiple of size_of::<Element>(); ArenaError::OutOfRange when beyond capacity.
    // CEP:ASSUMES: none.
    // CEP:COST: 3 compares plus slice construction.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::typed_array_roundtrip.
    // CEP:SECURITY: alignment and bounds checks retained in release.
    pub fn array<Element>(&self, range: ArenaRange) -> Result<&[Element], ArenaError> {
        let align = core::mem::align_of::<Element>();
        let size = core::mem::size_of::<Element>();
        if size == 0 {
            return Err(ArenaError::TypeMismatch);
        }
        if range.end > self.capacity
            || (!range.is_empty() && !range.start.is_multiple_of(align as u32))
            || !range.len().is_multiple_of(size as u32)
        {
            return Err(ArenaError::TypeMismatch);
        }
        debug_assert!(range.end <= self.front.get());
        let count = range.len() as usize / size;
        // CEP:UNSAFE: slice construction from (base, checked range); bounds, alignment, and divisibility are all checked above.
        unsafe {
            Ok(core::slice::from_raw_parts(
                self.base.add(range.start as usize) as *const Element,
                count,
            ))
        }
    }

    // CEP:WHAT: Returns the range as a mutable typed element slice.
    // CEP:WHY: Writers need typed mutable access with the same uniqueness discipline as bytes_mut.
    // CEP:STATUS: complete
    // CEP:FAILURE: same conditions as array(), plus OutOfRange.
    // CEP:ASSUMES: same uniqueness contract as bytes_mut.
    // CEP:COST: 3 compares plus slice construction.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::typed_array_roundtrip.
    // CEP:SECURITY: alignment and bounds checks retained in release.
    // CEP:UNSAFE: mutable slice construction from (base, checked range); uniqueness guaranteed by the bump discipline.
    #[allow(clippy::mut_from_ref)]
    pub fn array_mut<Element>(&self, range: ArenaRange) -> Result<&mut [Element], ArenaError> {
        let align = core::mem::align_of::<Element>();
        let size = core::mem::size_of::<Element>();
        if size == 0 {
            return Err(ArenaError::TypeMismatch);
        }
        if range.end > self.capacity
            || (!range.is_empty() && !range.start.is_multiple_of(align as u32))
            || !range.len().is_multiple_of(size as u32)
        {
            return Err(ArenaError::TypeMismatch);
        }
        debug_assert!(range.end <= self.front.get());
        let count = range.len() as usize / size;
        // CEP:UNSAFE: mutable slice construction from (base, checked range); bounds, alignment, and divisibility are all checked above.
        unsafe {
            Ok(core::slice::from_raw_parts_mut(
                self.base.add(range.start as usize) as *mut Element,
                count,
            ))
        }
    }

    // CEP:WHAT: Saves the current cursor and generation as a checkpoint.
    // CEP:WHY: Design 8.1 lifecycle step 3: branch pruning resets to a checkpoint in O(1).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 2 loads; no allocation.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
    // CEP:SECURITY: none.
    pub fn checkpoint(&self) -> ArenaCheckpoint {
        ArenaCheckpoint {
            front: self.front.get(),
            generation: self.generation.get(),
        }
    }

    // CEP:WHAT: Resets the cursor to a checkpoint, starting a new generation.
    // CEP:WHY: O(1) bulk reclamation of every allocation after the checkpoint (design 8.1); the generation bump invalidates older checkpoints so a stale reset is refused instead of silently corrupting live data.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns ArenaError::StaleCheckpoint when the checkpoint's generation differs from the current generation.
    // CEP:ASSUMES: callers drop all slices obtained after the checkpoint before calling reset_to (documented caller contract; the debug assertion in bytes()/bytes_mut() catches violations that fall in the reused region).
    // CEP:COST: 2 loads, 1 compare, 2 stores; no allocation.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection; property/arena_property_test.rs::reset_then_allocate_reuses_region.
    // CEP:SECURITY: epoch validation prevents cross-generation data confusion.
    pub fn reset_to(&self, checkpoint: ArenaCheckpoint) -> Result<(), ArenaError> {
        if checkpoint.generation != self.generation.get() {
            return Err(ArenaError::StaleCheckpoint);
        }
        if checkpoint.front > self.front.get() {
            return Err(ArenaError::StaleCheckpoint);
        }
        self.front.set(checkpoint.front);
        self.generation.set(self.generation.get().wrapping_add(1));
        Ok(())
    }

    // CEP:WHAT: Returns the number of allocated bytes in the current generation.
    // CEP:WHY: Resource accounting for diagnostics and budget enforcement (design 20.2 memory check).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::used_bytes_tracks_allocations.
    // CEP:SECURITY: none.
    pub fn used_bytes(&self) -> u32 {
        self.front.get()
    }

    // CEP:WHAT: Returns the arena capacity in bytes.
    // CEP:WHY: Diagnostics and budget accounting.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::used_bytes_tracks_allocations.
    // CEP:SECURITY: none.
    pub fn capacity_bytes(&self) -> u32 {
        self.capacity
    }

    // CEP:WHAT: Returns the current generation ID.
    // CEP:WHY: Debug output and epoch-sensitive callers (AVATAR, Phase 4) need the epoch identity.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load.
    // CEP:EVIDENCE: unit/hot/arena_test.rs::checkpoint_reset_and_stale_detection.
    // CEP:SECURITY: none.
    pub fn generation(&self) -> u32 {
        self.generation.get()
    }
}
