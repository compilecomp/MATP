// CEP:FILE: cold/arena_host.rs
// CEP:WHAT: Arena host: allocates the kMaxAlignment-aligned backing region from the system heap, leaks it for a 'static lifetime, and hands it to the CEP-0 arena.
// CEP:WHY: Design 8.1 lifecycle step 1: the region is allocated once before the hot path by CEP-1 code; all runtime allocation (Box::leak of one buffer) happens here and nowhere else in the MAPT process, which is what makes the CEP-0 allocation ban (CEP&CC 25.5) achievable without static buffers of fixed size.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns ArenaHostError::CapacityInvalid for zero or oversize requests and ArenaHostError::AllocationFailed when the system cannot provide the region; never panics.
// CEP:ASSUMES: The returned region is exclusively owned by the caller and must be handed to exactly one Arena; the process intentionally never frees it (design 8.1 lifecycle step 4 is process exit).
// CEP:COST: one system allocation of the requested capacity plus alignment slack; O(1).
// CEP:EVIDENCE: unit/hot/arena_test.rs uses this host for every arena test; property/arena_property_test.rs.
// CEP:SECURITY: capacity is validated against kArenaCapacityBytes before any allocation, so untrusted problem sizes cannot request unbounded memory (CEP&CC 22.10).
// CEP:SECURITY: the aligned sub-slice is computed with checked arithmetic on the leaked buffer only.

use mapt_config::limits::{kArenaCapacityBytes, kMaxAlignment};

/// CEP:WHAT: Error cases of the arena host.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the host never panics.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/arena_test.rs::host_rejects_bad_capacities.
/// CEP:SECURITY: capacity validation is the memory bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArenaHostError {
    /// CEP:WHAT: The requested capacity is zero or exceeds kArenaCapacityBytes.
    CapacityInvalid,
    /// CEP:WHAT: The system allocator refused the request.
    AllocationFailed,
}

// CEP:WHAT: Allocates a kMaxAlignment-aligned, zero-initialized region of exactly capacity bytes with 'static lifetime.
// CEP:WHY: The arena requires an aligned, caller-owned, stable region (hot/memory/arena.rs Arena::new); Box::leak provides the 'static guarantee without unsafe code.
// CEP:STATUS: complete
// CEP:FAILURE: Returns CapacityInvalid for bad sizes and AllocationFailed when the allocator refuses.
// CEP:ASSUMES: capacity <= kArenaCapacityBytes; the caller hands the region to exactly one Arena.
// CEP:COST: one allocation of capacity + alignment slack bytes, then a subslice; O(1).
// CEP:EVIDENCE: unit/hot/arena_test.rs::{construction_validates_alignment, host_rejects_bad_capacities}.
// CEP:SECURITY: bounds validated first; zero-initialization leaves no uninitialized bytes (CEP&CC 22.4).
pub fn allocate_aligned_region(capacity_bytes: u32) -> Result<&'static mut [u8], ArenaHostError> {
    if capacity_bytes == 0 || capacity_bytes > kArenaCapacityBytes {
        return Err(ArenaHostError::CapacityInvalid);
    }
    let align = kMaxAlignment as usize;
    let slack = align - 1;
    let total = capacity_bytes as usize + slack;
    let buffer = alloc_zeroed_vec(total)?;
    let base = buffer.as_ptr() as usize;
    let offset = ((base + slack) & !slack) - base;
    let leaked: &'static mut [u8] = Box::leak(buffer.into_boxed_slice());
    let region_end = offset + capacity_bytes as usize;
    if region_end > leaked.len() {
        return Err(ArenaHostError::AllocationFailed);
    }
    Ok(&mut leaked[offset..region_end])
}

// CEP:WHAT: Zero-fills a Vec of the given length.
// CEP:WHY: Keeps the allocation call in one auditable place.
// CEP:STATUS: complete
// CEP:FAILURE: Returns AllocationFailed when the allocator refuses.
// CEP:ASSUMES: none.
// CEP:COST: one allocation plus memset.
// CEP:EVIDENCE: unit/hot/arena_test.rs.
// CEP:SECURITY: zero-initialized, no uninitialized reads.
fn alloc_zeroed_vec(total: usize) -> Result<Vec<u8>, ArenaHostError> {
    let mut buffer: Vec<u8> = Vec::new();
    buffer
        .try_reserve_exact(total)
        .map_err(|_| ArenaHostError::AllocationFailed)?;
    buffer.resize(total, 0);
    Ok(buffer)
}
