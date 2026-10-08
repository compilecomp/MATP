// CEP:FILE: hot/sat/bcp.rs
// CEP:WHAT: Boolean constraint propagation (BCP): drains the trail queue, scans the watch lists of falsified literals, moves watches to non-false literals, enqueues units, and reports conflicts.
// CEP:WHY: Design 11.1 S9/S10/S11 and 11.2: BCP is the hottest path in the entire system ("2 loads + 1 branch per watch check") and must be OPT-0; the watched-literal scheme (Chaff, Moskewicz et al. DAC 2001; CaDiCaL, Biere SAT 2020) makes each propagation step O(1) amortized because a clause is inspected only when one of its two watched literals becomes false.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns SatCoreError on structural failures (unreadable records, trail overflow); returns PropagationOutcome::Conflict when a clause is falsified — a legitimate SAT result, not an error. Never panics.
// CEP:ASSUMES: Watch-list invariant: a clause appears in exactly the lists of its literals at positions 0 and 1; every assignment went through SatCore::assign (trail and values consistent); a variable is assigned at most once between backtracks.
// CEP:COST: amortized O(1) per propagation, worst O(clause length) per watch scan; measured 44.5 cycles median per propagation step (queue dequeue, value evaluation, watch scan, unit assignment) on an implication chain on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-08, bench CEP-BENCH-0005, artifact benches/artifacts/sat_bcp_step.json.
// CEP:EVIDENCE: bench CEP-BENCH-0005; unit/hot/sat_bcp_test.rs (implication chains, conflicts, unit enqueues, watch moves, queue draining); property/bcp_property_test.rs (soundness against brute-force implication on random formulas, watch-list integrity); disassembly artifact benches/artifacts/disasm_sat.txt.
// CEP:SECURITY: all clause and literal reads are bounds-checked; a corrupted watch link surfaces as an error, never as out-of-bounds access.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the trail is drained in FIFO order and watch lists are walked in list order.
// CEP:OPTIMAL: not-optimal
// CEP:OPTPROOF: N/A.
// CEP:OPTNOTE: per-literal access goes through bounds-checked accessors (required security cost, CEP&CC 23.7) and the loop lacks a blocking-literal cache; both optimizations are deferred pending measurement on Phase 2 workloads; tickets CEP-1015 (batched literal reads) and CEP-1017 (blocker literals).

use crate::sat::assignment::SatValue;
use crate::sat::database::SatCore;
use crate::sat::literal::SatLiteral;
use mapt_config::limits::kInvalidClauseOffset;

/// CEP:WHAT: Result of one propagation run.
/// CEP:WHY: BCP either drains the queue without conflict or finds a falsified clause whose offset conflict analysis (Phase 2) will consume; conflating conflict with error would hide a legitimate SAT outcome (CEP&CC Law 6: explicit failure vocabulary).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::{propagation_drains_queue, conflict_detected}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropagationOutcome {
    /// CEP:WHAT: Queue drained; no conflict found.
    NoConflict,
    /// CEP:WHAT: Clause at the given offset is falsified under the current assignment.
    Conflict(u32),
}

/// CEP:WHAT: Position of a node inside a watch list traversal: before the head or after a clause's slot link.
/// CEP:WHY: Unlinking a clause from a singly-linked intrusive list needs the predecessor; the cursor makes every list mutation explicit and auditable (CEP&CC Law 5).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a cursor vocabulary type.
/// CEP:ASSUMES: the cursor always refers to a valid position in one list.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_watch_test.rs::attach_and_traverse.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy)]
enum WatchCursor {
    /// CEP:WHAT: Position before the first node of the list of this literal.
    Head(SatLiteral),
    /// CEP:WHAT: Position after the clause at this offset, following its slot link.
    Node(u32, u32),
}

impl<'a> SatCore<'a> {
    // CEP:WHAT: Propagates all pending assignments to fixpoint or the first conflict.
    // CEP:WHY: Design 11.1 S9: the BCP engine; drains the trail queue in FIFO order (S11) and maintains the watch invariants (S10) while enqueuing forced literals.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns SatCoreError on structural failures; conflicts are returned as PropagationOutcome::Conflict.
    // CEP:ASSUMES: see file header.
    // CEP:COST: amortized O(1) per propagation step; measured in bench CEP-BENCH-0005.
    // CEP:EVIDENCE: bench CEP-BENCH-0005; unit/hot/sat_bcp_test.rs; property/bcp_property_test.rs.
    // CEP:SECURITY: every read is bounds-checked; corrupted links error out.
    // CEP:HPC-DETERMINISM: FIFO queue drain, deterministic list order.
    pub fn propagate(&self) -> Result<PropagationOutcome, crate::sat::database::SatCoreError> {
        while self.trail().qhead() < self.trail().len() {
            let propagated = match self.trail().literal_at(self.trail().qhead()) {
                Some(literal) => literal,
                None => break,
            };
            self.trail().advance_qhead();
            let falsified = propagated.negate();
            let conflict = self.scan_watch_list(falsified)?;
            if let PropagationOutcome::Conflict(offset) = conflict {
                return Ok(PropagationOutcome::Conflict(offset));
            }
        }
        Ok(PropagationOutcome::NoConflict)
    }

    // CEP:WHAT: Scans the watch list of a now-false literal, moving watches and enqueueing units.
    // CEP:WHY: Design 11.3: the inner loop of CDCL; only clauses watching the falsified literal are inspected, which is what bounds work per propagation to the actually-affected clauses.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SatCoreError; returns Conflict when a clause cannot be satisfied or extended.
    // CEP:ASSUMES: the watched literal of each clause in this list is exactly the falsified literal at slot 0 or 1 (verified per clause, surfaced as an error on corruption).
    // CEP:COST: O(1) amortized per clause visit; O(clause length) on a full scan that moves a watch.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::{watch_moves_preserve_clause_contents, implication_chain}; property/bcp_property_test.rs::watch_lists_consistent.
    // CEP:SECURITY: bounds checks on every literal and header read.
    fn scan_watch_list(
        &self,
        falsified: SatLiteral,
    ) -> Result<PropagationOutcome, crate::sat::database::SatCoreError> {
        let mut cursor = WatchCursor::Head(falsified);
        loop {
            let current = match cursor {
                WatchCursor::Head(literal) => self.watches().head(literal),
                WatchCursor::Node(offset, slot) => self.clauses().next_in_watch(offset, slot)?,
            };
            if current == kInvalidClauseOffset {
                break;
            }
            let watch0 = self.clauses().literal(current, 0)?;
            let slot = if watch0 == falsified { 0 } else { 1 };
            let other = self.clauses().literal(current, slot ^ 1)?;
            let other_watch = self.clauses().literal(current, slot)?;
            if other_watch != falsified {
                return Err(crate::sat::database::SatCoreError::Storage(
                    crate::sat::clause::SatClauseError::InvalidClauseOffset,
                ));
            }
            if self.value_of_literal(other) == SatValue::True {
                cursor = WatchCursor::Node(current, slot);
                continue;
            }
            let header = self.clauses().header(current)?;
            let mut moved = false;
            let mut candidate_index: u32 = kWatchSearchStart;
            while candidate_index < header.length {
                let candidate = self.clauses().literal(current, candidate_index)?;
                if self.value_of_literal(candidate) != SatValue::False {
                    self.move_watch(
                        current,
                        slot,
                        candidate_index,
                        candidate,
                        falsified,
                        &cursor,
                    )?;
                    moved = true;
                    break;
                }
                candidate_index += 1;
            }
            if moved {
                continue;
            }
            if self.value_of_literal(other) == SatValue::False {
                return Ok(PropagationOutcome::Conflict(current));
            }
            self.assign(other)?;
            cursor = WatchCursor::Node(current, slot);
        }
        Ok(PropagationOutcome::NoConflict)
    }

    // CEP:WHAT: Moves a clause's watch from a falsified literal to a non-false candidate literal.
    // CEP:WHY: Design 11.3: keeping the watch invariant (both watches non-false or the clause unit/conflict) is what gives BCP its amortized O(1); the move swaps the candidate into the watched position, unlinks the clause from the falsified literal's list, and links it into the candidate's list.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates SatCoreError on structural failures.
    // CEP:ASSUMES: the candidate literal is not false under the current assignment (checked by the caller).
    // CEP:COST: 2 literal writes, 2 link writes, 1 head write.
    // CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents; property/bcp_property_test.rs::watch_lists_consistent.
    // CEP:SECURITY: bounds checks on every write.
    fn move_watch(
        &self,
        clause_offset: u32,
        slot: u32,
        candidate_index: u32,
        candidate: SatLiteral,
        falsified: SatLiteral,
        cursor: &WatchCursor,
    ) -> Result<(), crate::sat::database::SatCoreError> {
        self.clauses()
            .set_literal(clause_offset, candidate_index, falsified)?;
        self.clauses().set_literal(clause_offset, slot, candidate)?;
        let successor = self.clauses().next_in_watch(clause_offset, slot)?;
        match cursor {
            WatchCursor::Head(literal) => {
                let moved = self.watches().set_head(*literal, successor);
                debug_assert!(moved, "unlinking from an in-range head must succeed");
            }
            WatchCursor::Node(offset, link_slot) => {
                self.clauses()
                    .set_next_in_watch(*offset, *link_slot, successor)?;
            }
        }
        let old_head = self.watches().head(candidate);
        self.clauses()
            .set_next_in_watch(clause_offset, slot, old_head)?;
        self.watches().push_front(candidate, clause_offset);
        Ok(())
    }
}

/// CEP:WHAT: First non-watched literal position in the watch-search loop.
/// CEP:WHY: Positions 0 and 1 hold the watches (design 11.3); the search starts at 2, and the constant is named rather than embedded (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: two watched positions.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/sat_bcp_test.rs::watch_moves_preserve_clause_contents.
/// CEP:SECURITY: none.
pub const kWatchSearchStart: u32 = 2;
