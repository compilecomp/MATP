// CEP:FILE: hot/sat/cdcl.rs
// CEP:WHAT: CDCL conflict analysis: first-UIP computation over the implication graph (design 11.1 S18-S19), recursive learnt-clause minimization by self-subsuming resolution (S20), LBD computation (S23), and backjump-level derivation (S22), with VSIDS bumping of the analyzed variables (S13).
// CEP:WHY: Design 11.2 names conflict analysis one of the three hottest paths (OPT-0, "called once per conflict. Millions of conflicts per solve"); the trail is walked backwards exactly once, the seen flags are generation-marked so no clearing pass exists, and every learnt clause is a resolvent of input and learnt clauses, which Formal Spec 06 proves is entailed; minimization removes literals whose reason chains resolve within the learnt set, shortening clauses without losing entailment (Sorensson & Biere 2009 recursive minimization).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns CdclError::LevelZeroConflict when called at level 0 (the solver must decide UNSAT first), MalformedConflict when the conflict clause has no literal at the current level (violated caller discipline: clauses are only added at level 0), LearntTooLong when the learnt clause exceeds the scratch or output buffers, Storage for unreadable clause records. Never panics.
// CEP:ASSUMES: Every propagated literal's reason was recorded at assign time (assign_with_reason); reason clauses are never deleted (deletion policy is ticket CEP-1003, Phase 3); the conflict offset came from BCP; the caller-owned output buffer has room for the clause it expects (the solver passes kMaxSatClauseLiterals and maps LearntTooLong to Indeterminate).
// CEP:COST: one backwards trail walk touching each current-level variable at most once plus one reason resolution per walked variable; minimization adds one reason scan per candidate literal; measured 697.42 cycles median per analysis of the fixed level-2 conflict graph (three-literal learnt with one minimized literal) on x86-64 (Intel Xeon, virtualized), rustc 1.99.0 -O, measured 2026-10-10, bench CEP-BENCH-0009, artifact benches/artifacts/cdcl_analyze.json.
// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs; unit/hot/sat_solver_test.rs; property/cdcl_property_test.rs::{learnt_clauses_are_entailed, solve_agrees_with_brute_force}; bench CEP-BENCH-0009.
// CEP:SECURITY: all trail and clause reads are bounds-checked; the seen, mark, and stack arrays are sized by the declared variable count and indexed by validated variables.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the trail walk is index-ordered, reason literals are scanned in storage order, and generation counters make the mark state a pure function of the call sequence.
// CEP:HPC-PASS-LEGALITY: Formal Spec 06 fixes the analysis contract: the first UIP exists and is unique (section 4), the learnt clause is the resolvent of the conflict clause with the reason clauses of every resolved variable and is therefore entailed (section 5), the backjump level is the maximum level among the non-asserting literals (section 5), and minimization preserves entailment (section 6); the property tests verify entailment against the brute-force oracle.
// CEP:OPTIMAL: not-optimal
// CEP:OPTNOTE: the trail walk and reason scans pay bounds checks per read; batching literal reads of a clause (ticket CEP-1015) and a watched-binaries fast path are the measured follow-ups; deferred pending Phase 3 workloads; ticket CEP-1031.

use crate::memory::arena::Arena;
use crate::sat::clause::SatClauseError;
use crate::sat::database::{SatCore, SatCoreError};
use crate::sat::literal::SatLiteral;
use crate::sat::vsids::VsidsHeap;
use core::cell::Cell;
use mapt_config::limits::kInvalidClauseOffset;

/// CEP:WHAT: Error cases of conflict analysis and the CDCL solver.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary for the CDCL component.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{level_zero_rejected, malformed_conflict_rejected}; unit/hot/sat_solver_test.rs::conflict_budget_returns_indeterminate.
/// CEP:SECURITY: bounds and budget errors are the resource boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CdclError {
    /// CEP:WHAT: The analysis was invoked at decision level 0 where UNSAT is already decided.
    LevelZeroConflict,
    /// CEP:WHAT: The conflict clause has no literal at the current level (violated caller discipline).
    MalformedConflict,
    /// CEP:WHAT: The learnt clause exceeds the scratch or output buffers.
    LearntTooLong,
    /// CEP:WHAT: The conflict budget kSatMaxConflicts is exhausted.
    ConflictBudgetExceeded,
    /// CEP:WHAT: A SAT-core structural failure (unreadable clause or trail records).
    Storage(SatCoreError),
}

// CEP:WHAT: Converts SAT-core errors into the CDCL vocabulary.
// CEP:WHY: CEP&CC 33.18: one explicit translation point.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::construction_requires_arena_room.
// CEP:SECURITY: none.
impl From<SatCoreError> for CdclError {
    fn from(error: SatCoreError) -> CdclError {
        CdclError::Storage(error)
    }
}

// CEP:WHAT: Converts clause-storage errors into the CDCL vocabulary.
// CEP:WHY: Clause reads inside analysis return SatClauseError directly; one translation point keeps the vocabulary closed (CEP&CC 33.18).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::construction_requires_arena_room.
// CEP:SECURITY: none.
impl From<SatClauseError> for CdclError {
    fn from(error: SatClauseError) -> CdclError {
        CdclError::Storage(SatCoreError::Storage(error))
    }
}

/// CEP:WHAT: Result of one analysis: the learnt literal count, the backjump level, and the LBD.
/// CEP:WHY: The solver needs exactly these three facts to learn, backjump, and record quality metadata (design 11.1 S21-S23).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: literals are in the caller's buffer, position 0 is the asserting (UIP) literal.
/// CEP:COST: 12 bytes.
/// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{first_uip_is_last_current_level_literal, backjump_level_is_max_other_level, lbd_counts_distinct_levels}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnalysisOutcome {
    /// CEP:WHAT: Number of learnt literals written to the output buffer.
    /// CEP:WHY: The learnt clause extent.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1 (position 0 is the asserting literal).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::first_uip_is_last_current_level_literal.
    /// CEP:SECURITY: none.
    pub literal_count: u32,
    /// CEP:WHAT: Backjump level (maximum level among the non-asserting literals, 0 for unit learnts).
    /// CEP:WHY: Design 11.1 S22: "Non-chronological backtracking to the second-highest decision level in the learnt clause."
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: < current level.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::backjump_level_is_max_other_level.
    /// CEP:SECURITY: none.
    pub backjump_level: u32,
    /// CEP:WHAT: Literal Block Distance: number of distinct decision levels in the learnt clause.
    /// CEP:WHY: Design 11.1 S23 quality metric for the future deletion policy.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: >= 1.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::lbd_counts_distinct_levels.
    /// CEP:SECURITY: none.
    pub lbd: u32,
}

/// CEP:WHAT: Conflict analyzer: generation-marked seen array, learnt literal buffer, level marks for LBD, and the minimization marks, stack, and undo list, all arena-backed and sized by the declared variable count.
/// CEP:WHY: Design 11.1 S18-S20: the analyzer owns exactly the scratch state of conflict analysis; generation counters replace clearing passes (u32 generations cannot wrap below kSatMaxConflicts within one solve), minimization marks live in their own array so they can never clobber or collide with the analysis marks, and arena arrays keep the analyzer allocation-free per conflict (design 8.1).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: construction returns CdclError::Storage on arena exhaustion.
/// CEP:ASSUMES: one analyzer per solver; single-threaded.
/// CEP:COST: 14 bytes per variable of scratch state.
/// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs; property/cdcl_property_test.rs::{learnt_clauses_are_entailed, solve_agrees_with_brute_force}.
/// CEP:SECURITY: bounds-checked accessors.
pub struct ConflictAnalyzer<'a> {
    /// CEP:WHAT: Generation-marked seen flags per variable (analysis marks).
    /// CEP:WHY: O(1) clearing between conflicts: a variable is seen iff its generation equals the current one.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one u32 per variable.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{first_uip_is_last_current_level_literal, repeated_analyses_are_independent}.
    /// CEP:SECURITY: bounds-checked.
    seen_generations: &'a [Cell<u32>],
    /// CEP:WHAT: Current seen generation.
    /// CEP:WHY: The generation counter.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none (cannot wrap below kSatMaxConflicts within one solve).
    /// CEP:ASSUMES: one increment per analysis.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::repeated_analyses_are_independent.
    /// CEP:SECURITY: none.
    seen_generation: Cell<u32>,
    /// CEP:WHAT: Learnt literal scratch buffer (literal encodings).
    /// CEP:WHY: The analysis assembles the learnt clause here before copying to the caller buffer.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized by the variable count; learnt clauses have at most one literal per variable.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::first_uip_is_last_current_level_literal.
    /// CEP:SECURITY: bounds-checked.
    learnt: &'a [Cell<u32>],
    /// CEP:WHAT: Generation-marked level flags for LBD counting.
    /// CEP:WHY: Counting distinct levels without a clearing pass.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized variable_count + 1 (levels are 0..=variable_count).
    /// CEP:COST: 4 bytes per level slot.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::lbd_counts_distinct_levels.
    /// CEP:SECURITY: bounds-checked.
    level_generations: &'a [Cell<u32>],
    /// CEP:WHAT: Generation-marked minimization flags per variable (separate mark space from the analysis marks).
    /// CEP:WHY: Redundancy checks need temporary marks that must neither clobber analysis marks nor collide with the seen generations; a dedicated array with its own counter makes both impossible by construction.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one u32 per variable.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    /// CEP:SECURITY: bounds-checked.
    minimize_marks: &'a [Cell<u32>],
    /// CEP:WHAT: Minimization work stack (variable indices).
    /// CEP:WHY: The iterative redundant-literal check pushes chain variables here instead of recursing (CEP&CC 22.10).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized by the variable count; each variable enters the stack at most once per check.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    /// CEP:SECURITY: bounds-checked.
    minimize_stack: &'a [Cell<u32>],
    /// CEP:WHAT: Undo list of variables marked during a minimization check.
    /// CEP:WHY: A failed check must unmark exactly the variables it marked (MiniSat discipline) so later checks start from the true mark state.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: sized by the variable count.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    /// CEP:SECURITY: bounds-checked.
    minimize_undo: &'a [Cell<u32>],
    /// CEP:WHAT: Current minimization generation.
    /// CEP:WHY: The counter for the temporary mark space.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: one increment per check.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    /// CEP:SECURITY: none.
    minimize_generation: Cell<u32>,
}

// CEP:WHAT: Maps arena allocation failures onto the CDCL vocabulary.
// CEP:WHY: One translation point for construction (CEP&CC 33.18).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::construction_requires_arena_room.
// CEP:SECURITY: none.
fn arena_full() -> CdclError {
    CdclError::Storage(SatCoreError::Storage(SatClauseError::ArenaFull))
}

// CEP:WHAT: Maps unreadable arena ranges onto the CDCL vocabulary.
// CEP:WHY: One translation point for construction (CEP&CC 33.18).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::construction_requires_arena_room.
// CEP:SECURITY: none.
fn arena_unreadable() -> CdclError {
    CdclError::Storage(SatCoreError::Storage(SatClauseError::InvalidClauseOffset))
}

impl<'a> ConflictAnalyzer<'a> {
    // CEP:WHAT: Constructs the analyzer scratch arrays for a declared variable count.
    // CEP:WHY: All scratch is allocated once before the hot path (design 19.4); arrays are cleared so the first analysis starts from a defined state.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns CdclError::Storage when the arrays do not fit.
    // CEP:ASSUMES: variables matches the solver's SatCore and is above zero.
    // CEP:COST: one-time allocation of 14 bytes per variable plus one slot.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{first_uip_is_last_current_level_literal, repeated_analyses_are_independent, construction_requires_arena_room}.
    // CEP:SECURITY: arrays cleared and bounded.
    pub fn new(arena: &'a Arena, variables: u32) -> Result<ConflictAnalyzer<'a>, CdclError> {
        if variables == 0 {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        let seen_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| arena_full())?;
        let seen_generations = arena
            .array::<Cell<u32>>(seen_range)
            .map_err(|_| arena_unreadable())?;
        let learnt_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| arena_full())?;
        let learnt = arena
            .array::<Cell<u32>>(learnt_range)
            .map_err(|_| arena_unreadable())?;
        let level_range = arena
            .alloc_array::<Cell<u32>>(variables + 1)
            .map_err(|_| arena_full())?;
        let level_generations = arena
            .array::<Cell<u32>>(level_range)
            .map_err(|_| arena_unreadable())?;
        let mark_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| arena_full())?;
        let minimize_marks = arena
            .array::<Cell<u32>>(mark_range)
            .map_err(|_| arena_unreadable())?;
        let stack_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| arena_full())?;
        let minimize_stack = arena
            .array::<Cell<u32>>(stack_range)
            .map_err(|_| arena_unreadable())?;
        let undo_range = arena
            .alloc_array::<Cell<u32>>(variables)
            .map_err(|_| arena_full())?;
        let minimize_undo = arena
            .array::<Cell<u32>>(undo_range)
            .map_err(|_| arena_unreadable())?;
        for index in 0..variables as usize {
            seen_generations[index].set(0);
            learnt[index].set(0);
            minimize_marks[index].set(0);
            minimize_stack[index].set(0);
            minimize_undo[index].set(0);
        }
        for slot in level_generations.iter() {
            slot.set(0);
        }
        Ok(ConflictAnalyzer {
            seen_generations,
            seen_generation: Cell::new(1),
            learnt,
            level_generations,
            minimize_marks,
            minimize_stack,
            minimize_undo,
            minimize_generation: Cell::new(1),
        })
    }

    // CEP:WHAT: Analyzes a conflict: computes the first-UIP learnt clause, minimizes it, and derives the backjump level and LBD.
    // CEP:WHY: Design 11.1 S18-S23 and Spec 06: the trail walk resolves every current-level variable of the conflict against its reason until one remains (the first UIP), the learnt clause collects the lower-level false literals, minimization drops literals whose reason chains resolve inside the clause, and the backjump level is the maximum remaining lower level.
    // CEP:STATUS: complete
    // CEP:FAILURE: see CdclError; the analysis never panics and leaves no stale marks (generation bump per call, separate minimization mark space).
    // CEP:ASSUMES: see file header; the current level is >= 1.
    // CEP:COST: one trail walk plus one reason scan per resolved variable; measured in bench CEP-BENCH-0009.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{first_uip_is_last_current_level_literal, backjump_level_is_max_other_level, lbd_counts_distinct_levels, minimization_removes_redundant_literals, repeated_analyses_are_independent}; property/cdcl_property_test.rs::learnt_clauses_are_entailed.
    // CEP:SECURITY: bounds-checked reads; buffers sized by the variable count.
    pub fn analyze(
        &self,
        core: &SatCore<'_>,
        vsids: &VsidsHeap<'_>,
        conflict: u32,
        output: &mut [SatLiteral],
    ) -> Result<AnalysisOutcome, CdclError> {
        let current_level = core.trail().level();
        if current_level == 0 {
            return Err(CdclError::LevelZeroConflict);
        }
        let generation = self.seen_generation.get().wrapping_add(1);
        self.seen_generation.set(generation);
        // Seed: mark every conflict literal above level 0; current-level literals count toward
        // the path, lower-level ones enter the learnt clause directly (Spec 06 section 3).
        let mut path_count: u32 = 0;
        let mut learnt_count: usize = 1; // position 0 reserved for the asserting literal
        let header = core.clauses().header(conflict)?;
        for position in 0..header.length {
            let literal = core.clauses().literal(conflict, position)?;
            let variable = literal.variable().0;
            let level = core.level_of(variable);
            if level >= current_level {
                if !self.is_seen(variable, generation) {
                    self.mark_seen(variable, generation)?;
                    vsids.bump(variable);
                    path_count += 1;
                }
            } else if level > 0 && !self.is_seen(variable, generation) {
                self.mark_seen(variable, generation)?;
                vsids.bump(variable);
                if learnt_count >= self.learnt.len() {
                    return Err(CdclError::LearntTooLong);
                }
                self.learnt[learnt_count].set(literal.encoding());
                learnt_count += 1;
            }
        }
        if path_count == 0 {
            return Err(CdclError::MalformedConflict);
        }
        // Backwards trail walk to the first UIP (Spec 06 section 4).
        let mut index = core.trail().len();
        let uip: SatLiteral = loop {
            if index == 0 {
                return Err(CdclError::MalformedConflict);
            }
            index -= 1;
            let entry = match core.trail().literal_at(index) {
                Some(literal) => literal,
                None => return Err(CdclError::MalformedConflict),
            };
            let variable = entry.variable().0;
            if !self.is_seen(variable, generation) {
                continue;
            }
            self.unmark_seen(variable);
            path_count -= 1;
            if path_count == 0 {
                break entry;
            }
            // Resolve the reason clause of this variable into the learnt clause (Spec 06
            // section 5); the propagated literal itself sits in a watch position, so the
            // skip is by variable identity rather than by index.
            let reason = core.reason_of(variable);
            if reason == kInvalidClauseOffset {
                return Err(CdclError::MalformedConflict);
            }
            let reason_header = core.clauses().header(reason)?;
            for position in 0..reason_header.length {
                let literal = core.clauses().literal(reason, position)?;
                let other = literal.variable().0;
                if other == variable {
                    continue;
                }
                let level = core.level_of(other);
                if level == 0 || self.is_seen(other, generation) {
                    continue;
                }
                self.mark_seen(other, generation)?;
                vsids.bump(other);
                if level >= current_level {
                    path_count += 1;
                } else {
                    if learnt_count >= self.learnt.len() {
                        return Err(CdclError::LearntTooLong);
                    }
                    self.learnt[learnt_count].set(literal.encoding());
                    learnt_count += 1;
                }
            }
        };
        self.learnt[0].set(uip.negate().encoding());
        // Minimization: drop literals whose reason chains resolve inside the learnt set
        // (Spec 06 section 6); removed literals keep their seen marks, matching the
        // MiniSat discipline that later checks treat them as covered.
        let mut kept: usize = 1;
        for position in 1..learnt_count {
            let literal = SatLiteral::from_encoding(self.learnt[position].get());
            if self.literal_redundant(core, literal, generation)? {
                continue;
            }
            self.learnt[kept].set(literal.encoding());
            kept += 1;
        }
        learnt_count = kept;
        // Backjump level: maximum level among the non-asserting literals; swap that literal
        // into position 1 so both watches (0, 1) are the asserting and backjump literals.
        let mut backjump_level: u32 = 0;
        let mut backjump_position: usize = 0;
        for position in 1..learnt_count {
            let literal = SatLiteral::from_encoding(self.learnt[position].get());
            let level = core.level_of(literal.variable().0);
            if level > backjump_level {
                backjump_level = level;
                backjump_position = position;
            }
        }
        if backjump_position > 1 && learnt_count > 1 {
            let swap = self.learnt[1].get();
            self.learnt[1].set(self.learnt[backjump_position].get());
            self.learnt[backjump_position].set(swap);
        }
        // LBD: distinct levels across the whole learnt clause (design 11.1 S23).
        let level_generation = self.minimize_generation.get().wrapping_add(1);
        self.minimize_generation.set(level_generation);
        let mut lbd: u32 = 0;
        for position in 0..learnt_count {
            let literal = SatLiteral::from_encoding(self.learnt[position].get());
            let level = core.level_of(literal.variable().0) as usize;
            if level >= self.level_generations.len() {
                continue;
            }
            if self.level_generations[level].get() != level_generation {
                self.level_generations[level].set(level_generation);
                lbd += 1;
            }
        }
        // Copy out to the caller buffer.
        if learnt_count > output.len() {
            return Err(CdclError::LearntTooLong);
        }
        for (position, slot) in output.iter_mut().enumerate().take(learnt_count) {
            *slot = SatLiteral::from_encoding(self.learnt[position].get());
        }
        Ok(AnalysisOutcome {
            literal_count: learnt_count as u32,
            backjump_level,
            lbd,
        })
    }

    // CEP:WHAT: Redundancy check: a learnt literal is redundant when every non-level-0 variable of its reason chain is already covered (seen) or itself resolvable within the chain.
    // CEP:WHY: Spec 06 section 6 (Sorensson & Biere 2009): resolving the literal away against its reason chain preserves entailment; the iterative stack with temporary marks implements the recursion without unbounded call depth (CEP&CC 22.10), and a failed check unmarks exactly what it marked.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates Storage errors from reason reads; LearntTooLong when the chain exceeds the stack bound (each variable enters once, so this is a defensive bound).
    // CEP:ASSUMES: the literal's variable is assigned (it is on the learnt clause) with a recorded reason or is a decision (decisions are never redundant).
    // CEP:COST: O(reason chain size) per candidate.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::{minimization_removes_redundant_literals, minimization_keeps_decision_literals}.
    // CEP:SECURITY: stack bounded by the variable count.
    fn literal_redundant(
        &self,
        core: &SatCore<'_>,
        literal: SatLiteral,
        seen_generation: u32,
    ) -> Result<bool, CdclError> {
        let variable = literal.variable().0;
        let reason = core.reason_of(variable);
        if reason == kInvalidClauseOffset {
            // Decisions (and reasonless root assignments) are never redundant.
            return Ok(false);
        }
        let mark = self.minimize_generation.get().wrapping_add(1);
        self.minimize_generation.set(mark);
        let mut stack_top: usize = 0;
        let mut undo_top: usize = 0;
        let mut redundant = true;
        self.minimize_stack[stack_top].set(variable);
        stack_top += 1;
        self.mark_minimize(variable, mark)?;
        while stack_top > 0 {
            stack_top -= 1;
            let current = self.minimize_stack[stack_top].get();
            let current_reason = core.reason_of(current);
            if current_reason == kInvalidClauseOffset {
                // A decision in the chain blocks removal.
                redundant = false;
                break;
            }
            let header = core.clauses().header(current_reason)?;
            for position in 0..header.length {
                let other_literal = core.clauses().literal(current_reason, position)?;
                let other = other_literal.variable().0;
                if other == current {
                    continue;
                }
                if core.level_of(other) == 0 {
                    continue;
                }
                if self.is_seen(other, seen_generation) {
                    continue;
                }
                if self.is_minimized(other, mark) {
                    continue;
                }
                if undo_top >= self.minimize_undo.len() || stack_top >= self.minimize_stack.len() {
                    return Err(CdclError::LearntTooLong);
                }
                self.mark_minimize(other, mark)?;
                self.minimize_undo[undo_top].set(other);
                undo_top += 1;
                self.minimize_stack[stack_top].set(other);
                stack_top += 1;
            }
        }
        if !redundant {
            // Unwind exactly the marks made during this check; the candidate keeps its
            // analysis mark because the literal stays in the learnt clause.
            for position in 0..undo_top {
                self.unmark_minimize(self.minimize_undo[position].get());
            }
        }
        Ok(redundant)
    }

    // CEP:WHAT: Marks a variable seen under the current analysis generation.
    // CEP:WHY: Generation-marked flags replace clearing passes.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Storage(InvariantViolation) for out-of-range variables (a caller bug surfaced loudly).
    // CEP:ASSUMES: variable below the declared count in solver use.
    // CEP:COST: 1 store.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::repeated_analyses_are_independent.
    // CEP:SECURITY: bounds-checked.
    fn mark_seen(&self, variable: u32, generation: u32) -> Result<(), CdclError> {
        let index = variable as usize;
        if index >= self.seen_generations.len() {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        self.seen_generations[index].set(generation);
        Ok(())
    }

    // CEP:WHAT: Clears a variable's seen mark.
    // CEP:WHY: Resolved-away variables leave the learnt set and must not stay seen.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (clamped).
    // CEP:ASSUMES: the variable was marked this generation.
    // CEP:COST: 1 store.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::first_uip_is_last_current_level_literal.
    // CEP:SECURITY: clamped.
    fn unmark_seen(&self, variable: u32) {
        let index = variable as usize;
        if index < self.seen_generations.len() {
            self.seen_generations[index].set(0);
        }
    }

    // CEP:WHAT: Tests a variable's seen mark for the given generation.
    // CEP:WHY: The generation compare is the seen test.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (false for out-of-range variables, deterministic).
    // CEP:ASSUMES: none.
    // CEP:COST: 1 load + 1 compare.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::repeated_analyses_are_independent.
    // CEP:SECURITY: clamped.
    fn is_seen(&self, variable: u32, generation: u32) -> bool {
        let index = variable as usize;
        if index >= self.seen_generations.len() {
            return false;
        }
        self.seen_generations[index].get() == generation
    }

    // CEP:WHAT: Marks a variable with a minimization mark.
    // CEP:WHY: Temporary chain marks live in the dedicated array so they can never clobber analysis marks.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Storage(InvariantViolation) for out-of-range variables.
    // CEP:ASSUMES: variable below the declared count in solver use.
    // CEP:COST: 1 store.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    // CEP:SECURITY: bounds-checked.
    fn mark_minimize(&self, variable: u32, mark: u32) -> Result<(), CdclError> {
        let index = variable as usize;
        if index >= self.minimize_marks.len() {
            return Err(CdclError::Storage(SatCoreError::InvariantViolation));
        }
        self.minimize_marks[index].set(mark);
        Ok(())
    }

    // CEP:WHAT: Tests a minimization mark.
    // CEP:WHY: Chain variables already visited in this check are skipped.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (false for out-of-range variables).
    // CEP:ASSUMES: none.
    // CEP:COST: 1 compare.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    // CEP:SECURITY: clamped.
    fn is_minimized(&self, variable: u32, mark: u32) -> bool {
        let index = variable as usize;
        if index >= self.minimize_marks.len() {
            return false;
        }
        self.minimize_marks[index].get() == mark
    }

    // CEP:WHAT: Clears a minimization mark (failed-check unwind).
    // CEP:WHY: Restores the mark state for later checks.
    // CEP:STATUS: complete
    // CEP:FAILURE: none (clamped).
    // CEP:ASSUMES: the slot was set by this check.
    // CEP:COST: 1 store.
    // CEP:EVIDENCE: unit/hot/sat_cdcl_test.rs::minimization_removes_redundant_literals.
    // CEP:SECURITY: clamped.
    fn unmark_minimize(&self, variable: u32) {
        let index = variable as usize;
        if index < self.minimize_marks.len() {
            self.minimize_marks[index].set(0);
        }
    }
}
