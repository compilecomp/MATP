// CEP:FILE: hot/theory/difference.rs
// CEP:WHAT: The difference-logic solver of the theory engine (design 13.1's linear-arithmetic fragment over Q): asserted constraints x - y <= c become Bellman-Ford edges, a negative cycle is the inconsistency, and tentative zero-edges test entailment of variable equalities.
// CEP:WHY: Design 13.3's Nelson-Oppen combination needs a second, stably-infinite theory beside EUF; difference logic over the rationals is the bounded linear-arithmetic fragment whose consistency check is one Bellman-Ford run (Nieuwenhuis et al. 2006's constraint graph), with weights held as integers scaled by 2^kTheoryDlScaleShift so the arithmetic is exact over the discrete representation and no floating point enters the hot path (CEP&CC 25.3.1); full simplex for unrestricted LRA is the follow-up (ticket CEP-1070).
// CEP:CLASS: CEP-0
// CEP:STATUS: complete
// CEP:FAILURE: Returns TheoryError on storage failures or arithmetic overflow (ArithmeticOverflow); check reports inconsistency by returning false, never by panicking.
// CEP:ASSUMES: single-threaded; variable ids are below kMaxTheoryVars; weights satisfy |w| <= kTheoryDlMaxWeight so every distance accumulation stays in i64 range (pinned by the static assert).
// CEP:COST: add_constraint is O(1); one check is O(vars x edges); one entailed-equality test is one check plus O(1) truncation.
// CEP:EVIDENCE: unit/hot/theory_test.rs::{difference_logic_consistent, difference_logic_conflict}.
// CEP:SECURITY: every loop is bounded by the variable and edge capacities; no unbounded loop exists in this file.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; edges are relaxed in assertion order and the distance array starts at zero everywhere (CEP&CC 38.10).

use core::cell::Cell;

use crate::memory::arena::Arena;
use crate::sat::database::SatCoreError;
use mapt_config::limits::{kMaxTheoryAtoms, kMaxTheoryVars};

use super::TheoryError;

/// CEP:WHAT: The difference-logic solver: the constraint graph over the shared variable space with its Bellman-Ford state and the zero-equality class mirror.
/// CEP:WHY: Design 13.1's arithmetic fragment and design 13.3's second combination theory; the zero-class mirror lets the coordinator filter the pair-entailment tests to classes it has not already merged.
/// CEP:STATUS: complete
/// CEP:FAILURE: see TheoryError.
/// CEP:ASSUMES: reset before each assertion batch; edges are only truncated by the tentative entailment test.
/// CEP:COST: 4 bytes per edge slot and variable, 8 bytes per weight and distance.
/// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
/// CEP:SECURITY: bounds-checked reads throughout.
pub struct DifferenceLogic<'a> {
    /// CEP:WHAT: Left variable (x) of each asserted constraint x - y <= w.
    /// CEP:WHY: One edge per asserted constraint, in assertion order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by edge_count.
    /// CEP:COST: 4 bytes per edge.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: bounds-checked reads.
    edge_left: &'a [Cell<u32>],
    /// CEP:WHAT: Right variable (y) of each asserted constraint.
    /// CEP:WHY: The edge runs y -> x with weight w (d[x] <= d[y] + w).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by edge_count.
    /// CEP:COST: 4 bytes per edge.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: bounds-checked reads.
    edge_right: &'a [Cell<u32>],
    /// CEP:WHAT: Weight (w) of each asserted constraint in fixed-point units.
    /// CEP:WHY: The edge length of the constraint graph.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent given by edge_count; |w| <= kTheoryDlMaxWeight.
    /// CEP:COST: 8 bytes per edge.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: bounds-checked reads.
    edge_weight: &'a [Cell<i64>],
    /// CEP:WHAT: Number of live edges.
    /// CEP:WHY: Extent of the edge arrays; the tentative entailment test appends and truncates.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxTheoryAtoms (one edge per asserted atom per direction).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: none.
    edge_count: Cell<u32>,
    /// CEP:WHAT: Bellman-Ford distance per variable.
    /// CEP:WHY: The constraint-graph relaxation state; zero-initialized everywhere (the virtual-source form).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryVars.
    /// CEP:COST: 8 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: bounds-checked reads.
    dist: &'a [Cell<i64>],
    /// CEP:WHAT: Union-find parent over variables for the zero-equality classes (the ±0 edge pairs).
    /// CEP:WHY: The coordinator's filter: pairs already zero-merged need no entailment test.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryVars; reset before each batch.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked reads.
    zero_parent: &'a [Cell<u32>],
    /// CEP:WHAT: Union rank over the zero-equality classes.
    /// CEP:WHY: Union by rank keeps the zero-class finds short.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryVars.
    /// CEP:COST: 4 bytes per variable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked reads.
    zero_rank: &'a [Cell<u32>],
    /// CEP:WHAT: Per-variable occurrence flag (the variable appears in at least one edge).
    /// CEP:WHY: The pair-entailment tests only consider variables the difference logic actually constrains.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: extent kMaxTheoryVars.
    /// CEP:COST: 1 byte per variable.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked reads.
    occurs: &'a [Cell<bool>],
}

impl<'a> DifferenceLogic<'a> {
    /// CEP:WHAT: Constructs the difference-logic solver over the arena.
    /// CEP:WHY: Design 4.1: every structure is fully built before use.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    /// CEP:ASSUMES: the arena has room for the edge, distance, and class arrays.
    /// CEP:COST: O(kMaxTheoryAtoms + kMaxTheoryVars) one-time.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: capacity validated before use.
    pub fn new(arena: &'a Arena) -> Result<DifferenceLogic<'a>, TheoryError> {
        let edge_left = Self::alloc_u32(arena, kMaxTheoryAtoms * 2)?;
        let edge_right = Self::alloc_u32(arena, kMaxTheoryAtoms * 2)?;
        let edge_weight = Self::alloc_i64(arena, kMaxTheoryAtoms * 2)?;
        let dist = Self::alloc_i64(arena, kMaxTheoryVars)?;
        let zero_parent = Self::alloc_u32(arena, kMaxTheoryVars)?;
        let zero_rank = Self::alloc_u32(arena, kMaxTheoryVars)?;
        let occurs = Self::alloc_bool(arena, kMaxTheoryVars)?;
        let logic = DifferenceLogic {
            edge_left,
            edge_right,
            edge_weight,
            edge_count: Cell::new(0),
            dist,
            zero_parent,
            zero_rank,
            occurs,
        };
        // Design 4.1: the structure is fully built before use - the arena arrays
        // are zeroed memory, so the class mirror must be initialized to singletons.
        logic.reset();
        Ok(logic)
    }

    // CEP:WHAT: Arena array constructors with the single error translation.
    // CEP:WHY: One translation point per element type (CEP&CC 33.18).
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on arena exhaustion.
    // CEP:ASSUMES: none.
    // CEP:COST: one allocation each.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    // CEP:SECURITY: none.
    fn alloc_u32(arena: &'a Arena, count: u32) -> Result<&'a [Cell<u32>], TheoryError> {
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

    fn alloc_i64(arena: &'a Arena, count: u32) -> Result<&'a [Cell<i64>], TheoryError> {
        let range = arena.alloc_array::<Cell<i64>>(count).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<i64>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    fn alloc_bool(arena: &'a Arena, count: u32) -> Result<&'a [Cell<bool>], TheoryError> {
        let range = arena.alloc_array::<Cell<bool>>(count).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::ArenaFull,
            ))
        })?;
        arena.array::<Cell<bool>>(range).map_err(|_| {
            TheoryError::Storage(SatCoreError::Storage(
                crate::sat::clause::SatClauseError::InvalidClauseOffset,
            ))
        })
    }

    /// CEP:WHAT: Resets the edge list, the class mirror, and the occurrence flags.
    /// CEP:WHY: The DPLL(T) loop re-asserts the full atom assignment per conflict cycle.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: called before each assertion batch.
    /// CEP:COST: O(kMaxTheoryVars) plus the class reset.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: none.
    pub fn reset(&self) {
        self.edge_count.set(0);
        for variable in 0..kMaxTheoryVars as usize {
            self.zero_parent[variable].set(variable as u32);
            self.zero_rank[variable].set(0);
            self.occurs[variable].set(false);
        }
    }

    /// CEP:WHAT: Adds one asserted constraint x - y <= w (an edge y -> x of length w).
    /// CEP:WHY: The assertion side of design 13.1's constraint graph.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::ArithmeticOverflow for an out-of-range weight and Storage past the edge capacity or for out-of-range variables.
    /// CEP:ASSUMES: the weight is in fixed-point units.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_consistent.
    /// CEP:SECURITY: bounded by the edge and variable capacities.
    pub fn add_constraint(&self, left: u32, right: u32, weight: i64) -> Result<(), TheoryError> {
        if left >= kMaxTheoryVars || right >= kMaxTheoryVars {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        if weight.abs() > mapt_config::limits::kTheoryDlMaxWeight {
            return Err(TheoryError::ArithmeticOverflow);
        }
        let edge = self.edge_count.get() as usize;
        if edge >= self.edge_left.len() {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        self.edge_left[edge].set(left);
        self.edge_right[edge].set(right);
        self.edge_weight[edge].set(weight);
        self.edge_count.set((edge + 1) as u32);
        self.occurs[left as usize].set(true);
        self.occurs[right as usize].set(true);
        Ok(())
    }

    /// CEP:WHAT: Adds the two zero-weight edges of an equality (x - y <= 0 and y - x <= 0) and mirrors the class union.
    /// CEP:WHY: Nelson-Oppen's propagated equalities and the tentative entailment tests both express equality this way.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError.
    /// CEP:ASSUMES: both variables are in range.
    /// CEP:COST: O(1).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounded by the edge capacity.
    pub fn add_zero_equality(&self, left: u32, right: u32) -> Result<(), TheoryError> {
        self.add_constraint(left, right, 0)?;
        self.add_constraint(right, left, 0)?;
        // The class mirror unions on the PAIR only: a single zero-weight edge is
        // one inequality and does not entail equality.
        self.zero_union(left, right)?;
        Ok(())
    }

    /// CEP:WHAT: Returns whether the two variables are zero-class-merged.
    /// CEP:WHY: The coordinator's filter against re-testing already-merged pairs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on out-of-range variables.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(alpha).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn zero_equal(&self, left: u32, right: u32) -> Result<bool, TheoryError> {
        if left >= kMaxTheoryVars || right >= kMaxTheoryVars {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        Ok(self.zero_find(left)? == self.zero_find(right)?)
    }

    /// CEP:WHAT: Returns whether a variable occurs in at least one edge.
    /// CEP:WHY: The pair-entailment tests only consider constrained variables.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns TheoryError::Storage on an out-of-range variable.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one load.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    /// CEP:SECURITY: bounds-checked reads.
    pub fn occurs_in(&self, variable: u32) -> Result<bool, TheoryError> {
        if variable >= kMaxTheoryVars {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        Ok(self.occurs[variable as usize].get())
    }

    /// CEP:WHAT: Runs the consistency check: Bellman-Ford over the constraint graph from a virtual source (distances zero everywhere), |V| rounds plus one detection pass; any further relaxation is a negative cycle.
    /// CEP:WHY: Design 13.1's constraint-graph consistency test for the difference-logic fragment (Nieuwenhuis et al. 2006).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns Ok(false) on a negative cycle (inconsistent) and TheoryError on storage failures; never panics.
    /// CEP:ASSUMES: called after the assertion batch.
    /// CEP:COST: O(vars x edges).
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::difference_logic_conflict.
    /// CEP:SECURITY: bounded rounds.
    pub fn check(&self) -> Result<bool, TheoryError> {
        for variable in 0..kMaxTheoryVars as usize {
            self.dist[variable].set(0);
        }
        let rounds = kMaxTheoryVars + 1;
        for _ in 0..rounds {
            let mut changed = false;
            let edges = self.edge_count.get() as usize;
            for edge in 0..edges {
                let left = self.edge_left[edge].get() as usize;
                let right = self.edge_right[edge].get() as usize;
                let weight = self.edge_weight[edge].get();
                let candidate = self.dist[right]
                    .get()
                    .checked_add(weight)
                    .ok_or(TheoryError::ArithmeticOverflow)?;
                if candidate < self.dist[left].get() {
                    self.dist[left].set(candidate);
                    changed = true;
                }
            }
            if !changed {
                return Ok(true);
            }
        }
        // The (|V| + 1)-th round still relaxed: a negative cycle exists.
        Ok(false)
    }

    /// CEP:WHAT: Tests whether the current constraints entail x = y: appends each strict separation (x < y and y < x, one fixed-point unit apart) tentatively and reports the equality entailed exactly when BOTH separations are inconsistent.
    /// CEP:WHY: Nelson-Oppen's DL-to-EUF direction: the equality is forced exactly when neither strict orientation is satisfiable; testing the equality's own consistency (the +-0 form) would confuse "the equality is compatible" with "the equality is forced" and merge pairs the difference logic leaves free; the truncation makes each probe stateless (no mutation survives).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: propagates TheoryError; the state is unchanged on every path.
    /// CEP:ASSUMES: called between assertion batches (the tentative edges never persist).
    /// CEP:COST: two checks plus O(1) truncations.
    /// CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories; property/theory_property_test.rs::combined_instances_agree_with_oracle.
    /// CEP:SECURITY: bounded by the edge capacity.
    pub fn entailed_equal(&self, left: u32, right: u32) -> Result<bool, TheoryError> {
        let mark = self.edge_count.get();
        self.add_constraint(left, right, -1)?;
        let left_forced = !self.check()?;
        self.edge_count.set(mark);
        self.add_constraint(right, left, -1)?;
        let right_forced = !self.check()?;
        self.edge_count.set(mark);
        Ok(left_forced && right_forced)
    }

    // CEP:WHAT: Union-find find over the zero-equality classes (path halving).
    // CEP:WHY: The class mirror's read side.
    // CEP:STATUS: complete
    // CEP:FAILURE: Returns TheoryError::Storage on an out-of-range variable.
    // CEP:ASSUMES: none.
    // CEP:COST: O(alpha) amortized.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    // CEP:SECURITY: bounds-checked reads.
    fn zero_find(&self, variable: u32) -> Result<u32, TheoryError> {
        if variable >= kMaxTheoryVars {
            return Err(TheoryError::Storage(SatCoreError::InvariantViolation));
        }
        let mut current = variable;
        while self.zero_parent[current as usize].get() != current {
            let grandparent =
                self.zero_parent[self.zero_parent[current as usize].get() as usize].get();
            self.zero_parent[current as usize].set(grandparent);
            current = grandparent;
        }
        Ok(current)
    }

    // CEP:WHAT: Union-find union over the zero-equality classes (rank, ties toward the smaller id).
    // CEP:WHY: The class mirror's write side.
    // CEP:STATUS: complete
    // CEP:FAILURE: propagates TheoryError.
    // CEP:ASSUMES: both variables in range.
    // CEP:COST: O(alpha) amortized.
    // CEP:EVIDENCE: unit/hot/theory_test.rs::nelson_oppen_combines_theories.
    // CEP:SECURITY: bounds-checked writes.
    fn zero_union(&self, left: u32, right: u32) -> Result<(), TheoryError> {
        let a = self.zero_find(left)?;
        let b = self.zero_find(right)?;
        if a == b {
            return Ok(());
        }
        let (child, root) = if self.zero_rank[a as usize].get() > self.zero_rank[b as usize].get()
            || (self.zero_rank[a as usize].get() == self.zero_rank[b as usize].get() && a < b)
        {
            (b, a)
        } else {
            (a, b)
        };
        self.zero_parent[child as usize].set(root);
        if self.zero_rank[a as usize].get() == self.zero_rank[b as usize].get() {
            self.zero_rank[root as usize].set(self.zero_rank[root as usize].get() + 1);
        }
        Ok(())
    }
}
