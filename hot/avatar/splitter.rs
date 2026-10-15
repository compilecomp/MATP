// CEP:FILE: hot/avatar/splitter.rs
// CEP:WHAT: The AVATAR splitting decision (design 12.3): partitions a clause's literals into the connected components of the variable-dependency graph via union-find over the clause's variable namespace, and applies the kAvatarMinComponentSize gate.
// CEP:WHY: Design 26 Phase 4 build order and Voronkov (CAV 2014) section 3: a clause C whose variable-dependency graph has multiple connected components C1, ..., Cn (variables adjacent when they share a literal) can be replaced by the components guarded by propositional assertion variables, because the components share no variables and therefore their satisfiability is independent; Spec 12 section 3 fixes the all-or-nothing reading of kAvatarMinComponentSize (a split happens only when every component has at least the threshold's literal count), which keeps tiny components from fragmenting the search for no factorization gain; failure to split is always sound (the clause stays whole), so budget exhaustion degrades to Unsplittable instead of an error.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: returns SplitDecision::Unsplittable for every non-split outcome (single component, threshold gate, variable-budget overflow, walk-budget exhaustion); never panics, never errors - splitting is an optimization and its absence is always sound.
// CEP:ASSUMES: literal atoms were interned by the given term store; variable ids below kMaxVariablesPerClause are dense (the restandardization discipline of the search loop and the controller's materialize path).
// CEP:COST: O(literals x term nodes) variable collection plus near-linear union-find; measured in bench CEP-BENCH-0031, artifact benches/artifacts/avatar_split_step.json.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, ground_singleton_blocks_split, min_component_size_gate, single_component_stays_whole, walk_budget_degrades_to_unsplittable, component_literals_tagged}; property/avatar_property_test.rs::{splits_preserve_literal_multiset, components_are_variable_disjoint, disjunction_of_components_is_original}.
// CEP:SECURITY: every walk is bounded by kAvatarSplitNodeBudget; a forged deep term degrades to Unsplittable, never to unbounded work.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic; the union-find, component numbering (first occurrence order), and gate are pure functions of the literal sequence.
// CEP:HPC-PASS-LEGALITY: Formal Spec 12 section 3 fixes the variable-dependency graph, the connected-component partition, and the threshold gate; the property tests verify executably that components partition the literal multiset and are pairwise variable-disjoint, which are exactly the two premises of the splitting soundness lemma (Spec 12 Lemma 1).

use crate::ir::literal::Literal;
use crate::ir::term::{TermPtr, TermStore, TermTag};
use mapt_config::limits::{
    kAvatarMinComponentSize, kAvatarSplitNodeBudget, kMaxClauseLiterals, kMaxTermDepth,
    kMaxVariablesPerClause,
};

/// CEP:WHAT: Maximum number of components one split can produce (kMaxClauseLiterals / 2 at the minimum component size of 2 literals).
/// CEP:WHY: The component-size and literal-count buffers are sized once; the bound is structural (every component holds at least 2 literals in any gated split), keeping the decision record a fixed-size stack value (CEP&CC 22.10 unbounded-buffering ban).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a representation bound.
/// CEP:ASSUMES: kAvatarMinComponentSize >= 2 keeps the bound sound; the limits assertion chain pins the gate range.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::min_component_size_gate.
/// CEP:SECURITY: none.
pub const kMaxSplitComponents: usize = (kMaxClauseLiterals as usize) / 2;

/// CEP:WHAT: Maximum variables one split's union-find tracks (kMaxVariablesPerClause).
/// CEP:WHY: The restandardization discipline gives every clause a dense variable namespace below kMaxVariablesPerClause (Spec 07 section 2), so the parent array is a fixed stack buffer.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a representation bound.
/// CEP:ASSUMES: callers restandardize before splitting (the controller's documented contract).
/// CEP:COST: 256 bytes on the stack.
/// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
/// CEP:SECURITY: none.
pub const kSplitVariableSlots: usize = kMaxVariablesPerClause as usize;

/// CEP:WHAT: The split decision: Unsplittable (the clause stays whole) or the component partition.
/// CEP:WHY: A vocabulary type that makes the no-split path explicit; every non-split reason collapses to one variant because they are all sound degradations (CEP&CC Law 6 - the stats, not the type, carry the reason).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{single_component_stays_whole, two_variable_disjoint_components_split}.
/// CEP:SECURITY: none.
// CEP:WHAT: Clippy allowance for the variant size difference (Unsplittable is a unit, Splittable carries the 1.5 KiB inline view).
// CEP:WHY: The no_std discipline forbids boxing the payload; the view is a fixed stack record by design (CEP&CC 22.10) and the enum is returned by value on a cold-ish path (once per new clause), so the size difference is the documented cost of allocation-free splitting.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: 1.5 KiB moved per decision.
// CEP:EVIDENCE: bench CEP-BENCH-0031 (the decision cost is measured).
// CEP:SECURITY: none.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SplitDecision {
    /// CEP:WHAT: The clause is not split (single component, gate refusal, or budget degradation).
    /// CEP:WHY: Keeping the clause whole is always sound; the controller adds it to the search unchanged.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::single_component_stays_whole.
    /// CEP:SECURITY: none.
    Unsplittable,
    /// CEP:WHAT: The clause splits; the payload carries the partition.
    /// CEP:WHY: The controller materializes one component clause per component (design 12.2 rule 1).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the view's buffers describe the caller's literal slice positionally.
    /// CEP:COST: enum value plus the 1.5 KiB inline view.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    /// CEP:SECURITY: none.
    Splittable(SplitView),
}

/// CEP:WHAT: The component partition of one clause: literal-to-component indices and per-component literal counts.
/// CEP:WHY: Design 12.2 rule 1: each component becomes a clause; the positional map lets the controller copy each component's literals without allocation (no_std discipline), and the counts drive the min-size gate and the component-clause creation.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: literal_component entries beyond the caller's literal count and component_size entries beyond component_count are zeroed and unused.
/// CEP:COST: 1.5 KiB inline (two fixed arrays); Copy.
/// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, component_literals_tagged}; property/avatar_property_test.rs::splits_preserve_literal_multiset.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SplitView {
    /// CEP:WHAT: Number of components (>= 2 by the gate).
    /// CEP:WHY: Drives the abstraction clause's literal count (design 12.2 rule 2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxSplitComponents.
    /// CEP:COST: 2 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    /// CEP:SECURITY: none.
    pub component_count: u16,
    /// CEP:WHAT: Component index (0..component_count) of each literal, positional over the caller's slice.
    /// CEP:WHY: The controller copies component literals by scanning this map; no per-component index lists are needed.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries at positions >= literals.len() are unused.
    /// CEP:COST: kMaxClauseLiterals x 2 bytes = 1 KiB.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split; property/avatar_property_test.rs::splits_preserve_literal_multiset.
    /// CEP:SECURITY: none.
    pub literal_component: [u16; kMaxClauseLiterals as usize],
    /// CEP:WHAT: Literal count of each component.
    /// CEP:WHY: The min-size gate and the component-clause literal counts.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries beyond component_count are zero.
    /// CEP:COST: kMaxSplitComponents x 2 bytes = 512 bytes.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::min_component_size_gate.
    /// CEP:SECURITY: none.
    pub component_size: [u16; kMaxSplitComponents],
}

// CEP:WHAT: DFS stack slots of the variable walk (kMaxTermDepth).
// CEP:WHY: Named for the walk's depth bound; matches the term construction depth bound so every internable term is walkable.
// CEP:STATUS: complete
// CEP:FAILURE: none; a representation bound.
// CEP:ASSUMES: kMaxTermDepth >= 1.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::walk_budget_degrades_to_unsplittable.
// CEP:SECURITY: none.
const kTermWalkStackSlots: usize = kMaxTermDepth as usize;

// CEP:WHAT: Collects the distinct variable ids of one atom into out; returns the count or None on budget exhaustion.
// CEP:WHY: The dependency graph is built per literal from its atom's variables; the explicit-stack walk respects the no-recursion discipline and makes the cost bound independent of term depth, and duplicates are skipped so the union-find sees each variable once per literal.
// CEP:STATUS: complete
// CEP:FAILURE: returns None when kAvatarSplitNodeBudget nodes are exceeded (the caller degrades to Unsplittable - sound) or a child is unreadable (a forged atom - degrade, never panic).
// CEP:ASSUMES: the atom was interned by the given store; out has at least kSplitVariableSlots slots.
// CEP:COST: O(term nodes) with one budget unit per node.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, walk_budget_degrades_to_unsplittable}.
// CEP:SECURITY: kAvatarSplitNodeBudget bounds adversarial term sizes.
fn collect_variables(terms: &TermStore, atom: TermPtr, out: &mut [u32]) -> Option<usize> {
    // CEP:WHAT: Explicit DFS stack of (node, next-child-cursor) pairs.
    // CEP:WHY: No recursion keeps the walk bounded by the node budget regardless of depth; the fixed stack mirrors kMaxTermDepth headroom.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns None (mapped up) when the stack itself would exceed the depth bound.
    // CEP:ASSUMES: terms are interned (acyclic as a DAG; the budget bounds the tree walk).
    // CEP:COST: 8 bytes per depth level.
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::walk_budget_degrades_to_unsplittable.
    // CEP:SECURITY: stack bounded by kMaxTermDepth.
    let mut stack: [(TermPtr, u16); kTermWalkStackSlots] =
        [(TermPtr::invalid(), 0); kTermWalkStackSlots];
    let mut stack_len: usize = 0;
    let mut found: usize = 0;
    let mut budget: u32 = kAvatarSplitNodeBudget;
    let mut top = atom;
    let mut next_child: u16 = 0;
    loop {
        if budget == 0 {
            return None;
        }
        budget -= 1;
        let view = match terms.term(top) {
            Ok(view) => view,
            Err(_) => return None,
        };
        if view.tag() == TermTag::Variable {
            let id = view.symbol();
            let mut present = false;
            for seen in out[..found].iter() {
                if *seen == id {
                    present = true;
                    break;
                }
            }
            if !present {
                if found >= out.len() || id >= kMaxVariablesPerClause {
                    return None;
                }
                out[found] = id;
                found += 1;
            }
        }
        // CEP:WHAT: Advance to the next unvisited child or pop.
        // CEP:WHY: The (node, cursor) pairs make the walk iterative; children are visited in index order for determinism.
        // CEP:STATUS: complete
        // CEP:FAILURE: an unreadable child degrades to None.
        // CEP:ASSUMES: child counts match the store's records.
        // CEP:COST: one iteration per (node, child) edge.
        // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
        // CEP:SECURITY: child index bounded by child_count.
        let children = view.child_count();
        // CEP:WHAT: Descend into the first unvisited child (single descent, no loop).
        // CEP:WHY: The stack saves the parent's resume cursor, so each visit handles at most one descent; the popped cursor drives the next visit (Spec 12 section 3's walk).
        // CEP:STATUS: complete
        // CEP:FAILURE: depth overflow returns None (TooDeep degradation).
        // CEP:ASSUMES: children > next_child on this path.
        // CEP:COST: one child read per descent.
        // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, walk_budget_degrades_to_unsplittable}.
        // CEP:SECURITY: none.
        if next_child < children {
            let child = match view.child(next_child) {
                Ok(child) => child,
                Err(_) => return None,
            };
            if stack_len >= stack.len() {
                return None;
            }
            stack[stack_len] = (top, next_child + 1);
            stack_len += 1;
            top = child;
            next_child = 0;
        } else {
            if stack_len == 0 {
                return Some(found);
            }
            stack_len -= 1;
            let (parent, cursor) = stack[stack_len];
            top = parent;
            next_child = cursor;
        }
    }
}

// CEP:WHAT: Union-find over the clause's dense variable namespace.
// CEP:WHY: Connected components of the dependency graph (design 12.3): union merges the variables of one literal, find names each literal's component representative; path halving keeps the trees shallow without recursion.
// CEP:STATUS: complete
// CEP:FAILURE: none (callers pass in-range ids; out-of-range ids are rejected before any find by the variable-budget gate in collect_variables).
// CEP:ASSUMES: ids < kSplitVariableSlots.
// CEP:COST: near-linear in unions (path halving).
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
// CEP:SECURITY: none.
struct VarUnionFind {
    // CEP:WHAT: Parent slot per variable id (self-parented roots).
    // CEP:WHY: Fixed-size, no_std-safe; self-parenting initializes every slot without a second occupancy array.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: untouched entries are self-parented by initialization.
    // CEP:COST: 1 KiB.
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    // CEP:SECURITY: none.
    parent: [u32; kSplitVariableSlots],
}

impl VarUnionFind {
    // CEP:WHAT: Initializes every slot as its own root.
    // CEP:WHY: Lazy-free initialization keeps find/union branch-free.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(slots).
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    // CEP:SECURITY: none.
    fn new() -> VarUnionFind {
        let mut parent: [u32; kSplitVariableSlots] = [0; kSplitVariableSlots];
        for (index, slot) in parent.iter_mut().enumerate() {
            *slot = index as u32;
        }
        VarUnionFind { parent }
    }

    // CEP:WHAT: Finds the root of a variable with path halving.
    // CEP:WHY: Path halving keeps the amortized cost near-linear without recursion (no_std stack discipline).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: id < kSplitVariableSlots (collect_variables gates the namespace).
    // CEP:COST: amortized near-constant.
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    // CEP:SECURITY: none.
    fn find(&mut self, id: u32) -> u32 {
        let mut current = id as usize;
        loop {
            let parent = self.parent[current] as usize;
            if parent == current {
                return current as u32;
            }
            let grandparent = self.parent[parent] as usize;
            self.parent[current] = grandparent as u32;
            current = grandparent;
        }
    }

    // CEP:WHAT: Merges the sets of two variables (root of left absorbs root of right).
    // CEP:WHY: The dependency edge union (design 12.3: variables adjacent when they share a literal).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: both ids < kSplitVariableSlots.
    // CEP:COST: two finds plus one store.
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    // CEP:SECURITY: none.
    fn union(&mut self, left: u32, right: u32) {
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root != right_root {
            self.parent[right_root as usize] = left_root;
        }
    }
}

// CEP:WHAT: Runs the split decision with an explicit minimum component size (the production entry uses kAvatarMinComponentSize).
// CEP:WHY: CEP&CC 34.3: the gate threshold is a named bound and must be injectable so tests exercise both gate sides at small scales on the production code path.
// CEP:STATUS: complete
// CEP:FAILURE: returns Unsplittable on every non-split path (see SplitDecision); never panics.
// CEP:ASSUMES: literals.len() <= kMaxClauseLiterals (the store's bound); the caller restandardized the namespace (defensive: a variable >= kMaxVariablesPerClause degrades to Unsplittable).
// CEP:COST: O(literals x nodes) collection plus O(literals^2) worst-case numbering (512 literals, typical < 10); bench CEP-BENCH-0031.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, ground_singleton_blocks_split, min_component_size_gate, single_component_stays_whole, walk_budget_degrades_to_unsplittable}; property/avatar_property_test.rs::{splits_preserve_literal_multiset, components_are_variable_disjoint}.
// CEP:SECURITY: node budget and variable budget bound adversarial input.
pub fn try_split_with(
    terms: &TermStore,
    literals: &[Literal],
    min_component_size: u16,
) -> SplitDecision {
    if literals.len() < 2 || literals.len() > kMaxClauseLiterals as usize {
        return SplitDecision::Unsplittable;
    }
    let mut union_find = VarUnionFind::new();
    // Per-literal variable scratch; sized to the namespace bound.
    let mut variables: [u32; kSplitVariableSlots] = [0; kSplitVariableSlots];
    // CEP:WHAT: Representative key per literal: the union-find root for variable-bearing literals, a unique high key for ground literals.
    // CEP:WHY: Ground literals share no variables with anything (design 12.3 graph), so each is a singleton component; the decrementing high keys start at u32::MAX and stay above kMaxVariablesPerClause, so they cannot collide with variable roots.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: at most kMaxClauseLiterals ground literals per clause (structurally true).
    // CEP:COST: 1 KiB.
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::ground_singleton_blocks_split.
    // CEP:SECURITY: none.
    let mut literal_keys: [u32; kMaxClauseLiterals as usize] = [0; kMaxClauseLiterals as usize];
    let mut ground_key: u32 = u32::MAX;
    for (position, literal) in literals.iter().enumerate() {
        match collect_variables(terms, literal.atom(), &mut variables) {
            Some(count) if count > 0 => {
                let first = variables[0];
                for other in variables[1..count].iter() {
                    union_find.union(first, *other);
                }
                literal_keys[position] = union_find.find(first);
            }
            Some(_) => {
                // Ground literal: singleton component.
                literal_keys[position] = ground_key;
                ground_key = ground_key.wrapping_sub(1);
            }
            None => return SplitDecision::Unsplittable,
        }
    }
    // Compress roots once more so equal components share equal keys.
    for key_slot in literal_keys[..literals.len()].iter_mut() {
        let key = *key_slot;
        if key < kMaxVariablesPerClause {
            *key_slot = union_find.find(key);
        }
    }
    // CEP:WHAT: First-occurrence component numbering.
    // CEP:WHY: Deterministic component ids (Spec 12 section 3) - the scan order is the literal order.
    // CEP:STATUS: complete
    // CEP:FAILURE: returns Unsplittable when more than kMaxSplitComponents distinct components appear (a pathological clause that the gate would reject anyway).
    // CEP:ASSUMES: none.
    // CEP:COST: O(literals^2) worst case (512^2 compares, typical < 10).
    // CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::two_variable_disjoint_components_split.
    // CEP:SECURITY: none.
    let mut view = SplitView {
        component_count: 0,
        literal_component: [0; kMaxClauseLiterals as usize],
        component_size: [0; kMaxSplitComponents],
    };
    for position in 0..literals.len() {
        let key = literal_keys[position];
        let mut assigned: Option<u16> = None;
        for (prior, prior_key) in literal_keys[..position].iter().enumerate() {
            if *prior_key == key {
                assigned = Some(view.literal_component[prior]);
                break;
            }
        }
        let component = match assigned {
            Some(component) => component,
            None => {
                if view.component_count as usize >= kMaxSplitComponents {
                    return SplitDecision::Unsplittable;
                }
                let component = view.component_count;
                view.component_count += 1;
                component
            }
        };
        view.literal_component[position] = component;
        view.component_size[component as usize] += 1;
    }
    // The gate (design 12.3): at least two components, every component at least min_component_size literals.
    if view.component_count < 2 {
        return SplitDecision::Unsplittable;
    }
    for component in 0..view.component_count as usize {
        if view.component_size[component] < min_component_size {
            return SplitDecision::Unsplittable;
        }
    }
    SplitDecision::Splittable(view)
}

// CEP:WHAT: Runs the split decision with the production gate kAvatarMinComponentSize.
// CEP:WHY: Design 12.3 names the constant; the production call sites stay single-argument against the store.
// CEP:STATUS: complete
// CEP:FAILURE: as try_split_with.
// CEP:ASSUMES: as try_split_with.
// CEP:COST: as try_split_with.
// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::{two_variable_disjoint_components_split, ground_singleton_blocks_split, min_component_size_gate}.
// CEP:SECURITY: as try_split_with.
pub fn try_split(terms: &TermStore, literals: &[Literal]) -> SplitDecision {
    try_split_with(terms, literals, kAvatarMinComponentSize)
}
