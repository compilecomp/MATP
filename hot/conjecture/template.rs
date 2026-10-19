// CEP:FILE: hot/conjecture/template.rs
// CEP:WHAT: The bounded conjecture-candidate templates (Spec 16 sections 3-4): collection of the recent derived unit equations, then the three deterministic templates - T1 symmetry (t2 = t1 from a derived t1 = t2), T2 transitivity (t1 = t3 from derived t1 = t2 and t2 = t3 joined by hash-consed term identity), and T3 constructor instantiation (the all-zero and all-successor-of-zero ground instances of a unit equation with at most kConjectureInstanceVariables variables, over a declared datatype).
// CEP:WHY: Speculative lemma generation must be bounded, deterministic, and content-addressable (CEP&CC 22.10, 38.10, 39.1): the unit window is the most recent kConjectureTransitivityWindow derived units (descending-id scan, window-capped), candidates enumerate in ascending unit order with templates in fixed order (T1, T2, T3), every join is hash-consed pointer equality (Spec 01 section 3: pointer identity IS structural identity), reflexive and duplicate candidates are skipped by the same identity, and the total candidate list is capped at kMaxConjectureCandidates - a deterministic prefix cut, never a silent drop (Law 4: the harvest reports tried candidates and the bounds tests pin the caps); T3 needs the datatype declaration and therefore runs only in the driver-invoked pre-search harvest (the in-loop harvest runs T1/T2 only), and its two canonical patterns (all-zero, all-successor-of-zero) are exactly the induction base and step witnesses of Spec 15, which is what makes T3 the induction-support template.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction-fatal intern failures surface as Ok-with-fewer-candidates (the enumeration counts and continues; a candidate that cannot be built is not a failure of the search); never panics.
// CEP:ASSUMES: the space's store is the search's store; derived units are identifiable by their derivation rule; the declaration (when given) is validated.
// CEP:COST: collection O(ids scanned until the window fills); T1 O(units); T2 O(units^2) pointer comparisons bounded by the window; T3 O(units x variables) substitution applications; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{symmetry_candidates, transitivity_pairs_recent_units, constructor_instances_bounded, candidate_budget_enforced, enumeration_is_deterministic}; bench CEP-BENCH-0037.
// CEP:SECURITY: every scan and buffer is bounded by named constants.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic: fixed scan direction, fixed template order, fixed variable numbering, hash-consed identity tests; unit/hot/conjecture_test.rs::enumeration_is_deterministic pins the double-run discipline.
// CEP:HPC-PASS-LEGALITY: Formal Spec 16 sections 3-4 fix the templates' syntactic definitions and the enumeration order; the section 6 theorem (only refutation-proved lemmas are added) depends on the filter, not the templates, so the templates carry no soundness obligation beyond determinism and boundedness, both pinned here.

use crate::induction::InductionDeclaration;
use crate::inference::{apply_literal, InferenceContext};
use crate::ir::literal::Literal;
use crate::ir::term::{TermPtr, TermStore};
use crate::search::given_clause::SearchSpace;
use crate::unification::substitution::Substitution;
use mapt_config::limits::{
    kConjectureInstanceVariables, kConjectureTransitivityWindow, kFirstClauseId,
    kMaxConjectureCandidates,
};

/// CEP:WHAT: One collected unit equation: the clause id and the two equation sides.
/// CEP:WHY: The templates join units by side identity and the import path never needs the full literal again; carrying (id, left, right) is the minimal deterministic record.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: filled by collect_recent_units.
/// CEP:COST: 16 bytes.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{symmetry_candidates, transitivity_pairs_recent_units}.
/// CEP:SECURITY: none.
#[derive(Clone, Copy)]
pub struct UnitEquation {
    /// CEP:WHAT: The unit clause's store id.
    /// CEP:WHY: Diagnostics and stable enumeration order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: a live store id.
    /// CEP:COST: 8 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::symmetry_candidates.
    /// CEP:SECURITY: none.
    pub id: u64,
    /// CEP:WHAT: The equation's left side.
    /// CEP:WHY: T2's join key and T1's swap target.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: interned term pointer.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::symmetry_candidates.
    /// CEP:SECURITY: none.
    pub left: TermPtr,
    /// CEP:WHAT: The equation's right side.
    /// CEP:WHY: T2's join key and T1's swap target.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: interned term pointer.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::symmetry_candidates.
    /// CEP:SECURITY: none.
    pub right: TermPtr,
}

/// CEP:WHAT: The candidate list: at most kMaxConjectureCandidates positive unit-equation literals in enumeration order.
/// CEP:WHY: The fixed array keeps the harvest allocation-free; the cap is the per-harvest work bound (Spec 16 section 5); duplicates are suppressed by hash-consed atom identity so the list is also a set.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: filled by enumerate_candidates.
/// CEP:COST: kMaxConjectureCandidates x 12 bytes.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{candidate_budget_enforced, enumeration_is_deterministic}.
/// CEP:SECURITY: bounded buffer.
pub struct CandidateList {
    /// CEP:WHAT: The candidate literals (positive unit equations).
    /// CEP:WHY: The filter's input.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries beyond count are filler.
    /// CEP:COST: fixed array.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
    /// CEP:SECURITY: none.
    pub literals: [Literal; kMaxConjectureCandidates as usize],
    /// CEP:WHAT: The fill level.
    /// CEP:WHY: Named bound, named fill (CEP&CC 11.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kMaxConjectureCandidates.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
    /// CEP:SECURITY: none.
    pub count: usize,
}

impl CandidateList {
    // CEP:WHAT: Constructs an empty list.
    // CEP:WHY: One constructor fixes the initial state.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
    // CEP:SECURITY: none.
    pub fn new() -> CandidateList {
        CandidateList {
            literals: [Literal::new(TermPtr::invalid(), true); kMaxConjectureCandidates as usize],
            count: 0,
        }
    }

    // CEP:WHAT: Appends one candidate unless the list is full or the atom is already present.
    // CEP:WHY: The dedup-by-identity rule (hash-consed pointer equality) keeps the candidate set duplicate-free, and the cap is the deterministic prefix cut (Law 4: the harvest's stats report what was tried).
    // CEP:STATUS: complete
    // CEP:FAILURE: returns false when the candidate was not appended (full or duplicate); the caller counts nothing.
    // CEP:ASSUMES: the atom is interned.
    // CEP:COST: O(count) identity checks.
    // CEP:EVIDENCE: unit/hot/conjecture_test.rs::{candidate_budget_enforced, enumeration_is_deterministic}.
    // CEP:SECURITY: none.
    pub fn push(&mut self, literal: Literal) -> bool {
        if self.count >= kMaxConjectureCandidates as usize {
            return false;
        }
        for index in 0..self.count {
            if self.literals[index].atom() == literal.atom() {
                return false;
            }
        }
        self.literals[self.count] = literal;
        self.count += 1;
        true
    }
}

impl Default for CandidateList {
    fn default() -> Self {
        Self::new()
    }
}

// CEP:WHAT: True when the derivation rule marks a genuinely inference-derived clause (the T1/T2 source filter).
// CEP:WHY: Input clauses, theory schemes, negated conjectures, assumption premises, and already-imported lemmas are excluded from T1/T2 sources: re-deriving what the input already states or re-harvesting lemmas is wasted speculation, and excluding ConjectureLemma sources breaks the harvest cycle (a lemma's subproof is never re-harvested).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum comparisons.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{symmetry_candidates, unprovable_candidate_adds_nothing}.
// CEP:SECURITY: none.
fn is_derived_rule(rule: crate::ir::clause::InferenceRule) -> bool {
    use crate::ir::clause::InferenceRule as Rule;
    !matches!(
        rule,
        Rule::Input
            | Rule::NegatedConjecture
            | Rule::StructuralInduction
            | Rule::WellFoundedInduction
            | Rule::ConjectureNegation
            | Rule::ConjectureLemma
    )
}

// CEP:WHAT: True when the rule marks a source eligible for constructor instantiation (T3).
// CEP:WHY: T3 instantiates unit equations from the problem statement AND derived units (both feed induction base cases); only proof-internal rules (the negation premise and lemmas themselves) are excluded to break the harvest cycle.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: enum comparisons.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
// CEP:SECURITY: none.
fn is_instantiable_rule(rule: crate::ir::clause::InferenceRule) -> bool {
    use crate::ir::clause::InferenceRule as Rule;
    !matches!(rule, Rule::ConjectureNegation | Rule::ConjectureLemma)
}

// CEP:WHAT: Collects the most recent derived positive unit equations into the window buffer, newest first.
// CEP:WHY: Spec 16 section 3: the scan walks ids descending from the store's next id (deterministic direction), keeps a clause only when it is a single positive equality literal whose derivation rule passes the T1/T2 source filter, and stops when the window (kConjectureTransitivityWindow) is full; the caller reverses to ascending order, so the enumeration order is id-ascending regardless of the scan direction.
// CEP:STATUS: complete
// CEP:FAILURE: unreadable clauses stop the scan (the window keeps what it has; a corrupt store is the search's failure, not the harvest's).
// CEP:ASSUMES: the store's id side table is consistent.
// CEP:COST: O(ids scanned) with an early stop at the window bound.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{transitivity_pairs_recent_units, enumeration_is_deterministic}.
// CEP:SECURITY: bounded scan and buffer.
pub fn collect_recent_units(space: &SearchSpace<'_>, context: &InferenceContext<'_>) -> UnitWindow {
    let mut window = UnitWindow {
        units: [UnitEquation {
            id: 0,
            left: TermPtr::invalid(),
            right: TermPtr::invalid(),
        }; kConjectureTransitivityWindow as usize],
        count: 0,
    };
    let next_id = space.store.next_clause_id().0;
    let mut id = next_id;
    while id > kFirstClauseId && window.count < kConjectureTransitivityWindow as usize {
        id -= 1;
        if id < kFirstClauseId {
            break;
        }
        let record = match space.store.clause_by_id(crate::ir::clause::ClauseId(id)) {
            Ok(record) => record,
            Err(_) => break,
        };
        if record.literal_count != 1 || !is_derived_rule(record.derivation.rule) {
            continue;
        }
        let literal = match space.store.literal(record, 0) {
            Ok(literal) => literal,
            Err(_) => break,
        };
        if !literal.is_positive() {
            continue;
        }
        let view = match context.terms.term(literal.atom()) {
            Ok(view) => view,
            Err(_) => break,
        };
        if view.tag() != crate::ir::term::TermTag::Equality {
            continue;
        }
        let left = match view.child(0) {
            Ok(child) => child,
            Err(_) => break,
        };
        let right = match view.child(1) {
            Ok(child) => child,
            Err(_) => break,
        };
        window.units[window.count] = UnitEquation { id, left, right };
        window.count += 1;
    }
    // Reverse to ascending id order (the enumeration order).
    window.units[..window.count].reverse();
    window
}

/// CEP:WHAT: The fixed-size unit window (newest collected, then reversed to ascending order by collect_recent_units).
/// CEP:WHY: no_std discipline: the window is a fixed array with a fill level, not an allocation.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: filled by collect_recent_units.
/// CEP:COST: kConjectureTransitivityWindow x 16 bytes.
/// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{transitivity_pairs_recent_units, candidate_budget_enforced}.
/// CEP:SECURITY: bounded buffer.
pub struct UnitWindow {
    /// CEP:WHAT: The collected units in ascending id order.
    /// CEP:WHY: The templates' source list.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: entries beyond count are filler.
    /// CEP:COST: fixed array.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::transitivity_pairs_recent_units.
    /// CEP:SECURITY: none.
    pub units: [UnitEquation; kConjectureTransitivityWindow as usize],
    /// CEP:WHAT: The fill level.
    /// CEP:WHY: Named bound, named fill.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kConjectureTransitivityWindow.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/conjecture_test.rs::candidate_budget_enforced.
    /// CEP:SECURITY: none.
    pub count: usize,
}

// CEP:WHAT: Counts a term's distinct variable indices (dense-or-gapped, bounded by the clause variable budget).
// CEP:WHY: T3's eligibility test (at most kConjectureInstanceVariables distinct variables); the walk is the induction scan's discipline (depth-bounded recursion).
// CEP:STATUS: complete
// CEP:FAILURE: None on unreadable terms (the unit is skipped); Some(count) otherwise.
// CEP:ASSUMES: the term is interned.
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
// CEP:SECURITY: depth-bounded recursion.
fn count_variables(
    terms: &TermStore<'_>,
    ptr: TermPtr,
    depth: u32,
    seen: &mut [u32; kConjectureInstanceVariables as usize + 1],
    seen_count: &mut usize,
) -> Option<()> {
    if depth > mapt_config::limits::kMaxTermDepth as u32 {
        return None;
    }
    let view = terms.term(ptr).ok()?;
    match view.tag() {
        crate::ir::term::TermTag::Variable => {
            let index = view.symbol();
            let mut present = false;
            for variable in seen[..*seen_count].iter() {
                if *variable == index {
                    present = true;
                    break;
                }
            }
            if !present {
                if *seen_count >= seen.len() {
                    return None;
                }
                seen[*seen_count] = index;
                *seen_count += 1;
            }
            Some(())
        }
        crate::ir::term::TermTag::Sort => Some(()),
        _ => {
            for child in view.children() {
                count_variables(terms, child, depth + 1, seen, seen_count)?;
            }
            Some(())
        }
    }
}

// CEP:WHAT: Binds every seen variable index of the unit to the pattern term and applies the substitution to the literal.
// CEP:WHY: T3's instantiation step: one fresh substitution per harvest (created by the caller), bind-all then apply then unwind - the trail discipline of Spec 02 section 4; the pattern terms (zero, successor-of-zero) are interned once per harvest by the caller and shared.
// CEP:STATUS: complete
// CEP:FAILURE: Ok(None) when binding or application fails (the unit is skipped; the trail is unwound first).
// CEP:ASSUMES: the substitution is at baseline depth on entry and on every Ok return.
// CEP:COST: O(variables + term nodes).
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
// CEP:SECURITY: bounded substitution use.
fn instantiate_at(
    context: &InferenceContext<'_>,
    substitution: &Substitution<'_>,
    literal: Literal,
    seen: &[u32; kConjectureInstanceVariables as usize + 1],
    seen_count: usize,
    pattern: TermPtr,
) -> Option<Literal> {
    let entry_depth = substitution.trail_depth();
    for variable in seen[..seen_count].iter() {
        if substitution.bind(*variable, pattern).is_err() {
            substitution.undo_to(entry_depth);
            return None;
        }
    }
    let applied = apply_literal(context.terms, context.symbols, substitution, literal);
    substitution.undo_to(entry_depth);
    let applied = match applied {
        Ok(literal) => literal,
        Err(_) => return None,
    };
    if applied.atom() == literal.atom() {
        // The unit was already ground at this pattern (no variables bound).
        return None;
    }
    Some(applied)
}

// CEP:WHAT: Enumerates the candidate lemmas from the unit window: T1 per unit (ascending), T2 per ordered pair (older joined to newer, both chain directions in fixed order), then T3 per instantiable unit (both canonical patterns) when a datatype declaration is given.
// CEP:WHY: Spec 16 section 4: the fixed template order and the fixed enumeration order make the candidate list a pure function of the window and the declaration (determinism); every join is hash-consed pointer identity; reflexive candidates (left == right) are skipped; duplicates are suppressed by atom identity; the kMaxConjectureCandidates cap cuts the list deterministically.
// CEP:STATUS: complete
// CEP:FAILURE: never returns Err: intern or substitution failures skip the individual candidate (counted by absence); the harvest's stats report what was tried.
// CEP:ASSUMES: the window is ascending by id; the declaration (when given) is validated.
// CEP:COST: O(window^2) for T2 plus O(window x variables) for T3; measured in bench CEP-BENCH-0037.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::{symmetry_candidates, transitivity_pairs_recent_units, constructor_instances_bounded, candidate_budget_enforced, enumeration_is_deterministic}.
// CEP:SECURITY: bounded loops throughout.
pub fn enumerate_candidates(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    window: &UnitWindow,
    declaration: Option<&InductionDeclaration>,
) -> CandidateList {
    let mut candidates = CandidateList::new();
    let units = &window.units[..window.count];
    // T1: symmetry of every derived unit, ascending id order.
    for unit in units.iter() {
        if unit.left == unit.right {
            continue;
        }
        if let Ok(atom) = context
            .terms
            .intern_eq(context.symbols, unit.right, unit.left)
        {
            candidates.push(Literal::new(atom, true));
        }
    }
    // T2: transitive chains between ordered pairs (older unit first).
    for newer in 1..units.len() {
        for older in 0..newer {
            let old_unit = units[older];
            let new_unit = units[newer];
            // Chain old -> new: old.right == new.left gives (old.left, new.right).
            if old_unit.right == new_unit.left && old_unit.left != new_unit.right {
                if let Ok(atom) =
                    context
                        .terms
                        .intern_eq(context.symbols, old_unit.left, new_unit.right)
                {
                    candidates.push(Literal::new(atom, true));
                }
            }
            // Chain new -> old: new.right == old.left gives (new.left, old.right).
            if new_unit.right == old_unit.left && new_unit.left != old_unit.right {
                if let Ok(atom) =
                    context
                        .terms
                        .intern_eq(context.symbols, new_unit.left, old_unit.right)
                {
                    candidates.push(Literal::new(atom, true));
                }
            }
        }
    }
    // T3: constructor instantiation over a declared datatype. Sources are the
    // input-range units (axioms and schemes, is_instantiable_rule) and the
    // window's derived units (both feed induction base cases); the window's
    // coverage of derived units is the recent-derivation front (Spec 16
    // section 4).
    if let Some(declaration) = declaration {
        let zero_term = context
            .terms
            .intern_fun(context.symbols, declaration.zero, &[]);
        let step_term = match zero_term {
            Ok(zero) => context
                .terms
                .intern_fun(context.symbols, declaration.succ, &[zero]),
            Err(_) => Err(crate::ir::term::TermError::UnknownSymbol),
        };
        if let (Ok(zero_term), Ok(step_term)) = (zero_term, step_term) {
            let substitution = Substitution::new(space.arena);
            for index in 0..space.input_count() as u64 {
                let id = kFirstClauseId + index;
                let record = match space.store.clause_by_id(crate::ir::clause::ClauseId(id)) {
                    Ok(record) => record,
                    Err(_) => break,
                };
                if record.literal_count != 1 || !is_instantiable_rule(record.derivation.rule) {
                    continue;
                }
                let literal = match space.store.literal(record, 0) {
                    Ok(literal) => literal,
                    Err(_) => break,
                };
                if !literal.is_positive() {
                    continue;
                }
                let view = match context.terms.term(literal.atom()) {
                    Ok(view) => view,
                    Err(_) => break,
                };
                if view.tag() != crate::ir::term::TermTag::Equality {
                    continue;
                }
                instantiate_unit_at_patterns(
                    context,
                    &substitution,
                    literal,
                    zero_term,
                    step_term,
                    &mut candidates,
                );
            }
            for unit in units.iter() {
                if let Ok(literal) = unit_literal(space, unit.id) {
                    instantiate_unit_at_patterns(
                        context,
                        &substitution,
                        literal,
                        zero_term,
                        step_term,
                        &mut candidates,
                    );
                }
            }
        }
    }
    candidates
}

// CEP:WHAT: Reads one unit clause's single literal by id.
// CEP:WHY: The T3 window-source reader: the window carries (id, left, right); re-reading the literal through the store keeps one access path.
// CEP:STATUS: complete
// CEP:FAILURE: Err on unreadable clauses.
// CEP:ASSUMES: the id is a live unit clause.
// CEP:COST: one side-table lookup and one literal read.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
// CEP:SECURITY: bounds-checked reads.
fn unit_literal(space: &SearchSpace<'_>, id: u64) -> Result<Literal, ()> {
    let record = space
        .store
        .clause_by_id(crate::ir::clause::ClauseId(id))
        .map_err(|_| ())?;
    space.store.literal(record, 0).map_err(|_| ())
}

// CEP:WHAT: Applies both canonical constructor patterns to one positive unit-equation literal and pushes the ground instances as candidates.
// CEP:WHY: The shared body of T3's two source loops (input-range units and window units): count the distinct variables (eligibility: at most kConjectureInstanceVariables, at least one), then instantiate all-zero and all-successor-of-zero through one trail-disciplined substitution.
// CEP:STATUS: complete
// CEP:FAILURE: skips the unit on any structural failure (never Err; the candidate simply does not appear).
// CEP:ASSUMES: the literal is a positive unit equation; the substitution is at baseline depth.
// CEP:COST: O(term nodes + variables) per pattern.
// CEP:EVIDENCE: unit/hot/conjecture_test.rs::constructor_instances_bounded.
// CEP:SECURITY: bounded recursion and substitution use.
fn instantiate_unit_at_patterns(
    context: &InferenceContext<'_>,
    substitution: &Substitution<'_>,
    literal: Literal,
    zero_term: TermPtr,
    step_term: TermPtr,
    candidates: &mut CandidateList,
) {
    let mut seen: [u32; kConjectureInstanceVariables as usize + 1] =
        [0; kConjectureInstanceVariables as usize + 1];
    let mut seen_count: usize = 0;
    let countable = count_variables(context.terms, literal.atom(), 0, &mut seen, &mut seen_count);
    if countable.is_none() || seen_count == 0 {
        return;
    }
    for pattern in [zero_term, step_term] {
        if let Some(instantiated) =
            instantiate_at(context, substitution, literal, &seen, seen_count, pattern)
        {
            candidates.push(instantiated);
        }
    }
}
