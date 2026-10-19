// CEP:FILE: hot/induction/mod.rs
// CEP:WHAT: Automated induction (revised build order Phase 4): validated datatype declarations, the input-signature scan, and the scheme installer that adds bounded clausal induction schemes (structural and well-founded) to a search space.
// CEP:WHY: Saturation provers cannot prove inductive theorems from first-order axioms alone (the induction axiom is second-order in the predicate); the SOTA answer - E's induction.ax and Vampire's induction mode - is to add the clausified induction-axiom INSTANCES for the problem's unary predicates under the free-datatype (initial-algebra) convention; MAPT implements exactly that mechanism with the CEP&CC discipline the published heuristics lack: the datatype is not guessed from symbol names or shapes but DECLARED and validated (arity and kind checks, skolem-absence proof by input scan, Spec 15 section 2), the predicate set is scanned in clause-id order and collected deduplicated then sorted by symbol id (deterministic, CEP&CC 38.10), every scheme is exactly the two-clause clausification of the induction axiom instance (Spec 15 section 3, pinned by unit test against the hand derivation), the total scheme mass is bounded by kMaxInductionAttempts (CEP&CC 22.10, 39.1), and each scheme clause carries the StructuralInduction or WellFoundedInduction rule so the proof walk, the TSTP writer, and the replay checker present and check the schemes as named theory axioms (Spec 17); the soundness obligation - the initial-algebra theorem and the well-foundedness argument - is fixed in Formal Spec 15 sections 3.1-3.2, and the zero-ML rule holds: no statistics, no learned weights, no hidden state.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: InductionError carries every rejection path: malformed declarations (kind/arity violations), a skolem that occurs in the input (the freshness proof failed), the input-scan node budget, unreadable terms, and SearchError from the space operations; no scheme is added after a rejection; never panics.
// CEP:ASSUMES: the space's input clauses were added before the call (the scan reads them by id); the declaration's symbols exist in the frozen table; the caller passes max_attempts (production: kMaxInductionAttempts).
// CEP:COST: validation O(1); the input scan O(input term nodes) bounded by kInductionScanNodeBudget with an O(collected) dedup test per symbol node; per covered predicate two (or four with a well-order) clause creations; measured in bench CEP-BENCH-0036.
// CEP:EVIDENCE: unit/hot/induction_test.rs; property/induction_property_test.rs::{schemes_match_hand_clausification, induction_deterministic_double_run, attempts_bound_respected}; bench CEP-BENCH-0036.
// CEP:SECURITY: the scan is node-budgeted (22.10); scheme mass is budgeted; all term and store reads are bounds-checked.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic: the scan walks clauses in id order and terms in child order, the predicate list is deduplicated then sorted by symbol id, and clause creation order fixes ids and passive order; property/induction_property_test.rs::induction_deterministic_double_run pins the two-run discipline.
// CEP:HPC-PASS-LEGALITY: Formal Spec 15 (15_structural_induction.md) fixes the declaration contract, the clausal derivations of both schemes (sections 3-4), the initial-algebra soundness theorems (sections 3.1-3.2), the bounds (section 5), and the TSTP presentation (section 7); the property tests verify executably that generated clauses equal the hand clausification for random predicates.

pub mod scheme;

use crate::inference::InferenceContext;
use crate::ir::clause::InferenceRule;
use crate::ir::symbol_table::{SymbolKind, SymbolTable};
use crate::ir::term::{TermPtr, TermStore, TermTag};
use crate::search::given_clause::{SearchOptions, SearchSpace};
use crate::search::SearchError;
use mapt_config::limits::{kFirstClauseId, kInductionMaxPredicates, kMaxTermDepth};

// CEP:WHAT: The well-order's required arity (a binary predicate).
// CEP:WHY: The validation's arity check names its value (CEP&CC 11.3).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: Spec 15 section 2 fixes the binary shape.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
// CEP:SECURITY: none.
const kWellFoundedArity: u16 = 2;

/// CEP:WHAT: A validated datatype declaration for scheme generation.
/// CEP:WHY: Spec 15 section 2: MAPT does not guess datatypes from symbol shapes or names (that is the unsound-by-convention heuristic the SOTA provers document as their known risk); the driver DECLARES the constructor family (and optionally the well-order) and the module validates the declaration against the frozen symbol table and the input clauses before any scheme exists.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: validation rejections are InductionError values; the record itself carries no failure.
/// CEP:ASSUMES: symbol ids come from the problem's frozen table.
/// CEP:COST: plain data, 16 bytes.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::{declaration_validation_rejects_bad_shapes, skolem_occurrence_rejected}.
/// CEP:SECURITY: the declaration is the trust boundary for scheme soundness; validation is mechanical.
pub struct InductionDeclaration {
    /// CEP:WHAT: The base constructor symbol id (a 0-ary function, e.g. zero).
    /// CEP:WHY: The induction base case instantiates the goal predicate at this constant.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kind Function, arity 0 (validated).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: none.
    pub zero: u32,
    /// CEP:WHAT: The step constructor symbol id (a unary function, e.g. succ).
    /// CEP:WHY: The induction step case instantiates the goal predicate at this constructor applied to the skolem.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: kind Function, arity 1 (validated).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: none.
    pub succ: u32,
    /// CEP:WHAT: The scheme skolem symbol id (a 0-ary function that must NOT occur in any input clause).
    /// CEP:WHY: The clausified schemes existentially introduce one witness constant (Spec 15 section 3); sharing one skolem across all scheme instances is sound because each instance is independently valid regardless of the constant's interpretation, and requiring the caller-provided symbol to be absent from the input keeps the symbol table frozen and the freshness mechanically provable.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: SkolemOccursInInput when the scan finds the symbol in any input atom or subterm.
    /// CEP:ASSUMES: kind Function, arity 0 (validated); absent from every input clause (proven by the scan).
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::skolem_occurrence_rejected.
    /// CEP:SECURITY: the freshness proof is part of the scheme-soundness trust boundary.
    pub skolem: u32,
    /// CEP:WHAT: The optional well-order symbol id (a binary predicate, e.g. less-than) enabling the strong schemes.
    /// CEP:WHY: Spec 15 section 3.2: when the caller declares that a binary relation is the well-order of the datatype (the standard justification: the relation is defined recursively over the constructors, hence well-founded in the initial algebra), every unary predicate additionally receives the two-clause strong-induction scheme.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: WellFoundedNotBinary when the symbol is not a binary predicate.
    /// CEP:ASSUMES: kind Predicate, arity 2 (validated); the semantic obligation (well-foundedness over the declared datatype) is the caller's, fixed by Spec 15 section 3.2.
    /// CEP:COST: 8 bytes (Option<u32>).
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::{well_founded_scheme_clauses_match_clausification, declaration_validation_rejects_bad_shapes}.
    /// CEP:SECURITY: none.
    pub well_founded: Option<u32>,
}

/// CEP:WHAT: Error cases of the induction module.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the module never panics and adds no scheme after a rejection.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy (Search payload for space operations).
/// CEP:EVIDENCE: unit/hot/induction_test.rs::{declaration_validation_rejects_bad_shapes, skolem_occurrence_rejected, scan_budget_rejects_runaway_input}.
/// CEP:SECURITY: validation failures are the soundness boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InductionError {
    /// CEP:WHAT: The zero constructor is not a 0-ary function symbol.
    /// CEP:WHY: The base case instantiates predicates at a ground constant; anything else is a malformed declaration.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: input validation.
    ZeroNotConstant,
    /// CEP:WHAT: The step constructor is not a unary function symbol.
    /// CEP:WHY: The step case applies one constructor to the skolem witness.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: input validation.
    SuccNotUnary,
    /// CEP:WHAT: The skolem is not a 0-ary function symbol.
    /// CEP:WHY: The schemes' existential witness is a constant.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: input validation.
    SkolemNotConstant,
    /// CEP:WHAT: The declared well-order is not a binary predicate symbol.
    /// CEP:WHY: The strong scheme relates two terms through the well-order.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
    /// CEP:SECURITY: input validation.
    WellFoundedNotBinary,
    /// CEP:WHAT: The skolem occurs in an input clause.
    /// CEP:WHY: The schemes are only valid when the witness constant is fresh (Spec 15 section 3): a collision would tie the schemes' existential to the problem's own constant, changing meaning; the scan proves freshness mechanically.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::skolem_occurrence_rejected.
    /// CEP:SECURITY: soundness boundary.
    SkolemOccursInInput,
    /// CEP:WHAT: The input-signature scan exceeded kInductionScanNodeBudget.
    /// CEP:WHY: Defense in depth (CEP&CC 22.10): the structural bounds should make this unreachable; exceeding it means bounds erosion and the module fails loudly instead of trusting the argument.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::scan_budget_rejects_runaway_input.
    /// CEP:SECURITY: denial-of-service bound.
    ScanBudgetExceeded,
    /// CEP:WHAT: A term or clause record could not be read during the scan.
    /// CEP:WHY: Law 6: corrupt-store reads surface loudly instead of being treated as absences.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::skolem_occurrence_rejected.
    /// CEP:SECURITY: corrupt-input detection.
    UnreadableRecord,
    /// CEP:WHAT: The term walk exceeded kMaxTermDepth.
    /// CEP:WHY: Interning enforces the depth bound, so this is defense in depth against structural-bounds erosion (CEP&CC 22.10).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::scan_budget_rejects_runaway_input.
    /// CEP:SECURITY: recursion bound.
    TermWalkOverflow,
    /// CEP:WHAT: A scheme clause's term construction (intern) failed.
    /// CEP:WHY: The builders intern through the production TermStore; table or arena exhaustion surfaces here (Law 6) instead of being swallowed into a partial clause.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
    /// CEP:SECURITY: memory bound reporting.
    TermConstruction,
    /// CEP:WHAT: A search-space operation failed (store bounds, passive capacity).
    /// CEP:WHY: Scheme installation uses the space's add path; its failures surface unchanged.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value with payload.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set.
    /// CEP:SECURITY: store bounds enforced.
    Search(SearchError),
}

impl From<SearchError> for InductionError {
    // CEP:WHAT: Converts search-space failures into the induction vocabulary.
    // CEP:WHY: CEP&CC 33.18: one translation point at the module boundary.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: enum copy.
    // CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set.
    // CEP:SECURITY: none.
    fn from(value: SearchError) -> Self {
        InductionError::Search(value)
    }
}

/// CEP:WHAT: The accounting of one add_induction_schemes call.
/// CEP:WHY: Law 4: bounded drops are counted - predicates skipped by the attempts or collection budgets, structural and well-founded scheme counts, and the scan totals are all reported so no silence hides a bound firing.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a statistics record.
/// CEP:ASSUMES: filled by add_induction_schemes.
/// CEP:COST: 24 bytes.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::{attempts_budget_enforced, schemes_enter_passive_set}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct InductionStats {
    /// CEP:WHAT: Distinct unary predicates found in the input signature.
    /// CEP:WHY: The scheme enumeration domain.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set.
    /// CEP:SECURITY: none.
    pub unary_predicates: u32,
    /// CEP:WHAT: Structural scheme clauses added.
    /// CEP:WHY: Two per covered predicate.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
    /// CEP:SECURITY: none.
    pub structural_schemes: u32,
    /// CEP:WHAT: Well-founded scheme clauses added.
    /// CEP:WHY: Two per covered predicate when a well-order is declared.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::well_founded_scheme_clauses_match_clausification.
    /// CEP:SECURITY: none.
    pub well_founded_schemes: u32,
    /// CEP:WHAT: Predicates skipped because a budget (attempts or collection) was exhausted.
    /// CEP:WHY: Law 4: the bounds' visible accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::attempts_budget_enforced.
    /// CEP:SECURITY: none.
    pub predicates_skipped: u32,
    /// CEP:WHAT: Input term nodes visited by the signature scan.
    /// CEP:WHY: The scan's measured work (CEP&CC 23).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::scan_budget_rejects_runaway_input.
    /// CEP:SECURITY: none.
    pub nodes_visited: u32,
}

// CEP:WHAT: Validates a declaration against the frozen symbol table.
// CEP:WHY: Spec 15 section 2: every shape claim is checked mechanically (kind and arity per field) before any scheme exists; a malformed declaration adds nothing.
// CEP:STATUS: complete
// CEP:FAILURE: ZeroNotConstant, SuccNotUnary, SkolemNotConstant, WellFoundedNotBinary.
// CEP:ASSUMES: the symbol table is the problem's frozen table.
// CEP:COST: O(1) (four info lookups).
// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
// CEP:SECURITY: the validation is the scheme-soundness trust boundary.
pub fn validate_declaration(
    symbols: &SymbolTable<'_>,
    declaration: &InductionDeclaration,
) -> Result<(), InductionError> {
    if !is_constant_function(symbols, declaration.zero) {
        return Err(InductionError::ZeroNotConstant);
    }
    if !is_unary_function(symbols, declaration.succ) {
        return Err(InductionError::SuccNotUnary);
    }
    if !is_constant_function(symbols, declaration.skolem) {
        return Err(InductionError::SkolemNotConstant);
    }
    if let Some(order) = declaration.well_founded {
        let is_binary = symbols
            .info(order)
            .map(|info| info.kind == SymbolKind::Predicate && info.arity == kWellFoundedArity)
            .unwrap_or(false);
        if !is_binary {
            return Err(InductionError::WellFoundedNotBinary);
        }
    }
    Ok(())
}

// CEP:WHAT: True when the symbol is a 0-ary function (a constant).
// CEP:WHY: The shared shape check of the zero constructor and the skolem.
// CEP:STATUS: complete
// CEP:FAILURE: false on unknown symbols.
// CEP:ASSUMES: none.
// CEP:COST: one table lookup.
// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
// CEP:SECURITY: none.
fn is_constant_function(symbols: &SymbolTable<'_>, symbol: u32) -> bool {
    symbols
        .info(symbol)
        .map(|info| info.kind == SymbolKind::Function && info.arity == 0)
        .unwrap_or(false)
}

// CEP:WHAT: True when the symbol is a unary function.
// CEP:WHY: The step-constructor shape check.
// CEP:STATUS: complete
// CEP:FAILURE: false on unknown symbols.
// CEP:ASSUMES: none.
// CEP:COST: one table lookup.
// CEP:EVIDENCE: unit/hot/induction_test.rs::declaration_validation_rejects_bad_shapes.
// CEP:SECURITY: none.
fn is_unary_function(symbols: &SymbolTable<'_>, symbol: u32) -> bool {
    symbols
        .info(symbol)
        .map(|info| info.kind == SymbolKind::Function && info.arity == 1)
        .unwrap_or(false)
}

// CEP:WHAT: The scan's mutable collector: the deduplicated unary-predicate list, the skolem-sighting flag, the node counter, and the overflow counts.
// CEP:WHY: One fixed state record keeps the recursive walk allocation-free (no_std) with every bound's accounting in one place (Law 4).
// CEP:STATUS: complete
// CEP:FAILURE: walk functions turn budget and depth overruns into InductionError values.
// CEP:ASSUMES: one collector per scan.
// CEP:COST: kInductionMaxPredicates x 4 bytes plus counters.
// CEP:EVIDENCE: unit/hot/induction_test.rs::{skolem_occurrence_rejected, scan_budget_rejects_runaway_input}.
// CEP:SECURITY: bounded collection.
struct SignatureScan {
    /// CEP:WHAT: Deduplicated unary predicate symbol ids (occurrence order).
    /// CEP:WHY: The scheme domain; sorted by symbol id after the scan.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: fixed array.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set.
    /// CEP:SECURITY: none.
    unary: [u32; kInductionMaxPredicates],
    /// CEP:WHAT: Fill level of the unary list.
    /// CEP:WHY: Named bounds need named fill levels (CEP&CC 11.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: <= kInductionMaxPredicates.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::attempts_budget_enforced.
    /// CEP:SECURITY: none.
    unary_count: usize,
    /// CEP:WHAT: Unary predicates seen but not collected (list full).
    /// CEP:WHY: Law 4: the collection bound's visible accounting.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::attempts_budget_enforced.
    /// CEP:SECURITY: none.
    unary_overflow: u32,
    /// CEP:WHAT: Whether the declaration's skolem was sighted in any input term.
    /// CEP:WHY: The freshness proof's verdict.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::skolem_occurrence_rejected.
    /// CEP:SECURITY: none.
    skolem_seen: bool,
    /// CEP:WHAT: Term nodes visited.
    /// CEP:WHY: The node-budget counter (CEP&CC 22.10) and the measured work (CEP&CC 23).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/induction_test.rs::scan_budget_rejects_runaway_input.
    /// CEP:SECURITY: none.
    nodes: u32,
}

impl SignatureScan {
    // CEP:WHAT: Constructs an empty collector.
    // CEP:WHY: One constructor fixes the initial state (no mem::zeroed tricks).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: O(1).
    // CEP:EVIDENCE: unit/hot/induction_test.rs::schemes_enter_passive_set.
    // CEP:SECURITY: none.
    fn new() -> SignatureScan {
        SignatureScan {
            unary: [0; kInductionMaxPredicates],
            unary_count: 0,
            unary_overflow: 0,
            skolem_seen: false,
            nodes: 0,
        }
    }
}

// CEP:WHAT: Walks one term collecting symbols into the scan state.
// CEP:WHY: The recursive depth-bounded discipline of the hot crate (demodulation's replace_at pattern): Variables and Sorts are leaves; every other node counts against the node budget, contributes its symbol to the skolem check, contributes unary predicate heads to the deduplicated domain list, and recurses into children in order.
// CEP:STATUS: complete
// CEP:FAILURE: ScanBudgetExceeded, TermWalkOverflow, UnreadableRecord.
// CEP:ASSUMES: the term was interned by the same store.
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: unit/hot/induction_test.rs::{skolem_occurrence_rejected, scan_budget_rejects_runaway_input}.
// CEP:SECURITY: node-budgeted, depth-bounded.
fn walk_term(
    terms: &TermStore<'_>,
    ptr: TermPtr,
    skolem: u32,
    depth: u32,
    budget: u32,
    scan: &mut SignatureScan,
) -> Result<(), InductionError> {
    if depth > kMaxTermDepth as u32 {
        return Err(InductionError::TermWalkOverflow);
    }
    scan.nodes += 1;
    if scan.nodes > budget {
        return Err(InductionError::ScanBudgetExceeded);
    }
    let view = terms
        .term(ptr)
        .map_err(|_| InductionError::UnreadableRecord)?;
    match view.tag() {
        TermTag::Variable | TermTag::Sort => Ok(()),
        tag => {
            let symbol = view.symbol();
            if symbol == skolem {
                scan.skolem_seen = true;
            }
            if tag == TermTag::Predicate && view.child_count() == 1 {
                let mut present = false;
                for index in 0..scan.unary_count {
                    if scan.unary[index] == symbol {
                        present = true;
                        break;
                    }
                }
                if present {
                    // Already collected.
                } else if scan.unary_count < kInductionMaxPredicates {
                    scan.unary[scan.unary_count] = symbol;
                    scan.unary_count += 1;
                } else {
                    scan.unary_overflow += 1;
                }
            }
            for child in view.children() {
                walk_term(terms, child, skolem, depth + 1, budget, scan)?;
            }
            Ok(())
        }
    }
}

// CEP:WHAT: Scans the space's input clauses, proving skolem freshness and collecting the unary-predicate domain.
// CEP:WHY: Spec 15 section 2: one pass over the input clauses in id order (deterministic); the collector is a fixed-size record; the returned slice is sorted by symbol id so the scheme enumeration order is content-independent.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InductionError from the walk; Search on unreadable clauses.
// CEP:ASSUMES: input clauses are the contiguous id range [kFirstClauseId, kFirstClauseId + input_count).
// CEP:COST: O(input term nodes) bounded by kInductionScanNodeBudget.
// CEP:EVIDENCE: unit/hot/induction_test.rs::{skolem_occurrence_rejected, scan_budget_rejects_runaway_input}.
// CEP:SECURITY: node-budgeted walk (22.10).
fn scan_input_signature(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    skolem: u32,
    budget: u32,
) -> Result<SignatureScan, InductionError> {
    let mut scan = SignatureScan::new();
    let input_count = space.input_count() as u64;
    for index in 0..input_count {
        let id = kFirstClauseId + index;
        let record = space
            .store
            .clause_by_id(crate::ir::clause::ClauseId(id))
            .map_err(|_| InductionError::UnreadableRecord)?;
        for literal_index in 0..record.literal_count {
            let literal = space
                .store
                .literal(record, literal_index)
                .map_err(|_| InductionError::UnreadableRecord)?;
            walk_term(context.terms, literal.atom(), skolem, 0, budget, &mut scan)?;
        }
    }
    scan.unary[..scan.unary_count].sort_unstable();
    Ok(scan)
}

// CEP:WHAT: Adds the bounded induction schemes for every collected unary predicate.
// CEP:WHY: The Phase 4 (revised) integration point: validate, scan (proving skolem freshness and collecting the predicate domain), then per predicate (symbol-id order) add the two-clause structural scheme and, when a well-order is declared, the two-clause strong scheme; the attempts budget cuts the enumeration deterministically (the domain is sorted, the cut is a prefix), skipped predicates are counted, and every clause enters through add_theory_clause so staging, flags, weights, ages, and passive order follow the production discipline.
// CEP:STATUS: complete
// CEP:FAILURE: propagates InductionError; no scheme is added after a rejection.
// CEP:ASSUMES: input clauses added; max_attempts and scan_node_budget are the caller's budgets (production: kMaxInductionAttempts and kInductionScanNodeBudget; CEP&CC 34.3 injectable).
// CEP:COST: see file header; measured in bench CEP-BENCH-0036.
// CEP:EVIDENCE: unit/hot/induction_test.rs; property/induction_property_test.rs::{schemes_match_hand_clausification, attempts_bound_respected}.
// CEP:SECURITY: budgets enforced (attempts, scan nodes, collection); store bounds enforced.
pub fn add_induction_schemes(
    space: &SearchSpace<'_>,
    context: &InferenceContext<'_>,
    options: &SearchOptions,
    declaration: &InductionDeclaration,
    max_attempts: u32,
    scan_node_budget: u32,
) -> Result<InductionStats, InductionError> {
    validate_declaration(context.symbols, declaration)?;
    let scan = scan_input_signature(space, context, declaration.skolem, scan_node_budget)?;
    if scan.skolem_seen {
        return Err(InductionError::SkolemOccursInInput);
    }
    let mut stats = InductionStats {
        unary_predicates: (scan.unary_count as u32).saturating_add(scan.unary_overflow),
        nodes_visited: scan.nodes,
        ..InductionStats::default()
    };
    let mut attempts = 0u32;
    let mut covered = 0u32;
    for predicate_index in 0..scan.unary_count {
        let predicate = scan.unary[predicate_index];
        if attempts + scheme::kStructuralClauseCount > max_attempts {
            break;
        }
        for clause_index in 0..scheme::kStructuralClauseCount {
            let (literals, count) = scheme::structural_scheme_literals(
                context.terms,
                context.symbols,
                predicate,
                declaration,
                clause_index,
            )?;
            space
                .add_theory_clause(
                    context,
                    options,
                    &literals[..count],
                    InferenceRule::StructuralInduction,
                )
                .map_err(InductionError::Search)?;
            stats.structural_schemes += 1;
            attempts += 1;
        }
        // The predicate is covered by its structural pair before the strong
        // pair is attempted; a wf-budget shortfall must not recount the
        // predicate as fully skipped (Task 26 sev-3(1) repair).
        covered += 1;
        if let Some(order) = declaration.well_founded {
            if attempts + scheme::kWellFoundedClauseCount > max_attempts {
                // The structural pair consumed the remaining budget; the strong
                // pair for this predicate (and everything after) is skipped;
                // the predicate itself stays covered (Law 4 accounting).
                continue;
            }
            for clause_index in 0..scheme::kWellFoundedClauseCount {
                let (literals, count) = scheme::well_founded_scheme_literals(
                    context.terms,
                    context.symbols,
                    predicate,
                    order,
                    declaration,
                    clause_index,
                )?;
                space
                    .add_theory_clause(
                        context,
                        options,
                        &literals[..count],
                        InferenceRule::WellFoundedInduction,
                    )
                    .map_err(InductionError::Search)?;
                stats.well_founded_schemes += 1;
                attempts += 1;
            }
        }
    }
    stats.predicates_skipped = stats.unary_predicates.saturating_sub(covered);
    Ok(stats)
}
