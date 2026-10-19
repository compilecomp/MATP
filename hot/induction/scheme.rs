// CEP:FILE: hot/induction/scheme.rs
// CEP:WHAT: The clausal induction-scheme builders: for one unary predicate over a declared constructor family, the two-clause structural scheme and the two-clause well-founded (strong) scheme, exactly as derived in Formal Spec 15 sections 3-4.
// CEP:WHY: The builders are the soundness-critical core of automated induction: each emitted clause is a step of the hand clausification of the induction-axiom instance, re-derived here so the derivation is checkable line by line - structural scheme for predicate p with base z, step s, and witness a: IA(p) = (p(z) AND ALL y.(p(y) -> p(s(y)))) -> ALL x.p(x) clausifies to {~p(z), p(a), p(X)} and {~p(z), ~p(s(a)), p(X)} (the existential witness of the negated antecedent becomes the skolem a); strong scheme with well-order lt and witness c: WFI(p) = (ALL x.((ALL y.(~lt(y,x) OR p(y))) -> p(x))) -> ALL x.p(x) clausifies to {~lt(Y,c), p(Y), p(X)} and {~p(c), p(X)}; unit/hot/induction_test.rs pins both shapes against this derivation and property/induction_property_test.rs re-verifies them for random predicates; the builders intern through the production TermStore (hash-consed, deterministic) and never allocate.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction when any intern fails (arena or table exhaustion); every failure is loud, no partial clause escapes.
// CEP:ASSUMES: the declaration was validated (arities and kinds) and the skolem is fresh; the predicate and order symbols exist in the frozen table.
// CEP:COST: five to seven term interns per scheme (three atoms plus constructor terms, most shared through hash-consing); measured in bench CEP-BENCH-0036.
// CEP:EVIDENCE: unit/hot/induction_test.rs::{structural_scheme_clauses_match_clausification, well_founded_scheme_clauses_match_clausification}; property/induction_property_test.rs::schemes_match_hand_clausification.
// CEP:SECURITY: all interns are bounds-checked (table capacity, depth, weight).
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic: fixed variable numbering (structural X = var 0; strong Y = var 0, X = var 1), fixed clause order, hash-consed interning.
// CEP:HPC-PASS-LEGALITY: Formal Spec 15 sections 3-4 fix the derivations and the variable numbering; the section 3 theorem (initial-algebra validity) and section 3.2 theorem (well-foundedness transfer) are the legality obligations, with the correspondence property test as the executable witness.

use crate::induction::{InductionDeclaration, InductionError};
use crate::ir::literal::Literal;
use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::{TermPtr, TermStore};

/// CEP:WHAT: Structural scheme clause count per predicate (the two clausification steps).
/// CEP:WHY: Names the loop bound of the installer and the granularity of the attempts budget (CEP&CC 11.3); equals config kInductionSchemeClauses by construction (asserted by use in unit tests).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: Spec 15 section 3 fixes the two-clause shape.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
/// CEP:SECURITY: none.
pub const kStructuralClauseCount: u32 = 2;

/// CEP:WHAT: Well-founded scheme clause count per predicate (the two clausification steps).
/// CEP:WHY: Names the loop bound of the installer's strong branch (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: Spec 15 section 4 fixes the two-clause shape.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::well_founded_scheme_clauses_match_clausification.
/// CEP:SECURITY: none.
pub const kWellFoundedClauseCount: u32 = 2;

// CEP:WHAT: Literal count of the well-founded scheme's second clause {~p(c), p(X)}.
// CEP:WHY: The literal count is a named value at the construction site (CEP&CC 11.3) instead of a bare 2.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: Spec 15 section 4 fixes the two-literal shape.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/induction_test.rs::well_founded_scheme_clauses_match_clausification.
// CEP:SECURITY: none.
pub const kWellFoundedSecondClauseLiterals: usize = 2;

/// CEP:WHAT: Maximum literals of any scheme clause (the structural and strong clauses carry at most three).
/// CEP:WHY: The builders return fixed three-slot arrays with a valid count; the constant names the array bound (CEP&CC 11.3).
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: Spec 15 sections 3-4 fix the literal counts.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/induction_test.rs::{structural_scheme_clauses_match_clausification, well_founded_scheme_clauses_match_clausification}.
/// CEP:SECURITY: none.
pub const kSchemeLiterals: usize = 3;

// CEP:WHAT: Builds one clause of the structural induction scheme for one unary predicate.
// CEP:WHY: Spec 15 section 3: clause 0 is {~p(z), p(a), p(X)} (the base disjunct with the witness's goal side), clause 1 is {~p(z), ~p(s(a)), p(X)} (the step disjunct with the negated successor goal); both share the witness a (the declaration's skolem) and the universally quantified conclusion variable X (var 0); interning is hash-consed so p(z) is shared between the two clauses.
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: clause_index < kStructuralClauseCount; the declaration is validated.
// CEP:COST: four interns (p(z), p(a), p(s(a)), p(X); z/a terms shared or trivial) per clause.
// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification; property/induction_property_test.rs::schemes_match_hand_clausification.
// CEP:SECURITY: bounds-checked interns.
pub fn structural_scheme_literals(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    predicate: u32,
    declaration: &InductionDeclaration,
    clause_index: u32,
) -> Result<([Literal; kSchemeLiterals], usize), InductionError> {
    let zero = intern_constant(terms, symbols, declaration.zero)?;
    let witness = intern_constant(terms, symbols, declaration.skolem)?;
    let succ_witness = intern_unary(terms, symbols, declaration.succ, witness)?;
    let var_x = intern_var(terms, 0)?;
    let p_zero = intern_unary_pred(terms, symbols, predicate, zero)?;
    let p_witness = intern_unary_pred(terms, symbols, predicate, witness)?;
    let p_succ_witness = intern_unary_pred(terms, symbols, predicate, succ_witness)?;
    let p_var = intern_unary_pred(terms, symbols, predicate, var_x)?;
    let literals = if clause_index == 0 {
        [
            Literal::new(p_zero, false),
            Literal::new(p_witness, true),
            Literal::new(p_var, true),
        ]
    } else {
        [
            Literal::new(p_zero, false),
            Literal::new(p_succ_witness, false),
            Literal::new(p_var, true),
        ]
    };
    Ok((literals, kSchemeLiterals))
}

// CEP:WHAT: Builds one clause of the well-founded (strong) induction scheme for one unary predicate and declared well-order.
// CEP:WHY: Spec 15 section 4: clause 0 is {~lt(Y,c), p(Y), p(X)} (the minimal-counterexample side: every lt-smaller element satisfies p), clause 1 is {~p(c), p(X)} (the counterexample side); the witness c is the declaration's skolem; Y is var 0 and X is var 1 in clause 0, X is var 0 in clause 1 (variable numbering fixed by the spec).
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: clause_index < kWellFoundedClauseCount; the declaration is validated.
// CEP:COST: three to four interns per clause.
// CEP:EVIDENCE: unit/hot/induction_test.rs::well_founded_scheme_clauses_match_clausification; property/induction_property_test.rs::schemes_match_hand_clausification.
// CEP:SECURITY: bounds-checked interns.
pub fn well_founded_scheme_literals(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    predicate: u32,
    order: u32,
    declaration: &InductionDeclaration,
    clause_index: u32,
) -> Result<([Literal; kSchemeLiterals], usize), InductionError> {
    let witness = intern_constant(terms, symbols, declaration.skolem)?;
    if clause_index == 0 {
        let var_y = intern_var(terms, 0)?;
        let var_x = intern_var(terms, 1)?;
        let lt_y_c = intern_binary_pred(terms, symbols, order, var_y, witness)?;
        let p_y = intern_unary_pred(terms, symbols, predicate, var_y)?;
        let p_x = intern_unary_pred(terms, symbols, predicate, var_x)?;
        Ok((
            [
                Literal::new(lt_y_c, false),
                Literal::new(p_y, true),
                Literal::new(p_x, true),
            ],
            kSchemeLiterals,
        ))
    } else {
        let var_x = intern_var(terms, 0)?;
        let p_c = intern_unary_pred(terms, symbols, predicate, witness)?;
        let p_x = intern_unary_pred(terms, symbols, predicate, var_x)?;
        Ok((
            [
                Literal::new(p_c, false),
                Literal::new(p_x, true),
                Literal::new(TermPtr::invalid(), true),
            ],
            kWellFoundedSecondClauseLiterals,
        ))
    }
}

// CEP:WHAT: Interns a 0-ary function application (a constant term).
// CEP:WHY: The zero constructor and the witness share one reader; failures map to the module vocabulary at one point.
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: the symbol is a validated constant.
// CEP:COST: one intern (hash-consed hit for repeats).
// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
// CEP:SECURITY: bounds-checked.
fn intern_constant(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    symbol: u32,
) -> Result<TermPtr, InductionError> {
    terms
        .intern_fun(symbols, symbol, &[])
        .map_err(|_| InductionError::TermConstruction)
}

// CEP:WHAT: Interns a unary function application.
// CEP:WHY: The step constructor applied to the witness (s(a)).
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: the symbol is a validated unary function.
// CEP:COST: one intern.
// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
// CEP:SECURITY: bounds-checked.
fn intern_unary(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    symbol: u32,
    child: TermPtr,
) -> Result<TermPtr, InductionError> {
    terms
        .intern_fun(symbols, symbol, &[child])
        .map_err(|_| InductionError::TermConstruction)
}

// CEP:WHAT: Interns a variable term by dense index.
// CEP:WHY: The schemes' universally quantified X and Y; dense numbering is the clause discipline (design 5.5).
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: the index is within the store's variable bound.
// CEP:COST: one intern (hash-consed hit for repeats).
// CEP:EVIDENCE: unit/hot/induction_test.rs::structural_scheme_clauses_match_clausification.
// CEP:SECURITY: bounds-checked.
fn intern_var(terms: &TermStore<'_>, index: u32) -> Result<TermPtr, InductionError> {
    terms
        .intern_var(index)
        .map_err(|_| InductionError::TermConstruction)
}

// CEP:WHAT: Interns a unary predicate atom p(child).
// CEP:WHY: Every goal-side atom of both schemes.
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: the predicate is a validated unary predicate.
// CEP:COST: one intern.
// CEP:EVIDENCE: unit/hot/induction_test.rs::{structural_scheme_clauses_match_clausification, well_founded_scheme_clauses_match_clausification}.
// CEP:SECURITY: bounds-checked.
fn intern_unary_pred(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    predicate: u32,
    child: TermPtr,
) -> Result<TermPtr, InductionError> {
    terms
        .intern_pred(symbols, predicate, &[child])
        .map_err(|_| InductionError::TermConstruction)
}

// CEP:WHAT: Interns a binary predicate atom lt(left, right).
// CEP:WHY: The strong scheme's minimality side lt(Y, c).
// CEP:STATUS: complete
// CEP:FAILURE: TermConstruction on intern failure.
// CEP:ASSUMES: the order is a validated binary predicate.
// CEP:COST: one intern.
// CEP:EVIDENCE: unit/hot/induction_test.rs::well_founded_scheme_clauses_match_clausification.
// CEP:SECURITY: bounds-checked.
fn intern_binary_pred(
    terms: &TermStore<'_>,
    symbols: &SymbolTable<'_>,
    order: u32,
    left: TermPtr,
    right: TermPtr,
) -> Result<TermPtr, InductionError> {
    terms
        .intern_pred(symbols, order, &[left, right])
        .map_err(|_| InductionError::TermConstruction)
}
