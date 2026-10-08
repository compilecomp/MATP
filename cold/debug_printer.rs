// CEP:FILE: cold/debug_printer.rs
// CEP:WHAT: Deterministic internal debug printer for terms and clauses: s-expression term syntax and disjunctive clause syntax written into a caller-provided String.
// CEP:WHY: Design 5.7 requires the IR to be printable; a stable, deterministic textual form is also the substrate for golden tests (CEP&CC 32.8) and for TSTP output in Phase 3.
// CEP:CLASS: CEP-1
// CEP:STATUS: complete
// CEP:FAILURE: Returns PrintError::UnreadableTerm or PrintError::UnreadableClause when a handle cannot be read; never panics.
// CEP:ASSUMES: Symbol names come from the CEP-1 builder; term depth is bounded by kMaxTermDepth so recursion is bounded.
// CEP:COST: O(term size) per term, O(clause size) per clause.
// CEP:EVIDENCE: unit/cold/debug_printer_test.rs; golden test tests/golden/ir_debug_print_test.rs.
// CEP:SECURITY: no untrusted input beyond already-validated IR handles.
// CEP:HPC-DETERMINISM: deterministic output for identical IR; traversal is child-index order, literals in stored order.

use crate::symbol_table_builder::SymbolTableBuilder;
use mapt_hot::ir::clause::ClauseStore;
use mapt_hot::ir::symbol_table::SymbolTable;
use mapt_hot::ir::term::{TermStore, TermTag};

/// CEP:WHAT: Error cases of the debug printer.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/cold/debug_printer_test.rs::unreadable_handles_rejected.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrintError {
    /// CEP:WHAT: A term handle could not be read.
    UnreadableTerm,
    /// CEP:WHAT: A clause reference could not be read.
    UnreadableClause,
}

// CEP:WHAT: Prints one term in s-expression syntax into out.
// CEP:WHY: The internal debug format (design 5.7 printable requirement); variables print as V<n>, functions as (name args...), predicates the same, equality as (= l r), application as (@ f x), sorts as (sort id).
// CEP:STATUS: complete
// CEP:FAILURE: Returns UnreadableTerm when the term or a descendant cannot be read.
// CEP:ASSUMES: names is the builder that produced the symbols.
// CEP:COST: O(term size).
// CEP:EVIDENCE: unit/cold/debug_printer_test.rs::term_syntax; tests/golden/ir_debug_print_test.rs.
// CEP:SECURITY: none.
pub fn print_term(
    terms: &TermStore,
    names: &SymbolTableBuilder,
    handle: mapt_hot::ir::term::TermPtr,
    out: &mut String,
) -> Result<(), PrintError> {
    let view = terms.term(handle).map_err(|_| PrintError::UnreadableTerm)?;
    match view.tag() {
        TermTag::Variable => {
            out.push('V');
            out.push_str(&view.symbol().to_string());
        }
        TermTag::Sort => {
            out.push_str("(sort ");
            out.push_str(&view.symbol().to_string());
            out.push(')');
        }
        TermTag::Equality => {
            let left = view.child(0).map_err(|_| PrintError::UnreadableTerm)?;
            let right = view.child(1).map_err(|_| PrintError::UnreadableTerm)?;
            out.push_str("(= ");
            print_term(terms, names, left, out)?;
            out.push(' ');
            print_term(terms, names, right, out)?;
            out.push(')');
        }
        TermTag::Application => {
            let func = view.child(0).map_err(|_| PrintError::UnreadableTerm)?;
            let arg = view.child(1).map_err(|_| PrintError::UnreadableTerm)?;
            out.push_str("(@ ");
            print_term(terms, names, func, out)?;
            out.push(' ');
            print_term(terms, names, arg, out)?;
            out.push(')');
        }
        TermTag::Lambda => {
            out.push_str("(lam ");
            out.push_str(&view.symbol().to_string());
            out.push(')');
        }
        TermTag::Function | TermTag::Predicate => {
            let symbol = view.symbol();
            let name = names.name_of(symbol).unwrap_or(kUnknownSymbolName);
            out.push('(');
            out.push_str(name);
            for child in view.children() {
                out.push(' ');
                print_term(terms, names, child, out)?;
            }
            out.push(')');
        }
    }
    Ok(())
}

/// CEP:WHAT: Placeholder name for symbols missing from the builder.
/// CEP:WHY: The printer must stay total; a named sentinel documents the fallback instead of a bare string literal (CEP&CC 11.3).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: builder and store are consistent in practice; the sentinel marks inconsistency loudly.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/cold/debug_printer_test.rs::missing_name_falls_back.
/// CEP:SECURITY: none.
pub const kUnknownSymbolName: &str = "<?symbol?>";

// CEP:WHAT: Prints one clause in disjunctive syntax into out.
// CEP:WHY: Clause printing closes the printable-IR contract; literals print in stored (canonical) order, negative literals with a tilde prefix.
// CEP:STATUS: complete
// CEP:FAILURE: Returns UnreadableClause on unreadable headers and UnreadableTerm on unreadable atoms.
// CEP:ASSUMES: the clause was built by the given stores.
// CEP:COST: O(clause size).
// CEP:EVIDENCE: unit/cold/debug_printer_test.rs::clause_syntax; tests/golden/ir_debug_print_test.rs.
// CEP:SECURITY: none.
pub fn print_clause(
    terms: &TermStore,
    names: &SymbolTableBuilder,
    clauses: &ClauseStore,
    handle: mapt_hot::ir::clause::ClausePtr,
    out: &mut String,
) -> Result<(), PrintError> {
    let clause = clauses
        .clause(handle)
        .map_err(|_| PrintError::UnreadableClause)?;
    out.push('c');
    out.push_str(&clause.id.0.to_string());
    out.push_str(": ");
    if clause.literal_count == 0 {
        out.push_str(kFalseClauseMarker);
        return Ok(());
    }
    for index in 0..clause.literal_count {
        if index > 0 {
            out.push_str(" | ");
        }
        let literal = clauses
            .literal(clause, index)
            .map_err(|_| PrintError::UnreadableClause)?;
        if !literal.is_positive() {
            out.push('~');
        }
        print_term(terms, names, literal.atom(), out)?;
    }
    Ok(())
}

/// CEP:WHAT: Marker printed for the empty clause.
/// CEP:WHY: The empty clause has no literals; a named sentinel keeps golden output stable and self-describing.
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: none.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: tests/golden/ir_debug_print_test.rs.
/// CEP:SECURITY: none.
pub const kFalseClauseMarker: &str = "<false>";

// CEP:WHAT: Reports whether the printer would query symbol weights (compatibility shim for future sort-aware printing).
// CEP:WHY: Keeps the printer independent of the frozen table so printing works on partially built states.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: unit/cold/debug_printer_test.rs.
// CEP:SECURITY: none.
pub fn printer_uses_symbol_table(_symbols: &SymbolTable) -> bool {
    false
}
