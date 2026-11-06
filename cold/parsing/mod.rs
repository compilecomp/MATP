// CEP:FILE: cold/parsing/mod.rs
/// CEP:WHAT: The input-parsing module (design 6): the shared parse-error and result vocabulary, the untyped FOF/CNF AST with its name table, and the bound-enforcement helpers; the format front ends are the DIMACS CNF parser (dimacs_parser.rs) and the TPTP parser (tptp_parser.rs).
/// CEP:WHY: Design 6.2 fixes one five-stage parser shape (lex, recursive descent, validate, IR construction, return) and design 6.3 the bound set (kMaxInputBytes, kMaxFormulaNodes, kMaxTermDepth, kMaxSymbolCount, kMaxQuantifierDepth, kMaxIncludeDepth, kMaxIncludeCount, plus kMaxParseDepth from 6.2); concentrating the shared vocabulary here keeps every format front end on the same error and bound contract (ticket CEP-1006); cold is the legal layer for allocation, std, and I/O (design 4.1).
/// CEP:CLASS: CEP-1
/// CEP:STATUS: complete
/// CEP:FAILURE: front ends return ParseError on every rejected input; no panic, no exception (design 6.3).
/// CEP:ASSUMES: the caller supplies a writable arena of sufficient capacity; input bytes are untrusted (CEP&CC 22.5).
/// CEP:COST: linear in input size under the bounds; allocations are cold-path legal.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs; unit/cold/tptp_parser_test.rs.
/// CEP:SECURITY: all input is untrusted: byte size, nesting depth, node count, symbol count, quantifier depth, and include fan-out are each enforced against a named config bound before any unbounded growth (design 6.3).
use crate::symbol_table_builder::{BuilderError, SymbolTableBuilder};
use mapt_hot::ir::clause::{ClauseError, ClausePtr, ClauseStore};
use mapt_hot::ir::symbol_table::SymbolTable;
use mapt_hot::ir::term::{TermError, TermStore};
use std::collections::HashMap;
use std::string::String;
use std::vec::Vec;

/// The DIMACS CNF front end: the header, comments, and 0-terminated clause lines into the unified IR.
pub mod dimacs_parser;
/// The TPTP front end: CNF and FOF directives with includes, roles, binding, and the design 6.3 bounds.
pub mod tptp_parser;

pub use dimacs_parser::parse_dimacs;
pub use tptp_parser::{parse_tptp, parse_tptp_with_limits, ParserLimits};

/// CEP:WHAT: The parse-error vocabulary: one variant per rejected-input cause, each mapping to a design 6.3 bound or a concrete syntax/semantics defect.
/// CEP:WHY: Design 6.3 requires a ParseError enum with no panics and no exceptions; exact variants (not a collapsed message) keep the driver able to distinguish resource exhaustion from malformed input (Law 6: honest failure kinds).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: none.
/// CEP:COST: enum value; the String-free variants avoid allocation on the error path.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::{rejects_variable_beyond_header, rejects_missing_header}; unit/cold/tptp_parser_test.rs::{syntax_error_reports_line, rejects_unknown_role, rejects_arity_change, rejects_free_variable, rejects_quantifier_depth, rejects_parse_depth, rejects_node_budget, include_depth_is_bounded, include_count_is_bounded}.
/// CEP:SECURITY: error construction never echoes input bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseError {
    /// The input exceeds kMaxInputBytes.
    TooLarge,
    /// The recursive descent exceeded kMaxParseDepth (design 6.2).
    TooDeep,
    /// Quantifier nesting exceeded kMaxQuantifierDepth.
    QuantifierTooDeep,
    /// The AST node budget kMaxFormulaNodes was exhausted.
    TooManyNodes,
    /// The symbol table would exceed kMaxSymbolCount.
    TooManySymbols,
    /// TPTP include nesting exceeded kMaxIncludeDepth.
    IncludeTooDeep,
    /// TPTP include files resolved per parse exceeded kMaxIncludeCount.
    TooManyIncludes,
    /// A TPTP include directive named a file that cannot be read.
    IncludeUnreadable,
    /// A TPTP input formula carried a role outside the accepted set.
    UnknownRole,
    /// A TPTP name was used with a different arity or a different symbol kind than its first declaration.
    ArityMismatch,
    /// An FOF formula referenced a variable that no enclosing quantifier binds.
    FreeVariable,
    /// A DIMACS clause used a variable index beyond the declared header count.
    VariableBeyondHeader,
    /// A DIMACS input carried clauses before the "p cnf" header, a second header, or a malformed header.
    MissingHeader,
    /// Byte-level syntax error with the 1-based line of the offending token.
    Syntax {
        /// The 1-based line of the offending token.
        line: u32,
        /// The 1-based byte column of the offending token.
        column: u32,
    },
    /// IR construction failed in the term store (hash table, arena, or bound exhaustion with the exact TermError kind).
    IrTerm(TermError),
    /// IR construction failed in the clause store with the exact ClauseError kind.
    IrClause(ClauseError),
    /// IR construction failed in the symbol-table builder with the exact BuilderError kind.
    IrSymbol(BuilderError),
}

impl From<TermError> for ParseError {
    /// CEP:WHAT: Translates a term-store failure into ParseError::IrTerm with the exact kind.
    /// CEP:WHY: Law 6: capacity and bound kinds stay inspectable through the translation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn from(error: TermError) -> Self {
        ParseError::IrTerm(error)
    }
}

impl From<ClauseError> for ParseError {
    /// CEP:WHAT: Translates a clause-store failure into ParseError::IrClause with the exact kind.
    /// CEP:WHY: Law 6: capacity and bound kinds stay inspectable through the translation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs.
    /// CEP:SECURITY: none.
    fn from(error: ClauseError) -> Self {
        ParseError::IrClause(error)
    }
}

impl From<BuilderError> for ParseError {
    /// CEP:WHAT: Translates a symbol-table-builder failure into ParseError::IrSymbol with the exact kind.
    /// CEP:WHY: Law 6: DuplicateName, NameTooLong, and capacity kinds stay inspectable through the translation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: constant.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs.
    /// CEP:SECURITY: none.
    fn from(error: BuilderError) -> Self {
        ParseError::IrSymbol(error)
    }
}

/// CEP:WHAT: The TPTP input-formula roles accepted by the parsers, in the TPTP role vocabulary.
/// CEP:WHY: The role decides the driver's handling (conjecture negation is design 7.2 stage 1); the parser validates and records it, the driver acts on it.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a vocabulary type.
/// CEP:ASSUMES: closed set.
/// CEP:COST: enum value.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, fof_formulas_reach_the_ast}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TptpRole {
    /// The `axiom` role: accepted as true, no special handling.
    Axiom,
    /// The `hypothesis` role: accepted as true for this problem.
    Hypothesis,
    /// The `definition` role: a symbol definition.
    Definition,
    /// The `lemma` role: an auxiliary proven statement.
    Lemma,
    /// The `negated_conjecture` role: the already-negated goal.
    NegatedConjecture,
    /// The `conjecture` role: the goal to prove (negation is the driver's stage 1).
    Conjecture,
    /// The `plain` role: no special semantics.
    Plain,
    /// The `type` role: a type declaration (recorded; sorts are untyped-TPTP placeholders in this delivery).
    Type,
    /// The `fi_domain` role: finite interpretation domain descriptions.
    FiDomain,
}

impl TptpRole {
    /// CEP:WHAT: Maps a TPTP role token to the vocabulary; the token must match the TPTP lowercase spelling exactly.
    /// CEP:WHY: The role grammar is fixed by the TPTP language; unknown tokens are rejected (ParseError::UnknownRole) rather than silently downgraded to plain.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns None for tokens outside the accepted set.
    /// CEP:ASSUMES: none.
    /// CEP:COST: linear scan over a short match.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::rejects_unknown_role.
    /// CEP:SECURITY: none.
    pub fn from_token(token: &str) -> Option<TptpRole> {
        match token {
            "axiom" => Some(TptpRole::Axiom),
            "hypothesis" => Some(TptpRole::Hypothesis),
            "definition" => Some(TptpRole::Definition),
            "lemma" => Some(TptpRole::Lemma),
            "negated_conjecture" => Some(TptpRole::NegatedConjecture),
            "conjecture" => Some(TptpRole::Conjecture),
            "plain" => Some(TptpRole::Plain),
            "type" => Some(TptpRole::Type),
            "fi_domain" => Some(TptpRole::FiDomain),
            _ => None,
        }
    }
}

/// CEP:WHAT: A first-order term of the parsed AST: a variable by name id, or a function application by symbol id with interned argument terms.
/// CEP:WHY: Design 6.2 stage 2-3: the AST is the validated intermediate form between parsing and IR interning; variables are name-table references so the binder check and the future clausifier (design 7) can reason about names.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data type.
/// CEP:ASSUMES: variable ids and symbol ids were produced by the same parse's NameTable and SymbolTableBuilder.
/// CEP:COST: enum with boxed children.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{cnf_clauses_reach_the_ir, fof_formulas_reach_the_ast}.
/// CEP:SECURITY: node count bounded by kMaxFormulaNodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FofTerm {
    /// A variable by name-table id (TPTP: an uppercase- or underscore-initial name).
    Variable(u32),
    /// A function application by symbol-table id with the argument terms.
    Application(u32, Vec<FofTerm>),
}

/// CEP:WHAT: A first-order formula of the parsed AST: atoms, equality atoms, the full TPTP connective set, and quantified formulas.
/// CEP:WHY: The TPTP FOF layer of design 6.1; the connective variants mirror the TPTP binary connectives one-to-one so no information is lost between input and the future clausification pipeline (design 7 stages 1-6 consume this AST).
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data type.
/// CEP:ASSUMES: symbol ids reference the same parse's SymbolTableBuilder; every Variable name is bound by an enclosing quantifier (enforced by the binder check).
/// CEP:COST: tree with boxed children; node count bounded by kMaxFormulaNodes.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{fof_formulas_reach_the_ast, binds_all_connectives, rejects_free_variable}.
/// CEP:SECURITY: node count bounded by kMaxFormulaNodes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FofFormula {
    /// The `$true` constant.
    True,
    /// The `$false` constant.
    False,
    /// A predicate atom by symbol-table id with argument terms.
    Predicate(u32, Vec<FofTerm>),
    /// An equality atom `left = right` (interned through TermStore::intern_eq in the IR).
    Equality(FofTerm, FofTerm),
    /// Negation.
    Not(Box<FofFormula>),
    /// Conjunction over one or more operands (associative flattening).
    And(Vec<FofFormula>),
    /// Disjunction over one or more operands (associative flattening).
    Or(Vec<FofFormula>),
    /// Implication `left => right` (right-associative chains nest right).
    Implies(Box<FofFormula>, Box<FofFormula>),
    /// Reverse implication `left <= right` (left-associative chains nest left).
    ReverseImplies(Box<FofFormula>, Box<FofFormula>),
    /// Equivalence `left <=> right` (non-associative in TPTP).
    Equivalent(Box<FofFormula>, Box<FofFormula>),
    /// Non-equivalence `left <~> right` (non-associative in TPTP).
    NotEquivalent(Box<FofFormula>, Box<FofFormula>),
    /// XOR disjunction `left ~| right` (non-associative in TPTP).
    NotOr(Box<FofFormula>, Box<FofFormula>),
    /// NAND conjunction `left ~& right` (non-associative in TPTP).
    NotAnd(Box<FofFormula>, Box<FofFormula>),
    /// Universal quantification over name-table ids with the body.
    Forall(Vec<u32>, Box<FofFormula>),
    /// Existential quantification over name-table ids with the body.
    Exists(Vec<u32>, Box<FofFormula>),
}

/// CEP:WHAT: The parse-time name table: dense u32 ids for every distinct variable and formula name, backed by a deduplicating map.
/// CEP:WHY: AST nodes reference variables by dense id instead of carrying a String per node; the table keeps name lookup exact and allocation bounded by the distinct-name count.
/// CEP:STATUS: complete
/// CEP:FAILURE: never fails; growth is bounded by kMaxFormulaNodes via the caller's node budget.
/// CEP:ASSUMES: one table per parse.
/// CEP:COST: O(1) amortized intern through the HashMap plus the owned String.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::fof_formulas_reach_the_ast.
/// CEP:SECURITY: names are owned copies; no input borrow escapes the parser.
#[derive(Debug, Default)]
pub struct NameTable {
    names: Vec<String>,
    index: HashMap<String, u32>,
}

impl NameTable {
    /// CEP:WHAT: Interns a name and returns its dense id, deduplicating.
    /// CEP:WHY: One id per distinct name keeps AST comparison and binder checks cheap.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: never fails.
    /// CEP:ASSUMES: none.
    /// CEP:COST: O(name length) amortized.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::fof_formulas_reach_the_ast.
    /// CEP:SECURITY: none.
    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(id) = self.index.get(name) {
            return *id;
        }
        let id = self.names.len() as u32;
        self.names.push(String::from(name));
        self.index.insert(String::from(name), id);
        id
    }

    /// CEP:WHAT: Returns the name for an id.
    /// CEP:WHY: Drivers and the future clausifier need the spelling for output formats.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: Returns None for an out-of-range id.
    /// CEP:ASSUMES: none.
    /// CEP:COST: one index plus a borrow.
    /// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::fof_formulas_reach_the_ast.
    /// CEP:SECURITY: none.
    pub fn name_of(&self, id: u32) -> Option<&str> {
        self.names.get(id as usize).map(|value| value.as_str())
    }
}

/// CEP:WHAT: One parsed TPTP input formula: its role, its name, and the validated AST.
/// CEP:WHY: The driver needs role (stage-1 negation), name (include selection and proof labels), and formula (design 7 clausification input) together.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: none.
/// CEP:COST: owned record.
/// CEP:EVIDENCE: unit/cold/tptp_parser_test.rs::{fof_formulas_reach_the_ast, include_selection_filters_by_name}.
/// CEP:SECURITY: none.
#[derive(Debug, Clone)]
pub struct ParsedFof {
    /// The declared role of the input formula.
    pub role: TptpRole,
    /// The declared formula name (owned copy of the TPTP name token).
    pub name: String,
    /// The validated formula AST.
    pub formula: FofFormula,
}

/// CEP:WHAT: The parse result handed to the driver: the frozen symbol table, the builder (retained for name lookup), the IR stores with every parsed CNF/DIMACS clause, the parsed FOF formulas, and the name table.
/// CEP:WHY: Design 6.2 stage 4-5: the parser hands over fully constructed IR (hash-consed terms, assigned clause ids) plus the FOF layer for the design 7 pipeline; one struct keeps the arena borrow coherent.
/// CEP:STATUS: complete
/// CEP:FAILURE: none; a data record.
/// CEP:ASSUMES: the arena outlives the problem; clause_ptrs index into clauses.
/// CEP:COST: owned record over the caller's arena.
/// CEP:EVIDENCE: unit/cold/dimacs_parser_test.rs::parses_header_and_clauses_into_ir; unit/cold/tptp_parser_test.rs::cnf_clauses_reach_the_ir.
/// CEP:SECURITY: every stored clause passed the store's own invariants at construction.
pub struct ParsedProblem<'a> {
    /// The frozen symbol table the term store was constructed against.
    pub symbols: SymbolTable<'a>,
    /// The retained builder: the name surface for output formats (the frozen table does not carry names).
    pub builder: SymbolTableBuilder,
    /// The term store with every parsed atom hash-consed.
    pub terms: TermStore<'a>,
    /// The clause store with every parsed CNF/DIMACS clause.
    pub clauses: ClauseStore<'a>,
    /// The clause records in input order (DIMACS: file order; TPTP: formula order with includes inlined).
    pub clause_ptrs: Vec<ClausePtr>,
    /// The parsed FOF formulas in input order (empty for DIMACS input).
    pub formulas: Vec<ParsedFof>,
    /// The parsed CNF directives with role and name, in input order (includes inlined).
    pub cnf_clauses: Vec<tptp_parser::ParsedCnf>,
    /// The variable and formula name table.
    pub names: NameTable,
}
