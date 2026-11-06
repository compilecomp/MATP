# Formal Specification 20: The Input Parsers (DIMACS CNF and TPTP CNF/FOF)

## Abstract

This document is the normative reference for `cold/parsing/` (ticket CEP-1006, design 6): the shared parse vocabulary (`mod.rs`), the DIMACS CNF front end (`dimacs_parser.rs`), and the TPTP CNF/FOF front end (`tptp_parser.rs`). Inputs are untrusted byte slices (plus, for TPTP, an include root directory); outputs are the `ParsedProblem` record (frozen symbol table, retained builder, hash-consed term store, clause store with input clauses, FOF ASTs, CNF directive records, name table) or a `ParseError`. References: design 6.1-6.3; Formal Specs 01 (syntax), 02 (renaming).

## Formal Definitions

**Parse error.** `ParseError` is the exact-kind failure vocabulary: `TooLarge` (kMaxInputBytes), `TooDeep` (kMaxParseDepth), `QuantifierTooDeep` (kMaxQuantifierDepth), `TooManyNodes` (kMaxFormulaNodes), `TooManySymbols` (kMaxSymbolCount), `IncludeTooDeep` (kMaxIncludeDepth), `TooManyIncludes` (kMaxIncludeCount), `IncludeUnreadable`, `UnknownRole`, `ArityMismatch`, `FreeVariable`, `VariableBeyondHeader`, `MissingHeader`, `Syntax { line, column }`, and the IR-construction kinds `IrTerm(TermError)`, `IrClause(ClauseError)`, `IrSymbol(BuilderError)` carried with their exact underlying kind.

**Parsed problem.** `ParsedProblem<'a>` holds: the frozen `SymbolTable<'a>` produced by `builder.finalize(arena)`; the retained `SymbolTableBuilder` (the name surface; the frozen table does not carry names); the `TermStore<'a>` and `ClauseStore<'a>`; `clause_ptrs` in input order; `formulas` (the FOF ASTs with roles and names); `cnf_clauses` (role/name/literal records); and the `NameTable`.

**FOF AST.** `FofFormula` is one variant per TPTP construct: `True`, `False`, `Predicate(symbol, args)`, `Equality(left, right)`, `Not`, flattened associative `And`/`Or`, the six binary connectives `Implies` (right-associative), `ReverseImplies` (left-associative), `Equivalent`, `NotEquivalent`, `NotOr`, `NotAnd` (non-associative), and `Forall`/`Exists` over name-table ids. `FofTerm` is `Variable(name_id)` or `Application(symbol, args)`.

**Symbol registry.** TPTP is untyped and declaration-free: the signature of a name is fixed by its first use. The parser's registry maps name to builder id and (kind, arity); a later use with a different kind or arity is the input defect `ArityMismatch`. The `$i` individual sort is declared at parser construction; the `$o` Boolean sort is declared lazily by the builder with the first predicate.

**Variable namespaces.** Variables are clause-local dense indices: within one clause, the n-th distinct variable name is interned as `intern_var(n-1)`, bounded by `kMaxVariablesPerClause` (the renamed-apart discipline of Spec 02 section 5). FOF formulas carry bound-variable names in the `NameTable` and reject free variables (`FreeVariable`); CNF clause variables are universally quantified by convention and are exempt from the binder check.

**True/False semantics.** In a CNF disjunction, `$true` (positive) and `$false` (negative) are tautologous; the opposite polarities are vacuous. A clause containing a tautologous literal is dropped; a clause whose every literal is vacuous becomes the empty clause (a refutation record).

## Algorithm

**DIMACS (`parse_dimacs`).** One fused lex/parse pass over the bytes: line-start `c` comments and the SAT-competition `%` end marker are lexical trivia; the single `p cnf <vars> <clauses>` header declares the variable universe (gated by `kMaxSymbolCount`; later indexes beyond it are `VariableBeyondHeader`); 0-terminated signed-integer runs accumulate clause literals (checked arithmetic; per-clause count bounded by the clause store at construction). Time O(input); IR construction is one interning pass (variable v<n> becomes the 0-ary predicate v<n>).

**TPTP (`parse_tptp`, `parse_tptp_with_limits`).** The five-stage shape of design 6.2: (1) the lexer produces one token at a time (word classes, quoted atoms, the multi-character connectives matched longest-first: `<=>`, `<~>` before `<=`, `=>`, `~|`, `~&`, `!=`); (2) recursive descent with precedence `&` over `|` over `=>`/`<=` over the non-associative layer, quantifier bodies as unit formulas per the TPTP grammar, CNF disjunctions with parenthesized recursion; (3) validation: roles via `TptpRole::from_token` (unknown roles rejected, never downgraded), signature consistency, FOF binding; (4) IR construction: `build_cnf_clause` interns atoms (`intern_pred`), equality atoms (`intern_eq`), and applies the True/False semantics; (5) the `ParsedProblem` return. Includes resolve under the caller-supplied root, share the semantic state (builder, name table, registries, budgets move into the child parser and back), and filter by the optional selection list. Time O(input + IR) under the bounds.

**Injectable limits.** `ParserLimits` carries the node budget, parse depth, and quantifier depth; `standard()` reads the design 6.3 constants, and injected values are clamped to them (a larger injection never exceeds the design bound).

## Invariants

1. Every rejected input returns an exact `ParseError` kind; no panic, no exception, no input echo in error values (design 6.3).
2. Every AST allocation charges the node budget; every quantifier layer and every recursive-descent entry (unit formula, term, CNF disjunction) charges its depth bound and releases it on every path.
3. The frozen table's symbol kinds match the interning calls: an atom head is declared a predicate, an equality side a function; a signature change is `ArityMismatch` at parse time, never a store error at IR time.
4. Clause records satisfy the clause store's own invariants (canonical order, weight, monotone ids); every stored clause carries the `Input` derivation with no parents.
5. Include resolution is acyclic and fan-out bounded: `kMaxIncludeDepth` nesting and `kMaxIncludeCount` files per parse; every include file passes the same `kMaxInputBytes` gate.
6. Symbol ids are coherent across include files (one shared signature per parse).

## Integration Points

Depends on:

- `cold/symbol_table_builder.rs` (`SymbolTableBuilder::declare_sort`, `declare_predicate`, `declare_function`, `finalize`) for CEP-1 signature construction.
- `hot/ir/term.rs` (`TermStore::new`, `intern_pred`, `intern_fun`, `intern_eq`, `intern_var`) and `hot/ir/clause.rs` (`ClauseStore::new`, `new_clause`, `DerivationStep`, `InferenceRule::Input`) for IR construction.
- `config/limits.rs` (`kMaxInputBytes`, `kMaxFormulaNodes`, `kMaxParseDepth`, `kMaxQuantifierDepth`, `kMaxSymbolCount`, `kMaxIncludeDepth`, `kMaxIncludeCount`) for the design 6.3 bound set.

Depended on by:

- The CEP-1 driver (the future input stage of design 6.1's API path), which receives `ParsedProblem` and drives the search; the FOF ASTs feed the design 7 preprocessing pipeline (stages 1-6).

## Known Limitations

- SMT-LIB 2.x and the TPTP TFF/THF dialects are not parsed (open under CEP-1006; the design 6.1 table lists them).
- Quoted atoms are accepted as ordinary constants named by their quoted spelling; distinct-object semantics for quoted atoms is not applied.
- Numeric terms (`1`, `2`, ...) are rejected in term position; arithmetic input belongs to the theory layer (28.6) and its input formats.
- `$distinct`, annotations beyond source skipping, and TPTP sequents are not parsed.
- The declared DIMACS clause count is recorded but not enforced as an equality (real-world files under-declare); the clause store's own bound governs the total.
- FOF formulas are returned as validated ASTs; clausification (design 7) is the consumer pipeline and is a separate build item.
