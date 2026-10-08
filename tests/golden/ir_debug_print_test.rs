// CEP:FILE: tests/golden/ir_debug_print_test.rs
// CEP:WHAT: Golden test for the IR debug printer: printed terms and clauses must match the committed golden files byte for byte.
// CEP:WHY: CEP&CC 32.8 (every generated or deterministic artifact requires golden tests) and 38.19 (stable printing): the debug format is the substrate for TSTP output and regression detection.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any byte of drift; set UPDATE_GOLDEN=1 to regenerate after an intentional format change (documented in the golden header).
// CEP:ASSUMES: fixtures from tests/common/mod.rs; golden files live in tests/golden/golden/.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file is the evidence cited by cold/debug_printer.rs.
// CEP:SECURITY: none.

#![allow(non_upper_case_globals)]
#[path = "../common/mod.rs"]
mod common;

use common::make_term_fixture;
use mapt::cold::debug_printer::{print_clause, print_term};
use mapt::hot::ir::clause::DerivationStep;
use mapt::hot::ir::literal::Literal;
use mapt_config::limits::{kInvalidClauseId, kInvalidSubstitutionOffset};
use std::env;
use std::fs;
use std::path::PathBuf;

// CEP:WHAT: Builds the golden corpus: one term block and one clause block.
// CEP:WHY: A fixed corpus keeps the golden file small and its diff meaningful.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: standard fixture.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn build_corpus() -> String {
    let (_arena, symbols, builder, terms, clauses) = make_term_fixture();
    let a = terms
        .intern_fun(&symbols, fixture_id(&builder, "a"), &[])
        .expect("a");
    let b = terms
        .intern_fun(&symbols, fixture_id(&builder, "b"), &[])
        .expect("b");
    let f_id = fixture_id(&builder, "f");
    let h_id = fixture_id(&builder, "h");
    let var = terms.intern_var(0).expect("V0");
    let fa = terms.intern_fun(&symbols, f_id, &[a]).expect("f(a)");
    let hab = terms.intern_fun(&symbols, h_id, &[a, b]).expect("h(a,b)");
    let fvar = terms.intern_fun(&symbols, f_id, &[var]).expect("f(V0)");
    let eq = terms.intern_eq(&symbols, fa, var).expect("f(a) = V0");
    let sort = terms.intern_sort(1).expect("sort term");
    let mut out = String::new();
    out.push_str(kGoldenHeader);
    for (name, handle) in [
        ("a", a),
        ("f(a)", fa),
        ("h(a,b)", hab),
        ("f(V0)", fvar),
        ("eq", eq),
        ("sort", sort),
    ] {
        out.push_str(name);
        out.push_str(" = ");
        print_term(&terms, &builder, handle, &mut out).expect("print term");
        out.push('\n');
    }
    let p_id = fixture_id(&builder, "p");
    let pa = terms.intern_pred(&symbols, p_id, &[a]).expect("p(a)");
    let pb = terms.intern_pred(&symbols, p_id, &[b]).expect("p(b)");
    let clause_ptr = clauses
        .new_clause(
            &terms,
            &[Literal::new(pa, true), Literal::new(pb, false)],
            0,
            input_derivation(),
        )
        .expect("clause");
    out.push_str("clause = ");
    print_clause(&terms, &builder, &clauses, clause_ptr, &mut out).expect("print clause");
    out.push('\n');
    out
}

// CEP:WHAT: Golden file header explaining regeneration.
// CEP:WHY: Golden files must document their own update procedure (CEP&CC 32.7 generator identity discipline).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
const kGoldenHeader: &str = "// MAPT IR debug-print golden file. Regenerate with UPDATE_GOLDEN=1 cargo test --test ir_debug_print_test\n";

// CEP:WHAT: Compares the corpus against the golden file, or regenerates it.
// CEP:WHY: Byte-exact stability is the contract.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by cold/debug_printer.rs.
// CEP:SECURITY: none.
#[test]
fn golden_debug_print_matches() {
    let corpus = build_corpus();
    let golden_path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/golden/ir_debug_print.txt");
    if env::var("UPDATE_GOLDEN").is_ok() {
        fs::write(&golden_path, &corpus).expect("write golden");
        return;
    }
    let golden = fs::read_to_string(&golden_path)
        .unwrap_or_else(|_| panic!("golden file missing; run with UPDATE_GOLDEN=1 once"));
    assert_eq!(golden, corpus, "debug output drifted from the golden file");
}

// CEP:WHAT: Resolves a fixture symbol ID by name.
// CEP:WHY: Readable tests.
// CEP:STATUS: complete
// CEP:FAILURE: panics on unknown name.
// CEP:ASSUMES: standard fixture.
// CEP:COST: linear scan.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn fixture_id(builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder, name: &str) -> u32 {
    for id in 0..builder.symbol_count() {
        if builder.name_of(id) == Some(name) {
            return id;
        }
    }
    panic!("fixture symbol {} not found", name);
}

// CEP:WHAT: Builds an input derivation step.
// CEP:WHY: Shared fixture.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: used by this file.
// CEP:SECURITY: none.
fn input_derivation() -> DerivationStep {
    DerivationStep {
        rule: mapt::hot::ir::clause::InferenceRule::Input,
        parent_count: 0,
        reserved: 0,
        parents: [kInvalidClauseId; 4],
        substitution: kInvalidSubstitutionOffset,
    }
}
