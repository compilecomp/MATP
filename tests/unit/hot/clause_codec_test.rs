// CEP:FILE: tests/unit/hot/clause_codec_test.rs
// CEP:WHAT: Unit tests of the portable clause codec: encode/decode roundtrips over the fixture vocabulary, the word bound, the pinned header layout, and the untrusted-record rejections (truncation, unknown tag, lambda).
// CEP:WHY: CEP&CC 34.3: the codec carries shared clauses across worker arenas (design 19.2); its layout and validation claims (Spec 13 section 4) must be pinned executably.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: the standard fixture vocabulary.
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/clause_codec_test.rs.
// CEP:SECURITY: the decode-side tests exercise the untrusted-record guards.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::concurrency::clause_codec::{decode_clause, encode_clause, CodecError};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;

// CEP:WHAT: Builds one predicate literal from the fixture vocabulary.
// CEP:WHY: Readable codec fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture stores.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn pred(
    terms: &mapt::hot::ir::term::TermStore<'_>,
    symbols: &mapt::hot::ir::symbol_table::SymbolTable<'_>,
    builder: &mapt::cold::symbol_table_builder::SymbolTableBuilder,
    name: &str,
    args: &[TermPtr],
    positive: bool,
) -> Literal {
    let atom = terms
        .intern_pred(symbols, symbol_id(builder, name), args)
        .expect("atom");
    Literal::new(atom, positive)
}

#[test]
// CEP:WHAT: encode-decode roundtrips preserve the literal multiset (atoms and polarities) over ground and variable-bearing clauses.
// CEP:WHY: Spec 13 section 4's tree-encoding lemma: decode(encode(c)) = c; the decode side re-interns, so atom identity (hash-consed pointers) must match.
// CEP:STATUS: complete
// CEP:FAILURE: panics on mismatch.
// CEP:ASSUMES: same store and symbol table on both sides (the single-arena case).
// CEP:COST: a few encodes/decodes.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::roundtrip_preserves_literals and property/concurrency_property_test.rs::codec_roundtrip_property.
// CEP:SECURITY: none.
fn roundtrip_preserves_literals() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let a_arg = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let p_x = pred(
        &terms,
        &symbols,
        &builder,
        "p",
        &[terms.intern_var(0).expect("var")],
        true,
    );
    let q_y = pred(
        &terms,
        &symbols,
        &builder,
        "q",
        &[terms.intern_var(1).expect("var"), a_arg],
        false,
    );
    let ground_a = pred(&terms, &symbols, &builder, "p", &[a_arg], true);
    let literals = [p_x, q_y, ground_a];
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let length = encode_clause(&terms, &literals, &mut record).expect("encode");
    assert!(length >= 4, "header + three literal sections");
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    let count = decode_clause(&record[..length], &terms, &symbols, &mut decoded).expect("decode");
    assert_eq!(count, 3);
    for (index, literal) in literals.iter().enumerate() {
        assert_eq!(
            decoded[index].atom(),
            literal.atom(),
            "atom {} must roundtrip to the same hash-consed pointer",
            index
        );
        assert_eq!(decoded[index].is_positive(), literal.is_positive());
    }
}

#[test]
// CEP:WHAT: Encoding a clause whose words exceed kSharedClauseMaxWords fails loudly with TooLarge.
// CEP:WHY: The per-record memory bound (design 19.2 degradation - skip and count).
// CEP:STATUS: complete
// CEP:FAILURE: panics if the bound is not enforced.
// CEP:ASSUMES: a wide clause (many literals) exceeds the word budget.
// CEP:COST: one encode.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::word_bound_enforced.
// CEP:SECURITY: memory bound.
fn word_bound_enforced() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    // One literal per variable: enough literals to blow the 256-word budget.
    // One wide clause: many variable literals over p/1 (the fixture's arity-1
    // predicate); one literal per word of budget.
    let mut literals: Vec<Literal> = Vec::new();
    for index in 0..(mapt_config::limits::kSharedClauseMaxWords + 4) {
        let var = terms.intern_var((index % 63) as u32).expect("var");
        let atom = terms
            .intern_pred(&symbols, symbol_id(&builder, "p"), &[var])
            .expect("atom");
        literals.push(Literal::new(
            atom,
            index % 63 == (index % 63) && index % 2 == 0,
        ));
    }
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    assert_eq!(
        encode_clause(&terms, &literals, &mut record),
        Err(CodecError::TooLarge)
    );
}

#[test]
// CEP:WHAT: The header and node-word layouts are pinned: header packs [total:16][literals:16], node packs [tag:3][symbol:32][children:10].
// CEP:WHY: CEP&CC 38.17 layout pins: the pool's length extraction and every decoder depend on the bit positions; drift is an interface break.
// CEP:STATUS: complete
// CEP:FAILURE: panics on layout drift.
// CEP:ASSUMES: the fixture literal (one variable atom).
// CEP:COST: one encode.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
fn header_layout_pinned() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let var = terms.intern_var(0).expect("var");
    let literal = pred(&terms, &symbols, &builder, "p", &[var], false);
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let length = encode_clause(&terms, &[literal], &mut record).expect("encode");
    // Header: total words in the low 16 bits, literal count in the next 16.
    assert_eq!((record[0] & 0xFFFF) as usize, length);
    assert_eq!(((record[0] >> 16) & 0xFFFF) as usize, 1);
    // Literal header: the polarity bit.
    assert_eq!(record[1], 0, "negative literal encodes polarity 0");
    // Root node word: tag = Predicate (2), symbol = p's id, children = 1.
    let p_id = symbol_id(&builder, "p") as u64;
    assert_eq!(
        record[2],
        2u64 | (p_id << 3) | (1u64 << 35),
        "predicate node packs tag=2, symbol=p, children=1"
    );
    // Child node word: tag = Variable (0), symbol = variable id 0, children = 0.
    assert_eq!(
        record[3], 0,
        "variable node packs tag=0, symbol=0, children=0"
    );
}

#[test]
// CEP:WHAT: A record that ends mid-term is rejected as Truncated.
// CEP:WHY: The untrusted-record guard (a partial record must never decode to a partial clause).
// CEP:STATUS: complete
// CEP:FAILURE: panics if a truncated record decodes.
// CEP:ASSUMES: none.
// CEP:COST: one decode.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::rejects_truncated_record.
// CEP:SECURITY: untrusted-record validation.
fn rejects_truncated_record() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    // The header is self-consistent (4 words) but the p/2 tree needs a fifth word:
    // the first child (a variable) completes, the second child read hits the end.
    let p_id = symbol_id(&builder, "p") as u64;
    let predicate_node = 2u64 | (p_id << 3) | (2u64 << 35);
    let record: Vec<u64> = vec![(1u64 << 16) | 4, 1, predicate_node, 0];
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    assert_eq!(
        decode_clause(&record, &terms, &symbols, &mut decoded),
        Err(CodecError::Truncated)
    );
    // An atom word missing entirely is also truncated.
    let deep: Vec<u64> = vec![(1u64 << 16) | 2, 1, 0];
    assert_eq!(
        decode_clause(&deep, &terms, &symbols, &mut decoded),
        Err(CodecError::Truncated)
    );
}

#[test]
// CEP:WHAT: A node word with a tag outside the term vocabulary is rejected as UnknownTag.
// CEP:WHY: The untrusted-record guard for forged tags.
// CEP:STATUS: complete
// CEP:FAILURE: panics if a forged tag decodes.
// CEP:ASSUMES: none.
// CEP:COST: one decode.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::rejects_unknown_tag.
// CEP:SECURITY: untrusted-record validation.
fn rejects_unknown_tag() {
    let (arena, symbols, _builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    // tag = 7 is outside the 0-6 term vocabulary (the header is self-consistent:
    // four words, one literal).
    let record: Vec<u64> = vec![(1u64 << 16) | 4, 1, 7, 0];
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    assert_eq!(
        decode_clause(&record, &terms, &symbols, &mut decoded),
        Err(CodecError::UnknownTag)
    );
}

#[test]
// CEP:WHAT: A Lambda node is rejected as UnsupportedTag (higher-order interning is Phase 5).
// CEP:WHY: The honest FOL-totality claim (CEP&CC Law 4): the codec does not pretend to support what the store cannot intern.
// CEP:STATUS: complete
// CEP:FAILURE: panics if a lambda record decodes.
// CEP:ASSUMES: none.
// CEP:COST: one decode.
// CEP:EVIDENCE: backs unit/hot/clause_codec_test.rs::rejects_lambda_terms.
// CEP:SECURITY: untrusted-record validation.
fn rejects_lambda_terms() {
    let (arena, symbols, _builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    // tag = 5 is Lambda (header self-consistent).
    let record: Vec<u64> = vec![(1u64 << 16) | 4, 1, 5, 0];
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    assert_eq!(
        decode_clause(&record, &terms, &symbols, &mut decoded),
        Err(CodecError::UnsupportedTag)
    );
}
