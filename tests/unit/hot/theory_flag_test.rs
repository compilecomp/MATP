// CEP:FILE: tests/unit/hot/theory_flag_test.rs
// CEP:WHAT: Unit tests of the theory-laden literal flags (CEP-1012): the TheoryTag vocabulary round trips, the coupling invariant between the theory-laden bit and the tag nibble, flag preservation through negation and AVATAR tagging, and the codec's carriage and validation of the flags byte.
// CEP:WHY: Design 5.2 reserves the flags byte's theory tag and Formal Spec 01 section 5 (amended) pins the vocabulary and the coupling invariant; the portable codec (Spec 13 section 4, amended) must carry the byte across worker boundaries and reject forged flag words, so every claim is pinned executably.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: tests fail loudly on any invariant break.
// CEP:ASSUMES: the standard fixture vocabulary; fixtures from tests/common/mod.rs.
// CEP:COST: offline; runtime cost irrelevant.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to unit/hot/theory_flag_test.rs.
// CEP:SECURITY: the decode-side tests exercise the untrusted-record guards.

#![allow(non_upper_case_globals)]

#[path = "../../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id};
use mapt::hot::concurrency::clause_codec::{decode_clause, encode_clause, CodecError};
use mapt::hot::ir::literal::{Literal, LiteralFlags, TheoryTag};
use mapt::hot::ir::term::TermPtr;

// CEP:WHAT: All seven vocabulary encodings round trip through the nibble.
// CEP:WHY: The flags byte stores numbers, not variants; the conversion pair must be an involution (Spec 01 section 5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any round-trip mismatch.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/literal.rs TheoryTag.
// CEP:SECURITY: none.
#[test]
fn theory_tag_roundtrip() {
    let all = [
        TheoryTag::None,
        TheoryTag::LinearInteger,
        TheoryTag::LinearReal,
        TheoryTag::NonLinearArithmetic,
        TheoryTag::Bitvectors,
        TheoryTag::Arrays,
        TheoryTag::AlgebraicDatatypes,
    ];
    for (index, tag) in all.iter().enumerate() {
        assert_eq!(tag.to_bits(), index as u8, "encoding gap in the vocabulary");
        assert_eq!(TheoryTag::from_bits(index as u8), Some(*tag));
    }
    for reserved in 7u8..16 {
        assert_eq!(
            TheoryTag::from_bits(reserved),
            None,
            "reserved encoding {reserved} must not decode to a theory"
        );
    }
}

// CEP:WHAT: The coupling invariant: set_theory_tag maintains the theory-laden bit in lockstep (non-None tag sets it, None clears both), and a reserved nibble never reads back as a theory.
// CEP:WHY: "Theory-laden" and "has a theory tag" must be one fact or the flags byte lies to the theory layer (Spec 01 section 5).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any invariant break.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/literal.rs set_theory_tag.
// CEP:SECURITY: none.
#[test]
fn theory_laden_coupling() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let arg = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let atom = terms
        .intern_pred(&symbols, symbol_id(&builder, "p"), &[arg])
        .expect("atom");
    let mut literal = Literal::new(atom, true);
    assert!(!literal.is_theory_laden());
    assert_eq!(literal.theory_tag(), Some(TheoryTag::None));
    literal.set_theory_tag(TheoryTag::LinearInteger);
    assert!(literal.is_theory_laden(), "a non-None tag must set the bit");
    assert_eq!(literal.theory_tag(), Some(TheoryTag::LinearInteger));
    literal.set_theory_tag(TheoryTag::Arrays);
    assert!(literal.is_theory_laden());
    assert_eq!(literal.theory_tag(), Some(TheoryTag::Arrays));
    literal.set_theory_tag(TheoryTag::None);
    assert!(
        !literal.is_theory_laden(),
        "None must clear the theory-laden bit"
    );
    assert_eq!(literal.theory_tag(), Some(TheoryTag::None));
    // AVATAR component tagging must preserve the theory bits (CEP-1011 contract).
    literal.set_theory_tag(TheoryTag::LinearReal);
    literal.set_avatar_component_tag(3);
    assert_eq!(literal.avatar_component_tag(), 3);
    assert!(literal.is_theory_laden());
    assert_eq!(literal.theory_tag(), Some(TheoryTag::LinearReal));
    // Negation preserves the whole flags byte.
    let negated = literal.negate();
    assert!(!negated.is_positive());
    assert!(negated.is_theory_laden());
    assert_eq!(negated.theory_tag(), Some(TheoryTag::LinearReal));
    assert_eq!(negated.avatar_component_tag(), 3);
}

// CEP:WHAT: The flags-byte masks partition the byte: avatar bits 0-2, theory-laden bit 3, tag nibble 4-7.
// CEP:WHY: The layout is the Spec 01 section 5 contract; a mask drift would silently overwrite the neighboring field.
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any layout drift.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: cited by hot/ir/literal.rs LiteralFlags.
// CEP:SECURITY: none.
#[test]
fn flags_masks_partition_the_byte() {
    assert_eq!(LiteralFlags::kAvatarComponentMask, 0x07);
    assert_eq!(LiteralFlags::kTheoryLaden, 0x08);
    assert_eq!(LiteralFlags::kTheoryTagMask, 0xF0);
    assert_eq!(LiteralFlags::kTheoryTagShift, 4);
    assert_eq!(
        LiteralFlags::kAvatarComponentMask
            | LiteralFlags::kTheoryLaden
            | LiteralFlags::kTheoryTagMask,
        0xFF
    );
}

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

// CEP:WHAT: The codec round trip preserves the flags byte (theory tag, theory-laden bit, avatar component tag) across encode/decode.
// CEP:WHY: Spec 13 section 4 (amended): the polarity word carries [polarity:1][theory flags:8][reserved:55]; a dropped flags byte would silently untag theory literals at the worker boundary (the CEP-1012 defect this closes).
// CEP:STATUS: complete
// CEP:FAILURE: test fails on any flag loss.
// CEP:ASSUMES: same store and symbol table on both sides.
// CEP:COST: one encode/decode.
// CEP:EVIDENCE: cited by hot/concurrency/clause_codec.rs encode_clause.
// CEP:SECURITY: none.
#[test]
fn codec_roundtrip_preserves_theory_flags() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let arg = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let mut l1 = pred(&terms, &symbols, &builder, "p", &[arg], true);
    let mut l2 = pred(&terms, &symbols, &builder, "q", &[arg, arg], false);
    l1.set_theory_tag(TheoryTag::LinearInteger);
    l1.set_avatar_component_tag(2);
    l2.set_theory_tag(TheoryTag::Bitvectors);
    let literals = [l1, l2];

    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let length = encode_clause(&terms, &literals, &mut record).expect("encode");
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    let count = decode_clause(&record[..length], &terms, &symbols, &mut decoded).expect("decode");
    assert_eq!(count, 2);
    for index in 0..count {
        let original = &literals[index];
        let back = &decoded[index];
        assert_eq!(original.is_positive(), back.is_positive());
        assert_eq!(original.theory_tag(), back.theory_tag());
        assert_eq!(original.is_theory_laden(), back.is_theory_laden());
        assert_eq!(original.avatar_component_tag(), back.avatar_component_tag());
        assert_eq!(
            original.atom(),
            back.atom(),
            "atom identity must round trip"
        );
    }
}

// CEP:WHAT: The codec rejects forged flag words: nonzero reserved bits, a reserved tag encoding, and a broken coupling invariant.
// CEP:WHY: Spec 13 section 4's untrusted-record discipline: a forged record must fail loudly, never decode to a mis-tagged literal.
// CEP:STATUS: complete
// CEP:FAILURE: test fails if any forged word decodes.
// CEP:ASSUMES: the fixture's valid clause as the tamper base.
// CEP:COST: three decodes.
// CEP:EVIDENCE: cited by hot/concurrency/clause_codec.rs decode_clause.
// CEP:SECURITY: untrusted-record guards.
#[test]
fn codec_rejects_bad_flag_words() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let arg = terms
        .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
        .expect("a");
    let literals = [pred(&terms, &symbols, &builder, "p", &[arg], true)];
    let mut record: Vec<u64> = vec![0; mapt_config::limits::kSharedClauseMaxWords];
    let length = encode_clause(&terms, &literals, &mut record).expect("encode");
    assert!(length >= 2, "header plus one polarity word");

    // Nonzero reserved bits above the flags byte.
    let mut tampered = record.clone();
    tampered[1] |= 1u64 << 40;
    let mut decoded: Vec<Literal> = vec![Literal::new(TermPtr::invalid(), true); 8];
    assert_eq!(
        decode_clause(&tampered[..length], &terms, &symbols, &mut decoded),
        Err(CodecError::Malformed)
    );

    // Reserved tag encoding 7 in the nibble (with the laden bit set, as a forged writer would).
    let mut tampered = record.clone();
    tampered[1] = (tampered[1] & !0x1F0) | (1u64 << 0) | (7u64 << 5) | (1u64 << 4);
    assert_eq!(
        decode_clause(&tampered[..length], &terms, &symbols, &mut decoded),
        Err(CodecError::Malformed)
    );

    // Broken coupling: tag nibble set but the theory-laden bit clear.
    let mut tampered = record;
    tampered[1] = (tampered[1] & !0x1F0) | (1u64 << 0) | (2u64 << 5);
    assert_eq!(
        decode_clause(&tampered[..length], &terms, &symbols, &mut decoded),
        Err(CodecError::Malformed)
    );
}
