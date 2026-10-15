// CEP:FILE: hot/concurrency/clause_codec.rs
// CEP:WHAT: The portable clause codec (design 19.2 clause sharing): encodes one clause as a fixed-budget u64-word record (header, per-literal polarity headers, one prefix-order node word per term node) and decodes it back into interned literals of another worker's arena.
// CEP:WHY: Portfolio workers own separate arenas (design 19.8 NUMA placement), so a shared clause cannot travel by pointer - it crosses by value; the word format is arena-independent (tags and symbol ids, never offsets) with the portfolio's symbol-table contract (every worker builds its table from the same symbol list in the same order, so ids agree - Spec 13 section 4); the tree encoding duplicates shared subterms (bounded by kSharedClauseMaxWords, the honest cost of a self-contained record; hash-consing on the receiving side restores sharing); encode uses an explicit DFS stack and decode an explicit (frame, child-slot) stack - no recursion, so adversarial depth cannot grow the native stack (CEP&CC 22.10); every bound is named and loud (TooLarge, TooDeep, Truncated, UnknownTag) and degradation is the exporter's documented skip.
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: encode returns TooLarge past the word budget (the exporter skips and counts); decode returns Truncated/TooDeep/UnknownTag/UnsupportedTag/WordBudget... never a wrong clause; never panics.
// CEP:ASSUMES: encode: atoms interned by the given store; decode: the receiving symbol table was built from the same symbol list in the same order (the portfolio contract); variable ids below kMaxVariablesPerClause.
// CEP:COST: encode O(term tree nodes), decode O(nodes) with one hash-consing intern per node; measured in bench CEP-BENCH-0035, artifact benches/artifacts/codec_roundtrip.json.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, word_bound_enforced, header_layout_pinned, rejects_truncated_record, rejects_unknown_tag, rejects_lambda_terms}; property/concurrency_property_test.rs::codec_roundtrip_property.
// CEP:SECURITY: the decoder validates every header, tag, child count, and symbol id before interning - a forged record degrades to a loud error, never to a corrupt clause.
// CEP:UNSAFE: none; this file is safe Rust.
// CEP:HPC-DETERMINISM: deterministic both ways (prefix order, fixed layouts).
// CEP:HPC-PASS-LEGALITY: Formal Spec 13 section 4 fixes the record layout, the node-word layout, the tree-encoding lemma (the prefix word sequence determines the term tree exactly), and the symbol-table contract; the property test verifies executably that decode(encode(c)) = c over generated clauses.

use mapt_config::limits::{
    kMaxClauseLiterals, kMaxSymbolArity, kMaxTermDepth, kMaxVariablesPerClause,
    kSharedClauseMaxWords,
};

use crate::ir::literal::Literal;
use crate::ir::symbol_table::SymbolTable;
use crate::ir::term::{TermPtr, TermStore, TermTag};

/// CEP:WHAT: Error cases of the codec.
/// CEP:WHY: CEP&CC Law 6: explicit failure vocabulary; the codec never panics and never returns a wrong clause.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; this type IS the failure vocabulary.
/// CEP:ASSUMES: none.
/// CEP:COST: enum copy.
/// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{word_bound_enforced, rejects_truncated_record, rejects_unknown_tag, rejects_lambda_terms}.
/// CEP:SECURITY: the decode-side variants are the untrusted-record guards.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodecError {
    /// CEP:WHAT: The record exceeds kSharedClauseMaxWords.
    /// CEP:WHY: The sharing path's per-clause memory bound; the exporter skips (counted, design 19.2 degradation).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::word_bound_enforced.
    /// CEP:SECURITY: memory bound.
    TooLarge,
    /// CEP:WHAT: The record ended mid-term (a child word is missing).
    /// CEP:WHY: A forged or truncated record must fail loudly (CEP&CC Law 6) - never a partially decoded clause.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::rejects_truncated_record.
    /// CEP:SECURITY: untrusted-record validation.
    Truncated,
    /// CEP:WHAT: The term tree exceeds kMaxTermDepth.
    /// CEP:WHY: The decode stack is a fixed frame array (no recursion); the depth bound is the frame bound (CEP&CC 22.10).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::rejects_truncated_record.
    /// CEP:SECURITY: denial-of-service bound on decode depth.
    TooDeep,
    /// CEP:WHAT: A node word carries a tag outside the term vocabulary.
    /// CEP:WHY: Forged records degrade loudly.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::rejects_unknown_tag.
    /// CEP:SECURITY: untrusted-record validation.
    UnknownTag,
    /// CEP:WHAT: The record contains a Lambda node (higher-order terms are Phase 5).
    /// CEP:WHY: The FOL codec is total over the Phase 1-4 term vocabulary; Lambda has no interning path yet and claiming support would be a lie (CEP&CC Law 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: Phase 5 adds the interning path and lifts this variant.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::rejects_lambda_terms.
    /// CEP:SECURITY: untrusted-record validation.
    UnsupportedTag,
    /// CEP:WHAT: A literal count, child count, symbol id, or variable id violates its bound.
    /// CEP:WHY: Every header field is validated before use (CEP&CC Law 3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; this variant IS a failure report.
    /// CEP:ASSUMES: none.
    /// CEP:COST: enum value.
    /// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{rejects_truncated_record, rejects_unknown_tag}.
    /// CEP:SECURITY: untrusted-record validation.
    Malformed,
}

// CEP:WHAT: Node-word tag bit width (bits 0-2).
// CEP:WHY: Seven term tags fit three bits; the layout is pinned by the constant assertion below (CEP&CC 38.17 layout pins).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: TermTag discriminants stay below 8.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
const kTagBits: u32 = 3;
// CEP:WHAT: Symbol-field shift (bits 3-34).
// CEP:WHY: Symbol and variable ids are u32 (kMaxSymbolCount and kMaxVariablesPerClause both fit).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
const kSymbolShift: u32 = 3;
// CEP:WHAT: Child-count shift (bits 35-44).
// CEP:WHY: kMaxSymbolArity (32) and the fixed-arity tags (2) fit ten bits.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: child counts <= 1023.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
const kChildShift: u32 = 35;

// CEP:WHAT: Packs one node word.
// CEP:WHY: One place defines the layout (CEP&CC 11.3); encode and the layout test share it.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: tag < 8, symbol < 2^32, children < 1024.
// CEP:COST: shifts and masks.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
fn pack_node(tag: u64, symbol: u64, children: u64) -> u64 {
    (tag & ((1 << kTagBits) - 1))
        | ((symbol << kSymbolShift) & (0xFFFF_FFFFu64 << kSymbolShift))
        | ((children << kChildShift) & (0x3FFu64 << kChildShift))
}

// CEP:WHAT: Unpacks one node word.
// CEP:WHY: The decode-side inverse of pack_node.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: the word came from pack_node (or is validated against the masks).
// CEP:COST: shifts and masks.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
// CEP:SECURITY: none.
fn unpack_node(word: u64) -> (u64, u64, u64) {
    let tag = word & ((1 << kTagBits) - 1);
    let symbol = (word >> kSymbolShift) & 0xFFFF_FFFF;
    let children = (word >> kChildShift) & 0x3FF;
    (tag, symbol, children)
}

// CEP:WHAT: Encodes one clause into out; returns the word count.
// CEP:WHY: Spec 13 section 4: word 0 = [total words:16][literal count:16][reserved:32]; then per literal one polarity word ([polarity:1][reserved:63]) followed by the atom's prefix node words (children before parents is wrong - the prefix order is parent first, then each child subtree left to right; the decoder rebuilds bottom-up through its frame stack); the explicit DFS stack keeps the walk non-recursive; the budget check on every word keeps the record bounded.
// CEP:STATUS: complete
// CEP:FAILURE: returns TooLarge when the words exceed kSharedClauseMaxWords (the exporter skips and counts).
// CEP:ASSUMES: literals.len() <= kMaxClauseLiterals; atoms interned by the given store.
// CEP:COST: O(term tree nodes); bench CEP-BENCH-0035.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, word_bound_enforced, header_layout_pinned}; property/concurrency_property_test.rs::codec_roundtrip_property.
// CEP:SECURITY: node budget enforced per word.
pub fn encode_clause(
    terms: &TermStore,
    literals: &[Literal],
    out: &mut [u64],
) -> Result<usize, CodecError> {
    if literals.len() > kMaxClauseLiterals as usize {
        return Err(CodecError::TooLarge);
    }
    if out.len() < kSharedClauseMaxWords {
        return Err(CodecError::TooLarge);
    }
    // CEP:WHAT: Write cursor (word 0 reserved for the header, filled at the end).
    // CEP:WHY: The total word count is known only after the walk; reserving slot 0 keeps the header at a fixed position for the pool's length extraction (Spec 13 section 4).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: out has at least kSharedClauseMaxWords slots.
    // CEP:COST: constant.
    // CEP:EVIDENCE: unit/hot/clause_codec_test.rs::header_layout_pinned.
    // CEP:SECURITY: none.
    let mut cursor: usize = 1;
    for literal in literals.iter() {
        if cursor >= kSharedClauseMaxWords {
            return Err(CodecError::TooLarge);
        }
        let polarity = if literal.is_positive() { 1u64 } else { 0u64 };
        out[cursor] = polarity;
        cursor += 1;
        // Explicit DFS over the atom: (node, next child cursor).
        let mut stack: [(TermPtr, u16); kMaxTermDepth as usize] =
            [(TermPtr::invalid(), 0); kMaxTermDepth as usize];
        let mut stack_len: usize = 0;
        let mut top = literal.atom();
        let mut next_child: u16 = 0;
        // CEP:WHAT: Whether the current node still needs its word written (first visit).
        // CEP:WHY: The DFS pops back into parents to continue their child scans; a resumed parent must NOT re-emit its node word or the prefix sequence would duplicate interior nodes and desynchronize the decoder (Spec 13 section 4's tree-encoding lemma requires exactly one word per node).
        // CEP:STATUS: complete
        // CEP:FAILURE: none.
        // CEP:ASSUMES: none.
        // CEP:COST: 1 byte.
        // CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, header_layout_pinned}.
        // CEP:SECURITY: none.
        let mut emit = true;
        loop {
            let view = match terms.term(top) {
                Ok(view) => view,
                Err(_) => return Err(CodecError::Malformed),
            };
            if emit {
                if cursor >= kSharedClauseMaxWords {
                    return Err(CodecError::TooLarge);
                }
                out[cursor] = pack_node(
                    view.tag() as u64,
                    view.symbol() as u64,
                    view.child_count() as u64,
                );
                cursor += 1;
            }
            let children = view.child_count();
            // CEP:WHAT: Descend into the first unvisited child (single descent; the stack saves the resume cursor).
            // CEP:WHY: Mirrors the splitter's walk discipline (Spec 13 section 4); the child needs its word emitted (emit = true), the resumed parent does not.
            // CEP:STATUS: complete
            // CEP:FAILURE: depth overflow returns TooDeep.
            // CEP:ASSUMES: children > next_child on this path.
            // CEP:COST: one child read per descent.
            // CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, rejects_truncated_record}.
            // CEP:SECURITY: none.
            if next_child < children {
                let child = match view.child(next_child) {
                    Ok(child) => child,
                    Err(_) => return Err(CodecError::Malformed),
                };
                if stack_len >= stack.len() {
                    return Err(CodecError::TooDeep);
                }
                stack[stack_len] = (top, next_child + 1);
                stack_len += 1;
                top = child;
                next_child = 0;
                emit = true;
            } else {
                if stack_len == 0 {
                    break;
                }
                stack_len -= 1;
                let (parent, resume) = stack[stack_len];
                top = parent;
                next_child = resume;
                emit = false;
            }
        }
    }
    if cursor > 0xFFFF {
        return Err(CodecError::TooLarge);
    }
    out[0] = (cursor as u64 & 0xFFFF) | ((literals.len() as u64 & 0xFFFF) << 16);
    Ok(cursor)
}

// CEP:WHAT: One decode frame: the node being rebuilt, its symbol, the expected child count, the collected child pointers, and the next child slot.
// CEP:WHY: The bottom-up rebuild needs each parent's children before interning the parent; the frame array replaces recursion with a fixed stack (CEP&CC 22.10).
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: child counts <= kMaxSymbolArity (validated before frame use).
// CEP:COST: about 150 bytes per frame.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, rejects_truncated_record}.
// CEP:SECURITY: child-count validation bounds the frame's child array use.
#[derive(Clone, Copy)]
struct DecodeFrame {
    tag: u64,
    symbol: u64,
    child_count: u16,
    children: [TermPtr; kMaxSymbolArity as usize],
    filled: u16,
}

// CEP:WHAT: Decodes one record into interned literals; returns the literal count.
// CEP:WHY: Spec 13 section 4 decode: validate the header (word count, literal count), then per literal read the polarity word and rebuild the atom through the frame stack (children first: a leaf interns immediately and fills its parent's slot; a completed parent interns through the store's hash-consing, restoring sharing); every tag, child count, symbol id, and variable id is validated before use - a forged record fails loudly, never decodes to a corrupt clause.
// CEP:STATUS: complete
// CEP:FAILURE: returns Truncated/TooDeep/UnknownTag/UnsupportedTag/Malformed on bad records; the receiving store's intern errors map to Malformed.
// CEP:ASSUMES: the receiving symbol table matches the encoder's symbol list order (the portfolio contract); out_literals has at least kMaxClauseLiterals slots.
// CEP:COST: O(nodes) with one intern per node; bench CEP-BENCH-0035.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, rejects_truncated_record, rejects_unknown_tag, rejects_lambda_terms}; property/concurrency_property_test.rs::codec_roundtrip_property.
// CEP:SECURITY: untrusted-record validation at every field.
pub fn decode_clause(
    record: &[u64],
    terms: &TermStore,
    symbols: &SymbolTable,
    out_literals: &mut [Literal],
) -> Result<usize, CodecError> {
    if record.is_empty() || record.len() > kSharedClauseMaxWords {
        return Err(CodecError::Truncated);
    }
    let total = (record[0] & 0xFFFF) as usize;
    let literal_count = ((record[0] >> 16) & 0xFFFF) as usize;
    if total < 1 || total > record.len() || literal_count > kMaxClauseLiterals as usize {
        return Err(CodecError::Malformed);
    }
    if literal_count > out_literals.len() {
        return Err(CodecError::Malformed);
    }
    let mut cursor: usize = 1;
    for slot in out_literals.iter_mut().take(literal_count) {
        if cursor >= total {
            return Err(CodecError::Truncated);
        }
        let polarity_word = record[cursor];
        cursor += 1;
        if polarity_word > 1 {
            return Err(CodecError::Malformed);
        }
        let atom = decode_atom(record, &mut cursor, total, terms, symbols)?;
        *slot = Literal::new(atom, polarity_word == 1);
    }
    if cursor != total {
        return Err(CodecError::Malformed);
    }
    Ok(literal_count)
}

// CEP:WHAT: Decodes one atom (the prefix node words from cursor) into an interned TermPtr.
// CEP:WHY: The frame-stack rebuild: a node word pushes a frame; each completed child fills the frame's next slot; a full frame interns its node and hands the pointer to its parent (or returns it at the root); the fixed frame array of kMaxTermDepth entries bounds depth without recursion.
// CEP:STATUS: complete
// CEP:FAILURE: returns the codec errors on bad words; intern failures map to Malformed.
// CEP:ASSUMES: cursor < total on entry.
// CEP:COST: O(nodes of the atom).
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, rejects_truncated_record, rejects_unknown_tag, rejects_lambda_terms}.
// CEP:SECURITY: validates tag, child count, symbol id, and variable id before any intern.
fn decode_atom(
    record: &[u64],
    cursor: &mut usize,
    total: usize,
    terms: &TermStore,
    symbols: &SymbolTable,
) -> Result<TermPtr, CodecError> {
    // CEP:WHAT: The frame stack (kMaxTermDepth frames).
    // CEP:WHY: Bounded rebuild state; TooDeep at the bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: TooDeep when the stack would overflow.
    // CEP:ASSUMES: depth <= kMaxTermDepth for legal terms (the interning bound).
    // CEP:COST: 150 bytes x 128 frames on the stack.
    // CEP:EVIDENCE: unit/hot/clause_codec_test.rs::rejects_truncated_record.
    // CEP:SECURITY: depth bound.
    let mut frames: [DecodeFrame; kMaxTermDepth as usize] = [DecodeFrame {
        tag: 0,
        symbol: 0,
        child_count: 0,
        children: [TermPtr::invalid(); kMaxSymbolArity as usize],
        filled: 0,
    }; kMaxTermDepth as usize];
    let mut frames_len: usize = 0;
    loop {
        // Read and validate one node word, push its frame.
        if *cursor >= total {
            return Err(CodecError::Truncated);
        }
        let (tag, symbol, child_count) = unpack_node(record[*cursor]);
        *cursor += 1;
        match tag {
            value if value == TermTag::Variable as u64 => {
                if symbol >= kMaxVariablesPerClause as u64 || child_count != 0 {
                    return Err(CodecError::Malformed);
                }
            }
            value if value == TermTag::Function as u64 || value == TermTag::Predicate as u64 => {
                // Zero-arity functions (constants) and predicates (propositions) are
                // legal; the receiving symbol table validates the arity against the
                // declared profile at intern time (the second validation layer).
                if symbol >= mapt_config::limits::kMaxSymbolCount as u64
                    || child_count > kMaxSymbolArity as u64
                {
                    return Err(CodecError::Malformed);
                }
            }
            value if value == TermTag::Equality as u64 || value == TermTag::Application as u64 => {
                if child_count != 2 {
                    return Err(CodecError::Malformed);
                }
            }
            value if value == TermTag::Sort as u64 => {
                if child_count != 0 || symbol >= mapt_config::limits::kMaxSymbolCount as u64 {
                    return Err(CodecError::Malformed);
                }
            }
            value if value == TermTag::Lambda as u64 => {
                return Err(CodecError::UnsupportedTag);
            }
            _ => return Err(CodecError::UnknownTag),
        }
        if frames_len >= frames.len() {
            return Err(CodecError::TooDeep);
        }
        frames[frames_len].tag = tag;
        frames[frames_len].symbol = symbol;
        frames[frames_len].child_count = child_count as u16;
        frames[frames_len].filled = 0;
        frames_len += 1;
        // Fill frames bottom-up until the root completes.
        loop {
            let frame_index = frames_len - 1;
            if frames[frame_index].filled < frames[frame_index].child_count {
                // The next child subtree is read from the record (outer loop continues).
                break;
            }
            // Frame complete: intern it.
            let handle = intern_frame(&frames[frame_index], terms, symbols)?;
            frames_len -= 1;
            if frames_len == 0 {
                return Ok(handle);
            }
            let parent_index = frames_len - 1;
            if frames[parent_index].filled >= frames[parent_index].child_count {
                return Err(CodecError::Malformed);
            }
            frames[parent_index].children[frames[parent_index].filled as usize] = handle;
            frames[parent_index].filled += 1;
        }
    }
}

// CEP:WHAT: Interns one completed decode frame into the receiving store.
// CEP:WHY: The tag-dispatched construction: Variable/Function/Predicate/Equality/Application/Sort map onto the store's interning API; Lambda is rejected by the decoder before reaching here; intern errors (unknown symbol, arity mismatch) map to Malformed (a record inconsistent with the receiving table is a contract violation, not a store bug).
// CEP:STATUS: complete
// CEP:FAILURE: returns Malformed on intern errors.
// CEP:ASSUMES: the frame passed validation.
// CEP:COST: one intern.
// CEP:EVIDENCE: unit/hot/clause_codec_test.rs::{roundtrip_preserves_literals, rejects_unknown_tag}.
// CEP:SECURITY: symbol ids validated against the receiving table by the intern itself.
fn intern_frame(
    frame: &DecodeFrame,
    terms: &TermStore,
    symbols: &SymbolTable,
) -> Result<TermPtr, CodecError> {
    let result = if frame.tag == TermTag::Variable as u64 {
        terms.intern_var(frame.symbol as u32)
    } else if frame.tag == TermTag::Function as u64 {
        terms.intern_fun(
            symbols,
            frame.symbol as u32,
            &frame.children[..frame.child_count as usize],
        )
    } else if frame.tag == TermTag::Predicate as u64 {
        terms.intern_pred(
            symbols,
            frame.symbol as u32,
            &frame.children[..frame.child_count as usize],
        )
    } else if frame.tag == TermTag::Equality as u64 {
        terms.intern_eq(symbols, frame.children[0], frame.children[1])
    } else if frame.tag == TermTag::Application as u64 {
        terms.intern_app(symbols, frame.children[0], frame.children[1])
    } else {
        terms.intern_sort(frame.symbol as u32)
    };
    result.map_err(|_| CodecError::Malformed)
}
