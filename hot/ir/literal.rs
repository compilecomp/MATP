// CEP:FILE: hot/ir/literal.rs
// CEP:WHAT: Literal representation: a polarity flag, an atom handle, selection/maximality flags, and a theory-flag byte.
// CEP:WHY: Design 5.2: literals are the unit of resolution and superposition; selected/maximal are cached per literal (computed lazily when a clause enters the active set) so ordering comparisons are not repeated during inference generation. An 8-byte struct keeps whole literal arrays cache-friendly (CEP&CC 23.6.2).
// CEP:CLASS: CEP-0
// CEP:HPC-CLASS: HPC-0
// CEP:STATUS: complete
// CEP:FAILURE: constructors validate nothing that can fail (the atom handle is opaque and validated by the term store); accessors cannot fail; never panics.
// CEP:ASSUMES: the atom handle references a term produced by the same store's TermStore; polarity true means positive literal.
// CEP:COST: 8-byte copy type; every operation is a load or a flag flip; no allocation.
// CEP:EVIDENCE: unit/hot/clause_test.rs (literals are exercised through clause construction); unit/hot/term_test.rs.
// CEP:SECURITY: no untrusted input reaches this type except through validated construction paths.
// CEP:OPTIMAL: target-optimal
// CEP:OPTPROOF: the struct is plain data; negate() is one XOR on the polarity byte; the layout is pinned by static assertions below.

use crate::ir::term::TermPtr;

/// CEP:WHAT: Theory and AVATAR flag bits for literals (bit positions in Literal::theory_flags).
/// CEP:WHY: Design 5.2 lists a theory-tag byte; named bit constants replace magic masks (CEP&CC 11.3).
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none.
/// CEP:ASSUMES: bits 0-2 carry the AVATAR component membership, bit 3 marks theory-laden literals; values are Phase 4/5 hooks.
/// CEP:COST: compile-time only.
/// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
/// CEP:SECURITY: none.
pub struct LiteralFlags;

impl LiteralFlags {
    /// CEP:WHAT: Bit mask extracting the AVATAR component ID (bits 0-2).
    /// CEP:WHY: Design 5.2 stores component membership in the literal flags.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: component IDs 0-7.
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: reserved for Phase 4; ticket CEP-1011.
    /// CEP:SECURITY: none.
    pub const kAvatarComponentMask: u8 = 0x07;
    /// CEP:WHAT: Bit marking a theory-laden literal.
    /// CEP:WHY: Design 5.2 theory tag.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the coupling invariant: bit 3 is set exactly when the theory-tag nibble (bits 4-7) is not `TheoryTag::None`; the sanctioned setters maintain it.
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs; ticket CEP-1012.
    /// CEP:SECURITY: none.
    pub const kTheoryLaden: u8 = 0x08;
    /// CEP:WHAT: Bit mask extracting the theory tag nibble (bits 4-7).
    /// CEP:WHY: Design 5.2 reserves the rest of the flags byte for the theory identity; the nibble encodes the design 13.1 theory vocabulary (CEP-1012).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: encodings 7-15 of the nibble are reserved and rejected on decoded records.
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub const kTheoryTagMask: u8 = 0xF0;
    /// CEP:WHAT: Bit shift of the theory tag nibble.
    /// CEP:WHY: Named shift for the nibble extraction (CEP&CC 11.3).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time only.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub const kTheoryTagShift: u32 = 4;
}

/// CEP:WHAT: The theory tag vocabulary of the literal flags byte (bits 4-7), enumerating the extensional theories of design 13.1.
/// CEP:WHY: Design 5.2 reserves a theory tag in the literal flags byte; the theory layer (design 13, later phases) routes theory-laden literals by this identity. Uninterpreted functions are deliberately not a tag: they are the FOL background itself, and untagged literals are exactly the uninterpreted ones.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: from_bits returns None (the Option) for the reserved encodings 7-15; to_bits is total.
/// CEP:ASSUMES: the encoding fits the 4-bit nibble; the coupling invariant ties a non-None tag to LiteralFlags::kTheoryLaden.
/// CEP:COST: enum copy; conversions are bit operations.
/// CEP:EVIDENCE: unit/hot/theory_flag_test.rs; ticket CEP-1012.
/// CEP:SECURITY: decoded codec records validate the vocabulary before construction (Spec 13 section 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TheoryTag {
    /// CEP:WHAT: No theory delegation; the literal is uninterpreted FOL.
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    None = 0,
    /// CEP:WHAT: Linear integer arithmetic (design 13.1 row 1).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    LinearInteger = 1,
    /// CEP:WHAT: Linear real arithmetic (design 13.1 row 2).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    LinearReal = 2,
    /// CEP:WHAT: Non-linear arithmetic within the bounded heuristic scope (design 13.1 row 3).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    NonLinearArithmetic = 3,
    /// CEP:WHAT: Bitvectors (design 13.1 row 4).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    Bitvectors = 4,
    /// CEP:WHAT: Arrays (design 13.1 row 5).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    Arrays = 5,
    /// CEP:WHAT: Algebraic datatypes (design 13.1 row 6).
    /// CEP:WHY: See the enum docs.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    AlgebraicDatatypes = 6,
}

impl TheoryTag {
    /// CEP:WHAT: Encodes the tag into its 4-bit nibble value.
    /// CEP:WHY: The flags byte stores the nibble, not the enum.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: compile-time.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub fn to_bits(self) -> u8 {
        self as u8
    }

    /// CEP:WHAT: Decodes a 4-bit nibble into the tag; the reserved encodings 7-15 decode to None (the Option), never to a variant.
    /// CEP:WHY: Decoded records must reject reserved encodings loudly instead of misreading them (CEP&CC Law 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; the Option IS the reserved-encoding outcome.
    /// CEP:ASSUMES: bits below 16.
    /// CEP:COST: one match.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: reserved encodings never become a tag.
    pub fn from_bits(bits: u8) -> Option<TheoryTag> {
        match bits {
            0 => Some(TheoryTag::None),
            1 => Some(TheoryTag::LinearInteger),
            2 => Some(TheoryTag::LinearReal),
            3 => Some(TheoryTag::NonLinearArithmetic),
            4 => Some(TheoryTag::Bitvectors),
            5 => Some(TheoryTag::Arrays),
            6 => Some(TheoryTag::AlgebraicDatatypes),
            _ => None,
        }
    }
}

/// CEP:WHAT: One literal: atom reference plus polarity and inference-relevant flags.
/// CEP:WHY: Design 5.2 field list as a fixed-layout struct; Copy semantics keep clause sorting and resolution cheap.
/// CEP:CLASS: CEP-0
/// CEP:STATUS: complete
/// CEP:FAILURE: none; plain data with infallible accessors.
/// CEP:ASSUMES: atom handles are produced by the owning term store.
/// CEP:COST: 8 bytes per literal.
/// CEP:EVIDENCE: layout pinned by static assertion; unit/hot/clause_test.rs.
/// CEP:SECURITY: no forged handles: the atom field is private and set only by constructors taking TermPtr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct Literal {
    /// CEP:WHAT: Handle of the atom term (predicate or equality term).
    /// CEP:WHY: Design 5.2: the literal's atom.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: interned by the term store.
    /// CEP:COST: 4 bytes.
    /// CEP:EVIDENCE: unit/hot/term_test.rs.
    /// CEP:SECURITY: private field; only constructors set it.
    atom: TermPtr,
    /// CEP:WHAT: Positive polarity flag (true = positive literal).
    /// CEP:WHY: Complementarity checks in resolution compare polarities (design 10.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    polarity: bool,
    /// CEP:WHAT: Selection flag set by the selection function.
    /// CEP:WHY: Design 5.2: cached to avoid re-running selection during inference generation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: computed lazily when the clause enters the active set (design 5.2).
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    selected: bool,
    /// CEP:WHAT: Maximality flag under the term ordering.
    /// CEP:WHY: Design 5.2: ordered resolution and superposition need maximality; cached per literal.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: computed lazily; ordering arrives in Phase 2 (ticket CEP-1013).
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    maximal: bool,
    /// CEP:WHAT: Theory tag and AVATAR component flags.
    /// CEP:WHY: Design 5.2 flags byte.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: masks in LiteralFlags.
    /// CEP:COST: 1 byte.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    theory_flags: u8,
}

// CEP:WHAT: Literal layout pin.
// CEP:WHY: The struct is embedded in clause headers and crosses to cold printers and later FFI; the size must stay 8 bytes (CEP&CC 22.8, 38.17).
// CEP:STATUS: complete
// CEP:FAILURE: compilation fails on layout drift.
// CEP:ASSUMES: target ABI sizes.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_layout.
// CEP:SECURITY: layout drift is an ABI break.
const _: () = assert!(core::mem::size_of::<Literal>() == 8);

impl Literal {
    /// CEP:WHAT: Constructs a literal from an atom handle and polarity.
    /// CEP:WHY: The single sanctioned constructor keeps flag defaults (unselected, non-maximal, no theory flags) uniform.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: atom was interned by the owning term store.
    /// CEP:COST: 4 stores.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: atom handle is an opaque interned token.
    pub fn new(atom: TermPtr, polarity: bool) -> Literal {
        Literal {
            atom,
            polarity,
            selected: false,
            maximal: false,
            theory_flags: 0,
        }
    }

    /// CEP:WHAT: Returns the atom handle.
    /// CEP:WHY: Inference rules need the atom for unification; printers need it for output.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs.
    /// CEP:SECURITY: none.
    pub fn atom(&self) -> TermPtr {
        self.atom
    }

    /// CEP:WHAT: Returns the polarity (true = positive).
    /// CEP:WHY: Complementarity checks (design 10.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn is_positive(&self) -> bool {
        self.polarity
    }

    /// CEP:WHAT: Returns the complementary literal (same atom, flipped polarity, flags copied).
    /// CEP:WHY: Resolution pairs complementary literals (design 10.2); copying flags keeps selection state consistent through negation.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load + 1 store + 1 XOR-equivalent flip.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    /// CEP:OPTIMAL: target-optimal
    /// CEP:OPTPROOF: negation of a boolean field is a single byte flip; nothing less is possible.
    pub fn negate(&self) -> Literal {
        Literal {
            atom: self.atom,
            polarity: !self.polarity,
            selected: self.selected,
            maximal: self.maximal,
            theory_flags: self.theory_flags,
        }
    }

    /// CEP:WHAT: Returns true when both literals share the atom and differ in polarity.
    /// CEP:WHY: This is the complementarity side condition of binary resolution (design 10.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: both literals come from the same term store (hash-consing makes handle equality atom equality).
    /// CEP:COST: 2 compares.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn is_complementary(&self, other: &Literal) -> bool {
        self.atom == other.atom && self.polarity != other.polarity
    }

    /// CEP:WHAT: Returns the selection flag.
    /// CEP:WHY: Inference legality depends on selection (design 10.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn is_selected(&self) -> bool {
        self.selected
    }

    /// CEP:WHAT: Sets the selection flag.
    /// CEP:WHY: The selection function (Phase 3) marks literals when a clause enters the active set.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 store.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn set_selected(&mut self, selected: bool) {
        self.selected = selected;
    }

    /// CEP:WHAT: Returns the maximality flag.
    /// CEP:WHY: Ordered inference legality (design 10.2).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: computed by the ordering (Phase 2).
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn is_maximal(&self) -> bool {
        self.maximal
    }

    /// CEP:WHAT: Sets the maximality flag.
    /// CEP:WHY: The term ordering (Phase 2) marks maximal literals at active-set entry.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 1 store.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn set_maximal(&mut self, maximal: bool) {
        self.maximal = maximal;
    }

    /// CEP:WHAT: Returns the theory/AVATAR flag byte.
    /// CEP:WHY: Theory reasoning and AVATAR splitting read these bits (Phases 4-5).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: masks in LiteralFlags.
    /// CEP:COST: 1 load.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn theory_flags(&self) -> u8 {
        self.theory_flags
    }

    /// CEP:WHAT: Sets the theory/AVATAR flag byte.
    /// CEP:WHY: AVATAR splitting (Phase 4) tags component membership.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: callers use LiteralFlags masks.
    /// CEP:COST: 1 store.
    /// CEP:EVIDENCE: unit/hot/clause_test.rs::literal_operations.
    /// CEP:SECURITY: none.
    pub fn set_theory_flags(&mut self, theory_flags: u8) {
        self.theory_flags = theory_flags;
    }

    /// CEP:WHAT: Returns the AVATAR component membership tag (bits 0-2; 0 = not a split-component literal).
    /// CEP:WHY: Design 5.2 and ticket CEP-1011: literals of an AVATAR component clause carry the component's membership tag; the tag is a fast per-literal hint - the authoritative component identity is the clause record's split_level (u16), and the 3-bit tag wraps modulo 8 beyond component 7 (Spec 12 section 4).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: tag values 0-7; theory-laden bit is preserved independently.
    /// CEP:COST: 1 load plus 1 mask.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::component_literals_tagged.
    /// CEP:SECURITY: none.
    pub fn avatar_component_tag(&self) -> u8 {
        self.theory_flags & LiteralFlags::kAvatarComponentMask
    }

    /// CEP:WHAT: Sets the AVATAR component membership tag without touching the theory-laden bit.
    /// CEP:WHY: The splitter tags each component clause's literals at creation (CEP-1011); preserving the theory bit keeps the Phase 5 hook intact.
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: tag <= kAvatarComponentMask (values beyond wrap by masking - the caller passes slot mod 8).
    /// CEP:COST: 2 loads, 1 store, 2 masks.
    /// CEP:EVIDENCE: unit/hot/avatar_splitter_test.rs::component_literals_tagged.
    /// CEP:SECURITY: none.
    pub fn set_avatar_component_tag(&mut self, tag: u8) {
        self.theory_flags = (self.theory_flags & !LiteralFlags::kAvatarComponentMask)
            | (tag & LiteralFlags::kAvatarComponentMask);
    }

    /// CEP:WHAT: Returns whether the theory-laden bit (bit 3) is set.
    /// CEP:WHY: Design 5.2 marks literals delegated to the theory layer; the bit is the fast membership test (CEP-1012).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: the coupling invariant (bit 3 set exactly when the tag is not None).
    /// CEP:COST: 1 load plus 1 mask.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub fn is_theory_laden(&self) -> bool {
        self.theory_flags & LiteralFlags::kTheoryLaden != 0
    }

    /// CEP:WHAT: Returns the decoded theory tag (bits 4-7); a reserved nibble decodes to None (the Option).
    /// CEP:WHY: The theory layer reads the identity; reserved encodings must never masquerade as a theory (CEP&CC Law 6).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none; the Option IS the reserved-encoding outcome.
    /// CEP:ASSUMES: the coupling invariant on sanctioned construction paths.
    /// CEP:COST: 1 load, 1 shift, 1 match.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub fn theory_tag(&self) -> Option<TheoryTag> {
        TheoryTag::from_bits(
            (self.theory_flags & LiteralFlags::kTheoryTagMask) >> LiteralFlags::kTheoryTagShift,
        )
    }

    /// CEP:WHAT: Sets the theory tag and maintains the coupling invariant: a non-None tag sets the theory-laden bit, None clears both the nibble and the bit.
    /// CEP:WHY: The single sanctioned writer of the theory identity keeps "theory-laden" and "has a theory tag" one fact (CEP-1012).
    /// CEP:STATUS: complete
    /// CEP:FAILURE: none.
    /// CEP:ASSUMES: none.
    /// CEP:COST: 2 loads, 1 store, 3 masks.
    /// CEP:EVIDENCE: unit/hot/theory_flag_test.rs.
    /// CEP:SECURITY: none.
    pub fn set_theory_tag(&mut self, tag: TheoryTag) {
        let mut flags = self.theory_flags & !LiteralFlags::kTheoryTagMask;
        flags |= (tag.to_bits() << LiteralFlags::kTheoryTagShift) & LiteralFlags::kTheoryTagMask;
        if tag != TheoryTag::None {
            flags |= LiteralFlags::kTheoryLaden;
        } else {
            flags &= !LiteralFlags::kTheoryLaden;
        }
        self.theory_flags = flags;
    }
}
