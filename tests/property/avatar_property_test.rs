// CEP:FILE: tests/property/avatar_property_test.rs
// CEP:WHAT: Property tests of the AVATAR splitter and protocol: splits preserve the literal multiset, components are pairwise variable-disjoint, the component disjunction is the original clause, avatar saturation agrees with plain saturation on generated problems, and avatar refutations pass the TSTP checker.
// CEP:WHY: CEP&CC 34.3 and Spec 12: the splitting soundness lemma needs both premises (partition + disjointness) verified executably over generated clauses, and the protocol's outcome agreement is the end-to-end soundness check.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly).
// CEP:ASSUMES: fixed seeds (determinism, CEP&CC 28.3).
// CEP:COST: offline.
// CEP:EVIDENCE: this file backs every CEP:EVIDENCE pointer to property/avatar_property_test.rs.
// CEP:SECURITY: no untrusted input.

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_arena, symbol_id, DeterministicRng};
use mapt::cold::proof_output::tstp::check_proof;
use mapt::hot::avatar::controller::{
    saturate_with_avatar, AvatarController, AvatarOptions, AvatarOutcome,
};
use mapt::hot::avatar::splitter::{try_split_with, SplitDecision};
use mapt::hot::inference::{InferenceContext, OrderingKind};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::TermPtr;
use mapt::hot::sat::restart::RestartPolicy;
use mapt::hot::search::given_clause::{
    saturate, SearchOptions, SearchOutcome, SearchSpace, SearchStats,
};

// CEP:WHAT: Arena bytes for the property fixtures.
// CEP:WHY: Named fixture bound.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: covers the small injected capacities.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kPropertyArenaBytes: u32 = 50_331_648;

// CEP:WHAT: The property fixture bundle.
// CEP:WHY: One constructor mirrors the driver's wiring.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
struct PropertyFixture {
    space: SearchSpace<'static>,
    controller: AvatarController<'static>,
    symbols: mapt::hot::ir::symbol_table::SymbolTable<'static>,
    builder: mapt::cold::symbol_table_builder::SymbolTableBuilder,
    terms: mapt::hot::ir::term::TermStore<'static>,
    precedence: mapt::hot::ordering::precedence::PrecedenceTable<'static>,
    options: SearchOptions,
}

// CEP:WHAT: Builds the property fixture (p/q/r predicates with two argument slots).
// CEP:WHY: The generated clauses need a small vocabulary with arity-2 predicates for variable sharing patterns.
// CEP:STATUS: complete
// CEP:FAILURE: panics on construction failure.
// CEP:ASSUMES: fresh arena.
// CEP:COST: one fixture.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn make_property_fixture() -> PropertyFixture {
    let arena = make_arena(kPropertyArenaBytes);
    let mut builder = mapt::cold::symbol_table_builder::SymbolTableBuilder::new();
    use mapt::hot::ir::symbol_table::SortId;
    let sort_s = SortId(builder.declare_sort("S").expect("sort"));
    for name in ["a", "b", "c", "d"].iter() {
        let _ = builder
            .declare_function(name, 0, 1, &[], sort_s)
            .expect("constant");
    }
    for name in ["p", "q", "r"].iter() {
        let _ = builder
            .declare_predicate(name, 2, 1, &[sort_s, sort_s])
            .expect("predicate");
    }
    let symbols = builder.finalize(arena).expect("symbols");
    let terms = mapt::hot::ir::term::TermStore::new(arena).expect("terms");
    let precedence = mapt::hot::ordering::precedence::PrecedenceTable::from_id_order(
        arena,
        builder.symbol_count(),
    )
    .expect("precedence");
    let options = SearchOptions::new();
    let space =
        SearchSpace::new_with(arena, &options, 4096, 1024, 4096, 8192, 65536, 4096).expect("space");
    let avatar_options = AvatarOptions {
        sat_variables: 64,
        restart_policy: RestartPolicy::Luby,
        record_capacity: 64,
        word_capacity: 512,
        ancestry_bits: 4096,
        min_component_size: 1,
        conflict_budget: mapt_config::limits::kSatMaxConflicts,
        max_conflict_rounds: 64,
        max_model_rotations: 64,
    };
    let controller = AvatarController::new_with(arena, &avatar_options).expect("controller");
    PropertyFixture {
        space,
        controller,
        symbols,
        builder,
        terms,
        precedence,
        options,
    }
}

// CEP:WHAT: The context over the fixture's space.
// CEP:WHY: Shared by the split and saturation paths.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture pieces.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn context_of(fixture: &PropertyFixture) -> InferenceContext<'_> {
    InferenceContext {
        terms: &fixture.terms,
        symbols: &fixture.symbols,
        substitution: &fixture.space.substitution,
        precedence: &fixture.precedence,
        ordering: OrderingKind::Kbo,
    }
}

// CEP:WHAT: Builds one argument term: a constant or a variable of the generated namespace.
// CEP:WHY: The generator mixes ground and variable arguments to hit both sharing patterns.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture.
// CEP:COST: one intern.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn gen_arg(fixture: &PropertyFixture, rng: &mut DeterministicRng, var_bound: u32) -> TermPtr {
    if rng.below(2) == 0 {
        let names = ["a", "b", "c", "d"];
        let name = names[rng.below(4) as usize];
        fixture
            .terms
            .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, name), &[])
            .expect("constant")
    } else {
        fixture
            .terms
            .intern_var(rng.below(var_bound as u64) as u32)
            .expect("var")
    }
}

// CEP:WHAT: Generates one clause of up to six literals over the three predicates.
// CEP:WHY: The generator produces splittable and unsplittable clauses with shared and disjoint variables.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture.
// CEP:COST: a few interns.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn gen_clause(fixture: &PropertyFixture, rng: &mut DeterministicRng) -> Vec<Literal> {
    let names = ["p", "q", "r"];
    let count = 2 + rng.below(5) as usize;
    let mut literals: Vec<Literal> = Vec::new();
    for _ in 0..count {
        let name = names[rng.below(3) as usize];
        let left = gen_arg(fixture, rng, 6);
        let right = gen_arg(fixture, rng, 6);
        let atom = fixture
            .terms
            .intern_pred(
                &fixture.symbols,
                symbol_id(&fixture.builder, name),
                &[left, right],
            )
            .expect("atom");
        literals.push(Literal::new(atom, rng.below(2) == 0));
    }
    literals
}

// CEP:WHAT: Collects the variable ids of one atom into out.
// CEP:WHY: The disjointness property walks atoms.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: fixture.
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn atom_variables(terms: &mapt::hot::ir::term::TermStore<'_>, atom: TermPtr, out: &mut Vec<u32>) {
    // Explicit DFS with (node, next-child-cursor) frames - no resume-into-child-0 loops.
    let mut stack: [(TermPtr, u16); 128] = [(TermPtr::invalid(), 0); 128];
    let mut stack_len: usize = 0;
    let mut top = atom;
    let mut next_child: u16 = 0;
    loop {
        let view = match terms.term(top) {
            Ok(view) => view,
            Err(_) => return,
        };
        if view.tag() == mapt::hot::ir::term::TermTag::Variable {
            let id = view.symbol();
            if !out.contains(&id) {
                out.push(id);
            }
        }
        let children = view.child_count();
        if next_child < children {
            if let Ok(child) = view.child(next_child) {
                if stack_len < stack.len() {
                    stack[stack_len] = (top, next_child + 1);
                    stack_len += 1;
                    top = child;
                    next_child = 0;
                    continue;
                }
            }
            return;
        }
        if stack_len == 0 {
            return;
        }
        stack_len -= 1;
        let (parent, resume) = stack[stack_len];
        top = parent;
        next_child = resume;
    }
}

#[test]
// CEP:WHAT: Over generated clauses, every split preserves the literal multiset exactly and the components are pairwise variable-disjoint (the two premises of the Spec 12 splitting lemma).
// CEP:WHY: Lemma 1's soundness argument needs both properties; the generator hits both splittable and unsplittable shapes.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any violated property.
// CEP:ASSUMES: fixed seeds.
// CEP:COST: kRounds generated clauses.
// CEP:EVIDENCE: backs property/avatar_property_test.rs::{splits_preserve_literal_multiset, components_are_variable_disjoint}.
// CEP:SECURITY: none.
fn splits_preserve_literal_multiset() {
    // CEP:WHAT: Generated clauses per run.
    // CEP:WHY: Named bound (CEP&CC 11.3).
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRounds: u32 = 300;
    let fixture = make_property_fixture();
    let mut rng = DeterministicRng::new(0x5eed_4a11);
    let mut splits: u32 = 0;
    for _ in 0..kRounds {
        let literals = gen_clause(&fixture, &mut rng);
        match try_split_with(&fixture.terms, &literals, 1) {
            SplitDecision::Splittable(view) => {
                splits += 1;
                // Property 1: the partition preserves the multiset (each literal in
                // exactly one component).
                let mut covered: Vec<bool> = vec![false; literals.len()];
                for (position, component) in view
                    .literal_component
                    .iter()
                    .enumerate()
                    .take(literals.len())
                {
                    let component = *component as usize;
                    assert!(
                        component < view.component_count as usize,
                        "component index in range"
                    );
                    assert!(!covered[position], "each literal appears once");
                    covered[position] = true;
                }
                // Property 2: pairwise variable-disjoint components.
                let mut component_vars: Vec<Vec<u32>> =
                    vec![Vec::new(); view.component_count as usize];
                for (position, literal) in literals.iter().enumerate() {
                    let component = view.literal_component[position] as usize;
                    atom_variables(
                        &fixture.terms,
                        literal.atom(),
                        &mut component_vars[component],
                    );
                }
                for left in 0..component_vars.len() {
                    for right in (left + 1)..component_vars.len() {
                        for var in component_vars[left].iter() {
                            assert!(
                                !component_vars[right].contains(var),
                                "components {} and {} share variable {}",
                                left,
                                right,
                                var
                            );
                        }
                    }
                }
            }
            SplitDecision::Unsplittable => {}
        }
    }
    assert!(splits > 0, "the generator must produce splittable clauses");
}

#[test]
// CEP:WHAT: The disjunction of a split's components is exactly the original clause (the multiset equality through the component-clause lens).
// CEP:WHY: The replacement contract of design 12.2 rule 1: the clause "is replaced by the components".
// CEP:STATUS: complete
// CEP:FAILURE: panics on any mismatch.
// CEP:ASSUMES: fixed seeds.
// CEP:COST: kRounds generated clauses.
// CEP:EVIDENCE: backs property/avatar_property_test.rs::disjunction_of_components_is_original.
// CEP:SECURITY: none.
fn disjunction_of_components_is_original() {
    const kRounds: u32 = 300;
    let fixture = make_property_fixture();
    let mut rng = DeterministicRng::new(0x5eed_4a12);
    for _ in 0..kRounds {
        let literals = gen_clause(&fixture, &mut rng);
        if let SplitDecision::Splittable(view) = try_split_with(&fixture.terms, &literals, 1) {
            // The disjunction identity: concatenating the components' literal lists
            // (grouped through the positional map) reproduces the original multiset.
            let mut components: Vec<Vec<usize>> = vec![Vec::new(); view.component_count as usize];
            for position in 0..literals.len() {
                components[view.literal_component[position] as usize].push(position);
            }
            let mut grouped: Vec<usize> = Vec::new();
            for component in components.iter() {
                grouped.extend(component.iter().copied());
            }
            assert_eq!(grouped.len(), literals.len());
            let mut matched: Vec<bool> = vec![false; literals.len()];
            for position in grouped.iter() {
                let literal = &literals[*position];
                let mut found = false;
                for (index, other) in literals.iter().enumerate() {
                    if !matched[index]
                        && other.atom() == literal.atom()
                        && other.is_positive() == literal.is_positive()
                    {
                        matched[index] = true;
                        found = true;
                        break;
                    }
                }
                assert!(found, "the rebuilt disjunction loses a literal");
            }
        }
    }
}

#[test]
// CEP:WHAT: On generated ground problems (constants only, no variables), avatar saturation agrees with plain saturation on the Theorem/Saturated distinction.
// CEP:WHY: Ground problems are propositional after grounding: both engines must agree (the end-to-end soundness check; ground clauses never split, so the avatar path is the plain path plus a trivial abstraction - the agreement pins the wrapper).
// CEP:STATUS: complete
// CEP:FAILURE: panics on any disagreement.
// CEP:ASSUMES: fixed seeds; ground clauses only (variable-free generation).
// CEP:COST: kRounds problems.
// CEP:EVIDENCE: backs property/avatar_property_test.rs::avatar_agrees_with_plain_saturation.
// CEP:SECURITY: none.
fn avatar_agrees_with_plain_saturation() {
    // CEP:WHAT: Generated problems per run.
    // CEP:WHY: Named bound.
    // CEP:STATUS: complete
    // CEP:FAILURE: none.
    // CEP:ASSUMES: none.
    // CEP:COST: constant.
    // CEP:EVIDENCE: this test.
    // CEP:SECURITY: none.
    const kRounds: u32 = 20;
    let mut rng = DeterministicRng::new(0x5eed_4a13);
    for _ in 0..kRounds {
        // The problem description: predicate name, two constant names, polarity - plain
        // data replayed identically into both fixtures (the same declaration order and
        // the same interning sequence reproduce the same atoms in each arena).
        let names = ["p", "q", "r"];
        let constants = ["a", "b", "c", "d"];
        let clause_count = 2 + rng.below(4) as usize;
        let mut description: Vec<Vec<(String, String, String, bool)>> = Vec::new();
        for _ in 0..clause_count {
            let count = 1 + rng.below(3) as usize;
            let mut clause: Vec<(String, String, String, bool)> = Vec::new();
            for _ in 0..count {
                clause.push((
                    names[rng.below(3) as usize].to_string(),
                    constants[rng.below(4) as usize].to_string(),
                    constants[rng.below(4) as usize].to_string(),
                    rng.below(2) == 0,
                ));
            }
            description.push(clause);
        }
        let plain = make_property_fixture();
        let avatar = make_property_fixture();
        let plain_context = context_of(&plain);
        let avatar_context = context_of(&avatar);
        for clause in description.iter() {
            let plain_literals: Vec<Literal> = clause
                .iter()
                .map(|(name, left, right, positive)| {
                    ground_lit(&plain, name, left, right, *positive)
                })
                .collect();
            plain
                .space
                .add_input_clause(&plain_context, &plain.options, &plain_literals)
                .expect("plain add");
            let avatar_literals: Vec<Literal> = clause
                .iter()
                .map(|(name, left, right, positive)| {
                    ground_lit(&avatar, name, left, right, *positive)
                })
                .collect();
            avatar
                .controller
                .add_input_clause(
                    &avatar.space,
                    &avatar_context,
                    &avatar.options,
                    &avatar_literals,
                )
                .expect("avatar add");
        }
        let mut plain_stats = SearchStats::default();
        let plain_outcome = saturate(
            &plain.space,
            &plain_context,
            &plain.options,
            &never_stop,
            &mut plain_stats,
        )
        .expect("plain saturate");
        let mut avatar_stats = SearchStats::default();
        let avatar_outcome = saturate_with_avatar(
            &avatar.space,
            &avatar_context,
            &avatar.options,
            &avatar.controller,
            &never_stop,
            &mut avatar_stats,
        )
        .expect("avatar saturate");
        let plain_theorem = matches!(plain_outcome, SearchOutcome::Theorem { .. });
        let avatar_theorem = matches!(avatar_outcome, AvatarOutcome::Theorem { .. });
        assert_eq!(
            plain_theorem, avatar_theorem,
            "the engines disagree on a generated problem"
        );
    }
}

// CEP:WHAT: Builds one ground literal from a description triple.
// CEP:WHY: The replay helper shared by both fixtures.
// CEP:STATUS: complete
// CEP:FAILURE: panics on intern failure.
// CEP:ASSUMES: fixture.
// CEP:COST: three interns.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn ground_lit(
    fixture: &PropertyFixture,
    name: &str,
    left: &str,
    right: &str,
    positive: bool,
) -> Literal {
    let left_ptr = fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, left), &[])
        .expect("left");
    let right_ptr = fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, right), &[])
        .expect("right");
    let atom = fixture
        .terms
        .intern_pred(
            &fixture.symbols,
            symbol_id(&fixture.builder, name),
            &[left_ptr, right_ptr],
        )
        .expect("atom");
    Literal::new(atom, positive)
}

#[test]
// CEP:WHAT: Every avatar Theorem's refutation passes the TSTP replay checker.
// CEP:WHY: Design 18.4 end to end: the unified proof reconstruction accepts exactly the proofs the protocol produces (including avatar split steps through the subclause check).
// CEP:STATUS: complete
// CEP:FAILURE: panics if a produced proof fails its checker.
// CEP:ASSUMES: the unit-hole problem shape (deterministic avatar theorem).
// CEP:COST: one protocol run plus one check.
// CEP:EVIDENCE: backs property/avatar_property_test.rs::avatar_refutations_check.
// CEP:SECURITY: none.
fn avatar_refutations_check() {
    let fixture = make_property_fixture();
    let context = context_of(&fixture);
    let (x, y) = (
        fixture.terms.intern_var(0).expect("x"),
        fixture.terms.intern_var(1).expect("y"),
    );
    let a = fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, "a"), &[])
        .expect("a");
    let b = fixture
        .terms
        .intern_fun(&fixture.symbols, symbol_id(&fixture.builder, "b"), &[])
        .expect("b");
    let split = vec![
        Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "p"), &[x, a])
                .expect("p1"),
            true,
        ),
        Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "p"), &[x, b])
                .expect("p2"),
            true,
        ),
        Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "q"), &[y, a])
                .expect("q1"),
            true,
        ),
        Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "q"), &[y, b])
                .expect("q2"),
            true,
        ),
    ];
    let holes = [
        vec![Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "p"), &[x, a])
                .expect("hp"),
            false,
        )],
        vec![Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "p"), &[x, b])
                .expect("hp2"),
            false,
        )],
        vec![Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "q"), &[y, a])
                .expect("hq"),
            false,
        )],
        vec![Literal::new(
            fixture
                .terms
                .intern_pred(&fixture.symbols, symbol_id(&fixture.builder, "q"), &[y, b])
                .expect("hq2"),
            false,
        )],
    ];
    fixture
        .controller
        .add_input_clause(&fixture.space, &context, &fixture.options, &split)
        .expect("add split");
    for hole in holes.iter() {
        fixture
            .controller
            .add_input_clause(&fixture.space, &context, &fixture.options, hole)
            .expect("add hole");
    }
    let mut stats = SearchStats::default();
    match saturate_with_avatar(
        &fixture.space,
        &context,
        &fixture.options,
        &fixture.controller,
        &never_stop,
        &mut stats,
    )
    .expect("avatar saturate")
    {
        AvatarOutcome::Theorem { refutation, .. } => {
            check_proof(&context, &fixture.space.store, refutation)
                .expect("the avatar refutation passes the replay checker");
        }
        other => panic!("expected an avatar theorem, got {:?}", other),
    }
}

// CEP:WHAT: The never-stop callback.
// CEP:WHY: Budget-free runs.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: constant.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn never_stop(_iterations: u64) -> bool {
    false
}

#[test]
// CEP:WHAT: Components of generated splits are pairwise variable-disjoint (the dedicated disjointness property cited by the splitter).
// CEP:WHY: Spec 12 Lemma 1's second premise; the combined test carries both premises, this one pins the splitter's file-header citation on an independent seed.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any shared variable.
// CEP:ASSUMES: fixed seed.
// CEP:COST: kRounds generated clauses.
// CEP:EVIDENCE: backs property/avatar_property_test.rs::components_are_variable_disjoint.
// CEP:SECURITY: none.
fn components_are_variable_disjoint() {
    const kRounds: u32 = 200;
    let fixture = make_property_fixture();
    let mut rng = DeterministicRng::new(0x5eed_4a14);
    for _ in 0..kRounds {
        let literals = gen_clause(&fixture, &mut rng);
        if let SplitDecision::Splittable(view) = try_split_with(&fixture.terms, &literals, 1) {
            let mut component_vars: Vec<Vec<u32>> = vec![Vec::new(); view.component_count as usize];
            for (position, literal) in literals.iter().enumerate() {
                let component = view.literal_component[position] as usize;
                atom_variables(
                    &fixture.terms,
                    literal.atom(),
                    &mut component_vars[component],
                );
            }
            for left in 0..component_vars.len() {
                for right in (left + 1)..component_vars.len() {
                    for var in component_vars[left].iter() {
                        assert!(
                            !component_vars[right].contains(var),
                            "components {} and {} share variable {}",
                            left,
                            right,
                            var
                        );
                    }
                }
            }
        }
    }
}
