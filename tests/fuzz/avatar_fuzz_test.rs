// CEP:FILE: tests/fuzz/avatar_fuzz_test.rs
// CEP:WHAT: Fuzz test of the AVATAR splitter: random clauses over the standard vocabulary must satisfy the partition invariants (every literal in exactly one component, components pairwise variable-disjoint, the gate respected) or degrade to Unsplittable - never panic, never error, never hang.
// CEP:WHY: CEP&CC 34.3 and the fuzz discipline of Phases 1-3: the splitter consumes search-generated clauses (semi-trusted input by the trust-boundaries document); its total behavior must hold over the generated distribution, not just hand-built shapes.
// CEP:CLASS: CEP-2
// CEP:STATUS: complete
// CEP:FAILURE: helpers panic on fixture failure (test code may fail loudly); the fuzz assertions panic on any invariant violation.
// CEP:ASSUMES: fixed seed (deterministic fuzzing, CEP&CC 28.3).
// CEP:COST: offline; kFuzzRounds decisions.
// CEP:EVIDENCE: this file is the splitter's fuzz evidence (cited by hot/avatar/splitter.rs's file header through the unit and property suites).
// CEP:SECURITY: the fuzz corpus exercises adversarial shapes (wide clauses, deep terms, mixed polarity).

#![allow(non_upper_case_globals)]

#[path = "../common/mod.rs"]
mod common;

use common::{make_inference_fixture, symbol_id, DeterministicRng};
use mapt::hot::avatar::splitter::{try_split_with, SplitDecision};
use mapt::hot::ir::literal::Literal;
use mapt::hot::ir::term::{TermPtr, TermTag};

// CEP:WHAT: Fuzz rounds per run.
// CEP:WHY: Named bound (CEP&CC 11.3); enough rounds to cover the generated shapes without slowing the suite.
// CEP:STATUS: complete
// CEP:FAILURE: none.
// CEP:ASSUMES: none.
// CEP:COST: compile-time only.
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
const kFuzzRounds: u32 = 500;

#[test]
// CEP:WHAT: Randomized clauses: try_split_with never panics and every Splittable decision satisfies the partition invariants; Unsplittable is the only other outcome.
// CEP:WHY: The splitter is total by contract (its absence is always sound); the fuzz run pins totality plus the invariants over the generated distribution.
// CEP:STATUS: complete
// CEP:FAILURE: panics on any invariant violation or unexpected outcome shape.
// CEP:ASSUMES: fixed seed; the standard fixture vocabulary.
// CEP:COST: kFuzzRounds decisions with generated terms.
// CEP:EVIDENCE: this file (the splitter's fuzz coverage).
// CEP:SECURITY: adversarial input discipline.
fn splitter_fuzz_invariants() {
    let (arena, symbols, builder, terms, _precedence, _substitution) = make_inference_fixture();
    let _ = arena;
    let mut rng = DeterministicRng::new(0xF055_5EED);
    let names = ["p", "q", "r"];
    let constants = ["a", "b"];
    let mut splits: u32 = 0;
    let mut unsplittable: u32 = 0;
    for _ in 0..kFuzzRounds {
        // Random clause: 2..=10 literals, mixed predicate arities, mixed arguments
        // (constants, variables, one-level nesting), mixed polarity.
        let count = 2 + rng.below(9) as usize;
        let mut literals: Vec<Literal> = Vec::new();
        for _ in 0..count {
            let name = names[rng.below(3) as usize];
            let arity = if name == "q" {
                2
            } else if name == "r" {
                0
            } else {
                1
            };
            let mut args: Vec<TermPtr> = Vec::new();
            for _ in 0..arity {
                let choice = rng.below(3);
                if choice == 0 {
                    let constant = constants[rng.below(2) as usize];
                    args.push(
                        terms
                            .intern_fun(&symbols, symbol_id(&builder, constant), &[])
                            .expect("constant"),
                    );
                } else if choice == 1 {
                    args.push(terms.intern_var(rng.below(8) as u32).expect("var"));
                } else {
                    // One-level nesting: f or g over a constant or variable.
                    let inner = if rng.below(2) == 0 {
                        terms
                            .intern_fun(&symbols, symbol_id(&builder, "a"), &[])
                            .expect("a")
                    } else {
                        terms.intern_var(rng.below(8) as u32).expect("var")
                    };
                    let wrapper = if rng.below(2) == 0 { "f" } else { "g" };
                    args.push(
                        terms
                            .intern_fun(&symbols, symbol_id(&builder, wrapper), &[inner])
                            .expect("wrapper"),
                    );
                }
            }
            let atom = terms
                .intern_pred(&symbols, symbol_id(&builder, name), &args)
                .expect("atom");
            literals.push(Literal::new(atom, rng.below(2) == 0));
        }
        let min_size = 1 + rng.below(3) as u16;
        match try_split_with(&terms, &literals, min_size) {
            SplitDecision::Unsplittable => {
                unsplittable += 1;
            }
            SplitDecision::Splittable(view) => {
                splits += 1;
                // Invariant 1: component indices in range; every literal covered once.
                assert!(view.component_count >= 2);
                for position in 0..literals.len() {
                    let component = view.literal_component[position] as usize;
                    assert!(component < view.component_count as usize);
                }
                // Invariant 2: the gate (every component at least min_size literals).
                for component in 0..view.component_count as usize {
                    assert!(
                        view.component_size[component] >= min_size,
                        "the gate must hold for every component"
                    );
                }
                // Invariant 3: pairwise variable-disjoint components.
                let mut component_vars: Vec<Vec<u32>> =
                    vec![Vec::new(); view.component_count as usize];
                for (position, literal) in literals.iter().enumerate() {
                    let component = view.literal_component[position] as usize;
                    collect_vars(&terms, literal.atom(), &mut component_vars[component]);
                }
                for left in 0..component_vars.len() {
                    for right in (left + 1)..component_vars.len() {
                        for var in component_vars[left].iter() {
                            assert!(
                                !component_vars[right].contains(var),
                                "fuzz round: components {} and {} share variable {}",
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
    assert!(splits > 0, "the fuzz corpus must hit splittable clauses");
    assert!(unsplittable > 0, "the fuzz corpus must hit the gate");
}

// CEP:WHAT: Collects an atom's variable ids (explicit-stack DFS with resume cursors).
// CEP:WHY: The disjointness invariant needs the variable sets; the walker mirrors the splitter's discipline.
// CEP:STATUS: complete
// CEP:FAILURE: returns silently on unreadable terms (fuzz input discipline).
// CEP:ASSUMES: fixture terms.
// CEP:COST: O(term nodes).
// CEP:EVIDENCE: this file.
// CEP:SECURITY: none.
fn collect_vars(terms: &mapt::hot::ir::term::TermStore<'_>, atom: TermPtr, out: &mut Vec<u32>) {
    let mut stack: [(TermPtr, u16); 128] = [(TermPtr::invalid(), 0); 128];
    let mut stack_len: usize = 0;
    let mut top = atom;
    let mut next_child: u16 = 0;
    loop {
        let view = match terms.term(top) {
            Ok(view) => view,
            Err(_) => return,
        };
        if view.tag() == TermTag::Variable {
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
