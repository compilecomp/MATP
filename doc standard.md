

# Documentation Style Guide

## 1. Core Principles

*   **Objectivity:** State facts, algorithms, and constraints. Do not use marketing language, subjective adjectives, or promotional phrasing.
*   **Precision:** Use exact terminology. Define all terms upon first use. Avoid ambiguity.
*   **Conciseness:** Omit filler words, transitional fluff, and redundant explanations. Every sentence must convey new, necessary information.
*   **Completeness:** Document all public interfaces, invariants, and edge cases. If a limitation exists, state it explicitly.

## 2. Prohibited Elements

*   **Hype and Overpromises:** Words such as "revolutionary", "massive", "ultimate", "perfect", "best possible", or "ruthless" are strictly forbidden.
*   **AI Idioms:** Phrases such as "In conclusion", "Let us dive in", "It is important to note", or "seamless integration" are prohibited.
*   **Excessive Punctuation:** Avoid exclamation marks. Minimize the use of hyphens and em-dashes; prefer direct sentence structures.
*   **Visual Clutter:** Do not use emojis. Limit the use of bold text to section headers and defined terms. Avoid nested bullet lists deeper than two levels; prefer numbered lists or plain paragraphs for complex logic.

## 3. Document Structure

Every component document in the `doc/` directory must follow this exact structure.

### 3.1 Title
The exact name of the component or module.

### 3.2 Abstract
A single paragraph stating the purpose of the component, its inputs, and its outputs. No background context or motivation is permitted here.

### 3.3 Formal Definitions
Mathematical or structural definitions of the core data types. 
*   Include Rust struct/enum signatures.
*   Define the domain and range of all fields.
*   State any type constraints.

### 3.4 Algorithm
A step-by-step description of the primary algorithm.
*   Use pseudocode or formal mathematical notation where appropriate.
*   State the time and space complexity using Big-O notation.
*   Specify any assumptions made by the algorithm.

### 3.5 Invariants
A numbered list of properties that must hold true before and after the execution of any public method. Violation of an invariant must result in a panic or a well-defined error state.

### 3.6 Integration Points
A precise description of dependencies.
*   **Depends on:** List of modules this component calls.
*   **Depended on by:** List of modules that call this component.
*   Include exact function signatures for cross-module boundaries.

### 3.7 Known Limitations
Explicit statements of what the component does not handle, edge cases that degrade performance, or theoretical bounds that are not currently implemented.

## 4. Example: Good vs. Bad Documentation

### Bad (Prohibited)
> **The Ultimate Borrow Checker**
> Let's dive into our revolutionary borrow checker! It seamlessly integrates with the Sea of Nodes to provide massive performance gains. Unlike other compilers, it perfectly handles all edge cases without breaking a sweat. Note that it uses a highly optimized bitset propagation method.

### Good (Required)
> **Borrow Checker**
> 
> **Abstract**
> The borrow checker validates memory safety properties of the Mid-Level Intermediate Representation (MIR). It computes lifetime bounds and verifies aliasing rules prior to code generation.
> 
> **Formal Definitions**
> A `Region` is defined as a set of program points $R \subseteq P$. A `Borrow` is a directed edge in the control flow graph annotated with a `RegionId` and a `BorrowKind` (Shared or Mutable).
> 
> **Algorithm**
> 1. Construct the constraint graph from explicit lifetime annotations and implicit usage sites.
> 2. Compute Strongly Connected Components (SCCs) using Tarjan's algorithm to condense the graph.
> 3. Propagate liveness bitsets in reverse topological order.
> 4. Verify that no Mutable Borrow intersects with any other Borrow to the same memory location.
> 
> Time complexity is $O(V + E)$ for SCC computation and $O(N \cdot \frac{W}{64})$ for bitset propagation, where $W$ is the number of program points.
> 
> **Invariants**
> 1. Every `RegionId` referenced in a `Borrow` edge must exist in the region table.
> 2. The liveness bitset of a child region must be a subset of its parent region's liveness bitset.
> 
> **Integration Points**
> *   Depends on: `name_resolution` (for DefId mapping), `mir_builder` (for control flow graph).
> *   Depended on by: `lir_lowering` (consumes validated MIR).
> 
> **Known Limitations**
> The current implementation does not support higher-ranked trait bounds (HRTBs) in closure signatures. Such constructs are rejected at the type-checking phase prior to borrow checking.

## 5. Maintenance and Enforcement

1.  **Co-location:** Documentation updates must be included in the same commit as the corresponding code changes.
2.  **CI Enforcement:** The continuous integration pipeline executes `cargo doc --no-deps --document-private-items`. The build fails if:
    *   Any public item lacks documentation.
    *   Any documentation contains broken internal links.
    *   Any documentation example fails to compile.
3.  **Review:** Pull requests containing documentation that violates this style guide will be rejected during code review.

This standard is effective immediately for all project documentation.
