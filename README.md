# Tseitin Transformation in Lean

This project implements the Tseitin transformation from propositional
formulas to conjunctive normal form (CNF) in Lean, with correctness
proofs and bounds on the generated encoding.

## Main correctness theorem

For every propositional formula φ and assignment σ to its original
variables, σ satisfies φ if and only if there exists an assignment τ
that agrees with σ on all original variables and satisfies `toCNF φ`.

This statement is proved by `toCNF_correct`

- `toCNF_sound`: every satisfying assignment of the generated CNF
  restricts to a satisfying assignment of the original formula.
- `toCNF_complete`: every satisfying original assignment can be
  explicitly extended to satisfy the generated CNF.
- `toCNF_equisatisfiable`: the original formula is satisfiable
  if and only if its generated CNF is satisfiable.

The construction preserves all original variable values. Auxiliary
variables use a separate constructor and are allocated in disjoint
ranges for recursive subformulas.


## Representation and transformation

Formulas contain variables, negation, conjunction, and disjunction.
Original and auxiliary variables use separate constructors:
`Var.original n` and `Var.aux n`.

The recursive encoder returns a representative variable, defining
clauses, and the next unused auxiliary index. For binary connectives,
the right subtree starts at the index returned by the left subtree.
The parent then receives a fresh auxiliary variable.

`toCNF` starts allocation at zero and appends a unit clause asserting
that the root representative is true.


## Checkpoint: November 6, 2026

### Semantic correctness

- Defined `restrictOriginal`, which restricts a target assignment
  to the original variables.
- Proved evaluation lemmas for concatenated CNFs.
- Proved `encode_root_correct`: any assignment satisfying the
  defining clauses gives the root representative the same value
  as the original formula.
- Proved `toCNF_sound`: any assignment satisfying the final CNF
  restricts to a satisfying assignment of the original formula.

The root correctness proof uses structural induction, combining
the induction hypotheses with the local encoding correctness lemmas.
The final soundness theorem additionally uses the root unit clause.

### Clause-count bounds

- Defined `Formula.clauseCount`, counting two defining clauses per
  negation and three per conjunction or disjunction.
- Proved exact counts for `encode` and `toCNF`
  (`encode_clauseCount`, `toCNF_clauseCount`).
- Proved `toCNF_length_le`:

  `(toCNF φ).length ≤ 3 * φ.numConnectives + 1`

This bound measures the number of generated clauses.


## Files

- `Tseitin/Basic.lean`: formula syntax and evaluation.
- `Tseitin/CNF.lean`: target variables, literals, clauses, and evaluation.
- `Tseitin/Encoding.lean`: local encodings and correctness proofs.
- `Tseitin/Transform.lean`: recursive transformation and root assertion.
- `Tseitin/Allocation.lean`: auxiliary-counter and variable-range proofs.
- `Tseitin/Correctness.lean`: root semantics and CNF-to-formula soundness.
- `Tseitin/Size.lean`: exact clause counts and a linear upper bound.
- `Tseitin/Assignment.lean`: assignment construction, preservation
  lemmas, and satisfaction of all defining clauses.
- `Tseitin/Completeness.lean`: completeness, assignment-extension
  correctness, and equisatisfiability.

## Build

The Lean version is specified in `lean-toolchain`.

```bash
lake exe cache get
lake build
```
