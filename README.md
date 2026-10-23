# Tseitin Transformation in Lean

This individual project aims to implement the Tseitin transformation
from propositional formulas to conjunctive normal form (CNF), prove its
correctness, and establish linear bounds on the generated encoding.

## Main correctness goal

For every propositional formula φ and assignment σ to its original
variables, σ satisfies φ if and only if there exists an assignment τ
that agrees with σ on all original variables and satisfies the
generated CNF.

The final CNF will include a unit clause asserting the variable
representing the whole formula.

## Checkpoint: October 23, 2026
Completed:

- Defined propositional formulas with variables, negation, conjunction,
  and disjunction, together with their Boolean evaluation.
- Defined original and auxiliary variables, literals, clauses, and CNF,
  together with their Boolean evaluation.
- Implemented local CNF encodings for AND, OR, and NOT.
- Proved `encodeAnd_correct`, `encodeOr_correct`, and
  `encodeNot_correct` by exhaustive Boolean case analysis.
- Added evaluation examples, including the distinction between an
  empty CNF and a CNF containing an empty clause.

## Representation choices

Source variables are indexed by natural numbers. In the output,
`Var.original n` and `Var.aux n` distinguish original variables from
auxiliary variables, even when they share the same numeric index.

Clauses are lists of literals, interpreted using disjunction.
CNF formulas are lists of clauses, interpreted using conjunction.
This representation also makes clause counts explicit.

## Planned recursive transformation

The encoder will take a formula and the next available auxiliary index.
It will return:

- a variable representing the formula;
- the generated clauses;
- the next unused auxiliary index.

For binary connectives, the right subtree will receive the next index
returned by the left subtree. The parent will then receive a fresh
auxiliary variable.

The final transformation will append a positive unit clause for the
root variable.

## Next checkpoint: October 30 - may change

- Implement the recursive transformation.
- Evaluate complete examples.
- Establish supporting properties of auxiliary-variable allocation.
- Develop the induction invariant for the global correctness proof.

## Files

- `Tseitin/Basic.lean`: formula syntax and evaluation.
- `Tseitin/CNF.lean`: variables, literals, clauses, and CNF evaluation.
- `Tseitin/Encoding.lean`: local encodings and correctness proofs.

## Build

The Lean version is specified in `lean-toolchain`.

```bash
lake exe cache get
lake build
```