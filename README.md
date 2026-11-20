# Verified Tseitin Encoding and Probability Bounds in Lean 4

This individual project for CMU 21-321 formalizes a Tseitin transformation
and connects it to finite model counting, rational weighted counts, and
probability bounds. The development ends with interval propagation for
AND/OR fault trees whose branches may share components.

- [Project report](report/21321_project_paper_v1.pdf)
- [Collaboration statement](COLLABORATION.md)
- [AI-use statement](AI_USE.md)

## Main results

- **Encoding correctness:** `toCNF_correct` proves that a source assignment
  satisfies a formula exactly when it has a satisfying CNF extension agreeing
  on all original variables. `toCNF_length_le` bounds the clause count by
  `3 * φ.numConnectives + 1`.
- **Finite model correspondence:** uniqueness on the allocated auxiliary
  interval gives `Formula.modelEquiv`, a bijection between source and CNF
  models over their finite variable domains.
- **Weighted counts and probability:**
  `Formula.weightedModelCount_eq_weightedCNFModelCount` preserves rational
  weighted counts when both auxiliary polarities have weight one.
  Product weights on independent basic events specialize this to probability.
- **Sensitivity and intervals:** `Formula.probability_withProb_affine` proves
  affine response in one parameter. For monotone formulas,
  `Formula.probability_mono` yields interval bounds;
  `FaultTree.failureProbability_cnf_interval_bounds` transfers the endpoints
  to CNF weighted counts.

The shared-supply example has failure event `(A ∨ B) ∧ (A ∨ C)`.
At probabilities `(0.01, 0.1, 0.1)`, its exact failure probability is 1.99%.
The supplied parameter box gives bounds of 1.1368% and 2.9184%.
These bounds assume parameter inclusion; the project does not estimate
confidence intervals from data. Distinct basic events are independent,
but branches containing the same event need not be.

## Code guide

| Part | Files in `Tseitin/` (`.lean`) |
| --- | --- |
| Syntax and encoding | `Basic`, `CNF`, `Encoding`, `Transform` |
| Correctness and size | `Allocation`, `Correctness`, `Size`, `Assignment`, `Completeness` |
| Finite models | `Uniqueness`, `Support`, `FiniteAssignment`, `ModelCount`, `FiniteCNF`, `ModelCorrespondence`, `ModelEquiv` |
| Weights and probability | `Weighted`, `Probability` |
| Fault-tree application | `FaultTree`, `FaultProbability`, `ReliabilityExample` |
| Sensitivity and bounds | `Sensitivity`, `Monotonicity`, `Intervals` |

## Build

Install Lean through elan. The version is specified in `lean-toolchain`.

```bash
lake exe cache get
lake build
```
