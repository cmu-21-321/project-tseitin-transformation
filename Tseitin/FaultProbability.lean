import Tseitin.FaultTree
import Tseitin.Probability

set_option linter.style.header false

/-!
# Fault-tree failure probabilities and verified CNF computation

Failure probability is computed by testing `FaultTree.fails` on each finite
assignment and summing its product weight. The variable domain is the set
of variables occurring in the translated formula. Repeated component indices
share one assignment value. Basic events follow the independent product model.
-/

open scoped BigOperators

namespace Tseitin
namespace FaultTree

/-- Directly sum the weights of basic-event states in which the tree fails. -/
def failureProbability (t : FaultTree) (m : IndependentModel) : ℚ :=
  ∑ a : t.toFormula.Assignment,
    if t.fails a.toTotal = true then a.weight m.weight else 0

/-- Translating the failure event preserves its probability. -/
theorem failureProbability_eq_formula (t : FaultTree) (m : IndependentModel) :
    t.failureProbability m = t.toFormula.probability m := by
  rw [Formula.probability_eq_sum]
  unfold failureProbability
  apply Finset.sum_congr rfl
  intro a _
  simp only [Formula.evalFinite, toFormula_correct]

/-- Direct fault-tree failure probability equals the weighted model count
of its generated CNF, with neutral auxiliary weights. -/
theorem failureProbability_eq_cnf (t : FaultTree) (m : IndependentModel) :
    t.failureProbability m = t.toFormula.weightedCNFModelCount m.weight := by
  rw [failureProbability_eq_formula]
  exact Formula.probability_eq_cnf t.toFormula m

/-- Every failure probability lies in the unit interval. -/
theorem failureProbability_bounds (t : FaultTree) (m : IndependentModel) :
    0 ≤ t.failureProbability m ∧ t.failureProbability m ≤ 1 := by
  rw [failureProbability_eq_formula]
  exact Formula.probability_bounds t.toFormula m

end FaultTree
end Tseitin
