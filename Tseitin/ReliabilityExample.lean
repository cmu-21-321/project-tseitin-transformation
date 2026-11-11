import Tseitin.FaultProbability
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# A shared-supply reliability example

Synthetic parameters: the shared supply fails with probability 1/100,
and each individual unit fails with probability 1/10. Basic events are
independent, but the two branches share the same supply event.
Only component indices 0, 1, and 2 occur in this example.
-/

namespace Tseitin
namespace ReliabilityExample

/-- Illustrative parameters, not estimates from observed failure data.
Values at unused component indices do not affect this example. -/
def sharedSupplyModel : IndependentModel where
  probTrue := fun n => if n = 0 then 1 / 100 else 1 / 10
  nonneg := by
    intro n
    split <;> norm_num
  le_one := by
    intro n
    split <;> norm_num

-- Direct enumeration of basic-event states.
#eval FaultTree.sharedSupply.failureProbability sharedSupplyModel

-- Weighted model counting of the generated CNF.
#eval FaultTree.sharedSupply.toFormula.weightedCNFModelCount
  sharedSupplyModel.weight

-- Probability that the system does not fail.
#eval 1 - FaultTree.sharedSupply.failureProbability sharedSupplyModel

/-- The generic correctness theorem applies to these concrete parameters. -/
theorem sharedSupply_cnf_correct :
    FaultTree.sharedSupply.failureProbability sharedSupplyModel =
      FaultTree.sharedSupply.toFormula.weightedCNFModelCount
        sharedSupplyModel.weight :=
  FaultTree.failureProbability_eq_cnf
    FaultTree.sharedSupply sharedSupplyModel


/-- Failure of the branch containing individual unit 1. -/
def leftBranch : FaultTree :=
  .orGate (.component 0) (.component 1)

/-- Failure of the branch containing individual unit 2. -/
def rightBranch : FaultTree :=
  .orGate (.component 0) (.component 2)

/-- An intentionally incorrect estimate: the branch events share component 0
and therefore must not be treated as independent. -/
def naiveIndependentFailure : ℚ :=
  leftBranch.failureProbability sharedSupplyModel *
    rightBranch.failureProbability sharedSupplyModel

/-- Signed difference: exact failure probability minus the naive estimate. -/
def independenceGap : ℚ :=
  FaultTree.sharedSupply.failureProbability sharedSupplyModel -
    naiveIndependentFailure

/-- Relative underestimate for this example, whose exact probability is positive. -/
def relativeUnderestimate : ℚ :=
  independenceGap /
    FaultTree.sharedSupply.failureProbability sharedSupplyModel

#eval leftBranch.failureProbability sharedSupplyModel
#eval rightBranch.failureProbability sharedSupplyModel
#eval naiveIndependentFailure
#eval independenceGap
#eval relativeUnderestimate


end ReliabilityExample
end Tseitin
