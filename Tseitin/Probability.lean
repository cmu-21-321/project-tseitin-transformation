import Tseitin.Weighted
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false

/-!
# Finite probabilities under an independent-event model

Each original variable has a rational probability of being true in [0, 1].
Assignment weights use the product model, which assumes mutual independence
of distinct original variables. Repeated occurrences refer to the same event.
-/
open scoped BigOperators
namespace Tseitin

/-- Parameters for the product model on any finite set of original variables. -/
structure IndependentModel where
  probTrue : Nat → ℚ
  nonneg : ∀ n, 0 ≤ probTrue n
  le_one : ∀ n, probTrue n ≤ 1

namespace IndependentModel

/-- A true value has weight `p`; a false value has weight `1 - p`. -/
def weight (m : IndependentModel) (n : Nat) (b : Bool) : ℚ :=
  if b then m.probTrue n else 1 - m.probTrue n

/-- Both truth-value weights are nonnegative. -/
theorem weight_nonneg (m : IndependentModel) (n : Nat) (b : Bool) :
    0 ≤ m.weight n b := by
  cases b with
  | false => exact sub_nonneg.mpr (m.le_one n)
  | true => exact m.nonneg n

/-- The two truth-value weights of a variable sum to one. -/
theorem weight_sum (m : IndependentModel) (n : Nat) :
    m.weight n false + m.weight n true = 1 := by
  simp [weight]

end IndependentModel

namespace Formula

/-- Every finite assignment has nonnegative product weight. -/
theorem Assignment.probWeight_nonneg {φ : Formula} (a : φ.Assignment)
    (m : IndependentModel) : 0 ≤ a.weight m.weight := by
  apply Finset.prod_nonneg
  intro n _
  exact m.weight_nonneg n.val (a n)

/-- Sum the product weights of assignments satisfying the formula. -/
def probability (φ : Formula) (m : IndependentModel) : ℚ :=
  φ.weightedModelCount m.weight

/-- The computed event weight is nonnegative. -/
theorem probability_nonneg (φ : Formula) (m : IndependentModel) :
    0 ≤ φ.probability m := by
  apply Finset.sum_nonneg
  intro a _
  exact a.probWeight_nonneg m

/-- The same event weight can be computed from the generated CNF. -/
theorem probability_eq_cnf (φ : Formula) (m : IndependentModel) :
    φ.probability m = φ.weightedCNFModelCount m.weight := by
  exact weightedModelCount_eq_weightedCNFModelCount φ m.weight


/-- The product weights of all finite source assignments sum to one. -/
theorem assignmentWeight_sum (φ : Formula) (m : IndependentModel) :
    (∑ a : φ.Assignment, a.weight m.weight) = 1 := by
  change (∑ a : {n : Nat // n ∈ φ.vars} → Bool,
    ∏ n, m.weight n.val (a n)) = 1
  rw [← Fintype.prod_sum]
  simp [IndependentModel.weight]

/-- An event's weight is at most the weight of the entire assignment space. -/
theorem probability_le_one (φ : Formula) (m : IndependentModel) :
    φ.probability m ≤ 1 := by
  calc
    φ.probability m = ∑ a ∈ φ.models, a.weight m.weight := rfl
    _ ≤ ∑ a : φ.Assignment, a.weight m.weight := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro a _ _
      exact a.probWeight_nonneg m
    _ = 1 := assignmentWeight_sum φ m

/-- Formula probabilities lie in the unit interval. -/
theorem probability_bounds (φ : Formula) (m : IndependentModel) :
    0 ≤ φ.probability m ∧ φ.probability m ≤ 1 :=
  ⟨probability_nonneg φ m, probability_le_one φ m⟩




/-- Express event probability as a sum over all finite assignments,
with zero contribution from assignments that do not satisfy the formula. -/
theorem probability_eq_sum (φ : Formula) (m : IndependentModel) :
    φ.probability m =
      ∑ a : φ.Assignment, if φ.evalFinite a = true then a.weight m.weight else 0 := by
  simp [probability, weightedModelCount, models, Finset.sum_filter]

/-- A formula and its negation partition the finite assignment space. -/
theorem probability_add_neg (φ : Formula) (m : IndependentModel) :
    φ.probability m + (Formula.neg φ).probability m = 1 := by
  rw [probability_eq_sum, probability_eq_sum]
  change
    (∑ a : φ.Assignment, if φ.evalFinite a = true then a.weight m.weight else 0) +
      (∑ a : φ.Assignment, if !(φ.evalFinite a) = true then a.weight m.weight else 0) = 1
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a : φ.Assignment, a.weight m.weight := by
      apply Finset.sum_congr rfl
      intro a _
      cases φ.evalFinite a <;> simp
    _ = 1 := assignmentWeight_sum φ m

/-- The probability of the complement is one minus the event probability. -/
theorem probability_neg (φ : Formula) (m : IndependentModel) :
    (Formula.neg φ).probability m = 1 - φ.probability m := by
  apply (eq_sub_iff_add_eq).mpr
  simpa only [add_comm] using probability_add_neg φ m



end Formula
end Tseitin
