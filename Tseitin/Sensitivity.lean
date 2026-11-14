import Tseitin.Probability
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Affine dependence on one basic-event probability

Changing one original variable's probability gives an affine combination of
the endpoint models in which that variable is always false or always true.
This applies to every formula, including formulas containing negation.
-/

open scoped BigOperators

namespace Tseitin
namespace IndependentModel

/-- Replace one basic-event probability, preserving all other parameters. -/
def withProb (m : IndependentModel) (i : Nat) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : IndependentModel where
  probTrue n := if n = i then q else m.probTrue n
  nonneg n := by
    split
    · exact hq0
    · exact m.nonneg n
  le_one n := by
    split
    · exact hq1
    · exact m.le_one n

end IndependentModel
namespace Formula

/-- Factor out the weight of one occurring variable. -/
private theorem weight_withProb_factor (φ : Formula) (a : φ.Assignment)
    (m : IndependentModel) (i : {n : Nat // n ∈ φ.vars})
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    a.weight (m.withProb i.val q hq0 hq1).weight =
      (if a i then q else 1 - q) *
        ∏ j ∈ (Finset.univ.erase i), m.weight j.val (a j) := by
  unfold Assignment.weight
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => (m.withProb i.val q hq0 hq1).weight j.val (a j))
    (Finset.mem_univ i)]
  congr 1
  · simp [IndependentModel.weight, IndependentModel.withProb]
  · apply Finset.prod_congr rfl
    intro j hj
    have hne : j.val ≠ i.val := by
      intro h
      exact (Finset.mem_erase.mp hj).1 (Subtype.ext h)
    simp [IndependentModel.weight, IndependentModel.withProb, hne]

/-- Each assignment weight is affine in one probability parameter. -/
theorem Assignment.weight_withProb_affine {φ : Formula} (a : φ.Assignment)
    (m : IndependentModel) (i : Nat) (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    a.weight (m.withProb i q hq0 hq1).weight =
      (1 - q) * a.weight (m.withProb i 0 (by norm_num) (by norm_num)).weight +
      q * a.weight (m.withProb i 1 (by norm_num) (by norm_num)).weight := by
  by_cases hi : i ∈ φ.vars
  · rw [weight_withProb_factor φ a m ⟨i, hi⟩,
        weight_withProb_factor φ a m ⟨i, hi⟩,
        weight_withProb_factor φ a m ⟨i, hi⟩]
    cases a ⟨i, hi⟩ <;> simp
  · have unchanged (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
        a.weight (m.withProb i r hr0 hr1).weight = a.weight m.weight := by
      unfold Assignment.weight
      apply Finset.prod_congr rfl
      intro j _
      have hne : j.val ≠ i := by
        intro h
        exact hi (h ▸ j.property)
      simp [IndependentModel.weight, IndependentModel.withProb, hne]
    rw [unchanged, unchanged, unchanged]
    ring

/-- The event probability is the affine interpolation of its endpoint models.
At endpoints the selected variable is deterministic, so no conditioning on
an event of positive probability is required. Unused variables are allowed. -/
theorem probability_withProb_affine (φ : Formula) (m : IndependentModel)
    (i : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    φ.probability (m.withProb i q hq0 hq1) =
      (1 - q) * φ.probability (m.withProb i 0 (by norm_num) (by norm_num)) +
      q * φ.probability (m.withProb i 1 (by norm_num) (by norm_num)) := by
  unfold probability weightedModelCount
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact a.weight_withProb_affine m i q hq0 hq1

/-- The signed change in event probability between deterministic endpoints. -/
def sensitivity (φ : Formula) (m : IndependentModel) (i : Nat) : ℚ :=
  φ.probability (m.withProb i 1 (by norm_num) (by norm_num)) -
  φ.probability (m.withProb i 0 (by norm_num) (by norm_num))

/-- Changing one parameter has an exact linear effect, not an approximation. -/
theorem probability_withProb_sub (φ : Formula) (m : IndependentModel)
    (i : Nat) (q r : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    φ.probability (m.withProb i q hq0 hq1) -
        φ.probability (m.withProb i r hr0 hr1) =
      (q - r) * φ.sensitivity m i := by
  rw [probability_withProb_affine φ m i q hq0 hq1,
      probability_withProb_affine φ m i r hr0 hr1]
  unfold sensitivity
  ring

end Formula
end Tseitin
