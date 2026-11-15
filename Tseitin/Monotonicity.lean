import Tseitin.Sensitivity
import Tseitin.FaultProbability

set_option linter.style.header false

/-!
# Monotonicity of static fault-tree probabilities

AND/OR failure events are monotone in their basic-event truth values.
Under the independent basic-event model, this implies nonnegative sensitivity
and monotonicity in each probability parameter. Shared and repeated component
indices are allowed; no independence of subtrees is assumed.
-/

open scoped BigOperators

namespace Tseitin
namespace Formula

/-- Making additional variables true cannot turn a true formula false. -/
def IsMonotone (φ : Formula) : Prop :=
  ∀ σ τ : Nat → Bool, (∀ n, σ n = true → τ n = true) →
    φ.eval σ = true → φ.eval τ = true

/-- Flip one occurring variable. If the index is absent, this is the identity. -/
private def flipAssignment (φ : Formula) (i : Nat) : φ.Assignment ≃ φ.Assignment where
  toFun a n := if n.val = i then !(a n) else a n
  invFun a n := if n.val = i then !(a n) else a n
  left_inv a := by
    funext n
    by_cases h : n.val = i <;> simp [h]
  right_inv a := by
    funext n
    by_cases h : n.val = i <;> simp [h]

/-- Flipping the selected bit swaps the probability-zero and probability-one
endpoint weights, while preserving all other factors. -/
private theorem flipAssignment_weight (φ : Formula) (m : IndependentModel)
    (i : Nat) (a : φ.Assignment) :
    ((flipAssignment φ i) a).weight
        (m.withProb i 1 (by norm_num) (by norm_num)).weight =
      a.weight (m.withProb i 0 (by norm_num) (by norm_num)).weight := by
  unfold Assignment.weight
  apply Finset.prod_congr rfl
  intro n _
  by_cases h : n.val = i
  · cases ha : a n <;> simp [flipAssignment, IndependentModel.weight,
      IndependentModel.withProb, h, ha]
  · simp [flipAssignment, IndependentModel.weight, IndependentModel.withProb, h]

/-- For a monotone event, the always-false endpoint has no greater probability
than the always-true endpoint. A bit-flip bijection compares the finite sums. -/
theorem probability_endpoints_le (φ : Formula) (hφ : φ.IsMonotone)
    (m : IndependentModel) (i : Nat) :
    φ.probability (m.withProb i 0 (by norm_num) (by norm_num)) ≤
      φ.probability (m.withProb i 1 (by norm_num) (by norm_num)) := by
  rw [probability_eq_sum, probability_eq_sum]
  conv_rhs => rw [← (flipAssignment φ i).sum_comp]
  apply Finset.sum_le_sum
  intro a _
  have hnonneg : 0 ≤
      (if φ.evalFinite ((flipAssignment φ i) a) = true then
        ((flipAssignment φ i) a).weight
          (m.withProb i 1 (by norm_num) (by norm_num)).weight else 0) := by
    split
    · exact Assignment.probWeight_nonneg _ _
    · exact le_rfl
  by_cases ha : φ.evalFinite a = true
  · by_cases hi : i ∈ φ.vars
    · cases hai : a ⟨i, hi⟩ with
      | false =>
          have hle : ∀ n, a.toTotal n = true →
              ((flipAssignment φ i) a).toTotal n = true := by
            intro n hn
            by_cases hmem : n ∈ φ.vars
            · simp only [Assignment.toTotal_apply _ n hmem] at hn ⊢
              by_cases hni : n = i
              · subst n
                simp [hai] at hn
              · simpa [flipAssignment, hni] using hn
            · simp [Assignment.toTotal, hmem] at hn
          have hb : φ.evalFinite ((flipAssignment φ i) a) = true :=
            hφ _ _ hle ha
          simp only [ite_eq_left ha, ite_eq_left hb]
          exact le_of_eq (flipAssignment_weight φ m i a).symm
      | true =>
          have hz : a.weight (m.withProb i 0 (by norm_num) (by norm_num)).weight = 0 := by
            unfold Assignment.weight
            apply Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : {n // n ∈ φ.vars}))
            simp [IndependentModel.weight, IndependentModel.withProb, hai]
          simpa only [ite_eq_left ha, hz] using hnonneg
    · have heq : (flipAssignment φ i) a = a := by
        funext n
        have hne : n.val ≠ i := by
          intro h
          exact hi (h ▸ n.property)
        simp [flipAssignment, hne]
      simp only [heq, ite_eq_left ha]
      exact le_of_eq (by simpa only [heq] using (flipAssignment_weight φ m i a).symm)
  · simpa only [ite_eq_right ha] using hnonneg

/-- A monotone formula has nonnegative sensitivity to every parameter. -/
theorem sensitivity_nonneg (φ : Formula) (hφ : φ.IsMonotone)
    (m : IndependentModel) (i : Nat) : 0 ≤ φ.sensitivity m i :=
  sub_nonneg.mpr (probability_endpoints_le φ hφ m i)

/-- A one-parameter sensitivity is at most one. -/
theorem sensitivity_le_one (φ : Formula) (m : IndependentModel) (i : Nat) :
    φ.sensitivity m i ≤ 1 := by
  unfold sensitivity
  exact le_trans (sub_le_self _ (probability_nonneg φ _)) (probability_le_one φ _)

/-- Increasing one basic-event probability increases the probability of a
monotone event, holding every other parameter fixed. -/
theorem probability_withProb_mono (φ : Formula) (hφ : φ.IsMonotone)
    (m : IndependentModel) (i : Nat) (q r : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : q ≤ r) :
    φ.probability (m.withProb i q hq0 hq1) ≤
      φ.probability (m.withProb i r hr0 hr1) := by
  apply sub_nonneg.mp
  rw [probability_withProb_sub]
  exact mul_nonneg (sub_nonneg.mpr hqr) (sensitivity_nonneg φ hφ m i)

end Formula
namespace FaultTree

/-- AND/OR fault trees are monotone, including when subtrees share variables. -/
theorem fails_mono (t : FaultTree) (σ τ : Nat → Bool)
    (hστ : ∀ n, σ n = true → τ n = true)
    (h : t.fails σ = true) : t.fails τ = true := by
  induction t with
  | component n => exact hστ n h
  | andGate left right ihLeft ihRight =>
      simp only [fails, Bool.and_eq_true] at h ⊢
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | orGate left right ihLeft ihRight =>
      simp only [fails, Bool.or_eq_true] at h ⊢
      exact h.elim (fun hl => Or.inl (ihLeft hl)) (fun hr => Or.inr (ihRight hr))

/-- The translated failure formula satisfies semantic monotonicity. -/
theorem toFormula_isMonotone (t : FaultTree) : t.toFormula.IsMonotone := by
  intro σ τ hστ h
  rw [toFormula_correct] at h ⊢
  exact fails_mono t σ τ hστ h

/-- Component sensitivities of an AND/OR fault tree belong to [0, 1]. -/
theorem sensitivity_bounds (t : FaultTree) (m : IndependentModel) (i : Nat) :
    0 ≤ t.toFormula.sensitivity m i ∧ t.toFormula.sensitivity m i ≤ 1 :=
  ⟨Formula.sensitivity_nonneg _ t.toFormula_isMonotone m i,
    Formula.sensitivity_le_one _ m i⟩

/-- Lowering one component's failure probability cannot increase system failure. -/
theorem failureProbability_withProb_mono (t : FaultTree) (m : IndependentModel)
    (i : Nat) (q r : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : q ≤ r) :
    t.failureProbability (m.withProb i q hq0 hq1) ≤
      t.failureProbability (m.withProb i r hr0 hr1) := by
  rw [failureProbability_eq_formula, failureProbability_eq_formula]
  exact Formula.probability_withProb_mono _ t.toFormula_isMonotone m i q r
    hq0 hq1 hr0 hr1 hqr

end FaultTree
end Tseitin
