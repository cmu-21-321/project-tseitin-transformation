import Tseitin.Monotonicity

set_option linter.style.header false

/-!
# Simultaneous parameter changes and interval bounds

Only probabilities of variables occurring in the formula matter. For monotone
formulas, changing finitely many parameters in the same direction preserves
probability order. AND/OR fault trees therefore admit bounds by evaluating the
lower and upper parameter vectors, directly or through the verified CNF.
These are deterministic bounds conditional on parameter inclusion, not a
statistical confidence statement about how the intervals were obtained.
-/

namespace Tseitin
namespace IndependentModel

/-- Use the target parameters on a finite set and the base parameters elsewhere. -/
private def replaceOn (base target : IndependentModel) (s : Finset Nat) : IndependentModel where
  probTrue n := if n ∈ s then target.probTrue n else base.probTrue n
  nonneg n := by
    split
    · exact target.nonneg n
    · exact base.nonneg n
  le_one n := by
    split
    · exact target.le_one n
    · exact base.le_one n

end IndependentModel
namespace Formula

/-- Changing parameters outside the formula's finite support has no effect. -/
theorem probability_congr (φ : Formula) (m₁ m₂ : IndependentModel)
    (h : ∀ i ∈ φ.vars, m₁.probTrue i = m₂.probTrue i) :
    φ.probability m₁ = φ.probability m₂ := by
  unfold probability weightedModelCount
  apply Finset.sum_congr rfl
  intro a _
  unfold Assignment.weight
  apply Finset.prod_congr rfl
  intro i _
  simp only [IndependentModel.weight, h i.val i.property]

/-- Replace finitely many parameters, using one-coordinate monotonicity at
successive insertions. No independence of formula subexpressions is needed. -/
private theorem probability_replaceOn_mono (φ : Formula) (hφ : φ.IsMonotone)
    (m₁ m₂ : IndependentModel) (s : Finset Nat)
    (h : ∀ i ∈ s, m₁.probTrue i ≤ m₂.probTrue i) :
    φ.probability m₁ ≤ φ.probability (m₁.replaceOn m₂ s) := by
  induction s using Finset.induction_on with
  | empty =>
      apply le_of_eq
      apply probability_congr
      intro i _
      simp [IndependentModel.replaceOn]
  | @insert i s hi ih =>
      have hs : ∀ j ∈ s, m₁.probTrue j ≤ m₂.probTrue j := by
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      have hii : m₁.probTrue i ≤ m₂.probTrue i := h i (Finset.mem_insert_self i s)
      calc
        φ.probability m₁ ≤ φ.probability (m₁.replaceOn m₂ s) := ih hs
        _ = φ.probability ((m₁.replaceOn m₂ s).withProb i (m₁.probTrue i)
              (m₁.nonneg i) (m₁.le_one i)) := by
          apply probability_congr
          intro j _
          by_cases hji : j = i
          · subst j
            simp [IndependentModel.replaceOn, IndependentModel.withProb, hi]
          · simp [IndependentModel.withProb, hji]
        _ ≤ φ.probability ((m₁.replaceOn m₂ s).withProb i (m₂.probTrue i)
              (m₂.nonneg i) (m₂.le_one i)) :=
          probability_withProb_mono φ hφ _ i _ _ _ _ _ _ hii
        _ = φ.probability (m₁.replaceOn m₂ (insert i s)) := by
          apply probability_congr
          intro j _
          by_cases hji : j = i
          · subst j
            simp [IndependentModel.replaceOn, IndependentModel.withProb]
          · simp [IndependentModel.replaceOn, IndependentModel.withProb, hji]

/-- A monotone formula's probability is monotone in all its occurring
parameters simultaneously. Unused indices require no comparison. -/
theorem probability_mono (φ : Formula) (hφ : φ.IsMonotone)
    (m₁ m₂ : IndependentModel)
    (h : ∀ i ∈ φ.vars, m₁.probTrue i ≤ m₂.probTrue i) :
    φ.probability m₁ ≤ φ.probability m₂ := by
  calc
    φ.probability m₁ ≤ φ.probability (m₁.replaceOn m₂ φ.vars) :=
      probability_replaceOn_mono φ hφ m₁ m₂ φ.vars h
    _ = φ.probability m₂ := by
      apply probability_congr
      intro i hi
      simp [IndependentModel.replaceOn, hi]

/-- Parameter-wise lower and upper bounds propagate to event probability. -/
theorem probability_interval_bounds (φ : Formula) (hφ : φ.IsMonotone)
    (lower actual upper : IndependentModel)
    (hLower : ∀ i ∈ φ.vars, lower.probTrue i ≤ actual.probTrue i)
    (hUpper : ∀ i ∈ φ.vars, actual.probTrue i ≤ upper.probTrue i) :
    φ.probability lower ≤ φ.probability actual ∧
      φ.probability actual ≤ φ.probability upper :=
  ⟨probability_mono φ hφ lower actual hLower,
    probability_mono φ hφ actual upper hUpper⟩

end Formula
namespace FaultTree

/-- Simultaneously lowering component failure probabilities cannot increase
system failure probability, including in trees with shared components. -/
theorem failureProbability_mono (t : FaultTree) (m₁ m₂ : IndependentModel)
    (h : ∀ i ∈ t.toFormula.vars, m₁.probTrue i ≤ m₂.probTrue i) :
    t.failureProbability m₁ ≤ t.failureProbability m₂ := by
  rw [failureProbability_eq_formula, failureProbability_eq_formula]
  exact Formula.probability_mono _ t.toFormula_isMonotone m₁ m₂ h

/-- A component-wise parameter box gives lower and upper system probabilities. -/
theorem failureProbability_interval_bounds (t : FaultTree)
    (lower actual upper : IndependentModel)
    (hLower : ∀ i ∈ t.toFormula.vars, lower.probTrue i ≤ actual.probTrue i)
    (hUpper : ∀ i ∈ t.toFormula.vars, actual.probTrue i ≤ upper.probTrue i) :
    t.failureProbability lower ≤ t.failureProbability actual ∧
      t.failureProbability actual ≤ t.failureProbability upper :=
  ⟨failureProbability_mono t lower actual hLower,
    failureProbability_mono t actual upper hUpper⟩

/-- The interval endpoints can be computed by the verified Tseitin encoding
with neutral auxiliary weights. This joins parameter bounds to CNF correctness. -/
theorem failureProbability_cnf_interval_bounds (t : FaultTree)
    (lower actual upper : IndependentModel)
    (hLower : ∀ i ∈ t.toFormula.vars, lower.probTrue i ≤ actual.probTrue i)
    (hUpper : ∀ i ∈ t.toFormula.vars, actual.probTrue i ≤ upper.probTrue i) :
    t.toFormula.weightedCNFModelCount lower.weight ≤ t.failureProbability actual ∧
      t.failureProbability actual ≤ t.toFormula.weightedCNFModelCount upper.weight := by
  rw [← failureProbability_eq_cnf, ← failureProbability_eq_cnf]
  exact failureProbability_interval_bounds t lower actual upper hLower hUpper

end FaultTree
end Tseitin
