import Tseitin.Basic
import Mathlib.Data.Finset.Basic

-- Keep the course project's header policy rather than Mathlib's prescribed header.
set_option linter.style.header false

/-!
# Variables occurring in a formula

`Formula.vars` collects the distinct variable indices occurring in a formula.
`Formula.eval_eq_of_agree` proves that agreement on these indices is sufficient
for equal evaluation, regardless of assignments to other variables.
-/

namespace Tseitin
namespace Formula

/-- The finite set of variable indices occurring in a formula.
Repeated occurrences are counted once; unused indices are excluded. -/
def vars : Formula → Finset Nat
  | .var n => {n}
  | .neg φ => φ.vars
  | .conj φ ψ => φ.vars ∪ ψ.vars
  | .disj φ ψ => φ.vars ∪ ψ.vars

/-- Formula evaluation depends only on its occurring variables. -/
theorem eval_eq_of_agree (φ : Formula) (σ ρ : Nat → Bool)
    (h : ∀ n ∈ φ.vars, σ n = ρ n) :
    φ.eval σ = φ.eval ρ := by
  induction φ with
  | var n =>
      exact h n (by simp [vars])
  | neg φ ih =>
      exact congrArg Bool.not (ih h)
  | conj φ ψ ihφ ihψ =>
      have hφ : ∀ n ∈ φ.vars, σ n = ρ n := by
        intro n hn
        exact h n (Finset.mem_union.mpr (Or.inl hn))
      have hψ : ∀ n ∈ ψ.vars, σ n = ρ n := by
        intro n hn
        exact h n (Finset.mem_union.mpr (Or.inr hn))
      simp only [eval, ihφ hφ, ihψ hψ]
  | disj φ ψ ihφ ihψ =>
      have hφ : ∀ n ∈ φ.vars, σ n = ρ n := by
        intro n hn
        exact h n (Finset.mem_union.mpr (Or.inl hn))
      have hψ : ∀ n ∈ ψ.vars, σ n = ρ n := by
        intro n hn
        exact h n (Finset.mem_union.mpr (Or.inr hn))
      simp only [eval, ihφ hφ, ihψ hψ]

end Formula
end Tseitin
