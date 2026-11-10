import Tseitin.FiniteAssignment
import Mathlib.Data.Fintype.Pi

set_option linter.style.header false

/-!
# Counting models of source formulas

We enumerate assignments on the occurring variables and retain exactly those
that satisfy the formula. This executable reference counter is exhaustive;
it is intended for small instances rather than efficient large-scale counting.
-/

namespace Tseitin
namespace Formula

/-- All satisfying assignments on the variables occurring in `φ`. -/
def models (φ : Formula) : Finset φ.Assignment :=
  Finset.univ.filter (fun a => φ.evalFinite a = true)

/-- The number of satisfying assignments on the occurring variables. -/
def modelCount (φ : Formula) : Nat :=
  φ.models.card

/-- Membership in the model set is exactly finite-assignment satisfaction. -/
@[simp] theorem mem_models (φ : Formula) (a : φ.Assignment) :
    a ∈ φ.models ↔ φ.evalFinite a = true := by
  simp [models]

/-- A positive finite model count is equivalent to satisfiability under
our original total-assignment semantics. -/
theorem modelCount_pos_iff (φ : Formula) :
    0 < φ.modelCount ↔ ∃ σ : Nat → Bool, φ.eval σ = true := by
  constructor
  · intro h
    have hne : φ.models.Nonempty := Finset.card_pos.mp h
    obtain ⟨a, ha⟩ := hne
    exact ⟨a.toTotal, (mem_models φ a).mp ha⟩
  · rintro ⟨σ, hσ⟩
    apply Finset.card_pos.mpr
    refine ⟨restrictAssignment φ σ, ?_⟩
    apply (mem_models φ _).mpr
    rw [evalFinite_restrictAssignment]
    exact hσ

end Formula

#eval (Formula.disj (.var 2) (.neg (.var 2))).modelCount
#eval (Formula.conj (.var 2) (.neg (.var 2))).modelCount
#eval (Formula.disj (.var 2) (.var 100)).modelCount

end Tseitin
