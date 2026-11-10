import Tseitin.Support

set_option linter.style.header false

/-!
# Finite assignments for source formulas

Assignments are defined only on variables occurring in the formula.
Extending them by `false` outside this set connects finite evaluation
with the existing total-assignment semantics.
-/

namespace Tseitin
namespace Formula

/-- A Boolean assignment to exactly the variables occurring in `φ`. -/
abbrev Assignment (φ : Formula) := {n : Nat // n ∈ φ.vars} → Bool

/-- Extend a finite assignment by `false` on unused variable indices. -/
def Assignment.toTotal {φ : Formula} (a : φ.Assignment) : Nat → Bool :=
  fun n => if h : n ∈ φ.vars then a ⟨n, h⟩ else false

/-- Restrict a total assignment to the variables occurring in `φ`. -/
def restrictAssignment (φ : Formula) (σ : Nat → Bool) : φ.Assignment :=
  fun n => σ n.val

/-- Extension preserves the value of every occurring variable. -/
@[simp] theorem Assignment.toTotal_apply {φ : Formula} (a : φ.Assignment)
    (n : Nat) (hn : n ∈ φ.vars) :
    a.toTotal n = a ⟨n, hn⟩ := by
  simp [Assignment.toTotal, hn]

/-- Restricting an extension recovers the original finite assignment. -/
@[simp] theorem restrictAssignment_toTotal (φ : Formula) (a : φ.Assignment) :
    restrictAssignment φ a.toTotal = a := by
  funext n
  exact Assignment.toTotal_apply a n.val n.property

/-- Evaluate using a finite assignment and its total extension. -/
def evalFinite (φ : Formula) (a : φ.Assignment) : Bool :=
  φ.eval a.toTotal

/-- Restriction to occurring variables preserves formula evaluation. -/
theorem evalFinite_restrictAssignment (φ : Formula) (σ : Nat → Bool) :
    φ.evalFinite (restrictAssignment φ σ) = φ.eval σ := by
  apply eval_eq_of_agree
  intro n hn
  simp [Assignment.toTotal, restrictAssignment, hn]

end Formula
end Tseitin
