import Tseitin.ModelEquiv
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.header false

/-!
# Rational weights and weighted model counts

Source weights assign a rational number to each truth value of each original
variable. Auxiliary truth values both receive weight one. No probability
normalization or independence interpretation is assumed in these definitions.
-/

open scoped BigOperators

namespace Tseitin

/-- Preserve source weights and give both auxiliary truth values weight one. -/
def extendWeight (w : Nat → Bool → ℚ) : Var → Bool → ℚ
  | .original n => w n
  | .aux _ => fun _ => 1

namespace Formula

/-- Multiply weights once per distinct occurring source variable. -/
def Assignment.weight {φ : Formula} (a : φ.Assignment)
    (w : Nat → Bool → ℚ) : ℚ :=
  ∏ n : {n : Nat // n ∈ φ.vars}, w n.val (a n)

/-- Multiply the weights of the original and generated auxiliary values. -/
def CNFAssignment.weight {φ : Formula} (b : φ.CNFAssignment)
    (w : Nat → Bool → ℚ) : ℚ :=
  (∏ n : {n : Nat // n ∈ φ.vars}, extendWeight w (.original n.val) (b.1 n)) *
    ∏ k : Fin φ.numConnectives, extendWeight w (.aux k.val) (b.2 k)

/-- Neutral auxiliary weights leave only the source component's weight. -/
@[simp] theorem CNFAssignment.weight_eq_source {φ : Formula}
    (b : φ.CNFAssignment) (w : Nat → Bool → ℚ) :
    b.weight w = b.1.weight w := by
  simp [CNFAssignment.weight, Assignment.weight, extendWeight]

/-- Extending a source assignment preserves its weight. -/
@[simp] theorem Assignment.toCNF_weight {φ : Formula}
    (a : φ.Assignment) (w : Nat → Bool → ℚ) :
    a.toCNF.weight w = a.weight w := by
  rw [CNFAssignment.weight_eq_source, Assignment.toCNF_fst]

/-- Sum the weights of all finite source models. -/
def weightedModelCount (φ : Formula) (w : Nat → Bool → ℚ) : ℚ :=
  ∑ a ∈ φ.models, a.weight w

/-- Sum the weights of all finite models of the generated CNF. -/
def weightedCNFModelCount (φ : Formula) (w : Nat → Bool → ℚ) : ℚ :=
  ∑ b ∈ φ.cnfModels, b.weight w


/-- Tseitin encoding preserves weighted model counts when both truth values
of every generated auxiliary variable have weight one. -/
theorem weightedModelCount_eq_weightedCNFModelCount
    (φ : Formula) (w : Nat → Bool → ℚ) :
    φ.weightedModelCount w = φ.weightedCNFModelCount w := by
  have h := (modelEquiv φ).sum_comp
    (fun b : {b : φ.CNFAssignment // b ∈ φ.cnfModels} => b.val.weight w)
  change
    (∑ a : {a : φ.Assignment // a ∈ φ.models}, a.val.toCNF.weight w) =
      (∑ b : {b : φ.CNFAssignment // b ∈ φ.cnfModels}, b.val.weight w) at h
  unfold weightedModelCount weightedCNFModelCount
  rw [Finset.sum_subtype φ.models (fun _ => Iff.rfl) (fun a => a.weight w),
      Finset.sum_subtype φ.cnfModels (fun _ => Iff.rfl) (fun b => b.weight w)]
  simpa only [Assignment.toCNF_weight] using h



end Formula
end Tseitin
