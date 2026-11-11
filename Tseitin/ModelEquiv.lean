import Tseitin.ModelCorrespondence
import Mathlib.Data.Fintype.Card

set_option linter.style.header false

/-!
# Model bijection and preservation of model counts

Extension and restriction give inverse maps between finite source models
and finite models of the generated CNF. The source domain consists of the
occurring variables; the target adds exactly the generated auxiliaries.
Their model counts are therefore equal for every formula.
-/

namespace Tseitin
namespace Formula

/-- Extension and restriction form a bijection between the finite model sets. -/
def modelEquiv (φ : Formula) :
    {a : φ.Assignment // a ∈ φ.models} ≃
      {b : φ.CNFAssignment // b ∈ φ.cnfModels} where
  toFun a := ⟨a.val.toCNF, Assignment.toCNF_mem a.val a.property⟩
  invFun b := ⟨b.val.1, CNFAssignment.fst_mem b.val b.property⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    exact CNFAssignment.reextend_eq b.val b.property

/-- Tseitin encoding preserves the number of models over the specified
finite variable domains. -/
theorem modelCount_eq_cnfModelCount (φ : Formula) :
    φ.modelCount = φ.cnfModelCount := by
  have h := Fintype.card_congr (modelEquiv φ)
  simpa only [Fintype.card_coe, modelCount, cnfModelCount] using h

end Formula
end Tseitin
