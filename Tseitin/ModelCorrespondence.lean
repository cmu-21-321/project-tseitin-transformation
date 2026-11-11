import Tseitin.FiniteCNF
import Tseitin.Uniqueness

set_option linter.style.header false

/-!
# Correspondence between finite source and target models

The forward map retains the source assignment and obtains the generated
auxiliary values from `extendAssignment`. Its satisfaction proof connects
the finite representation with the existing total-assignment correctness theorem.
-/

namespace Tseitin
namespace Formula

/-- Extend a finite source assignment to the generated auxiliary variables. -/
def Assignment.toCNF {φ : Formula} (a : φ.Assignment) : φ.CNFAssignment :=
  (a, fun k => extendAssignment φ 0 (initialAssignment a.toTotal) (.aux k.val))

/-- The forward map preserves the source assignment exactly. -/
@[simp] theorem Assignment.toCNF_fst {φ : Formula} (a : φ.Assignment) :
    a.toCNF.1 = a := rfl

/-- The finite forward map and the total extension evaluate the generated
CNF identically, since they agree on every variable allowed by its bounds. -/
theorem Assignment.toCNF_eval {φ : Formula} (a : φ.Assignment) :
    CNF.eval a.toCNF.toTotal (Tseitin.toCNF φ) =
      CNF.eval (extendAssignment φ 0 (initialAssignment a.toTotal))
        (Tseitin.toCNF φ) := by
  apply CNF.eval_eq_of_agree _ _ 0 φ.numConnectives _ (toCNF_inRange φ)
  intro v hv
  cases v with
  | original n =>
      simp [CNFAssignment.toTotal, Assignment.toCNF,
        extendAssignment_original, initialAssignment]
  | aux k =>
      have hk : k < φ.numConnectives := hv.2
      simp [CNFAssignment.toTotal, Assignment.toCNF, hk]

/-- Every finite source model extends to a finite model of the generated CNF. -/
theorem Assignment.toCNF_mem {φ : Formula} (a : φ.Assignment)
    (ha : a ∈ φ.models) : a.toCNF ∈ φ.cnfModels := by
  apply (mem_cnfModels φ _).mpr
  rw [Assignment.toCNF_eval]
  apply toCNF_complete
  exact (mem_models φ a).mp ha


/-- Restricting a finite CNF model to its source component gives a source model. -/
theorem CNFAssignment.fst_mem {φ : Formula} (b : φ.CNFAssignment)
    (hb : b ∈ φ.cnfModels) : b.1 ∈ φ.models := by
  apply (mem_models φ b.1).mpr
  exact toCNF_sound φ b.toTotal ((mem_cnfModels φ b).mp hb)

/-- Re-extending the source component of a CNF model recovers that model.
The auxiliary component is forced by the uniqueness theorem. -/
theorem CNFAssignment.reextend_eq {φ : Formula} (b : φ.CNFAssignment)
    (hb : b ∈ φ.cnfModels) : b.1.toCNF = b := by
  apply Prod.ext
  · rfl
  · funext k
    have haux := toCNF_aux_eq_extension φ b.1.toTotal b.toTotal
      (fun _ => rfl) ((mem_cnfModels φ b).mp hb) k.val k.isLt
    change extendAssignment φ 0 (initialAssignment b.1.toTotal) (.aux k.val) = b.2 k
    simpa only [CNFAssignment.toTotal_aux] using haux.symm

end Formula
end Tseitin
