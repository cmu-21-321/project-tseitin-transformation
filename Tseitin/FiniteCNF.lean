import Tseitin.ModelCount
import Tseitin.Allocation
import Mathlib.Data.Fintype.Prod

set_option linter.style.header false

/-!
# Finite assignments for generated CNFs

A target assignment consists of a source assignment and values for exactly
`numConnectives` auxiliary variables. Indices outside these finite domains
are assigned `false` when evaluating with the existing CNF semantics.
-/

namespace Tseitin
namespace Formula

/-- Assignments to the source variables and exactly the generated auxiliaries. -/
abbrev CNFAssignment (φ : Formula) :=
  φ.Assignment × (Fin φ.numConnectives → Bool)

/-- Interpret a finite target assignment as a total assignment. -/
def CNFAssignment.toTotal {φ : Formula} (a : φ.CNFAssignment) : Var → Bool
  | .original n => a.1.toTotal n
  | .aux k => if h : k < φ.numConnectives then a.2 ⟨k, h⟩ else false

/-- Total extension preserves the source component. -/
@[simp] theorem CNFAssignment.toTotal_original {φ : Formula}
    (a : φ.CNFAssignment) (n : Nat) :
    a.toTotal (.original n) = a.1.toTotal n := rfl

/-- Total extension preserves every generated auxiliary value. -/
@[simp] theorem CNFAssignment.toTotal_aux {φ : Formula}
    (a : φ.CNFAssignment) (k : Fin φ.numConnectives) :
    a.toTotal (.aux k.val) = a.2 k := by
  simp [CNFAssignment.toTotal, k.isLt]

/-- The finite models of the CNF generated from `φ`. -/
def cnfModels (φ : Formula) : Finset φ.CNFAssignment :=
  Finset.univ.filter (fun a => CNF.eval a.toTotal (toCNF φ) = true)

/-- Count models over the source variables and generated auxiliaries only. -/
def cnfModelCount (φ : Formula) : Nat :=
  φ.cnfModels.card

/-- Membership in the target model set is exactly CNF satisfaction. -/
@[simp] theorem mem_cnfModels (φ : Formula) (a : φ.CNFAssignment) :
    a ∈ φ.cnfModels ↔ CNF.eval a.toTotal (toCNF φ) = true := by
  simp [cnfModels]

end Formula

#eval (Formula.disj (.var 2) (.neg (.var 2))).cnfModelCount
#eval (Formula.conj (.var 2) (.neg (.var 2))).cnfModelCount
#eval (Formula.disj (.var 2) (.var 100)).cnfModelCount

end Tseitin
