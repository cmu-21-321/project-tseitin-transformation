import Tseitin.Basic

/-!
# Static Boolean fault trees

A component variable is true exactly when that component has failed.
An AND gate fails when both children fail; an OR gate fails when either
child fails. Repeated component indices denote the same basic event.
-/

namespace Tseitin

/-- A finite static fault tree with basic events and binary AND/OR gates. -/
inductive FaultTree where
  | component : Nat → FaultTree
  | andGate : FaultTree → FaultTree → FaultTree
  | orGate : FaultTree → FaultTree → FaultTree
  deriving Repr

namespace FaultTree

/-- Evaluate failure directly under an assignment of basic failure events. -/
def fails (σ : Nat → Bool) : FaultTree → Bool
  | .component n => σ n
  | .andGate left right => left.fails σ && right.fails σ
  | .orGate left right => left.fails σ || right.fails σ

/-- Translate a fault tree into a formula describing its failure event. -/
def toFormula : FaultTree → Formula
  | .component n => .var n
  | .andGate left right => .conj left.toFormula right.toFormula
  | .orGate left right => .disj left.toFormula right.toFormula

/-- Translation preserves the failure event under every basic-event assignment. -/
theorem toFormula_correct (t : FaultTree) (σ : Nat → Bool) :
    t.toFormula.eval σ = t.fails σ := by
  induction t with
  | component n => rfl
  | andGate left right ihLeft ihRight =>
      simp only [toFormula, Formula.eval, fails, ihLeft, ihRight]
  | orGate left right ihLeft ihRight =>
      simp only [toFormula, Formula.eval, fails, ihLeft, ihRight]

/-- Two redundant branches share a supply (0), with individual units 1 and 2.
A branch fails if its supply or unit fails; the system fails if both branches fail. -/
def sharedSupply : FaultTree :=
  .andGate
    (.orGate (.component 0) (.component 1))
    (.orGate (.component 0) (.component 2))

#eval sharedSupply.fails (fun _ => false)
#eval sharedSupply.fails (fun n => n == 0)
#eval sharedSupply.fails (fun n => n == 1)
#eval sharedSupply.fails (fun n => n == 1 || n == 2)

end FaultTree
end Tseitin
