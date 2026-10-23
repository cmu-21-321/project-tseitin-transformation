namespace Tseitin

/-- Propositional formulas with variables indexed by natural numbers. -/
inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving Repr

namespace Formula

/-- Evaluate a formula under a Boolean assignment to its variables. -/
def eval (σ : Nat → Bool) : Formula → Bool
  | .var n => σ n
  | .neg φ => !(eval σ φ)
  | .conj φ ψ => eval σ φ && eval σ ψ
  | .disj φ ψ => eval σ φ || eval σ ψ

end Formula

/-- p ∧ (q ∨ r), where variables 0, 1, 2 represent p, q, r. -/
def demo : Formula :=
  .conj (.var 0) (.disj (.var 1) (.var 2))

#eval demo.eval (fun n => (n == 0) || (n == 2))
#eval demo.eval (fun n => n == 0)

end Tseitin
