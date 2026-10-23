import Tseitin.Basic

namespace Tseitin

/-- Original variables and auxiliary variables have separate names. -/
inductive Var where
  | original : Nat → Var
  | aux : Nat → Var
  deriving Repr, DecidableEq

/-- A literal is a variable or its negation. -/
inductive Literal where
  | pos : Var → Literal
  | neg : Var → Literal
  deriving Repr, DecidableEq

/-- Evaluate a literal under an assignment to both kinds of variables. -/
def Literal.eval (τ : Var → Bool) : Literal → Bool
  | .pos v => τ v
  | .neg v => !(τ v)

abbrev Clause := List Literal
abbrev CNF := List Clause

/-- A clause is true when at least one of its literals is true. -/
def Clause.eval (τ : Var → Bool) (clause : Clause) : Bool :=
  clause.any (Literal.eval τ)

/-- A CNF is true when all of its clauses are true. -/
def CNF.eval (τ : Var → Bool) (cnf : CNF) : Bool :=
  cnf.all (Clause.eval τ)

#eval Clause.eval (fun _ => false) [.neg (.original 0), .pos (.aux 0)]
#eval CNF.eval (fun _ => false) []
#eval CNF.eval (fun _ => false) [[]]

end Tseitin
