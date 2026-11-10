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

/--
Clauses and CNFs are represented as lists so that the encoder can
construct them directly and combine generated clauses by concatenation.
No ordering or duplicate-removal invariant is required.

List order and repeated entries do not affect the Boolean meaning of
disjunction or conjunction. They do affect the stored representation;
our clause-count bounds count list entries, including any duplicates.
-/

abbrev Clause := List Literal
abbrev CNF := List Clause

/--
Evaluate a clause as a finite disjunction of its literals.

Use Boolean semantics to keep evaluation executable, consistent
with `Formula.eval` and `Literal.eval`. Satisfaction is expressed in
the correctness theorems by requiring the result to equal `true`.

`List.any` implements disjunction: the clause is true exactly when
some literal evaluates to true. The empty clause evaluates to false,
representing an unsatisfiable disjunction.
-/
def Clause.eval (τ : Var → Bool) (clause : Clause) : Bool :=
  clause.any (Literal.eval τ)

/--
Evaluate a CNF as a finite conjunction of its clauses.

`List.all` implements conjunction: every clause must evaluate to true.
The empty CNF evaluates to true, representing the absence of constraints.
In contrast, a CNF containing an empty clause evaluates to false.

This representation also supports compositional proofs: evaluating
concatenated clause lists corresponds to conjoining their evaluations,
as established by `CNF.eval_append`.
-/
def CNF.eval (τ : Var → Bool) (cnf : CNF) : Bool :=
  cnf.all (Clause.eval τ)

#eval Clause.eval (fun _ => false) [.neg (.original 0), .pos (.aux 0)]
#eval CNF.eval (fun _ => false) []
#eval CNF.eval (fun _ => false) [[]]

end Tseitin
