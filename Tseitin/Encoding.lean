import Tseitin.CNF

namespace Tseitin

/-- The clauses encoding d ↔ (a ∧ b). -/
def encodeAnd (d a b : Var) : CNF :=
  [ [.neg d, .pos a],
    [.neg d, .pos b],
    [.neg a, .neg b, .pos d] ]

/-- The AND encoding holds exactly when d has the value of a ∧ b. -/
theorem encodeAnd_correct (τ : Var → Bool) (d a b : Var) :
    CNF.eval τ (encodeAnd d a b) = true ↔
      τ d = (τ a && τ b) := by
  cases hd : τ d <;>
    cases ha : τ a <;>
      cases hb : τ b <;>
        simp [encodeAnd, CNF.eval, Clause.eval, Literal.eval, hd, ha, hb]


/-- The clauses encoding d ↔ (a ∨ b). -/
def encodeOr (d a b : Var) : CNF :=
  [ [.neg d, .pos a, .pos b],
    [.neg a, .pos d],
    [.neg b, .pos d] ]

/-- The OR encoding holds exactly when d has the value of a ∨ b. -/
theorem encodeOr_correct (τ : Var → Bool) (d a b : Var) :
    CNF.eval τ (encodeOr d a b) = true ↔
      τ d = (τ a || τ b) := by
  cases hd : τ d <;>
    cases ha : τ a <;>
      cases hb : τ b <;>
        simp [encodeOr, CNF.eval, Clause.eval, Literal.eval, hd, ha, hb]

/-- The clauses encoding d ↔ ¬a. -/
def encodeNot (d a : Var) : CNF :=
  [ [.neg d, .neg a],
    [.pos d, .pos a] ]

/-- The NOT encoding holds exactly when d has the opposite value of a. -/
theorem encodeNot_correct (τ : Var → Bool) (d a : Var) :
    CNF.eval τ (encodeNot d a) = true ↔
      τ d = !(τ a) := by
  cases hd : τ d <;>
    cases ha : τ a <;>
      simp [encodeNot, CNF.eval, Clause.eval, Literal.eval, hd, ha]

end Tseitin
