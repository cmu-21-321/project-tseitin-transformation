import Tseitin.Allocation

namespace Tseitin

/-- Count defining clauses: two per NOT and three per AND or OR. -/
def Formula.clauseCount : Formula → Nat
  | .var _ => 0
  | .neg φ => φ.clauseCount + 2
  | .conj φ ψ => φ.clauseCount + ψ.clauseCount + 3
  | .disj φ ψ => φ.clauseCount + ψ.clauseCount + 3

/-- The recursive encoder generates exactly the predicted number of clauses. -/
theorem encode_clauseCount (φ : Formula) (start : Nat) :
    (encode φ start).clauses.length = φ.clauseCount := by
  induction φ generalizing start with
  | var n =>
      simp [encode, Formula.clauseCount]
  | neg φ ih =>
      simp [encode, encodeNot, Formula.clauseCount, ih]
  | conj φ ψ ihφ ihψ =>
      simp [encode, encodeAnd, Formula.clauseCount,
        ihφ, ihψ, Nat.add_assoc]
  | disj φ ψ ihφ ihψ =>
      simp [encode, encodeOr, Formula.clauseCount,
        ihφ, ihψ, Nat.add_assoc]

/-- Each connective contributes at most three defining clauses. -/
theorem Formula.clauseCount_le (φ : Formula) :
    φ.clauseCount ≤ 3 * φ.numConnectives := by
  induction φ with
  | var n =>
      simp [Formula.clauseCount, Formula.numConnectives]
  | neg φ ih =>
      simp only [Formula.clauseCount, Formula.numConnectives]
      omega
  | conj φ ψ ihφ ihψ =>
      simp only [Formula.clauseCount, Formula.numConnectives]
      omega
  | disj φ ψ ihφ ihψ =>
      simp only [Formula.clauseCount, Formula.numConnectives]
      omega

/-- The final CNF adds exactly one clause asserting the root variable. -/
theorem toCNF_clauseCount (φ : Formula) :
    (toCNF φ).length = φ.clauseCount + 1 := by
  simp [toCNF, encode_clauseCount]

/-- The final CNF has at most three clauses per connective, plus the root clause. -/
theorem toCNF_length_le (φ : Formula) :
    (toCNF φ).length ≤ 3 * φ.numConnectives + 1 := by
  rw [toCNF_clauseCount]
  exact Nat.add_le_add_right (Formula.clauseCount_le φ) 1

end Tseitin
