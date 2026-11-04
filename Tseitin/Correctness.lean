import Tseitin.Allocation

namespace Tseitin

/-- Restrict an assignment to the original propositional variables. -/
def restrictOriginal (τ : Var → Bool) : Nat → Bool :=
  fun n => τ (.original n)

/-- Concatenating CNFs corresponds to conjunction of their evaluations. -/
theorem CNF.eval_append (τ : Var → Bool) (xs ys : CNF) :
    CNF.eval τ (xs ++ ys) = (CNF.eval τ xs && CNF.eval τ ys) := by
  simp [CNF.eval]

/-- A concatenation is satisfied exactly when both component CNFs are satisfied. -/
theorem CNF.eval_append_true (τ : Var → Bool) (xs ys : CNF) :
    CNF.eval τ (xs ++ ys) = true ↔
      CNF.eval τ xs = true ∧ CNF.eval τ ys = true := by
  simp [CNF.eval_append]

/-- Satisfying the defining clauses forces the root to equal the source formula. -/
theorem encode_root_correct (φ : Formula) (start : Nat) (τ : Var → Bool)
    (h : CNF.eval τ (encode φ start).clauses = true) :
    τ (encode φ start).root = φ.eval (restrictOriginal τ) := by
  induction φ generalizing start with
  | var n =>
      rfl
  | neg φ ih =>
      have hs := (CNF.eval_append_true τ _ _).mp h
      have hg := (encodeNot_correct τ _ _).mp hs.2
      change τ (.aux (encode φ start).nextFresh) =
        !(φ.eval (restrictOriginal τ))
      rw [hg, ih start hs.1]
  | conj φ ψ ihφ ihψ =>
      have hs := (CNF.eval_append_true τ _ _).mp h
      have hc := (CNF.eval_append_true τ _ _).mp hs.1
      have hg := (encodeAnd_correct τ _ _ _).mp hs.2
      change τ (.aux (encode ψ (encode φ start).nextFresh).nextFresh) =
        (φ.eval (restrictOriginal τ) && ψ.eval (restrictOriginal τ))
      rw [hg, ihφ start hc.1, ihψ (encode φ start).nextFresh hc.2]
  | disj φ ψ ihφ ihψ =>
      have hs := (CNF.eval_append_true τ _ _).mp h
      have hc := (CNF.eval_append_true τ _ _).mp hs.1
      have hg := (encodeOr_correct τ _ _ _).mp hs.2
      change τ (.aux (encode ψ (encode φ start).nextFresh).nextFresh) =
        (φ.eval (restrictOriginal τ) || ψ.eval (restrictOriginal τ))
      rw [hg, ihφ start hc.1, ihψ (encode φ start).nextFresh hc.2]

/-- Every satisfying assignment of the final CNF satisfies the original formula. -/
theorem toCNF_sound (φ : Formula) (τ : Var → Bool)
    (h : CNF.eval τ (toCNF φ) = true) :
    φ.eval (restrictOriginal τ) = true := by
  have hs := (CNF.eval_append_true τ _ _).mp h
  have hroot : τ (encode φ 0).root = true := by
    simpa [CNF.eval, Clause.eval, Literal.eval] using hs.2
  rw [← encode_root_correct φ 0 τ hs.1]
  exact hroot

end Tseitin
