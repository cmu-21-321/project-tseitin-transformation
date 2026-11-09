import Tseitin.Assignment

namespace Tseitin

/-- The extension restricts to the same original assignment. -/
theorem restrictOriginal_extendAssignment (φ : Formula) (start : Nat)
    (τ : Var → Bool) :
    restrictOriginal (extendAssignment φ start τ) = restrictOriginal τ := by
  funext n
  exact extendAssignment_original φ start τ n

/-- Under the constructed extension, the root has the source formula's value. -/
theorem extendAssignment_root (φ : Formula) (start : Nat) (τ : Var → Bool) :
    extendAssignment φ start τ (encode φ start).root =
      φ.eval (restrictOriginal τ) := by
  have hroot := encode_root_correct φ start (extendAssignment φ start τ)
    (extendAssignment_satisfies φ start τ)
  simpa only [restrictOriginal_extendAssignment] using hroot

/-- A satisfying source assignment extends to satisfy the final CNF. -/
theorem toCNF_complete (φ : Formula) (τ : Var → Bool)
    (h : φ.eval (restrictOriginal τ) = true) :
    CNF.eval (extendAssignment φ 0 τ) (toCNF φ) = true := by
  apply (CNF.eval_append_true _ _ _).mpr
  constructor
  · exact extendAssignment_satisfies φ 0 τ
  · have hroot := (extendAssignment_root φ 0 τ).trans h
    simpa [CNF.eval, Clause.eval, Literal.eval] using hroot

/-- Lift a source assignment, initially setting every auxiliary variable to false. -/
def initialAssignment (σ : Nat → Bool) : Var → Bool
  | .original n => σ n
  | .aux _ => false

/-- A source assignment satisfies the formula exactly when it has a CNF extension. -/
theorem toCNF_correct (φ : Formula) (σ : Nat → Bool) :
    φ.eval σ = true ↔
      ∃ τ : Var → Bool,
        (∀ n, τ (.original n) = σ n) ∧ CNF.eval τ (toCNF φ) = true := by
  constructor
  · intro h
    refine ⟨extendAssignment φ 0 (initialAssignment σ), ?_, ?_⟩
    · intro n
      exact extendAssignment_original φ 0 (initialAssignment σ) n
    · apply toCNF_complete
      exact h
  · rintro ⟨τ, hagree, hcnf⟩
    have hσ : restrictOriginal τ = σ := by
      funext n
      exact hagree n
    have hs := toCNF_sound φ τ hcnf
    simpa only [hσ] using hs

/-- The source formula and its generated CNF are equisatisfiable. -/
theorem toCNF_equisatisfiable (φ : Formula) :
    (∃ σ : Nat → Bool, φ.eval σ = true) ↔
      ∃ τ : Var → Bool, CNF.eval τ (toCNF φ) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, _, hτ⟩ := (toCNF_correct φ σ).mp hσ
    exact ⟨τ, hτ⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨restrictOriginal τ, toCNF_sound φ τ hτ⟩

end Tseitin
