import Tseitin.Completeness

namespace Tseitin

/-- Assignments agreeing on the original variables and satisfying the
same defining clauses agree on the root representative. -/
theorem encode_root_unique (φ : Formula) (start : Nat)
    (τ₁ τ₂ : Var → Bool)
    (hOriginal : ∀ n, τ₁ (.original n) = τ₂ (.original n))
    (h₁ : CNF.eval τ₁ (encode φ start).clauses = true)
    (h₂ : CNF.eval τ₂ (encode φ start).clauses = true) :
    τ₁ (encode φ start).root = τ₂ (encode φ start).root := by
  have hRestrict : restrictOriginal τ₁ = restrictOriginal τ₂ := by
    funext n
    exact hOriginal n
  rw [encode_root_correct φ start τ₁ h₁,
      encode_root_correct φ start τ₂ h₂,
      hRestrict]


/-- Fixing the original assignment uniquely determines all auxiliary
values in the interval allocated by the encoder. -/
theorem encode_aux_unique (φ : Formula) (start : Nat)
    (τ₁ τ₂ : Var → Bool)
    (hOriginal : ∀ n, τ₁ (.original n) = τ₂ (.original n))
    (h₁ : CNF.eval τ₁ (encode φ start).clauses = true)
    (h₂ : CNF.eval τ₂ (encode φ start).clauses = true)
    (k : Nat) (hlo : start ≤ k)
    (hhi : k < (encode φ start).nextFresh) :
    τ₁ (.aux k) = τ₂ (.aux k) := by
  induction φ generalizing start with
  | var n =>
      change k < start at hhi
      omega
  | neg φ ih =>
      have hs₁ := (CNF.eval_append_true τ₁ _ _).mp h₁
      have hs₂ := (CNF.eval_append_true τ₂ _ _).mp h₂
      by_cases hk : k < (encode φ start).nextFresh
      · exact ih start hs₁.1 hs₂.1 hlo hk
      · have heq : k = (encode φ start).nextFresh := by
          change k < (encode φ start).nextFresh + 1 at hhi
          omega
        subst k
        exact encode_root_unique (.neg φ) start τ₁ τ₂ hOriginal h₁ h₂
  | conj φ ψ ihφ ihψ =>
      have hs₁ := (CNF.eval_append_true τ₁ _ _).mp h₁
      have hs₂ := (CNF.eval_append_true τ₂ _ _).mp h₂
      have hc₁ := (CNF.eval_append_true τ₁ _ _).mp hs₁.1
      have hc₂ := (CNF.eval_append_true τ₂ _ _).mp hs₂.1
      by_cases hleft : k < (encode φ start).nextFresh
      · exact ihφ start hc₁.1 hc₂.1 hlo hleft
      · by_cases hright : k < (encode ψ (encode φ start).nextFresh).nextFresh
        · exact ihψ (encode φ start).nextFresh hc₁.2 hc₂.2
            (by omega) hright
        · have heq : k = (encode ψ (encode φ start).nextFresh).nextFresh := by
            change k < (encode ψ (encode φ start).nextFresh).nextFresh + 1 at hhi
            omega
          subst k
          exact encode_root_unique (.conj φ ψ) start τ₁ τ₂ hOriginal h₁ h₂
  | disj φ ψ ihφ ihψ =>
      have hs₁ := (CNF.eval_append_true τ₁ _ _).mp h₁
      have hs₂ := (CNF.eval_append_true τ₂ _ _).mp h₂
      have hc₁ := (CNF.eval_append_true τ₁ _ _).mp hs₁.1
      have hc₂ := (CNF.eval_append_true τ₂ _ _).mp hs₂.1
      by_cases hleft : k < (encode φ start).nextFresh
      · exact ihφ start hc₁.1 hc₂.1 hlo hleft
      · by_cases hright : k < (encode ψ (encode φ start).nextFresh).nextFresh
        · exact ihψ (encode φ start).nextFresh hc₁.2 hc₂.2
            (by omega) hright
        · have heq : k = (encode ψ (encode φ start).nextFresh).nextFresh := by
            change k < (encode ψ (encode φ start).nextFresh).nextFresh + 1 at hhi
            omega
          subst k
          exact encode_root_unique (.disj φ ψ) start τ₁ τ₂ hOriginal h₁ h₂


/-- Every satisfying assignment of the defining clauses agrees with the
constructed extension on the generated auxiliary variables. -/
theorem encode_aux_eq_extension (φ : Formula) (start : Nat)
    (τ υ : Var → Bool)
    (hOriginal : ∀ n, τ (.original n) = υ (.original n))
    (h : CNF.eval τ (encode φ start).clauses = true)
    (k : Nat) (hlo : start ≤ k)
    (hhi : k < (encode φ start).nextFresh) :
    τ (.aux k) = extendAssignment φ start υ (.aux k) := by
  apply encode_aux_unique φ start τ (extendAssignment φ start υ)
  · intro n
    rw [extendAssignment_original]
    exact hOriginal n
  · exact h
  · exact extendAssignment_satisfies φ start υ
  · exact hlo
  · exact hhi

/-- A model of the final CNF has the canonical auxiliary values determined
by its original assignment, for every generated auxiliary index. -/
theorem toCNF_aux_eq_extension (φ : Formula) (σ : Nat → Bool)
    (τ : Var → Bool)
    (hOriginal : ∀ n, τ (.original n) = σ n)
    (h : CNF.eval τ (toCNF φ) = true)
    (k : Nat) (hk : k < φ.numConnectives) :
    τ (.aux k) = extendAssignment φ 0 (initialAssignment σ) (.aux k) := by
  have hDef := (CNF.eval_append_true τ _ _).mp h
  apply encode_aux_eq_extension φ 0 τ (initialAssignment σ)
  · exact hOriginal
  · exact hDef.1
  · exact Nat.zero_le k
  · simpa [encode_nextFresh] using hk



end Tseitin
