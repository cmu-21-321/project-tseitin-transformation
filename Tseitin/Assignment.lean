import Tseitin.Correctness

namespace Tseitin

/-- Update one auxiliary variable, leaving every other variable unchanged. -/
def setAux (τ : Var → Bool) (k : Nat) (b : Bool) : Var → Bool
  | .original n => τ (.original n)
  | .aux j => if j = k then b else τ (.aux j)

@[simp] theorem setAux_original (τ : Var → Bool) (k n : Nat) (b : Bool) :
    setAux τ k b (.original n) = τ (.original n) := by
  rfl

@[simp] theorem setAux_same (τ : Var → Bool) (k : Nat) (b : Bool) :
    setAux τ k b (.aux k) = b := by
  simp [setAux]

/-- Updating a fresh index preserves every smaller auxiliary index. -/
theorem setAux_of_lt (τ : Var → Bool) (k j : Nat) (b : Bool)
    (h : j < k) :
    setAux τ k b (.aux j) = τ (.aux j) := by
  simp [setAux, Nat.ne_of_lt h]

/-- Assign auxiliary values following the encoder's recursive allocation order. -/
def extendAssignment : Formula → Nat → (Var → Bool) → (Var → Bool)
  | .var _, _, τ => τ
  | .neg φ, start, τ =>
      let child := encode φ start
      let τchild := extendAssignment φ start τ
      setAux τchild child.nextFresh (!(τchild child.root))
  | .conj φ ψ, start, τ =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      let τleft := extendAssignment φ start τ
      let τright := extendAssignment ψ left.nextFresh τleft
      setAux τright right.nextFresh (τright left.root && τright right.root)
  | .disj φ ψ, start, τ =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      let τleft := extendAssignment φ start τ
      let τright := extendAssignment ψ left.nextFresh τleft
      setAux τright right.nextFresh (τright left.root || τright right.root)

/-- Extending an assignment preserves all original variable values. -/
theorem extendAssignment_original (φ : Formula) (start : Nat)
    (τ : Var → Bool) (n : Nat) :
    extendAssignment φ start τ (.original n) = τ (.original n) := by
  induction φ generalizing start τ with
  | var m =>
      rfl
  | neg φ ih =>
      simp [extendAssignment, ih]
  | conj φ ψ ihφ ihψ =>
      simp [extendAssignment, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [extendAssignment, ihφ, ihψ]


/-- Extending from start preserves every auxiliary index smaller than start. -/
theorem extendAssignment_below (φ : Formula) (start : Nat)
    (τ : Var → Bool) (j : Nat) (h : j < start) :
    extendAssignment φ start τ (.aux j) = τ (.aux j) := by
  induction φ generalizing start τ with
  | var n =>
      rfl
  | neg φ ih =>
      have hchild : j < (encode φ start).nextFresh :=
        Nat.lt_of_lt_of_le h (encode_nextFresh_ge φ start)
      simp only [extendAssignment]
      rw [setAux_of_lt _ _ _ _ hchild]
      exact ih start τ h
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      have hleft : j < (encode φ start).nextFresh :=
        Nat.lt_of_lt_of_le h (encode_nextFresh_ge φ start)
      have hright : j < (encode ψ (encode φ start).nextFresh).nextFresh :=
        Nat.lt_of_lt_of_le hleft
          (encode_nextFresh_ge ψ (encode φ start).nextFresh)
      simp only [extendAssignment]
      rw [setAux_of_lt _ _ _ _ hright]
      rw [ihψ (encode φ start).nextFresh (extendAssignment φ start τ) hleft]
      exact ihφ start τ h

/-- Variables whose auxiliary indices lie below start retain their values. -/
theorem extendAssignment_preserves_var (φ : Formula) (start : Nat)
    (τ : Var → Bool) {lo : Nat} {v : Var}
    (hv : v.AuxInRange lo start) :
    extendAssignment φ start τ v = τ v := by
  cases v with
  | original n =>
      exact extendAssignment_original φ start τ n
  | aux j =>
      exact extendAssignment_below φ start τ j hv.2

/-- Extending the right subtree preserves the left subtree's root value. -/
theorem extendAssignment_preserves_left_root (φ ψ : Formula) (start : Nat)
    (τ : Var → Bool) :
    extendAssignment ψ (encode φ start).nextFresh τ (encode φ start).root =
      τ (encode φ start).root := by
  exact extendAssignment_preserves_var ψ (encode φ start).nextFresh τ
    (encode_root_inRange φ start)

/-- Agreement on each literal preserves the value of a clause. -/
theorem Clause.eval_eq_of_agree (τ υ : Var → Bool) (clause : Clause)
    (h : ∀ lit ∈ clause, Literal.eval τ lit = Literal.eval υ lit) :
    Clause.eval τ clause = Clause.eval υ clause := by
  induction clause with
  | nil => rfl
  | cons lit rest ih =>
      have hhead := h lit (by simp)
      have htail := ih (by
        intro l hl
        exact h l (by simp [hl]))
      change (Literal.eval τ lit || Clause.eval τ rest) =
        (Literal.eval υ lit || Clause.eval υ rest)
      rw [hhead, htail]

/-- Agreement on the allowed variables preserves the value of a bounded CNF. -/
theorem CNF.eval_eq_of_agree (τ υ : Var → Bool) (lo hi : Nat) (cnf : CNF)
    (h : cnf.AuxInRange lo hi)
    (hagree : ∀ v, v.AuxInRange lo hi → τ v = υ v) :
    CNF.eval τ cnf = CNF.eval υ cnf := by
  induction cnf with
  | nil => rfl
  | cons clause rest ih =>
      have hhead : Clause.eval τ clause = Clause.eval υ clause := by
        apply Clause.eval_eq_of_agree
        intro lit hl
        have hv := h clause (by simp) lit hl
        cases lit with
        | pos v => exact hagree v hv
        | neg v => exact congrArg Bool.not (hagree v hv)
      have htail := ih (by
        intro c hc lit hl
        exact h c (by simp [hc]) lit hl)
      change (Clause.eval τ clause && CNF.eval τ rest) =
        (Clause.eval υ clause && CNF.eval υ rest)
      rw [hhead, htail]

/-- Updating index k preserves variables whose auxiliary indices are below k. -/
theorem setAux_preserves_var (τ : Var → Bool) (k : Nat) (b : Bool)
    {lo : Nat} {v : Var} (hv : v.AuxInRange lo k) :
    setAux τ k b v = τ v := by
  cases v with
  | original n => rfl
  | aux j => exact setAux_of_lt τ k j b hv.2

/-- Setting a fresh parent variable preserves clauses using older variables. -/
theorem setAux_preserves_cnf (τ : Var → Bool) (k : Nat) (b : Bool)
    {lo : Nat} {cnf : CNF} (h : cnf.AuxInRange lo k) :
    CNF.eval (setAux τ k b) cnf = CNF.eval τ cnf := by
  apply CNF.eval_eq_of_agree _ _ lo k cnf h
  intro v hv
  exact setAux_preserves_var τ k b hv

/-- Extending from start preserves any CNF whose auxiliary indices are below start. -/
theorem extendAssignment_preserves_cnf (φ : Formula) (start : Nat)
    (τ : Var → Bool) {lo : Nat} {cnf : CNF}
    (h : cnf.AuxInRange lo start) :
    CNF.eval (extendAssignment φ start τ) cnf = CNF.eval τ cnf := by
  apply CNF.eval_eq_of_agree _ _ lo start cnf h
  intro v hv
  exact extendAssignment_preserves_var φ start τ hv

/-- The constructed extension satisfies all defining clauses of the encoding. -/
theorem extendAssignment_satisfies (φ : Formula) (start : Nat)
    (τ : Var → Bool) :
    CNF.eval (extendAssignment φ start τ) (encode φ start).clauses = true := by
  induction φ generalizing start τ with
  | var n =>
      rfl
  | neg φ ih =>
      let child := encode φ start
      let υ := extendAssignment φ start τ
      change CNF.eval (setAux υ child.nextFresh (!(υ child.root)))
        (child.clauses ++ encodeNot (.aux child.nextFresh) child.root) = true
      apply (CNF.eval_append_true _ _ _).mpr
      constructor
      · rw [setAux_preserves_cnf _ _ _ (encode_clauses_inRange φ start)]
        exact ih start τ
      · apply (encodeNot_correct _ _ _).mpr
        rw [setAux_same,
          setAux_preserves_var _ _ _ (encode_root_inRange φ start)]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      let τleft := extendAssignment φ start τ
      let τright := extendAssignment ψ left.nextFresh τleft
      have hcounter : left.nextFresh ≤ right.nextFresh :=
        encode_nextFresh_ge ψ left.nextFresh
      have hleftClauses : left.clauses.AuxInRange start right.nextFresh :=
        (encode_clauses_inRange φ start).widen (Nat.le_refl _) hcounter
      have hleftRoot : left.root.AuxInRange start right.nextFresh :=
        (encode_root_inRange φ start).widen (Nat.le_refl _) hcounter
      change CNF.eval (setAux τright right.nextFresh _)
        (left.clauses ++ right.clauses ++ _) = true
      apply (CNF.eval_append_true _ _ _).mpr
      constructor
      · apply (CNF.eval_append_true _ _ _).mpr
        constructor
        · rw [setAux_preserves_cnf _ _ _ hleftClauses]
          rw [extendAssignment_preserves_cnf ψ left.nextFresh τleft
            (encode_clauses_inRange φ start)]
          exact ihφ start τ
        · rw [setAux_preserves_cnf _ _ _
            (encode_clauses_inRange ψ left.nextFresh)]
          exact ihψ left.nextFresh τleft
      · first
        | apply (encodeAnd_correct _ _ _ _).mpr
        | apply (encodeOr_correct _ _ _ _).mpr
        rw [setAux_same,
          setAux_preserves_var _ _ _ hleftRoot,
          setAux_preserves_var _ _ _ (encode_root_inRange ψ left.nextFresh)]
end Tseitin
