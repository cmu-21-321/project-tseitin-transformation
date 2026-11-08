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


end Tseitin
