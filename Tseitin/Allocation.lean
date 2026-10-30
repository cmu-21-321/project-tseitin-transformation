import Tseitin.Transform

namespace Tseitin

/-- Count connective occurrences in the formula's syntax tree. -/
def Formula.numConnectives : Formula → Nat
  | .var _ => 0
  | .neg φ => φ.numConnectives + 1
  | .conj φ ψ => φ.numConnectives + ψ.numConnectives + 1
  | .disj φ ψ => φ.numConnectives + ψ.numConnectives + 1

/-- Each connective advances the auxiliary-variable counter by one. -/
theorem encode_nextFresh (φ : Formula) (start : Nat) :
    (encode φ start).nextFresh = start + φ.numConnectives := by
  induction φ generalizing start with
  | var n =>
      simp [encode, Formula.numConnectives]
  | neg φ ih =>
      simp [encode, Formula.numConnectives, ih, Nat.add_assoc]
  | conj φ ψ ihφ ihψ =>
      simp [encode, Formula.numConnectives, ihφ, ihψ, Nat.add_assoc]
  | disj φ ψ ihφ ihψ =>
      simp [encode, Formula.numConnectives, ihφ, ihψ, Nat.add_assoc]

/-- Encoding never decreases the auxiliary-variable counter. -/
theorem encode_nextFresh_ge (φ : Formula) (start : Nat) :
    start ≤ (encode φ start).nextFresh := by
  rw [encode_nextFresh]
  exact Nat.le_add_right start φ.numConnectives


/-- Original variables are unrestricted; auxiliary indices lie in [lo, hi). -/
def Var.AuxInRange (lo hi : Nat) : Var → Prop
  | .original _ => True
  | .aux k => lo ≤ k ∧ k < hi

/-- Any auxiliary variable returned as the root lies in the allocated interval. -/
theorem encode_root_inRange (φ : Formula) (start : Nat) :
    Var.AuxInRange start (encode φ start).nextFresh
      (encode φ start).root := by
  cases φ with
  | var n =>
      trivial
  | neg φ =>
      change start ≤ (encode φ start).nextFresh ∧
        (encode φ start).nextFresh < (encode φ start).nextFresh + 1
      exact ⟨encode_nextFresh_ge φ start, Nat.lt_succ_self _⟩
  | conj φ ψ =>
      change start ≤ (encode ψ (encode φ start).nextFresh).nextFresh ∧
        (encode ψ (encode φ start).nextFresh).nextFresh <
          (encode ψ (encode φ start).nextFresh).nextFresh + 1
      exact ⟨Nat.le_trans (encode_nextFresh_ge φ start)
        (encode_nextFresh_ge ψ (encode φ start).nextFresh),
        Nat.lt_succ_self _⟩
  | disj φ ψ =>
      change start ≤ (encode ψ (encode φ start).nextFresh).nextFresh ∧
        (encode ψ (encode φ start).nextFresh).nextFresh <
          (encode ψ (encode φ start).nextFresh).nextFresh + 1
      exact ⟨Nat.le_trans (encode_nextFresh_ge φ start)
        (encode_nextFresh_ge ψ (encode φ start).nextFresh),
        Nat.lt_succ_self _⟩

/-- A literal has the same auxiliary-index bounds as its variable. -/
def Literal.AuxInRange (lo hi : Nat) : Literal → Prop
  | .pos v => v.AuxInRange lo hi
  | .neg v => v.AuxInRange lo hi

/-- Every auxiliary variable occurring in the CNF lies in [lo, hi). -/
def CNF.AuxInRange (lo hi : Nat) (cnf : CNF) : Prop :=
  ∀ clause ∈ cnf, ∀ lit ∈ clause, lit.AuxInRange lo hi

/-- A variable in an interval remains in any larger interval. -/
theorem Var.AuxInRange.widen {v : Var} {lo hi lo' hi' : Nat}
    (h : v.AuxInRange lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    v.AuxInRange lo' hi' := by
  cases v with
  | original n => trivial
  | aux k =>
      exact ⟨Nat.le_trans hlo h.1, Nat.lt_of_lt_of_le h.2 hhi⟩

/-- Widening the interval preserves the bounds for every literal in a CNF. -/
theorem CNF.AuxInRange.widen {cnf : CNF} {lo hi lo' hi' : Nat}
    (h : cnf.AuxInRange lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    cnf.AuxInRange lo' hi' := by
  intro clause hc lit hl
  have hvar := h clause hc lit hl
  cases lit with
  | pos v => exact hvar.widen hlo hhi
  | neg v => exact hvar.widen hlo hhi

/-- Concatenating two CNFs preserves their common bounds. -/
theorem CNF.AuxInRange.append {lo hi : Nat} {xs ys : CNF}
    (hx : xs.AuxInRange lo hi) (hy : ys.AuxInRange lo hi) :
    (xs ++ ys).AuxInRange lo hi := by
  intro clause hc lit hl
  rcases List.mem_append.mp hc with hc | hc
  · exact hx clause hc lit hl
  · exact hy clause hc lit hl

/-- The negation encoding uses only the two supplied variables. -/
theorem encodeNot_inRange {lo hi : Nat} {d a : Var}
    (hd : d.AuxInRange lo hi) (ha : a.AuxInRange lo hi) :
    (encodeNot d a).AuxInRange lo hi := by
  simp [encodeNot, CNF.AuxInRange, Literal.AuxInRange, hd, ha]

/-- The conjunction encoding uses only the three supplied variables. -/
theorem encodeAnd_inRange {lo hi : Nat} {d a b : Var}
    (hd : d.AuxInRange lo hi) (ha : a.AuxInRange lo hi)
    (hb : b.AuxInRange lo hi) :
    (encodeAnd d a b).AuxInRange lo hi := by
  simp [encodeAnd, CNF.AuxInRange, Literal.AuxInRange, hd, ha, hb]

/-- The disjunction encoding uses only the three supplied variables. -/
theorem encodeOr_inRange {lo hi : Nat} {d a b : Var}
    (hd : d.AuxInRange lo hi) (ha : a.AuxInRange lo hi)
    (hb : b.AuxInRange lo hi) :
    (encodeOr d a b).AuxInRange lo hi := by
  simp [encodeOr, CNF.AuxInRange, Literal.AuxInRange, hd, ha, hb]


/-- Every auxiliary variable in the generated clauses lies in the allocated interval. -/
theorem encode_clauses_inRange (φ : Formula) (start : Nat) :
    (encode φ start).clauses.AuxInRange start
      (encode φ start).nextFresh := by
  induction φ generalizing start with
  | var n =>
      simp [encode, CNF.AuxInRange]
  | neg φ ih =>
      let child := encode φ start
      have hstep : child.nextFresh ≤ child.nextFresh + 1 := Nat.le_succ _
      change (child.clauses ++ encodeNot (.aux child.nextFresh) child.root).AuxInRange
        start (child.nextFresh + 1)
      apply CNF.AuxInRange.append
      · exact (ih start).widen (Nat.le_refl _) hstep
      · exact encodeNot_inRange
          (encode_root_inRange (.neg φ) start)
          ((encode_root_inRange φ start).widen (Nat.le_refl _) hstep)
  | conj φ ψ ihφ ihψ =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      have hstart : start ≤ left.nextFresh := encode_nextFresh_ge φ start
      have hright : right.nextFresh ≤ right.nextFresh + 1 := Nat.le_succ _
      have hleft : left.nextFresh ≤ right.nextFresh + 1 :=
        Nat.le_trans (encode_nextFresh_ge ψ left.nextFresh) hright
      change (left.clauses ++ right.clauses ++
        encodeAnd (.aux right.nextFresh) left.root right.root).AuxInRange
          start (right.nextFresh + 1)
      apply CNF.AuxInRange.append
      · exact ((ihφ start).widen (Nat.le_refl _) hleft).append
          ((ihψ left.nextFresh).widen hstart hright)
      · exact encodeAnd_inRange
          (encode_root_inRange (.conj φ ψ) start)
          ((encode_root_inRange φ start).widen (Nat.le_refl _) hleft)
          ((encode_root_inRange ψ left.nextFresh).widen hstart hright)
  | disj φ ψ ihφ ihψ =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      have hstart : start ≤ left.nextFresh := encode_nextFresh_ge φ start
      have hright : right.nextFresh ≤ right.nextFresh + 1 := Nat.le_succ _
      have hleft : left.nextFresh ≤ right.nextFresh + 1 :=
        Nat.le_trans (encode_nextFresh_ge ψ left.nextFresh) hright
      change (left.clauses ++ right.clauses ++
        encodeOr (.aux right.nextFresh) left.root right.root).AuxInRange
          start (right.nextFresh + 1)
      apply CNF.AuxInRange.append
      · exact ((ihφ start).widen (Nat.le_refl _) hleft).append
          ((ihψ left.nextFresh).widen hstart hright)
      · exact encodeOr_inRange
          (encode_root_inRange (.disj φ ψ) start)
          ((encode_root_inRange φ start).widen (Nat.le_refl _) hleft)
          ((encode_root_inRange ψ left.nextFresh).widen hstart hright)

/-- The final CNF, including its root assertion, uses only bounded auxiliary indices. -/
theorem toCNF_inRange (φ : Formula) :
    (toCNF φ).AuxInRange 0 φ.numConnectives := by
  unfold toCNF
  apply CNF.AuxInRange.append
  · simpa [encode_nextFresh] using encode_clauses_inRange φ 0
  · have hroot := encode_root_inRange φ 0
    simpa [CNF.AuxInRange, Literal.AuxInRange, encode_nextFresh] using hroot


end Tseitin
