import Tseitin.Encoding

namespace Tseitin

/-- The representative variable, generated clauses, and next unused index. -/
structure EncodingResult where
  root : Var
  clauses : CNF
  nextFresh : Nat
  deriving Repr

/-- Encode a formula, allocating auxiliary variables starting at `start`. -/
def encode : Formula → Nat → EncodingResult
  | .var n, start =>
      { root := .original n, clauses := [], nextFresh := start }

  | .neg φ, start =>
      let child := encode φ start
      let d := Var.aux child.nextFresh
      { root := d
        clauses := child.clauses ++ encodeNot d child.root
        nextFresh := child.nextFresh + 1 }

  | .conj φ ψ, start =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      let d := Var.aux right.nextFresh
      { root := d
        clauses := left.clauses ++ right.clauses ++
          encodeAnd d left.root right.root
        nextFresh := right.nextFresh + 1 }

  | .disj φ ψ, start =>
      let left := encode φ start
      let right := encode ψ left.nextFresh
      let d := Var.aux right.nextFresh
      { root := d
        clauses := left.clauses ++ right.clauses ++
          encodeOr d left.root right.root
        nextFresh := right.nextFresh + 1 }

/-- Assert that the representative of the whole formula is true. -/
def toCNF (φ : Formula) : CNF :=
  let result := encode φ 0
  result.clauses ++ [[.pos result.root]]

#eval (encode demo 0).root
#eval (encode demo 0).nextFresh
#eval (toCNF demo).length

end Tseitin
