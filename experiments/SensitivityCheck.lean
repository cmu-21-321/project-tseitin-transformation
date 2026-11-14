import Tseitin.Sensitivity
import Tseitin.ReliabilityExample

#print axioms Tseitin.Formula.probability_withProb_affine
#print axioms Tseitin.Formula.probability_withProb_sub

open Tseitin

def main : IO Unit := do
  let m := ReliabilityExample.sharedSupplyModel
  let f := FaultTree.sharedSupply.toFormula
  let checks : List (String × ℚ × ℚ) := [
    ("shared_supply", f.sensitivity m 0, 99 / 100),
    ("unit_1", f.sensitivity m 1, 99 / 1000),
    ("unit_2", f.sensitivity m 2, 99 / 1000),
    ("unused_variable", f.sensitivity m 100, 0),
    ("negation", (Formula.neg (.var 0)).sensitivity m 0, -1),
    ("repeated_variable", (Formula.conj (.var 0) (.var 0)).sensitivity m 0, 1),
    ("supply_reduction", f.probability m -
      f.probability (m.withProb 0 (1 / 200) (by norm_num) (by norm_num)),
      99 / 20000)]
  IO.println "case,sensitivity_or_probability_change"
  for (name, actual, expected) in checks do
    unless actual == expected do
      throw <| IO.userError s!"{name}: expected {expected}, got {actual}"
    IO.println s!"{name},{actual}"
  IO.println "All 7 checks passed."
