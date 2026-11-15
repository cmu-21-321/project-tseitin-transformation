import Tseitin.Intervals
import Mathlib.Tactic.NormNum

set_option linter.style.header false

#print axioms Tseitin.Formula.probability_mono
#print axioms Tseitin.FaultTree.failureProbability_interval_bounds
#print axioms Tseitin.FaultTree.failureProbability_cnf_interval_bounds

namespace Tseitin.IntervalExample

abbrev Prob := {q : ℚ // 0 ≤ q ∧ q ≤ 1}

/-- Three basic-event probabilities; unused indices receive zero. -/
def makeModel (a b c : Prob) : IndependentModel where
  probTrue
    | 0 => a.val
    | 1 => b.val
    | 2 => c.val
    | _ => 0
  nonneg n := by
    rcases n with _ | _ | _ | n
    · exact a.property.1
    · exact b.property.1
    · exact c.property.1
    · norm_num
  le_one n := by
    rcases n with _ | _ | _ | n
    · exact a.property.2
    · exact b.property.2
    · exact c.property.2
    · norm_num

-- Illustrative parameter ranges, not confidence intervals estimated from data.
def lowerModel : IndependentModel := makeModel
  ⟨1 / 200, by norm_num⟩ ⟨2 / 25, by norm_num⟩ ⟨2 / 25, by norm_num⟩

def nominalModel : IndependentModel := makeModel
  ⟨1 / 100, by norm_num⟩ ⟨1 / 10, by norm_num⟩ ⟨1 / 10, by norm_num⟩

def upperModel : IndependentModel := makeModel
  ⟨3 / 200, by norm_num⟩ ⟨3 / 25, by norm_num⟩ ⟨3 / 25, by norm_num⟩

/-- The generic bound applies to this nominal model, with CNF-computed endpoints. -/
theorem nominal_cnf_bounds :
    FaultTree.sharedSupply.toFormula.weightedCNFModelCount lowerModel.weight ≤
        FaultTree.sharedSupply.failureProbability nominalModel ∧
      FaultTree.sharedSupply.failureProbability nominalModel ≤
        FaultTree.sharedSupply.toFormula.weightedCNFModelCount upperModel.weight := by
  apply FaultTree.failureProbability_cnf_interval_bounds
  · intro i _
    rcases i with _ | _ | _ | i <;> norm_num [lowerModel, nominalModel, makeModel]
  · intro i _
    rcases i with _ | _ | _ | i <;> norm_num [nominalModel, upperModel, makeModel]

def supplyValues : List Prob :=
  [⟨1 / 200, by norm_num⟩, ⟨1 / 100, by norm_num⟩, ⟨3 / 200, by norm_num⟩]

def unitValues : List Prob :=
  [⟨2 / 25, by norm_num⟩, ⟨1 / 10, by norm_num⟩, ⟨3 / 25, by norm_num⟩]

end Tseitin.IntervalExample

#print axioms Tseitin.IntervalExample.nominal_cnf_bounds

open Tseitin Tseitin.IntervalExample

def main : IO Unit := do
  let t := FaultTree.sharedSupply
  let lo := t.failureProbability lowerModel
  let nom := t.failureProbability nominalModel
  let hi := t.failureProbability upperModel
  unless lo == (1421 / 125000 : ℚ) && nom == (199 / 10000 : ℚ) &&
      hi == (456 / 15625 : ℚ) do
    throw <| IO.userError "Unexpected endpoint or nominal probabilities"
  IO.println "case,source_probability,cnf_probability"
  for (name, m) in [("lower", lowerModel), ("nominal", nominalModel), ("upper", upperModel)] do
    let direct := t.failureProbability m
    let cnf := t.toFormula.weightedCNFModelCount m.weight
    unless direct == cnf do
      throw <| IO.userError s!"Source/CNF mismatch for {name}"
    IO.println s!"{name},{direct},{cnf}"
  let mut checked := 0
  for a in supplyValues do
    for b in unitValues do
      for c in unitValues do
        let m := makeModel a b c
        let p := t.failureProbability m
        let cnf := t.toFormula.weightedCNFModelCount m.weight
        -- Independent reference calculation for this particular shared-supply tree.
        let reference := a.val + (1 - a.val) * b.val * c.val
        unless p == cnf && p == reference && decide (lo ≤ p ∧ p ≤ hi) do
          throw <| IO.userError s!"Grid check failed at ({a.val}, {b.val}, {c.val})"
        checked := checked + 1
  IO.println s!"All {checked} parameter-grid checks passed."
