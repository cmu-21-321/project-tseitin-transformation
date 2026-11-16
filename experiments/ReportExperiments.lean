import Tseitin.ReliabilityExample
import Tseitin.Size

/-!
# Reproducible experiments for the report

Compare finite source and target model counts and rational weights.
Also measure the generated clause counts for a growing formula family.

These are executable checks, not additional general correctness theorems.
-/

namespace ReportExperiments

open Tseitin

/-- A series system fails when either individual unit fails. -/
def series : FaultTree :=
  .orGate (.component 1) (.component 2)

/-- A parallel system fails when both individual units fail. -/
def parallel : FaultTree :=
  .andGate (.component 1) (.component 2)

/-- Repeated occurrences must refer to the same basic event. -/
def repeated : FaultTree :=
  .andGate (.component 1) (.component 1)

/-- Large gaps between indices must not introduce extra variables. -/
def sparse : Formula :=
  .disj (.var 2) (.var 100)

def contradiction : Formula :=
  .conj (.var 2) (.neg (.var 2))

def tautology : Formula :=
  .disj (.var 2) (.neg (.var 2))

/-- Input n constructs a disjunction of n + 1 conjunctions.
Each conjunction uses a distinct pair of original variables. -/
def disjunctionOfPairs : Nat → Formula
  | 0 =>
      .conj (.var 0) (.var 1)
  | n + 1 =>
      .disj
        (disjunctionOfPairs n)
        (.conj
          (.var (2 * (n + 1)))
          (.var (2 * (n + 1) + 1)))

/-- Compare both counts and weights, failing explicitly on a mismatch. -/
def checkCase (name : String) (f : Formula) : IO Unit := do
  let m := ReliabilityExample.sharedSupplyModel

  let source := f.weightedModelCount m.weight
  let target := f.weightedCNFModelCount m.weight

  let count := f.modelCount
  let targetCount := f.cnfModelCount

  if source != target || count != targetCount then
    throw (IO.userError s!"mismatch in {name}")

  IO.println
    s!"{name},{f.vars.card},{f.numConnectives},{(toCNF f).length},{count},{targetCount},{source},{target}"

/-- Run the semantic checks and the encoding-size experiment. -/
def run : IO Unit := do
  IO.println
    "case,original_variables,auxiliary_variables,clauses,source_models,cnf_models,source_weight,cnf_weight"

  for (name, f) in [
      ("series", series.toFormula),
      ("parallel", parallel.toFormula),
      ("shared_supply", FaultTree.sharedSupply.toFormula),
      ("repeated_component", repeated.toFormula),
      ("sparse_indices", sparse),
      ("contradiction", contradiction),
      ("tautology", tautology)] do
    checkCase name f

  IO.println
    "growth_k,original_variables,auxiliary_variables,tseitin_clauses,distribution_clause_count"

  for k in [1, 2, 5, 10, 20, 50] do
    let f := disjunctionOfPairs (k - 1)
    let actual := (toCNF f).length

    if actual != 6 * k - 2 then
      throw (IO.userError "unexpected clause count")

    IO.println
      s!"{k},{f.vars.card},{f.numConnectives},{actual},{2 ^ k}"

end ReportExperiments

def main : IO Unit :=
  ReportExperiments.run
