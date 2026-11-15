import Tseitin.Monotonicity
import Tseitin.ReliabilityExample

#print axioms Tseitin.Formula.probability_endpoints_le
#print axioms Tseitin.FaultTree.toFormula_isMonotone
#print axioms Tseitin.FaultTree.sensitivity_bounds
#print axioms Tseitin.FaultTree.failureProbability_withProb_mono

open Tseitin

-- Negation gives a genuine counterexample: semantic monotonicity cannot
-- be dropped from the probability monotonicity theorem.
example : ¬ (Formula.neg (.var 0)).IsMonotone := by
  intro h
  have hc := h (fun _ => false) (fun _ => true)
    (by intro n _; rfl) (by rfl)
  change false = true at hc
  cases hc

private def check (name : String) (t : FaultTree) (m : IndependentModel)
    (i : Nat) (expectedLow expectedHigh : ℚ) : IO Unit := do
  let low := t.failureProbability (m.withProb i 0 (by norm_num) (by norm_num))
  let high := t.failureProbability (m.withProb i 1 (by norm_num) (by norm_num))
  let s := t.toFormula.sensitivity m i
  unless low == expectedLow && high == expectedHigh && s == high - low do
    throw <| IO.userError s!"{name}: unexpected endpoint values or sensitivity"
  unless decide (0 ≤ s ∧ s ≤ 1 ∧ low ≤ high) do
    throw <| IO.userError s!"{name}: monotonicity or sensitivity bounds failed"
  IO.println s!"{name},{low},{high},{s}"

def main : IO Unit := do
  let m := ReliabilityExample.sharedSupplyModel
  let zero : IndependentModel := ⟨fun _ => 0, fun _ => by norm_num, fun _ => by norm_num⟩
  let one : IndependentModel := ⟨fun _ => 1, fun _ => by norm_num, fun _ => by norm_num⟩
  IO.println "case,P_at_0,P_at_1,sensitivity"
  check "shared_supply" FaultTree.sharedSupply m 0 (1 / 100) 1
  check "individual_unit" FaultTree.sharedSupply m 1 (1 / 100) (109 / 1000)
  check "repeated_component" (.andGate (.component 0) (.component 0)) m 0 0 1
  check "sparse_indices" (.orGate (.component 2) (.component 100)) m 100 (1 / 10) 1
  check "unused_variable" FaultTree.sharedSupply m 100 (199 / 10000) (199 / 10000)
  check "all_other_probs_zero" FaultTree.sharedSupply zero 0 0 1
  check "all_other_probs_one" FaultTree.sharedSupply one 0 1 1
  IO.println "All 7 checks passed; the negation counterexample is proved."
