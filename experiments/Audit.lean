import Tseitin

-- Semantic correctness.
#print axioms Tseitin.toCNF_correct

-- Uniqueness of generated auxiliary values.
#print axioms Tseitin.encode_aux_unique

-- Linear clause-count bound.
#print axioms Tseitin.toCNF_length_le

-- Finite model-count preservation.
#print axioms Tseitin.Formula.modelCount_eq_cnfModelCount

-- Rational weighted model-count preservation.
#print axioms Tseitin.Formula.weightedModelCount_eq_weightedCNFModelCount

-- Probability bounds and complement.
#print axioms Tseitin.Formula.probability_bounds
#print axioms Tseitin.Formula.probability_neg

-- Fault-tree semantics and probability preservation.
#print axioms Tseitin.FaultTree.toFormula_correct
#print axioms Tseitin.FaultTree.failureProbability_eq_cnf

-- Sensitivity and interval bounds.
#print axioms Tseitin.Formula.probability_withProb_affine
#print axioms Tseitin.Formula.probability_mono
#print axioms Tseitin.FaultTree.failureProbability_interval_bounds
#print axioms Tseitin.FaultTree.failureProbability_cnf_interval_bounds
