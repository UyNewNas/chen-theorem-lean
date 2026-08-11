import MathlibNt.ChensTheorem

/-!
# Kernel trust audit

Run with `lake env lean Audit.lean` after `lake build`. The output must not
contain `sorryAx` for the conditional Chen-theorem derivations and the
imported PNT and Mertens interfaces.
-/

#print axioms MathlibNt.ChensTheorem.chens_theorem
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.key_inequality_implies_chen
#print axioms MathlibNt.SieveTheory.MertensTheorem.prime_number_theorem
#print axioms MathlibNt.SieveTheory.MertensTheorem.mertens_second_theorem
#print axioms MathlibNt.SieveTheory.MertensTheorem.mertens_product_formula
#print axioms MathlibNt.SieveTheory.MertensTheorem.primeProduct_asymptotic_order
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.chen_pointwise_analytic_bounds_at
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.chen_key_inequality_of_error_budget
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.range_sub_eq_one_card_le_one
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.chenUnitCandidates_card_le_one
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.mem_correctedChenGood_or_bad
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.correctedChenGoodCandidates_subset_goodRepresentations
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.correctedChenBad_penalty_ge_two
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.corrected_counting_bridge
