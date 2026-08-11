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
