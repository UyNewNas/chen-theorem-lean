import MathlibNt.ChensTheorem

/-!
# Kernel trust audit

Run with `lake env lean Audit.lean` after `lake build`. The output must not
contain `sorryAx` for the two conditional Chen-theorem derivations or the
local PNT theorem supplied by `analytic-number-theory-lean`.
-/

#print axioms MathlibNt.ChensTheorem.chens_theorem
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.key_inequality_implies_chen
#print axioms MathlibNt.SieveTheory.MertensTheorem.prime_number_theorem
