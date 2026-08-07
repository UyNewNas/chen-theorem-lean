import MathlibNt.ChensTheorem

/-!
# Kernel trust audit

Run with `lake env lean Audit.lean` after `lake build`.  The output must not
contain `sorryAx` for the two conditional Chen-theorem derivations.
-/

#print axioms MathlibNt.ChensTheorem.chens_theorem
#print axioms MathlibNt.SieveTheory.SwitchingPrinciple.key_inequality_implies_chen
