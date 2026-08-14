import MathlibNt.ChensTheorem
import MathlibNt.SieveTheory.BombieriVinogradov
import MathlibNt.SieveTheory.LinearSieve
import MathlibNt.SieveTheory.PrimePair
import MathlibNt.SieveTheory.TripleMain

/-!
# Public build root

`lake build` builds this module and therefore the complete public Chen-theorem
development below.  Keep every shipped Lean module imported here so that CI
cannot silently omit part of the auditable proof chain.
-/
