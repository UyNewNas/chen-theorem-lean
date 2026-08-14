import MathlibNt.ChensTheorem
import MathlibNt.SieveTheory.BombieriVinogradov
import MathlibNt.SieveTheory.LinearSieve
import MathlibNt.SieveTheory.PanTruncation
import MathlibNt.SieveTheory.PrimePair
import MathlibNt.SieveTheory.PrimePairLinearForm
import MathlibNt.SieveTheory.TripleMain

/-!
# Public build root

 builds this module and therefore the complete public Chen-theorem
development below.  Keep every shipped Lean module imported here so that CI
cannot silently omit part of the auditable proof chain.
-/
