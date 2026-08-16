import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# Source-faithful transport for the corrected triple penalty

This module records the finite objects needed to compare the corrected
triple-factor penalty with the historical source sum `chenOmega`.  It makes
no analytic estimate and does not use the coarse `switchingCount` bound,
which forgets the essential ordering condition `p₂ ≤ p₃`.

The intended map sends a corrected non-boundary witness `(p, p₁)` with
`N - p = p₁*p₂*p₃` to `(p₁*p₂, p₃)`.  The comparison theorem is deliberately
left for a later finite proof: these definitions make all of its cutoffs and
quantifiers public and reviewable first.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open scoped Classical

/-- The finite pairs counted by the source Ω sum, presented without the
real-valued indicator `chenF`.  The first coordinate is `a = p₁*p₂`; the
second is the remaining prime `p₃`. -/
noncomputable def sourceOmegaPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter (fun w =>
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
      (N : ℝ) ^ (1 / 10 : ℝ) < p₁ ∧
      p₁ ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) < p₂ ∧
      (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1 / 2 : ℝ) ∧
      w.1 = p₁ * p₂ ∧ w.2.Prime ∧ w.1 * w.2 ≤ N ∧
      (N - w.1 * w.2).Prime)

/-- The part of the corrected triple penalty whose strict cutoff conditions
already match the source Ω ranges.  Boundary fibres
`p₁ = floor(N^(1/10))` and `p₂ = N^(1/3)` are deliberately excluded: their
separate elementary estimates are a different theorem. -/
noncomputable def correctedTripleNonBoundaryIndex (N : ℕ) : Finset (ℕ × ℕ) :=
  ((correctedChenCandidates N).product (Finset.range (N + 1))).filter (fun w =>
    w.2.Prime ∧ correctedChenZ N ≤ w.2 ∧ w.2 < correctedChenY N ∧
      (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))) < w.2 ∧
      ∃ p₂ p₃ : ℕ, p₂.Prime ∧ p₃.Prime ∧
        correctedChenY N ≤ p₂ ∧ p₂ ≤ p₃ ∧
        (N : ℝ) ^ (1 / 3 : ℝ) < p₂ ∧
        w.2 * p₂ * p₃ = N - w.1 ∧ w.2 < p₂)

end MathlibNt.SieveTheory.SwitchingPrinciple
