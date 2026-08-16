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

/-- Membership in `sourceOmegaPairs` exposes the exact source-factor
witnesses.  This is a finite unpacking lemma, not a comparison with the
numeric sum `chenOmega`. -/
theorem sourceOmegaPairs_mem_witness {N : ℕ} {w : ℕ × ℕ}
    (hw : w ∈ sourceOmegaPairs N) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
      (N : ℝ) ^ (1 / 10 : ℝ) < p₁ ∧
      p₁ ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      (N : ℝ) ^ (1 / 3 : ℝ) < p₂ ∧
      (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1 / 2 : ℝ) ∧
      w.1 = p₁ * p₂ ∧ w.2.Prime ∧ w.1 * w.2 ≤ N ∧
      (N - w.1 * w.2).Prime := by
  simpa only [sourceOmegaPairs, Finset.mem_filter] using
    (Finset.mem_filter.mp hw).2

/-- Membership in the corrected non-boundary index exposes a triple witness
with its ordering intact.  In particular, no later transport may silently
discard `p₂ ≤ p₃`. -/
theorem correctedTripleNonBoundaryIndex_mem_witness {N : ℕ} {w : ℕ × ℕ}
    (hw : w ∈ correctedTripleNonBoundaryIndex N) :
    w.2.Prime ∧ correctedChenZ N ≤ w.2 ∧ w.2 < correctedChenY N ∧
      (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))) < w.2 ∧
      ∃ p₂ p₃ : ℕ, p₂.Prime ∧ p₃.Prime ∧
        correctedChenY N ≤ p₂ ∧ p₂ ≤ p₃ ∧
        (N : ℝ) ^ (1 / 3 : ℝ) < p₂ ∧
        w.2 * p₂ * p₃ = N - w.1 ∧ w.2 < p₂ := by
  simpa only [correctedTripleNonBoundaryIndex, Finset.mem_filter] using
    (Finset.mem_filter.mp hw).2

/-- The ordering retained by the corrected triple count gives the integer
core of the source square-root cutoff.  No estimate is involved: the square
of `p₂` may replace `p₂*p₃` because `p₂ ≤ p₃`, and the complement is at most
`N`. -/
theorem ordered_triple_sq_le_N {N p p₁ p₂ p₃ : ℕ}
    (hp₂₃ : p₂ ≤ p₃) (hprod : p₁ * p₂ * p₃ = N - p) :
    p₁ * p₂ * p₂ ≤ N := by
  calc
    p₁ * p₂ * p₂ = p₁ * (p₂ * p₂) := by rw [Nat.mul_assoc]
    _ ≤ p₁ * (p₂ * p₃) := Nat.mul_le_mul_left p₁ (Nat.mul_le_mul_left p₂ hp₂₃)
    _ = p₁ * p₂ * p₃ := by rw [Nat.mul_assoc]
    _ = N - p := hprod
    _ ≤ N := Nat.sub_le _ _

end MathlibNt.SieveTheory.SwitchingPrinciple
