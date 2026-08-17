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

/-- The factor-range predicate used by the source Ω indicator `chenF`. -/
def sourceOmegaFactorCondition (N a : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    (N : ℝ) ^ (1 / 10 : ℝ) < p₁ ∧
    p₁ ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
    (N : ℝ) ^ (1 / 3 : ℝ) < p₂ ∧
    (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1 / 2 : ℝ) ∧
    a = p₁ * p₂

/-- The remaining-prime condition in the source Ω sum. -/
def sourceOmegaPrimeCondition (N a p₃ : ℕ) : Prop :=
  p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime

/-- `chenF` is exactly the real indicator of the named source factor
condition.  Naming this equality prevents future finite transports from
silently changing the source range. -/
theorem chenF_eq_sourceOmegaFactorIndicator (N a : ℕ) :
    chenF N a = if sourceOmegaFactorCondition N a then 1 else 0 := rfl

/-- The finite pairs counted by the source Ω sum, presented without the
real-valued indicator `chenF`.  The first coordinate is `a = p₁*p₂`; the
second is the remaining prime `p₃`. -/
noncomputable def sourceOmegaPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter (fun w =>
    sourceOmegaFactorCondition N w.1 ∧ sourceOmegaPrimeCondition N w.1 w.2)

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
  unfold sourceOmegaPairs at hw
  rcases Finset.mem_filter.mp hw with ⟨_, hfactor, hprime⟩
  rcases hfactor with ⟨p₁, p₂, hp₁, hp₂, hp₁low, hp₁high, hp₂low, hp₂high, ha⟩
  exact ⟨p₁, p₂, hp₁, hp₂, hp₁low, hp₁high, hp₂low, hp₂high, ha,
    hprime.1, hprime.2.1, hprime.2.2⟩

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

/-- The source square-root condition follows from the retained ordered
triple.  This is the real-valued form of `ordered_triple_sq_le_N`; the only
extra hypothesis is positivity of the first prime so division is legitimate. -/
theorem ordered_triple_rpow_half_bound {N p p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂₃ : p₂ ≤ p₃)
    (hprod : p₁ * p₂ * p₃ = N - p) :
    (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1 / 2 : ℝ) := by
  have hnat : p₁ * p₂ * p₂ ≤ N := ordered_triple_sq_le_N hp₂₃ hprod
  have hcore : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (N : ℝ) := by
    have hnat' : p₁ * p₂ ^ 2 ≤ N := by
      simpa only [pow_two, Nat.mul_assoc] using hnat
    exact_mod_cast hnat'
  have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁.pos
  have hratio : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := by
    apply (le_div_iff₀ hp₁pos).mpr
    calc
      (p₂ : ℝ) ^ 2 * (p₁ : ℝ) = (p₁ : ℝ) * (p₂ : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) := hcore
  have hbase : 0 ≤ (N : ℝ) / (p₁ : ℝ) := by positivity
  have hroot_nonneg : 0 ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hbase _
  have hroot_sq : (((N : ℝ) / (p₁ : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 =
      (N : ℝ) / (p₁ : ℝ) := by
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hbase (1 / 2 : ℝ) (2 : ℝ)]
    norm_num
  have hp₂nonneg : 0 ≤ (p₂ : ℝ) := by positivity
  nlinarith

/-- A first factor strictly below the corrected ceiling cutoff lies in the
source Ω cube-root range.  The strict form is important: it is what makes a
natural number below `ceil x` at most the real number `x`. -/
theorem p1_le_cuberoot_of_lt_correctedChenY {N p₁ : ℕ}
    (hp₁ : p₁ < correctedChenY N) :
    (p₁ : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
  apply le_of_lt
  rw [correctedChenY] at hp₁
  exact Nat.lt_ceil.mp hp₁

end MathlibNt.SieveTheory.SwitchingPrinciple
