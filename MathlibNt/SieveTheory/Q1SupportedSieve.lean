import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# q¹ supported-sieve finite core

This module begins the replacement for the legacy q¹ all-divisor Möbius
interface.  It contains only finite definitions and inclusions.  In
particular, it supplies no AP distribution estimate and does not consume the
legacy `q1APErrorUniformBound`.

For a fixed prime factor `q | N-p`, the source-matched route first enlarges
the corrected candidate fibre to the direct coprimality condition with the
actual corrected sifting product.  A supported Selberg upper sieve can then
be applied to this one-modulus AP sequence.  The exceptional `q | N` fibre
and every analytic input are deliberately left to later, separately audited
interfaces.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open scoped Classical

/-- The direct q¹ AP core before applying a supported upper sieve.  It uses
the corrected sifting product directly, rather than expanding its complement
over all forbidden divisors. -/
noncomputable def q1SupportedCoreCount (N q : ℕ) : ℕ :=
  ((Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧ q ∣ N - p ∧
      Nat.Coprime (correctedChenSiftingProduct N) (N - p))).card

/-- The legacy candidate q¹ fibre is contained in the direct supported-sieve
core.  This is a finite inclusion only: the future upper sieve may bound the
larger right-hand side without reintroducing the old forbidden-product
Möbius expansion. -/
theorem q1CandidateAPCount_le_supportedCore (N q : ℕ) :
    q1CandidateAPCount N q ≤ (q1SupportedCoreCount N q : ℝ) := by
  unfold q1CandidateAPCount q1SupportedCoreCount
  exact_mod_cast Finset.card_le_card (by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpCand, hq⟩
    rcases Finset.mem_filter.mp hpCand with ⟨hpRange, hpPrime, hpTwo, hsmall⟩
    refine Finset.mem_filter.mpr ⟨hpRange, hpPrime, hpTwo, hq, ?_⟩
    apply coprime_correctedChenSiftingProduct_iff.mpr
    intro r hrPrime hrlt hrgtTwo hrNotN hrDvd
    exact hsmall r hrPrime hrlt hrDvd)

/-- In the non-coprime q-fibre, `q | N` and `q | N-p` force a prime `p` to
equal the prime `q`.  Thus this exceptional fibre contributes at most one
point to the supported-sieve core. -/
theorem q1SupportedCoreCount_le_one_of_prime_dvd_N {N q : ℕ}
    (hqPrime : q.Prime) (hqN : q ∣ N) :
    q1SupportedCoreCount N q ≤ 1 := by
  unfold q1SupportedCoreCount
  calc
    ((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ q ∣ N - p ∧
        Nat.Coprime (correctedChenSiftingProduct N) (N - p))).card ≤
        ({q} : Finset ℕ).card := by
          apply Finset.card_le_card
          intro p hp
          rcases Finset.mem_filter.mp hp with ⟨hpRange, hpPrime, hpTwo, hqNp, hpCoprime⟩
          have hqP : q ∣ p := by
            rcases hqN with ⟨a, ha⟩
            rcases hqNp with ⟨b, hb⟩
            refine ⟨a - b, ?_⟩
            have hpN : p ≤ N := by omega
            calc
              p = q * a - q * b := by omega
              _ = q * (a - b) := by rw [Nat.mul_sub_left_distrib]
          have hqp : q = p :=
            (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqPrime)
              (Nat.prime_iff.mp hpPrime)).mp hqP
          simpa [hqp]
    _ = 1 := Finset.card_singleton q

/-- Every divisor of the corrected sifting product is coprime to a prime in
the q¹ range.  This is the finite separation which turns the surviving AP
modulus from an lcm into the product `q * r`. -/
theorem q1_coprime_sifting_divisor {N q r : ℕ} (hq : q.Prime)
    (hqz : correctedChenZ N ≤ q) (hr : r ∣ correctedChenSiftingProduct N) :
    Nat.Coprime q r := by
  apply Nat.coprime_of_dvd'
  intro s hs hs_dvd_q hs_dvd_r
  have hs_dvd_P : s ∣ correctedChenSiftingProduct N := dvd_trans hs_dvd_r hr
  have hs_z : s < correctedChenZ N :=
    (prime_dvd_correctedChenSiftingProduct hs).mp hs_dvd_P |>.1
  have hs_eq_q : s = q := by
    rcases (Nat.dvd_prime hq).mp hs_dvd_q with hs_one | hs_q
    · exact False.elim (hs.ne_one hs_one)
    · exact hs_q
  subst s
  exact False.elim (by omega)

/-- The q¹ prime is recoverable from a surviving supported modulus.  Hence
`(q,r) ↦ q*r` is injective when `q` is in the large-prime range and `r` is a
divisor of the corrected sifting product.  This is only the finite
repackaging part of the future weighted-BV application. -/
theorem q1_supported_modulus_injective {N q q' r r' : ℕ}
    (hq : q.Prime) (hqz : correctedChenZ N ≤ q)
    (hq' : q'.Prime)
    (hr : r ∣ correctedChenSiftingProduct N)
    (hr' : r' ∣ correctedChenSiftingProduct N)
    (hmul : q * r = q' * r') : q = q' ∧ r = r' := by
  have hq_dvd : q ∣ q' * r' := by
    rw [← hmul]
    exact dvd_mul_right q r
  rcases (Nat.Prime.dvd_mul hq).mp hq_dvd with hq_q' | hq_r'
  · have hqq' : q = q' :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hq)
        (Nat.prime_iff.mp hq')).mp hq_q'
    refine ⟨hqq', ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos hq)
    simpa [hqq'] using hmul
  · exact False.elim (Nat.not_coprime_of_dvd_of_dvd hq.one_lt (by rfl) hq_r'
      (q1_coprime_sifting_divisor hq hqz hr'))

/-- Outside the separately treated fibre `q | N`, the residue `N` is
primitive modulo every supported modulus `q*r`.  This supplies the exact
coprimality side condition for a later prime-counting-in-progressions input. -/
theorem q1_supported_modulus_coprime_N {N q r : ℕ} (hq : q.Prime)
    (hqN : ¬ q ∣ N) (hr : r ∣ correctedChenSiftingProduct N) :
    Nat.Coprime (q * r) N := by
  apply (Nat.coprime_mul_iff_left).mpr
  constructor
  · exact hq.coprime_iff_not_dvd.mpr hqN
  · exact (coprime_siftingProduct_N N).coprime_dvd_left hr

end MathlibNt.SieveTheory.SwitchingPrinciple
