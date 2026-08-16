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
            have hsub : q ∣ N - (N - p) := dvd_sub' hqN hqNp
            have hdiff : N - (N - p) = p := by omega
            rwa [hdiff] at hsub
          have hqp : q = p :=
            (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqPrime)
              (Nat.prime_iff.mp hpPrime)).mp hqP
          simpa [hqp]
    _ = 1 := Finset.card_singleton q

end MathlibNt.SieveTheory.SwitchingPrinciple
