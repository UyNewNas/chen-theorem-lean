/-
! # MathlibNt.SieveTheory.SingularSeries

## Goldbach 奇异级数 (Singular Series)

陈氏定理证明中, 所有上下界估计均含有奇异级数因子 𝔖(N):

  𝔖(N) = Π_{p | N, p > 2} (p-1)/(p-2) · Π_{p > 2} (1 - 1/(p-1)²)

其中第二个乘积为孪生素数常数 C₂ ≈ 0.66016...

对于偶数 N, 局部因子可化简为:
  - p = 2: 因子 = 2
  - p > 2, p | N: 因子 = p/(p-1)
  - p > 2, p ∤ N: 因子 = p(p-2)/(p-1)²

参考:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), "A Corrected Simplified Proof of Chen's Theorem", arXiv:2203.07871
  - Halberstam & Richert, "Sieve Methods" (1974)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace MathlibNt.SieveTheory.SingularSeries

open Nat Real Finset

/-! ## 1. 局部因子 (Local Factors) -/

/-- 素数 p > 2 处的奇异级数局部因子.

对于 p > 2:
  - 若 p | N:  g(p, N) = (p-1)/(p-2) · (1 - 1/(p-1)²) = p/(p-1)
  - 若 p ∤ N:  g(p, N) = (1 - 1/(p-1)²) = p(p-2)/(p-1)²

p = 2 的因子单独处理 (偶数 N 时为 2). -/
noncomputable def localFactor (p N : ℕ) : ℝ :=
  if p = 2 then
    if 2 ∣ N then 2 else 1
  else
    if p ∣ N then
      (p : ℝ) / (p - 1)
    else
      (p : ℝ) * (p - 2) / ((p - 1) ^ 2)

/-- p = 2 的因子: 偶数 N 时为 2. -/
theorem localFactor_two (hN : Even N) : localFactor 2 N = 2 := by
  unfold localFactor
  rw [if_pos rfl]
  obtain ⟨k, hk⟩ := hN
  rw [if_pos ⟨k, by omega⟩]

/-- p = 2 的因子: 奇数 N 时为 1. -/
theorem localFactor_two_odd (hN : Odd N) : localFactor 2 N = 1 := by
  unfold localFactor
  rw [if_pos rfl]
  have h : ¬ (2 : ℕ) ∣ N := by
    rintro ⟨k, hk⟩
    rw [hk] at hN
    obtain ⟨m, hm⟩ := hN
    omega
  rw [if_neg h]

/-- 素因子 p > 2 且 p | N 时的因子: p/(p-1). -/
theorem localFactor_of_dvd {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpdvd : p ∣ N) :
    localFactor p N = (p : ℝ) / (p - 1) := by
  simp [localFactor, ne_of_gt hp2, hpdvd]

/-- 素因子 p > 2 且 p ∤ N 时的因子: p(p-2)/(p-1)². -/
theorem localFactor_of_not_dvd {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N = (p : ℝ) * (p - 2) / ((p - 1) ^ 2) := by
  simp [localFactor, ne_of_gt hp2, hpn]

/-! ## 2. 局部因子的正性 -/

/-- 所有局部因子为正. -/
theorem localFactor_pos {p N : ℕ} (hp : p.Prime) : 0 < localFactor p N := by
  by_cases h2 : p = 2
  · simp [localFactor, h2]; split_ifs <;> linarith
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · omega
      · have : 2 ≤ p := hp.two_le; omega
    by_cases hpdvd : p ∣ N
    · rw [localFactor_of_dvd hp hp2 hpdvd]
      have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      exact div_pos (by exact_mod_cast hp.pos) (by linarith)
    · rw [localFactor_of_not_dvd hp hp2 hpdvd]
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp2_pos : (0 : ℝ) < p - 2 := by
        have : (2 : ℝ) < p := by exact_mod_cast hp2
        linarith
      have hp1_pos : (0 : ℝ) < p - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        linarith
      exact div_pos (mul_pos hp_pos hp2_pos) (sq_pos_of_pos hp1_pos)

/-! ## 3. 截断奇异级数 (Truncated Singular Series) -/

/-- 截断奇异级数: 素数 p ≤ z 的局部因子之积.

  𝔖(N, z) = Π_{p ≤ z, p.Prime} localFactor p N

当 z → ∞ 时收敛到 𝔖(N). -/
noncomputable def singularSeriesTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter Nat.Prime).prod (fun p => localFactor p N)

/-- 截断奇异级数为正 (所有因子为正). -/
theorem singularSeriesTruncated_pos (N z : ℕ) (hz : 1 ≤ z) :
    0 < singularSeriesTruncated N z := by
  unfold singularSeriesTruncated
  apply Finset.prod_pos
  intro p hp
  have hp_prime : p.Prime := by simp_all
  exact localFactor_pos hp_prime

/-! ## 4. 完整奇异级数 (Full Singular Series) -/

/-- 完整奇异级数: 截断乘积的极限.

  𝔖(N) = lim_{z→∞} 𝔖(N, z)

收敛性依赖于 Mertens 型估计 (Σ_{p≤x} 1/p ~ log log x). -/
noncomputable def singularSeries (N : ℕ) : ℝ :=
  -- 使用截断乘积在足够大处的值作为定义
  -- 严格定义需要无穷乘积收敛性, 此处用 z = N 作为工作定义
  singularSeriesTruncated N N

/-- 奇异级数为正. -/
theorem singularSeries_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < singularSeries N := by
  exact singularSeriesTruncated_pos N N (by omega : 1 ≤ N)

/-! ## 5. 偶数情形的显式形式 -/

/-- 偶数 N 的奇异级数: 至少包含因子 2. -/
theorem singularSeries_even_factor (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N) :
    singularSeriesTruncated N 2 = 2 := by
  unfold singularSeriesTruncated
  have h_range : (range 3).filter Nat.Prime = {2} := by decide
  rw [h_range]
  simp [localFactor_two hN]

/-! ## 6. 局部因子的上界估计 -/

/-- p > 2 且 p | N 时, 因子 p/(p-1) ≤ 3/2 (p ≥ 3). -/
theorem localFactor_dvd_le {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpdvd : p ∣ N) :
    localFactor p N ≤ 3 / 2 := by
  rw [localFactor_of_dvd hp hp2 hpdvd]
  have hp3 : 3 ≤ p := by omega
  have hp1 : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have : (p : ℝ) / (p - 1) ≤ 3 / 2 := by
    field_simp
    have : (2 : ℝ) * p ≤ 3 * (p - 1) := by
      have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      nlinarith
    linarith
  exact this

/-- p > 2 且 p ∤ N 时, 因子 p(p-2)/(p-1)² < 1 (p ≥ 3). -/
theorem localFactor_not_dvd_lt_one {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    localFactor p N < 1 := by
  rw [localFactor_of_not_dvd hp hp2 hpn]
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have : (p : ℝ) * (p - 2) / ((p - 1) ^ 2) < 1 := by
    field_simp
    have h : (p : ℝ) * (p - 2) < (p - 1) * (p - 1) := by
      have hp_cast : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      nlinarith
    linarith
  exact this

/-! ## 7. 奇异级数的界 (初等证明) -/

/-- 奇素数局部因子的下界: localFactor p N ≥ 1 - 1/(p-1)² (对 p > 2). -/
private lemma localFactor_ge_square {p N : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ localFactor p N := by
  by_cases hpdvd : p ∣ N
  · rw [localFactor_of_dvd hp hp2 hpdvd]
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [ne_of_gt hp1_pos]
    nlinarith [show (0 : ℝ) ≤ (p : ℝ) by exact_mod_cast (Nat.zero_le p)]
  · rw [localFactor_of_not_dvd hp hp2 hpdvd]
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    field_simp [ne_of_gt hp1_pos]
    nlinarith

/-- 望远镜和 (A): ∏_{k<n} (k+1)/(k+2) = 1/(n+1). -/
private lemma telescope_a (n : ℕ) :
    (Finset.range n).prod (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
      1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hn1, hn2]
      ring

/-- 望远镜和 (B): ∏_{k<n} (k+3)/(k+2) = (n+2)/2. -/
private lemma telescope_b (n : ℕ) :
    (Finset.range n).prod (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) =
      ((n : ℝ) + 2) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      norm_num [Nat.cast_add]
      field_simp [hn2]
      ring

/-- 望远镜和: ∏_{n=2}^{N-1} (1 - 1/n²) = N / (2(N-1)) (N ≥ 2). -/
private lemma int_square_product (N : ℕ) (hN : 2 ≤ N) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) =
      (N : ℝ) / (2 * ((N : ℝ) - 1)) := by
  rw [Finset.prod_Ico_eq_prod_range (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) 2 N]
  have hfac : ∀ k : ℕ,
      1 - 1 / ((2 + k : ℕ) : ℝ) ^ 2 =
        (((k : ℝ) + 1) / ((k : ℝ) + 2)) * (((k : ℝ) + 3) / ((k : ℝ) + 2)) := by
    intro k
    have hk2 : (k : ℝ) + 2 ≠ 0 := by
      have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Nat.zero_le k
      nlinarith
    norm_num [Nat.cast_add]
    field_simp [hk2]
    ring
  rw [Finset.prod_congr rfl (fun k hk => hfac k)]
  rw [Finset.prod_mul_distrib]
  have h1 : (Finset.range (N - 2)).prod (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
      1 / ((N : ℝ) - 1) := by
    rw [telescope_a (N - 2)]
    have hcast : (((N - 2 : ℕ) : ℝ) + 1) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub hN]
      ring
    rw [hcast]
  have h2 : (Finset.range (N - 2)).prod (fun k : ℕ => ((k : ℝ) + 3) / ((k : ℝ) + 2)) =
      (N : ℝ) / 2 := by
    rw [telescope_b (N - 2)]
    have hcast : (((N - 2 : ℕ) : ℝ) + 2) = (N : ℝ) := by
      rw [Nat.cast_sub hN]
      ring
    rw [hcast]
  rw [h1, h2]
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    linarith
  field_simp [hN1]

/-- 素数乘积 ≥ 全体整数乘积:
∏_{3 ≤ p ≤ N, p 素数} (1 - 1/(p-1)²) ≥ ∏_{n=2}^{N-1} (1 - 1/n²). -/
private lemma prime_square_product_ge_int (N : ℕ) :
    (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  classical
  let T : Finset ℕ := (Finset.Ico 2 N).filter (fun n => (n + 1).Prime)
  have hsubset : T ⊆ Finset.Ico 2 N := Finset.filter_subset _ _
  have h_int_le_T :
      (Finset.Ico 2 N).prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) ≤
        T.prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) := by
    exact Finset.prod_le_prod_of_subset_of_le_one hsubset
      (by
        intro n hn
        have hn2 : (2 : ℝ) ≤ n := by
          exact_mod_cast (mem_Ico.mp hn).1
        have hn1 : (1 : ℝ) ≤ n ^ 2 := by nlinarith
        have hdiv : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 :=
          div_le_one_of_le₀ hn1 (by exact_mod_cast (sq_nonneg n) : (0 : ℝ) ≤ n ^ 2)
        linarith)
      (by
        intro n hn hnT
        have hsq : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
        linarith)
  have hreindex :
      T.prod (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ) ^ 2) =
        ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
          (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    symm
    refine Finset.prod_bij (fun p hp => p - 1) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨hp_range, hp_prime, hp2⟩
      have hp_lt : p < N + 1 := mem_range.mp hp_range
      have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
      have hp1_ge2 : 2 ≤ p - 1 := by omega
      have hp1_lt : p - 1 < N := by omega
      have hp1_prime : (p - 1 + 1).Prime := by rwa [hp1]
      simp [T, mem_filter, hp1_ge2, hp1_lt, hp1_prime]
    · intro p hp
      intro p' hp' hpp'
      rw [mem_filter] at hp hp'
      rcases hp with ⟨_, _, hp2⟩
      rcases hp' with ⟨_, _, hp2'⟩
      omega
    · intro n hn
      rw [mem_filter] at hn
      rcases hn with ⟨hn_Ico, hn_prime⟩
      have hn2 : 2 ≤ n := (mem_Ico.mp hn_Ico).1
      have hnlt : n < N := (mem_Ico.mp hn_Ico).2
      refine ⟨n + 1, ?_, ?_⟩
      · rw [mem_filter]
        exact ⟨mem_range.mpr (by omega), hn_prime, by omega⟩
      · omega
    · intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨_, _, hp2⟩
      have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]
        norm_num
      rw [hcast]
  exact le_trans h_int_le_T hreindex.le

/-- 局部因子 ≤ 2 (对所有素数 p). -/
private lemma localFactor_le_two {p N : ℕ} (hp : p.Prime) : localFactor p N ≤ 2 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    split_ifs <;> norm_num
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h h2
      · have : 2 ≤ p := hp.two_le
        omega
    by_cases hpdvd : p ∣ N
    · rw [localFactor_of_dvd hp hp2 hpdvd]
      have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      field_simp [ne_of_gt hp1]
      nlinarith
    · exact le_trans (le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpdvd)) (by norm_num)

/-- p ∤ N 时局部因子 ≤ 1. -/
private lemma localFactor_le_one_of_not_dvd {p N : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ N) :
    localFactor p N ≤ 1 := by
  by_cases h2 : p = 2
  · subst h2
    unfold localFactor
    simp [hpn]
  · have hp2 : 2 < p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h h2
      · have : 2 ≤ p := hp.two_le
        omega
    exact le_of_lt (localFactor_not_dvd_lt_one hp hp2 hpn)

/-- 偶数 N 的奇异级数有正下界: 𝔖(N) ≥ 1 (所有偶数 N ≥ 2).

初等证明: 对偶数 N, 𝔖(N) = 2 · ∏_{p|N, p>2} p/(p-1) · ∏_{p∤N, p>2} p(p-2)/(p-1)².
其中 p/(p-1) ≥ 1, 而素数乘积 ∏_{p>2} (1 - 1/(p-1)²) ≥ ∏_{n=2}^{N-1} (1 - 1/n²)
= N/(2(N-1)) ≥ 1/2 (后者是望远镜和), 故 𝔖(N) ≥ 2 · 1 · 1/2 = 1. -/
theorem singularSeries_bounded_below :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → Even N → c ≤ singularSeries N := by
  refine ⟨1, by norm_num, ?_⟩
  intro N hN hEven
  unfold singularSeries singularSeriesTruncated
  set A := (range (N + 1)).filter Nat.Prime with hA_def
  have h2mem : 2 ∈ A := by
    rw [hA_def]
    simp [mem_filter, hN, Nat.prime_two]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h2mem]
  rw [localFactor_two hEven]
  have hfilter_eq : A \ {2} = (range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p) := by
    rw [hA_def]
    ext p
    constructor
    · intro hp
      rw [mem_sdiff, mem_filter] at hp
      rcases hp with ⟨hp_mem, hp_ne⟩
      rcases hp_mem with ⟨hp_range, hp_prime⟩
      rw [mem_filter]
      refine ⟨hp_range, hp_prime, ?_⟩
      have hp_ne' : p ≠ 2 := by
        intro h
        exact hp_ne (by simp [h])
      rcases hp_prime.eq_two_or_odd' with h2 | hodd
      · exact absurd h2 hp_ne'
      · have : 2 ≤ p := hp_prime.two_le
        omega
    · intro hp
      rw [mem_filter] at hp
      rcases hp with ⟨hp_range, hp_props⟩
      rcases hp_props with ⟨hp_prime, hp2⟩
      rw [mem_sdiff, mem_filter]
      constructor
      · exact ⟨hp_range, hp_prime⟩
      · intro hp_mem2
        have hp_eq2 : p = 2 := by simpa using hp_mem2
        omega
  rw [hfilter_eq]
  have hfac : ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => localFactor p N) := by
    apply Finset.prod_le_prod
    · intro p hp
      rw [mem_filter] at hp
      have hp3 : 3 ≤ p := by omega
      have hp1_ge : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
        have : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        nlinarith
      have hdiv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        exact div_le_one_of_le₀ hp1_ge (sq_nonneg ((p : ℝ) - 1))
      linarith
    · intro p hp
      rw [mem_filter] at hp
      exact localFactor_ge_square hp.2.1 hp.2.2
  have htel : (N : ℝ) / (2 * ((N : ℝ) - 1)) ≤
      ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    rw [← int_square_product N hN]
    exact prime_square_product_ge_int N
  calc
    (1 : ℝ) ≤ 2 * ((N : ℝ) / (2 * ((N : ℝ) - 1))) := by
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      field_simp
      nlinarith [show (2 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
    _ ≤ 2 * ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left htel (by norm_num)
    _ ≤ 2 * ((range (N + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
        (fun p => localFactor p N) :=
          mul_le_mul_of_nonneg_left hfac (by norm_num)

/-- 奇异级数的上界: 𝔖(N) ≤ 2^ω(N) ≤ 2N (截断定义下).

注意: 原陈述 𝔖(N) ≤ C (绝对常数) 是**假的** —— 当 N 取素因子阶乘
(primorial, 如 2·3·5·7·…·x) 时, 𝔖(N) = ∏_{p|N} p/(p-1) ~ log log N 无界.
正确且初等可证的界为: 每个局部因子 ≤ 2 (整除情形) 或 ≤ 1 (非整除情形),
故 𝔖(N) ≤ 2^{ω(N)+1} ≤ 2N. -/
theorem singularSeries_bounded_above :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → singularSeries N ≤ C * (N : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN
  unfold singularSeries singularSeriesTruncated
  set A := (range (N + 1)).filter Nat.Prime with hA_def
  have hsplit := Finset.prod_filter_mul_prod_filter_not A (fun p => p ∣ N)
    (fun p => localFactor p N)
  -- 第一部分 (p | N): 每个因子 ≤ 2, 共 ω(N) 个
  have h1 : (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N) ≤
      (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
    calc
      (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N)
          ≤ (A.filter (fun p => p ∣ N)).prod (fun _ => (2 : ℝ)) := by
              apply Finset.prod_le_prod
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact le_of_lt (localFactor_pos hpPrime)
              · intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact localFactor_le_two hpPrime
      _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by
              rw [Finset.prod_const]
  -- 第二部分 (p ∤ N): 每个因子 ≤ 1
  have h2 : (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := by
        rw [mem_filter] at hpA
        exact hpA.2
      exact le_of_lt (localFactor_pos hpPrime)
    · intro p hp
      rw [mem_filter] at hp
      have hpA : p ∈ A := hp.1
      have hpPrime : p.Prime := by
        rw [mem_filter] at hpA
        exact hpA.2
      exact localFactor_le_one_of_not_dvd hpPrime hp.2
  -- 2^ω(N) ≤ N
  have hpow : (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card ≤ (N : ℝ) := by
    have hsubset : A.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
      intro p hp
      rw [mem_filter] at hp
      rcases hp with ⟨hpA, hpdvd⟩
      rw [mem_filter] at hpA
      exact (Nat.mem_primeFactors_of_ne_zero (by omega : N ≠ 0)).2 ⟨hpA.2, hpdvd⟩
    have hcard : (A.filter (fun p => p ∣ N)).card ≤ N.primeFactors.card :=
      Finset.card_le_card hsubset
    calc
      (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card ≤ (2 : ℝ) ^ N.primeFactors.card :=
          by
            have hpow_nat : 2 ^ (A.filter (fun p => p ∣ N)).card ≤ 2 ^ N.primeFactors.card :=
              Nat.pow_le_pow_right (by norm_num) hcard
            exact_mod_cast hpow_nat
      _ = (N.primeFactors.prod fun _ => (2 : ℝ)) := by
          rw [← Finset.prod_const]
      _ ≤ N.primeFactors.prod (fun p => (p : ℝ)) := by
          apply Finset.prod_le_prod
          · intro p hp
            norm_num
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            linarith
      _ ≤ (N : ℝ) := by
          have hdvd_nat : (N.primeFactors.prod fun p => p) ∣ N := Nat.prod_primeFactors_dvd N
          have hNpos : 0 < N := by omega
          have hle_nat : N.primeFactors.prod (fun p => p) ≤ N :=
            Nat.le_of_dvd hNpos hdvd_nat
          rw [← cast_prod]
          exact_mod_cast hle_nat
  calc
    A.prod (fun p => localFactor p N)
        = (A.filter (fun p => p ∣ N)).prod (fun p => localFactor p N) *
          (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) := hsplit.symm
    _ ≤ (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card * 1 :=
            by
              have h3 : 0 ≤ (A.filter (fun p => ¬ p ∣ N)).prod (fun p => localFactor p N) := by
                apply Finset.prod_nonneg
                intro p hp
                rw [mem_filter] at hp
                have hpA : p ∈ A := hp.1
                have hpPrime : p.Prime := by
                  rw [mem_filter] at hpA
                  exact hpA.2
                exact le_of_lt (localFactor_pos hpPrime)
              have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by positivity
              exact mul_le_mul h1 h2 h3 h4
    _ = (2 : ℝ) ^ (A.filter (fun p => p ∣ N)).card := by ring
    _ ≤ (N : ℝ) := hpow
    _ ≤ 2 * (N : ℝ) := by
        have hN0 : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : 0 ≤ N)
        nlinarith

/-! ## 8. 总结 -/

/-
**奇异级数形式化状态**:

1. **定义层** (已完成):
   - `localFactor p N`: 素数 p 处的局部因子
   - `singularSeriesTruncated N z`: 截断奇异级数 (p ≤ z)
   - `singularSeries N`: 完整奇异级数 (工作定义, 严格定义需无穷乘积收敛)

2. **正性层** (已完成):
   - `localFactor_pos`: 局部因子为正
   - `singularSeriesTruncated_pos`: 截断奇异级数为正
   - `singularSeries_pos`: 奇异级数为正

3. **界估计层** (已完成, 初等证明):
   - `singularSeries_bounded_above`: 上界 𝔖(N) ≤ 2^ω(N) ≤ 2N
     (原陈述 𝔖(N) ≤ C 为假: N 取素因子阶乘时 𝔖(N) ~ log log N 无界;
     已修正为可证的真界, 证明用局部因子 ≤ 2/≤1 的分拆)
   - `singularSeries_bounded_below`: 正下界 𝔖(N) ≥ 1 (偶数 N)
     (证明: 素数乘积 ≥ 全体整数乘积, 望远镜和 ∏(1-1/n²) = N/(2(N-1)) ≥ 1/2)
   - 两者均无需 Mertens 定理或 PNT

4. **陈氏定理中的作用**:
   - W(N) ≥ 2.6408 𝔖(N) N/log²N  (下界, Jurkat-Richert)
   - Ω ≤ 3.9404 𝔖(N) N/log²N     (上界, Selberg 筛 + 大筛法)
   - 结论: W(N) - Ω/2 > 0  (因 𝔖(N) > 0)
-/

end MathlibNt.SieveTheory.SingularSeries
