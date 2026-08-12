/-
! # MathlibNt.SieveTheory.SwitchingPrinciple

## 切换原理 (Switching Principle)

切换原理是陈氏定理证明的核心技巧. 陈景润通过引入权重函数 w(n) 将问题
从"N-p 至多两个素因子"转化为筛法可处理的估计.

**核心思路** (Chen 1973, Liu 2022):

1. **W(N)**: 满足筛法条件的素数 p 的计数
   - N-p 无 ≤ N^(1/10) 的素因子
   - N-p 在 (N^(1/10), N^(1/3)] 中至多一个素因子
   - 由 Jurkat-Richert 下界: W(N) ≥ 2.6408 𝔖(N) N/log²N

2. **Ω**: 切换和 (Switched Sum), 计算 N-p 恰好三个素因子的情形
   - Ω = Σ_a Σ_{ap₃ ≤ N, N-ap₃ 素数} f(a)
   - f(a) 为 a = p₁p₂ (满足范围条件) 的特征函数
   - 由 Selberg 筛: Ω ≤ 3.9404 𝔖(N) N/log²N

3. **关键不等式**: W(N) - Ω/2 > 0
   - W(N) - Ω/2 ≥ (2.6408 - 3.9404/2) 𝔖(N) N/log²N
   - = 0.6706 𝔖(N) N/log²N > 0
   - 故存在 N = p + q, q 半素数

参考:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), arXiv:2203.07871
  - Nathanson, "Additive Number Theory", GTM 164, Ch. 10
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import AnalyticNumberTheory
import MathlibNt.SieveTheory.SelbergUpperBound

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset

open scoped Classical

/-! ## 1. 权重函数 w(n) -/

/-- 素数幂精确整除: q^k ∥ n 表示 q^k | n 但 q^(k+1) ∤ n -/
def exactDiv (q k n : ℕ) : Prop :=
  q ^ k ∣ n ∧ ¬ q ^ (k + 1) ∣ n

/-- 在范围 [z, y) 中的素数幂精确整除 n 的重数之和:
  Σ_{z ≤ q < y, q 素数, q^k ∥ n} k -/
noncomputable def primePowerSum (n z y : ℕ) : ℝ :=
  ((range y).filter (fun q => q.Prime ∧ z ≤ q ∧
    ∃ k : ℕ, 1 ≤ k ∧ exactDiv q k n)).sum (fun q =>
      -- 取最大的 k 使得 q^k | n (即 q 的重数)
      (n.factorization q : ℝ))

/-- 三因子分解计数: Σ_{p₁p₂p₃ = n, z ≤ p₁ < y ≤ p₂ ≤ p₃} 1

注: 使用 p₂ ≤ p₃ (非严格不等式) 以正确计数 n = q * r² 的情况
(即 p₂ = p₃ = r 的情形). 原定义中 p₂ < p₃ 会遗漏此类分解. -/
noncomputable def tripleFactorCount (n z y : ℕ) : ℝ :=
  (Finset.card ((Finset.range (n + 1)).filter (fun p₁ =>
    p₁.Prime ∧ z ≤ p₁ ∧ p₁ < y ∧
    ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ * p₂ * p₃ = n ∧ p₁ < p₂ ∧ p₂ ≤ p₃)) : ℝ)

/-- **权重函数 w(n)** (Chen 的切换权重):

  w(n) = 1 - (1/2) Σ_{z ≤ q < y, q^k ∥ n} k - (1/2) Σ_{p₁p₂p₃=n, z ≤ p₁ < y ≤ p₂ ≤ p₃} 1

当 w(n) > 0 且 n 无 ≤ z 的素因子时, n ∈ {1, p, p₁p₂ : p, p₁, p₂ ≥ z}. -/
noncomputable def chenWeight (n z y : ℕ) : ℝ :=
  1 - (1/2) * primePowerSum n z y - (1/2) * tripleFactorCount n z y

/-- primePowerSum 的求和范围: [z, y) 中的素数, 且 q^k ∥ n 对某 k ≥ 1. -/
private noncomputable def Sfilter (n z y : ℕ) : Finset ℕ :=
  (range y).filter (fun q => q.Prime ∧ z ≤ q ∧ ∃ k : ℕ, 1 ≤ k ∧ exactDiv q k n)

/-- tripleFactorCount 的计数范围. -/
private noncomputable def Tfilter (n z y : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p₁ =>
    p₁.Prime ∧ z ≤ p₁ ∧ p₁ < y ∧
    ∃ p₂ p₃, p₂.Prime ∧ p₃.Prime ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ * p₂ * p₃ = n ∧ p₁ < p₂ ∧ p₂ ≤ p₃)

/-- exactDiv 的平凡构造: p 素数, p | n ⟹ p^(n.factorization p) ∥ n. -/
private lemma exactDiv_of_factorization {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpdvd : p ∣ n) :
    exactDiv p (n.factorization p) n := by
  unfold exactDiv
  constructor
  · exact (hp.pow_dvd_iff_le_factorization hn).2 le_rfl
  · intro h
    have hle : n.factorization p + 1 ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn).1 h
    omega

/-- 素数 p | n 且 z ≤ p < y ⟹ p 属于 primePowerSum 的求和范围. -/
private lemma primePowerSum_mem_of_dvd {n z y p : ℕ} (hp : p.Prime) (hz : z ≤ p)
    (hp_lt : p < y) (hn : n ≠ 0) (hpdvd : p ∣ n) :
    p ∈ Sfilter n z y := by
  rw [Sfilter, mem_filter]
  exact ⟨by simpa using hp_lt, hp, hz, n.factorization p,
    (hp.dvd_iff_one_le_factorization hn).1 hpdvd, exactDiv_of_factorization hp hn hpdvd⟩

/-- S = (Σ (n.factorization q : ℕ) : ℝ). -/
private lemma primePowerSum_eq_cast (n z y : ℕ) :
    primePowerSum n z y = ((Sfilter n z y).sum (fun q => n.factorization q) : ℝ) := by
  unfold primePowerSum Sfilter
  rw [← Nat.cast_sum]

/-- T = (card : ℝ). -/
private lemma tripleFactorCount_eq_cast (n z y : ℕ) :
    tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) := by
  rfl

/-- q ∈ Sfilter ⟹ 1 ≤ S (作为实数). -/
private lemma primePowerSum_ge_one_of_mem {n z y q : ℕ} (hz : 2 ≤ z) (hn : 1 ≤ n)
    (hq : q ∈ Sfilter n z y) : (1 : ℝ) ≤ primePowerSum n z y := by
  have hq' : q ∈ (range y).filter (fun x => x.Prime ∧ z ≤ x ∧
      ∃ k : ℕ, 1 ≤ k ∧ exactDiv x k n) := by simpa [Sfilter] using hq
  rw [mem_filter] at hq'
  rcases hq' with ⟨_, hq_prime, _, k, hk, hex⟩
  have hn0 : n ≠ 0 := by omega
  have hk_le : k ≤ n.factorization q := (hq_prime.pow_dvd_iff_le_factorization hn0).1 hex.1
  have hfact_ge : (1 : ℕ) ≤ n.factorization q := by omega
  have hsum_ge : (1 : ℕ) ≤ (Sfilter n z y).sum (fun x => n.factorization x) := by
    exact le_trans hfact_ge
      (Finset.single_le_sum (s := Sfilter n z y) (f := fun x : ℕ => n.factorization x)
        (by intro x hx; exact Nat.zero_le _) hq)
  rw [primePowerSum_eq_cast n z y]
  exact_mod_cast hsum_ge

/-- T ≥ 1 ⟹ S ≥ 1. -/
private lemma tripleFactorCount_pos_imp_primePowerSum_pos {n z y : ℕ} (hz : 2 ≤ z)
    (hn : 1 ≤ n) (hT : 0 < tripleFactorCount n z y) : 0 < primePowerSum n z y := by
  have hcard_pos : 0 < (Tfilter n z y).card := by
    rw [tripleFactorCount_eq_cast n z y] at hT
    exact_mod_cast hT
  have hne : (Tfilter n z y).Nonempty := Finset.card_pos.mp hcard_pos
  rcases hne with ⟨p₁, hp₁⟩
  rw [Tfilter, mem_filter] at hp₁
  rcases hp₁ with ⟨_, hp₁_prime, hz₁, hp₁_lt_y, p₂, p₃, hp₂_prime, hp₃_prime,
    hyp₂, hp₂p₃, hprod, hqlt, _⟩
  have hdvd : p₁ ∣ n := by
    rw [← hprod]
    simpa [Nat.mul_assoc] using dvd_mul_right p₁ (p₂ * p₃)
  have hp₁S : p₁ ∈ Sfilter n z y :=
    primePowerSum_mem_of_dvd hp₁_prime hz₁ hp₁_lt_y (by omega : n ≠ 0) hdvd
  have hS_ge : (1 : ℝ) ≤ primePowerSum n z y := primePowerSum_ge_one_of_mem hz hn hp₁S
  linarith

/-- List 乘积下界: 每项 ≥ y ⟹ y^length ≤ prod. -/
private lemma prod_ge_pow_length {y : ℕ} (l : List ℕ) (h : ∀ p ∈ l, y ≤ p) :
    y ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : y ≤ a := h a (by simp)
      have ht : y ^ t.length ≤ t.prod := ih (by
        intro p hp
        exact h p (by simp [hp]))
      calc
        y ^ (a :: t).length = y ^ (t.length + 1) := rfl
        _ = y * y ^ t.length := by rw [pow_succ']
        _ ≤ a * t.prod := Nat.mul_le_mul ha ht

/-- List length ≤ 2 的分解. -/
private lemma length_le_two_cases {l : List ℕ} (hl : l.length ≤ 2) :
    l = [] ∨ ∃ a, l = [a] ∨ ∃ a b, l = [a, b] := by
  cases l with
  | nil => left; rfl
  | cons a t =>
      right
      use a
      cases t with
      | nil => left; rfl
      | cons b u =>
          right
          use a, b
          cases u with
          | nil => rfl
          | cons c v =>
              have hlen : (a :: b :: c :: v).length = v.length + 3 := by simp
              have : v.length + 3 ≤ 2 := by
                rw [hlen] at hl
                exact hl
              omega

/-- S = 0 且 n 无 < z 素因子 ⟹ n 的所有素因子 ≥ y. -/
private lemma all_prime_factors_ge_y_of_S_zero {n z y : ℕ} (hz : 2 ≤ z) (hy : z < y)
    (hn : 1 ≤ n) (hS : primePowerSum n z y = 0)
    (hcop : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) :
    ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p := by
  intro p hp hpdvd
  by_contra h
  have hp_lt_y : p < y := by omega
  by_cases hp_lt_z : p < z
  · exact absurd hpdvd (hcop p hp hp_lt_z)
  · have hz_le_p : z ≤ p := by omega
    have hpS : p ∈ Sfilter n z y :=
      primePowerSum_mem_of_dvd hp hz_le_p hp_lt_y (by omega : n ≠ 0) hpdvd
    have hS_ge : (1 : ℝ) ≤ primePowerSum n z y := primePowerSum_ge_one_of_mem hz hn hpS
    linarith

/-- 所有素因子 ≥ y 且 n < y³ ⟹ Ω(n) ≤ 2. -/
private lemma omega_le_two_of_lt_cube {n y : ℕ} (hy : 2 ≤ y) (hn : n ≠ 0)
    (hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p) (hn_lt : (n : ℝ) < (y : ℝ) ^ 3) :
    (n.primeFactorsList.length) ≤ 2 := by
  have hprod : y ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
    apply prod_ge_pow_length
    intro p hp
    exact hall p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  by_contra h
  have hlen_ge3 : 3 ≤ n.primeFactorsList.length := by omega
  have hpow_le : y ^ 3 ≤ y ^ n.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega : 1 ≤ y) hlen_ge3
  have hle_n : y ^ 3 ≤ n := by
    calc
      y ^ 3 ≤ y ^ n.primeFactorsList.length := hpow_le
      _ ≤ n.primeFactorsList.prod := hprod
      _ = n := Nat.prod_primeFactorsList hn
  have hcast : (y : ℝ) ^ 3 ≤ (n : ℝ) := by exact_mod_cast hle_n
  have : (y : ℝ) ^ 3 < (y : ℝ) ^ 3 := lt_of_le_of_lt hcast hn_lt
  linarith

/-- n < y³ 且所有素因子 ≥ y ⟹ n = 1 / 素数 / 两素数乘积 (各 ≥ y). -/
private lemma at_most_two_factors {n y : ℕ} (hy : 2 ≤ y) (hn : 1 ≤ n)
    (hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p) (hn_lt : (n : ℝ) < (y : ℝ) ^ 3) :
    n = 1 ∨ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ y ≤ p₁ ∧ y ≤ p₂ ∧ n = p₁ * p₂ := by
  have hlen : n.primeFactorsList.length ≤ 2 :=
    omega_le_two_of_lt_cube hy (by omega : n ≠ 0) hall hn_lt
  have hcases := length_le_two_cases hlen
  rcases hcases with hnil | ⟨a, hrest⟩
  · left
    have hprod : n.primeFactorsList.prod = 1 := by
      rw [hnil]
      simp
    have : n = 1 := by
      rw [← Nat.prod_primeFactorsList (by omega : n ≠ 0)]
      exact hprod
    exact this
  · rcases hrest with h1 | ⟨a₂, b, h2⟩
    · right; left
      have hn_eq : n = a := by
        rw [← Nat.prod_primeFactorsList (by omega : n ≠ 0)]
        rw [h1]
        simp
      rw [hn_eq]
      exact Nat.prime_of_mem_primeFactorsList (by rw [h1]; simp)
    · right; right
      have hn_eq : n = a₂ * b := by
        rw [← Nat.prod_primeFactorsList (by omega : n ≠ 0)]
        rw [h2]
        simp
      have ha_prime : a₂.Prime := Nat.prime_of_mem_primeFactorsList (by rw [h2]; simp)
      have hb_prime : b.Prime := Nat.prime_of_mem_primeFactorsList (by rw [h2]; simp)
      have ha_y : y ≤ a₂ := hall a₂ ha_prime (by rw [hn_eq]; exact dvd_mul_right a₂ b)
      have hb_y : y ≤ b := hall b hb_prime (by rw [hn_eq]; exact dvd_mul_left b a₂)
      exact ⟨a₂, b, ha_prime, hb_prime, ha_y, hb_y, hn_eq⟩

/-- 三重分解 q·p₂·p₃ = n 给出 T ≥ 1. -/
private lemma tripleFactorCount_ge_one {n z y q p₂ p₃ : ℕ} (hq : q.Prime) (hzq : z ≤ q)
    (hqy : q < y) (hp2 : p₂.Prime) (hp3 : p₃.Prime) (hyp2 : y ≤ p₂)
    (hp2p3 : p₂ ≤ p₃) (hqlt : q < p₂) (hn : n = q * p₂ * p₃) :
    (1 : ℝ) ≤ tripleFactorCount n z y := by
  have hq_lt_n : q < n + 1 := by
    have : q ≤ n := by
      rw [hn]
      nlinarith [show (1 : ℕ) ≤ p₂ * p₃ by nlinarith [hp2.two_le, hp3.two_le]]
    omega
  have hq_mem : q ∈ Tfilter n z y := by
    rw [Tfilter, mem_filter]
    exact ⟨by simpa using hq_lt_n, hq, hzq, hqy,
      p₂, p₃, hp2, hp3, hyp2, hp2p3, hn.symm, hqlt, hp2p3⟩
  have hcard_ge : (1 : ℕ) ≤ (Tfilter n z y).card := by
    have hpos : 0 < (Tfilter n z y).card := Finset.card_pos.mpr ⟨q, hq_mem⟩
    omega
  have hT_cast : tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) :=
    tripleFactorCount_eq_cast n z y
  rw [hT_cast]
  exact_mod_cast hcard_ge

/-- S = 1 ⟹ 存在唯一的 q ∈ [z,y) 素数, n = q·m, m 的素因子 ≥ y. -/
private lemma S_one_structure {n z y : ℕ} (hz : 2 ≤ z) (hy : z < y) (hn : 1 ≤ n)
    (hS : primePowerSum n z y = 1)
    (hcop : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) :
    ∃ q m : ℕ, q.Prime ∧ z ≤ q ∧ q < y ∧ n = q * m ∧
      (∀ p : ℕ, p.Prime → p ∣ m → y ≤ p) := by
  have hS_nat : (Sfilter n z y).sum (fun q => n.factorization q) = 1 := by
    rw [primePowerSum_eq_cast n z y] at hS
    exact_mod_cast hS
  have hfact_ge : ∀ q ∈ Sfilter n z y, (1 : ℕ) ≤ n.factorization q := by
    intro q hq
    rw [Sfilter, mem_filter] at hq
    rcases hq with ⟨_, hq_prime, _, k, hk, hex⟩
    have hn0 : n ≠ 0 := by omega
    have hk_le : k ≤ n.factorization q := (hq_prime.pow_dvd_iff_le_factorization hn0).1 hex.1
    omega
  have hcard : (Sfilter n z y).card = 1 := by
    have hle : (Sfilter n z y).card ≤ 1 := by
      have hcl : (Sfilter n z y).card ≤ (Sfilter n z y).sum (fun q => n.factorization q) := by
        rw [Finset.card_eq_sum_ones (Sfilter n z y)]
        exact Finset.sum_le_sum (by
          intro q hq
          exact hfact_ge q hq)
      omega
    have hge : 1 ≤ (Sfilter n z y).card := by
      have hnonempty : (Sfilter n z y).Nonempty := by
        by_contra hne
        have h_empty : Sfilter n z y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [h_empty] at hS_nat
      have hpos : 0 < (Sfilter n z y).card := Finset.card_pos.mpr hnonempty
      omega
    omega
  rcases Finset.card_eq_one.mp hcard with ⟨q, hq_singleton⟩
  have hq_mem : q ∈ Sfilter n z y := by
    rw [hq_singleton]
    simp
  rw [Sfilter, mem_filter] at hq_mem
  rcases hq_mem with ⟨hq_range, hq_prime, hzq, k, hk, hex⟩
  have hq_lt_y : q < y := by simpa using hq_range
  have hfact1 : n.factorization q = 1 := by
    have : (Sfilter n z y).sum (fun x => n.factorization x) = n.factorization q := by
      rw [hq_singleton]
      simp
    omega
  have hn0 : n ≠ 0 := by omega
  have hdvd : q ∣ n := (hq_prime.dvd_iff_one_le_factorization hn0).2 (by omega)
  obtain ⟨m, hm⟩ := exists_eq_mul_right_of_dvd hdvd
  refine ⟨q, m, hq_prime, hzq, hq_lt_y, hm, ?_⟩
  intro p hp hpdvd_m
  have hpdvd_n : p ∣ n := by
    rw [hm]
    exact dvd_trans hpdvd_m (dvd_mul_left m q)
  by_contra h
  have hp_lt_y : p < y := by omega
  by_cases hp_lt_z : p < z
  · exact absurd hpdvd_n (hcop p hp hp_lt_z)
  · have hz_le_p : z ≤ p := by omega
    have hpS : p ∈ Sfilter n z y :=
      primePowerSum_mem_of_dvd hp hz_le_p hp_lt_y hn0 hpdvd_n
    have hp_eq : q = p := by
      rw [hq_singleton] at hpS
      simpa [eq_comm] using hpS
    have hq_dvd_m : q ∣ m := by
      rw [hp_eq]
      exact hpdvd_m
    have hq2_dvd : q ^ 2 ∣ n := by
      rw [hm, hp_eq]
      simpa [pow_two] using mul_dvd_mul_left p hpdvd_m
    have hexact1 : exactDiv q 1 n := by
      rw [← hfact1]
      exact exactDiv_of_factorization hq_prime hn0 hdvd
    exact hexact1.2 (by simpa using hq2_dvd)

/-- w(n) > 0 蕴含 n 为 1, 素数, 或两素数乘积 (当 n 无 ≤ z 的素因子且 n < y³ 时).

需要额外假设 `n < y³`: 当 n 的所有素因子都 ≥ y 时, w(n) = 1 > 0, 但若 n ≥ y³
则 n 可能有 3 个或更多素因子 (每个 ≥ y). 假设 n < y³ 排除此情形, 保证 n 至多
2 个素因子. -/
theorem chenWeight_pos_implies_semiprime
    (n z y : ℕ) (hz : 2 ≤ z) (hy : z < y) (hn : 1 ≤ n)
    (hn_lt : (n : ℝ) < (y : ℝ) ^ 3)
    (h_coprime : ∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n)
    (hw : 0 < chenWeight n z y) :
    n = 1 ∨ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ z ≤ p₁ ∧ z ≤ p₂ ∧ n = p₁ * p₂ := by
  have hy2 : 2 ≤ y := by omega
  have hS_cast : primePowerSum n z y =
      ((Sfilter n z y).sum (fun q => n.factorization q) : ℝ) := primePowerSum_eq_cast n z y
  have hT_cast : tripleFactorCount n z y = ((Tfilter n z y).card : ℝ) :=
    tripleFactorCount_eq_cast n z y
  have hST : primePowerSum n z y + tripleFactorCount n z y < 2 := by
    unfold chenWeight at hw
    nlinarith
  have hST_nat : (Sfilter n z y).sum (fun q => n.factorization q) + (Tfilter n z y).card < 2 := by
    rw [hS_cast, hT_cast] at hST
    exact_mod_cast hST
  have hSTle : (Sfilter n z y).sum (fun q => n.factorization q) + (Tfilter n z y).card ≤ 1 := by
    omega
  have hS_cases : (Sfilter n z y).sum (fun q => n.factorization q) = 0 ∨
      (Sfilter n z y).sum (fun q => n.factorization q) = 1 := by omega
  have hT_cases : (Tfilter n z y).card = 0 ∨ (Tfilter n z y).card = 1 := by omega
  rcases hS_cases with hS0 | hS1 <;> rcases hT_cases with hT0 | hT1
  · -- S = 0, T = 0: 所有素因子 ≥ y, 至多两个, 结构结论
    have hS0r : primePowerSum n z y = 0 := by
      rw [hS_cast]
      exact_mod_cast hS0
    have hall : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p :=
      all_prime_factors_ge_y_of_S_zero hz hy hn hS0r h_coprime
    rcases at_most_two_factors hy2 hn hall hn_lt with hn1 | hprime | ⟨p₁, p₂, hp₁, hp₂, hp₁y, hp₂y, hn_eq⟩
    · exact Or.inl hn1
    · exact Or.inr (Or.inl hprime)
    · exact Or.inr (Or.inr ⟨p₁, p₂, hp₁, hp₂,
        le_trans (le_of_lt hy) hp₁y, le_trans (le_of_lt hy) hp₂y, hn_eq⟩)
  · -- S = 0, T = 1: T > 0 → S > 0 矛盾
    have hT_pos : 0 < tripleFactorCount n z y := by
      rw [hT_cast]
      exact_mod_cast (by omega : 0 < (Tfilter n z y).card)
    have hS_pos : 0 < primePowerSum n z y :=
      tripleFactorCount_pos_imp_primePowerSum_pos hz hn hT_pos
    have hS0r : primePowerSum n z y = 0 := by
      rw [hS_cast]
      exact_mod_cast hS0
    linarith
  · -- S = 1, T = 0
    have hS1r : primePowerSum n z y = 1 := by
      rw [hS_cast]
      exact_mod_cast hS1
    have hT0r : tripleFactorCount n z y = 0 := by
      rw [hT_cast]
      exact_mod_cast hT0
    rcases S_one_structure hz hy hn hS1r h_coprime with
      ⟨q, m, hq_prime, hzq, hq_lt_y, hn_eq, hm_factors⟩
    have hm_pos : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      rw [hm0, mul_zero] at hn_eq
      omega
    have hm_ne0 : m ≠ 0 := by omega
    have hm_lt_n : m < n := by
      have hq_ge2 : 2 ≤ q := hq_prime.two_le
      have hmul : 2 * m ≤ n := by
        rw [hn_eq]
        exact Nat.mul_le_mul_right m hq_ge2
      nlinarith
    have hn_lt_nat : n < y ^ 3 := by exact_mod_cast hn_lt
    have hm_lt_cube : (m : ℝ) < (y : ℝ) ^ 3 := by
      exact_mod_cast (lt_trans hm_lt_n hn_lt_nat)
    have hlen_m : m.primeFactorsList.length ≤ 2 :=
      omega_le_two_of_lt_cube hy2 hm_ne0 hm_factors hm_lt_cube
    rcases length_le_two_cases hlen_m with hmnil | ⟨a, hmrest⟩
    · -- m = 1 → n = q 素数
      right; left
      have hm_eq : m = 1 := by
        rw [← Nat.prod_primeFactorsList hm_ne0]
        rw [hmnil]
        simp
      rw [hn_eq, hm_eq, mul_one]
      exact hq_prime
    · rcases hmrest with hm1 | ⟨a₂, b, hm2⟩
      · -- m = a 素数 → n = q·a 半素数
        right; right
        have hm_eq : m = a := by
          rw [← Nat.prod_primeFactorsList hm_ne0]
          rw [hm1]
          simp
        have ha_prime : a.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hm1]; simp)
        have ha_y : y ≤ a := hm_factors a ha_prime (by rw [hm_eq])
        refine ⟨q, a, hq_prime, ha_prime, hzq, le_trans (le_of_lt hy) ha_y, ?_⟩
        rw [hn_eq, hm_eq]
      · -- m = a·b 两素数 → 三重分解 → T ≥ 1 矛盾
        have hm_eq : m = a₂ * b := by
          rw [← Nat.prod_primeFactorsList hm_ne0]
          rw [hm2]
          simp
        have ha_prime : a₂.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hm2]; simp)
        have hb_prime : b.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hm2]; simp)
        have ha_y : y ≤ a₂ := hm_factors a₂ ha_prime (by rw [hm_eq]; exact dvd_mul_right a₂ b)
        have hb_y : y ≤ b := hm_factors b hb_prime (by rw [hm_eq]; exact dvd_mul_left b a₂)
        have hn_triple : n = q * a₂ * b := by
          rw [hn_eq, hm_eq]
          rw [Nat.mul_assoc]
        have hab : a₂ ≤ b ∨ b ≤ a₂ := le_total a₂ b
        rcases hab with hab | hba
        · have hT_ge : (1 : ℝ) ≤ tripleFactorCount n z y :=
            tripleFactorCount_ge_one hq_prime hzq hq_lt_y ha_prime hb_prime ha_y hab
              (lt_of_lt_of_le hq_lt_y ha_y) hn_triple
          linarith
        · have hT_ge : (1 : ℝ) ≤ tripleFactorCount n z y :=
            tripleFactorCount_ge_one hq_prime hzq hq_lt_y hb_prime ha_prime hb_y hba
              (lt_of_lt_of_le hq_lt_y hb_y) (by
                rw [hn_triple]
                ring_nf)
          linarith
  · -- S = 1, T = 1: S + T = 2 > 1 矛盾
    omega

/-! ## 2. W(N) 的定义 -/

/-- The finite candidate set underlying the working W-count.  It is named so
that a corrected switching argument can partition its good, bad, and boundary
fibres without changing the analytic-facing count all at once. -/
noncomputable def chenWCandidates (N : ℕ) : Finset ℕ :=
  let z := Nat.floor ((N : ℝ) ^ (1/10 : ℝ))
  let y := Nat.floor ((N : ℝ) ^ (1/3 : ℝ))
  (Finset.range N).filter (fun p =>
    p.Prime ∧
    (∀ q : ℕ, q.Prime → q ≤ z → ¬ q ∣ (N - p)) ∧
    (Finset.card ((Finset.range (y + 1)).filter (fun q =>
      q.Prime ∧ z < q ∧ q ≤ y ∧ q ∣ (N - p))) ≤ 1))

/-- **W(N)**: 满足筛法条件的素数 p 的计数.

W(N) = |{p 素数 : N - p 无 ≤ N^(1/10) 的素因子, 且 (N^(1/10), N^(1/3)] 中至多一个素因子}|

由 Jurkat-Richert 下界: W(N) ≥ 2.6408 𝔖(N) N/log²N -/
noncomputable def chenW (N : ℕ) : ℝ :=
  (chenWCandidates N).card

/-- **W(N) 下界的逐点余项接口**.

当前线性筛接口中的误差常数可依赖固定 `N`，因此不能在没有统一性
假设时删除余项。真正的 Jurkat--Richert 统一下界收集在下面的
`ChenAnalyticBounds` 输入中。 -/
theorem chenW_lower_bound (N : ℕ) (hN : Even N) (hN_large : 1000 ≤ N) :
    ∃ C : ℝ,
      2.6408 * chenW N ≥
        2.6408 * 2.6408 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 -
          C * (N : ℝ) / (log N) ^ 10 := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ 10 :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (pow_pos hlog 10)
  let L : ℝ := 2.6408 * chenW N
  let M : ℝ := 2.6408 * 2.6408 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2
  refine ⟨(M - L) / ((N : ℝ) / (log N) ^ 10), ?_⟩
  change L ≥ M - (M - L) / ((N : ℝ) / (log N) ^ 10) * (N : ℝ) /
    (log N) ^ 10
  rw [mul_div_assoc, div_mul_cancel₀ _ (ne_of_gt hscale)]
  linarith

/-- The working `chenW` is bounded by the number of primes below `N`.

This is only the filter-inclusion `chenW ≤ π(N - 1)`.  It is not a lower
bound for Chen representations and is not used by the conditional Chen chain. -/
theorem chenW_le_primeCount (N : ℕ) :
    chenW N ≤ ((Finset.card ((range N).filter Nat.Prime) : ℕ) : ℝ) := by
  unfold chenW chenWCandidates
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  obtain ⟨hp_range, hp_prime, -, -⟩ := hp
  exact ⟨hp_range, hp_prime⟩

/-! ## 3. Ω 的定义 (切换和) -/

/-- **特征函数 f(a)**: a = p₁p₂ 满足 N^(1/10) < p₁ ≤ N^(1/3) < p₂ ≤ (N/p₁)^(1/2) -/
noncomputable def chenF (N a : ℕ) : ℝ :=
  if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
      (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
      (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
      a = p₁ * p₂ then 1 else 0

/-- **切换和 Ω**:

  Ω = Σ_a Σ_{ap₃ ≤ N, N-ap₃ 素数} f(a)

其中 f(a) 为 a = p₁p₂ 满足范围条件的特征函数.
Ω 计算 N-p 恰好三个素因子且满足特定范围关系的情形数. -/
noncomputable def chenOmega (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum (fun a =>
    chenF N a *
      (Finset.range (N + 1)).sum (fun p₃ =>
        if p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime then 1 else 0))

/-- **Ω 上界的逐点余项接口**. -/
theorem chenOmega_upper_bound (N : ℕ) (hN : Even N) (hN_large : 1000 ≤ N) :
    ∃ C : ℝ,
      chenOmega N ≤ 3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 +
        C * (N : ℝ) / (log N) ^ 10 := by
  simpa [chenOmega, chenF] using
    SelbergUpperBound.chenOmega_simple_bound N hN hN_large

/-- The two analytic estimates currently available at one fixed `N`, with
their remainders made explicit.  This is deliberately weaker than the uniform
Jurkat--Richert/Selberg input needed for Chen's theorem: the errors may still
depend on `N`. -/
def ChenPointwiseAnalyticBoundsAt (N : ℕ) : Prop :=
  ∃ errorW errorOmega : ℝ,
    2.6408 * chenW N ≥
      2.6408 * 2.6408 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 - errorW
      ∧ chenOmega N ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 + errorOmega

/-- Package the existing pointwise remainder interfaces into an explicit error
budget.  No uniformity in `N` is claimed here. -/
theorem chen_pointwise_analytic_bounds_at (N : ℕ) (hN : Even N)
    (hN_large : 1000 ≤ N) : ChenPointwiseAnalyticBoundsAt N := by
  obtain ⟨CW, hW⟩ := chenW_lower_bound N hN hN_large
  obtain ⟨CO, hO⟩ := chenOmega_upper_bound N hN hN_large
  exact ⟨CW * (N : ℝ) / (log N) ^ 10,
    CO * (N : ℝ) / (log N) ^ 10, hW, hO⟩

/-- A closed pointwise error budget forces Chen's numerical key inequality.

This isolates the precise analytic work still needed for a uniform theorem:
prove that the two remainders fit this strict budget uniformly for all
sufficiently large even `N`. -/
theorem chen_key_inequality_of_error_budget {N : ℕ} {errorW errorOmega : ℝ}
    (hW :
      2.6408 * chenW N ≥
        2.6408 * 2.6408 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 - errorW)
    (hO :
      chenOmega N ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 + errorOmega)
    (hbudget :
      0 <
        (2.6408 * 2.6408 - 2.6408 * 3.9404 / 2) *
            ((N : ℝ) / (log N) ^ 2) - errorW -
          2.6408 * errorOmega / 2) :
    chenW N - chenOmega N / 2 > 0 := by
  have hcoeff : (0 : ℝ) < 2.6408 := by norm_num
  ring_nf at hW hO hbudget ⊢
  nlinarith

/-- 陈氏定理中真正需要的、对所有充分大 `N` 统一的两个解析估计。 -/
def ChenAnalyticBounds : Prop :=
  ∀ N : ℕ, Even N → 1000 ≤ N →
    2.6408 * chenW N ≥
        2.6408 * 2.6408 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 ∧
      chenOmega N ≤ 3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2

/-! ## 4. 关键不等式 -/

/-- **陈氏定理关键不等式**: W(N) - Ω/2 > 0

  W(N) - Ω/2 ≥ (2.6408 - 3.9404/2) 𝔖(N) N/log²N
             = 0.6706 𝔖(N) N/log²N
             > 0

因 𝔖(N) > 0 (奇异级数正性), 故 W(N) - Ω/2 > 0.

这意味着存在素数 p 使 N - p 为至多两个素数乘积:
  - W(N) 计数满足筛法条件的 p (N-p 至多三个素因子)
  - Ω/2 计数 N-p 恰好三个素因子的情形 (对称性取一半)
  - W(N) - Ω/2 > 0 → 存在 p 使 N-p 至多两个素因子 -/
theorem chen_key_inequality (h_analytic : ChenAnalyticBounds)
    (N : ℕ) (hN : Even N) (hN_large : 1000 ≤ N) :
    chenW N - chenOmega N / 2 > 0 := by
  obtain ⟨hW, hO⟩ := h_analytic N hN hN_large
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let X : ℝ := (N : ℝ) / (log N) ^ 2
  have hscale : 0 < X := by
    dsimp [X]
    positivity
  have hW' : 2.6408 * chenW N ≥ 2.6408 * 2.6408 * (1 : ℝ) * X := by
    convert hW using 1
    dsimp [X]
    ring
  have hO' : chenOmega N ≤ 3.9404 * (1 : ℝ) * X := by
    convert hO using 1
    dsimp [X]
    ring
  norm_num at hW' hO' ⊢
  nlinarith

/-- 已经得到陈氏结论的素数候选集。 -/
noncomputable def chenGoodRepresentations (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧ Nat.IsAtMostAlmostPrime 2 (N - p))

/-- The unit boundary fibre of the W-candidates. -/
noncomputable def chenUnitCandidates (N : ℕ) : Finset ℕ :=
  (chenWCandidates N).filter (fun p => N - p = 1)

/-- The exceptional candidate with `N - p = 1` occurs at most once.  A
corrected switching count must either remove this fibre from `chenW` or carry
this explicit boundary term. -/
theorem range_sub_eq_one_card_le_one (N : ℕ) :
    ((Finset.range N).filter (fun p => N - p = 1)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  omega

/-- The unit fibre inside the named W-candidate set also has cardinality at
most one. -/
theorem chenUnitCandidates_card_le_one (N : ℕ) :
    (chenUnitCandidates N).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (range_sub_eq_one_card_le_one N)
  intro p hp
  simp only [chenUnitCandidates, Finset.mem_filter] at hp
  refine Finset.mem_filter.mpr ⟨?_, hp.2⟩
  simpa [chenWCandidates] using (Finset.mem_filter.mp hp.1).1

/-- Corrected lower sieve cutoff.  The `max 2` removes the small-`N`
degeneracy of the historical floor cutoff. -/
noncomputable def correctedChenZ (N : ℕ) : ℕ :=
  max 2 (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)))

/-- Corrected upper switching cutoff.  Using a ceiling makes the intended
cube-scale coverage an explicit parameter condition rather than a rounding
accident. -/
noncomputable def correctedChenY (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (1 / 3 : ℝ))

/-- The base candidates for a replacement switching argument.  Unlike the
historical W-candidates, the unit fibre is excluded at the definition level.
The future analytic lower bound must be proved anew for this object. -/
noncomputable def correctedChenCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → ¬ r ∣ N - p)

/-- Complements used before the corrected sieve removes small primes not
already forced away by parity or by a prime factor of `N`. -/
noncomputable def correctedChenUnsiftedComplements (N : ℕ) : Finset ℕ :=
  ((Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N →
        (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p)).image (fun p => N - p)

/-- Product of the small primes which remain to be sieved from the corrected
complement support. -/
noncomputable def correctedChenSiftingProduct (N : ℕ) : ℕ :=
  ((Finset.range (correctedChenZ N)).filter
    (fun r => r.Prime ∧ 2 < r ∧ ¬ r ∣ N)).prod id

/-- The corrected sifting product is squarefree because its factors are
distinct primes. -/
theorem correctedChenSiftingProduct_squarefree (N : ℕ) :
    Squarefree (correctedChenSiftingProduct N) := by
  unfold correctedChenSiftingProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes hp.2.1 hq.2.1).mpr hpq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1.squarefree

/-- Goldbach local density for the corrected sieve: the reusable ant density
`ν(d) = ∏_{p | d} 1/(p-1)` (`AnalyticNumberTheory.Sieve.goldbachNu`). -/
noncomputable abbrev correctedChenNu : ArithmeticFunction ℝ :=
  AnalyticNumberTheory.Sieve.goldbachNu

/-- The prime factors of a product of distinct primes are exactly the set of
those primes. -/
private theorem primeFactors_prod_eq_self {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) : (S.prod id).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp [Nat.primeFactors_one]
  | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : S.prod id ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
        ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl

/-- The corrected sifting product is nonzero: it is a product of primes. -/
theorem correctedChenSiftingProduct_ne_zero (N : ℕ) :
    correctedChenSiftingProduct N ≠ 0 := by
  unfold correctedChenSiftingProduct
  exact ne_of_gt (Finset.prod_pos (by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    exact hr.2.1.pos))

/-- The prime divisors of the corrected sifting product are exactly its
factor primes: `2 < r < z` with `r ∤ N`. -/
theorem correctedChenSiftingProduct_primeFactors (N : ℕ) :
    (correctedChenSiftingProduct N).primeFactors =
      ((Finset.range (correctedChenZ N)).filter
        (fun r => r.Prime ∧ 2 < r ∧ ¬ r ∣ N)) := by
  unfold correctedChenSiftingProduct
  exact primeFactors_prod_eq_self (by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp.2.1)

/-- A prime divides the corrected sifting product exactly when it is one of
the sieved primes: `2 < p < z` and `p ∤ N`. -/
theorem prime_dvd_correctedChenSiftingProduct {N p : ℕ} (hp : p.Prime) :
    p ∣ correctedChenSiftingProduct N ↔
      p < correctedChenZ N ∧ 2 < p ∧ ¬ p ∣ N := by
  constructor
  · intro hdvd
    have hmem : p ∈ (correctedChenSiftingProduct N).primeFactors :=
      (Nat.mem_primeFactors_of_ne_zero (correctedChenSiftingProduct_ne_zero N)).mpr
        ⟨hp, hdvd⟩
    rw [correctedChenSiftingProduct_primeFactors N] at hmem
    rcases Finset.mem_filter.mp hmem with ⟨hp_range, hcond⟩
    exact ⟨by simpa using hp_range, hcond.2.1, hcond.2.2⟩
  · intro hmem
    have hmem' : p ∈ (correctedChenSiftingProduct N).primeFactors := by
      rw [correctedChenSiftingProduct_primeFactors N]
      exact Finset.mem_filter.mpr ⟨by simpa using hmem.1, ⟨hp, hmem.2.1, hmem.2.2⟩⟩
    exact (Nat.mem_primeFactors_of_ne_zero (correctedChenSiftingProduct_ne_zero N)).mp hmem' |>.2

/-- The corrected Chen sieve as a mathlib `BoundingSieve` record: the
unsifted complements as support, the surviving small-prime product as
`prodPrimes`, unit weights, and the Goldbach local density
`ν(p) = 1/(p-1)`.

The total mass is the analytic main term `N / log N`.  With the density
identification `ν(d) = 1/φ(d)` for squarefree `d`, the remainder
`rem d = multSum d − ν(d)·N/log N` is exactly the congruence-count error that
the averaged Pan-type distribution condition (`CorrectedChenDistributionCondition`)
controls; the difference between `N/log N` and the true support cardinality is
absorbed by the main-term constants of the analytic workline, not by the
`errSum`. -/
noncomputable def correctedChenBoundingSieve (N : ℕ) : BoundingSieve where
  support := correctedChenUnsiftedComplements N
  prodPrimes := correctedChenSiftingProduct N
  prodPrimes_squarefree := correctedChenSiftingProduct_squarefree N
  weights := fun _ => 1
  weights_nonneg := by intro n; norm_num
  totalMass := (N : ℝ) / log (N : ℝ)
  nu := correctedChenNu
  nu_mult := AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative
  nu_pos_of_prime := by
    intro p hp hdiv
    exact AnalyticNumberTheory.Sieve.goldbachNu_pos_of_prime hp
  nu_lt_one_of_prime := by
    intro p hp hdiv
    have hpcond := (prime_dvd_correctedChenSiftingProduct hp).mp hdiv
    exact AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hp hpcond.2.1

/-- The corrected sieve total mass is the analytic main term `N / log N`. -/
theorem correctedChenTotalMass_eq (N : ℕ) :
    (correctedChenBoundingSieve N).totalMass = (N : ℝ) / log (N : ℝ) := rfl

/-- An element is coprime to the corrected sifting product exactly when no
sieved prime (that is, no prime `2 < r < z` with `r ∤ N`) divides it. -/
theorem coprime_correctedChenSiftingProduct_iff {N a : ℕ} :
    Nat.Coprime (correctedChenSiftingProduct N) a ↔
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → 2 < r → ¬ r ∣ N → ¬ r ∣ a := by
  constructor
  · intro hcop r hr hr_z hr_gt2 hr_ndvd hr_dvd
    have hr_dvd_P : r ∣ correctedChenSiftingProduct N :=
      (prime_dvd_correctedChenSiftingProduct hr).mpr ⟨hr_z, hr_gt2, hr_ndvd⟩
    exact Nat.not_coprime_of_dvd_of_dvd hr.one_lt hr_dvd_P hr_dvd hcop
  · intro hno
    apply Nat.coprime_of_dvd'
    intro r hr hr_dvd_P hr_dvd
    rcases (prime_dvd_correctedChenSiftingProduct hr).mp hr_dvd_P with ⟨hr_z, hr_gt2, hr_ndvd⟩
    exact False.elim (hno r hr hr_z hr_gt2 hr_ndvd hr_dvd)

/-- The small-prime sieve leaves exactly the corrected candidates: an
unsifted complement survives the sieve precisely when its prime partner lies
in the corrected candidate set. -/
theorem correctedChenSiftedComplements_eq_correctedCandidate_image (N : ℕ) :
    (correctedChenUnsiftedComplements N).filter
        (fun a => Nat.Coprime (correctedChenSiftingProduct N) a) =
      (correctedChenCandidates N).image (fun p => N - p) := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨ha_sup, hacop⟩
    rcases Finset.mem_image.mp ha_sup with ⟨p, hp_base, hpa⟩
    refine Finset.mem_image.mpr ⟨p, ?_, hpa⟩
    rcases Finset.mem_filter.mp hp_base with ⟨hp_range, hp_prime, hp_two, hp_small⟩
    refine Finset.mem_filter.mpr ⟨hp_range, ⟨hp_prime, hp_two, ?_⟩⟩
    intro r hr hr_z hr_dvd
    by_cases hr_le2 : r ≤ 2
    · exact False.elim (hp_small r hr hr_z (Or.inl hr_le2) hr_dvd)
    · by_cases hrN : r ∣ N
      · exact False.elim (hp_small r hr hr_z (Or.inr hrN) hr_dvd)
      · have hr_gt2 : 2 < r := by omega
        have hnot : ¬ r ∣ a :=
          (coprime_correctedChenSiftingProduct_iff.mp hacop) r hr hr_z hr_gt2 hrN
        have hnot' : ¬ r ∣ N - p := by
          rw [hpa]
          exact hnot
        exact False.elim (hnot' hr_dvd)
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨p, hp_cand, hpa⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [hpa.symm]
      rcases Finset.mem_filter.mp hp_cand with ⟨hp_range, hp_prime, hp_two, hstrong⟩
      refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨hp_range, ⟨hp_prime, hp_two, ?_⟩⟩
      intro r hr hr_z hcond
      exact hstrong r hr hr_z
    · rw [hpa.symm]
      apply coprime_correctedChenSiftingProduct_iff.mpr
      intro r hr hr_z hr_gt2 hrN hr_dvd
      rcases Finset.mem_filter.mp hp_cand with ⟨hp_range, hp_prime, hp_two, hstrong⟩
      exact hstrong r hr hr_z hr_dvd

/-- The number of unsifted complements that survive the corrected sieve is
exactly the number of corrected candidates. -/
theorem correctedChenSiftedCard_eq_correctedCandidateCard (N : ℕ) :
    ((correctedChenUnsiftedComplements N).filter
        (fun a => Nat.Coprime (correctedChenSiftingProduct N) a)).card =
      (correctedChenCandidates N).card := by
  rw [correctedChenSiftedComplements_eq_correctedCandidate_image]
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  rcases Finset.mem_filter.mp hp with ⟨hp_range, _⟩
  rcases Finset.mem_filter.mp hq with ⟨hq_range, _⟩
  have hp_lt : p < N := by simpa using hp_range
  have hq_lt : q < N := by simpa using hq_range
  change N - p = N - q at hpq
  omega

/-- The `BoundingSieve` sifted sum for the corrected Chen sieve is exactly the
corrected candidate count. -/
theorem correctedChenBoundingSieve_siftedSum_eq_card (N : ℕ) :
    (correctedChenBoundingSieve N).siftedSum = (correctedChenCandidates N).card := by
  change (∑ d ∈ correctedChenUnsiftedComplements N,
      if Nat.Coprime (correctedChenSiftingProduct N) d then (1 : ℝ) else 0) =
    ↑(correctedChenCandidates N).card
  rw [Finset.sum_boole]
  exact_mod_cast correctedChenSiftedCard_eq_correctedCandidateCard N

/-- The prime support of the unsifted complements: primes `p < N` whose
complement is at least two and carries no `r ≤ 2` or `r | N` prime divisor
below `z`.  It is the preimage of the sieve support under `p ↦ N - p`. -/
noncomputable def correctedChenUnsiftedPrimeSupport (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N →
        (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p)

/-- The unsifted complement support is definitionally the image of the prime
support under `p ↦ N - p`. -/
theorem correctedChenUnsiftedComplements_eq_image (N : ℕ) :
    correctedChenUnsiftedComplements N =
      (correctedChenUnsiftedPrimeSupport N).image (fun p => N - p) := by
  rfl

/-- The corrected sieve `multSum` is the number of support elements divisible
by `d`. -/
theorem correctedChenMultSum_eq_multiples_card (N d : ℕ) :
    (correctedChenBoundingSieve N).multSum d =
      ((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card := by
  unfold BoundingSieve.multSum
  change (∑ a ∈ correctedChenUnsiftedComplements N,
      if d ∣ a then (1 : ℝ) else 0) =
    ↑((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card
  rw [Finset.sum_boole]

/-- Counting the multiples of `d` in the sieve support is the same as
counting the prime-support partners with `d ∣ N - p`. -/
theorem correctedChenMultiples_card_eq_primeSupport (N d : ℕ) :
    ((correctedChenUnsiftedComplements N).filter (fun a => d ∣ a)).card =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => d ∣ N - p)).card := by
  rw [correctedChenUnsiftedComplements_eq_image, Finset.filter_image]
  apply Finset.card_image_of_injOn
  intro p hp q hq hpq
  change N - p = N - q at hpq
  have hp_full : (p < N ∧ p.Prime ∧ 2 ≤ N - p ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - p) ∧
        d ∣ N - p := by
    simpa [correctedChenUnsiftedPrimeSupport] using hp
  have hq_full : (q < N ∧ q.Prime ∧ 2 ≤ N - q ∧
      ∀ r : ℕ, r.Prime → r < correctedChenZ N → (r ≤ 2 ∨ r ∣ N) → ¬ r ∣ N - q) ∧
        d ∣ N - q := by
    simpa [correctedChenUnsiftedPrimeSupport] using hq
  have hp_lt : p < N := hp_full.1.1
  have hq_lt : q < N := hq_full.1.1
  omega

/-- The corrected sieve distribution count is the number of prime-support
partners congruent to `N` modulo `d`.  This is the finite seam at which a
Bombieri--Vinogradov/Pan input bounds `multSum` and hence `errSum`. -/
theorem correctedChenMultSum_eq_modEq_count (N d : ℕ) :
    (correctedChenBoundingSieve N).multSum d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card := by
  rw [correctedChenMultSum_eq_multiples_card, correctedChenMultiples_card_eq_primeSupport]
  have hf :
      (correctedChenUnsiftedPrimeSupport N).filter (fun p => d ∣ N - p) =
        (correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d]) := by
    apply Finset.filter_congr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_range, _⟩
    exact AnalyticNumberTheory.Sieve.prime_dvd_complement_iff_modEq (by simpa using hp_range)
  rw [hf]

/-- The corrected sieve remainder at `d` is the prime-support congruence
count minus the density main term. -/
theorem correctedChenRem_eq_modEq_count (N d : ℕ) :
    (correctedChenBoundingSieve N).rem d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
        correctedChenNu d * (correctedChenBoundingSieve N).totalMass := by
  unfold BoundingSieve.rem
  rw [correctedChenMultSum_eq_modEq_count]
  simp [correctedChenBoundingSieve]

/-- The corrected sieve `errSum` is the sum over sieve divisors of the
absolute congruence-count error.  This is the exact finite form that a
uniform distribution estimate must bound. -/
theorem correctedChenErrSum_eq_modEq (N : ℕ) (muPlus : ℕ → ℝ) :
    (correctedChenBoundingSieve N).errSum muPlus =
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        |muPlus d| *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * (correctedChenBoundingSieve N).totalMass| := by
  unfold BoundingSieve.errSum
  simp_rw [correctedChenRem_eq_modEq_count]
  rfl

/-- The uniform Bombieri--Vinogradov-style distribution condition required by
the corrected sieve: for every `A > 0` there is a uniform `C` such that the
`3^{ω(d)}`-weighted sum over sieve divisors of the congruence-count errors is
at most `C · N/log^A N`, uniformly for all sufficiently large even `N`.

This is the **averaged Pan form**, not a per-modulus bound: the individual
errors do not sum to a `log^{-A}` bound because the divisor count of the
sifting product is exponential in `z`.  The local `bombieri_vinogradov`
interface in `BombieriVinogradov.lean` is only its fixed-parameter remainder
form; this averaged target is what actually bounds the corrected sieve's
`errSum` (see `correctedChenErrSum_le_panWeighted`). -/
def CorrectedChenDistributionCondition : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1000 ≤ N → Even N →
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * ((N : ℝ) / log (N : ℝ))| ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A

/-- The counting-sieve `errSum` is bounded by the `3^{ω(d)}`-weighted
congruence-error sum controlled by `CorrectedChenDistributionCondition`. -/
theorem correctedChenErrSum_le_panWeighted (N : ℕ) :
    (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      ∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * (correctedChenBoundingSieve N).totalMass| := by
  rw [correctedChenErrSum_eq_modEq]
  apply Finset.sum_le_sum
  intro d hd
  have hw : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  simpa using le_mul_of_one_le_left (abs_nonneg _) hw

/-- Given the averaged Pan-type distribution condition, the counting-sieve
`errSum` of the corrected sieve is uniformly `O(N / log^A N)`.  This closes
the `errSum` line conditionally on the single analytic input
`CorrectedChenDistributionCondition`. -/
theorem correctedChenErrSum_uniform_of_distribution {A : ℝ} (hA : 0 < A)
    (N : ℕ) (hN : 1000 ≤ N) (hEven : Even N)
    (hdist : CorrectedChenDistributionCondition) :
    ∃ C : ℝ, 0 < C ∧
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A := by
  rcases hdist A hA with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact le_trans (correctedChenErrSum_le_panWeighted N) (hbound N hN hEven)

/-! ## 消费 ant 的加权 Pan-BV 输入 (chen issue #6) -/

/-- The reusable ant weighted Pan-BV input
(`AnalyticNumberTheory.Sieve.WeightedPanCondition`) instantiated at the
corrected Chen sieve: `x N = N`, `S N = correctedChenBoundingSieve N`,
`w d = 3^{ω(d)}`.  This is exactly the input formalized in
[ant issue #7](https://github.com/UyNewNas/analytic-number-theory-lean/issues/7). -/
def ChenWeightedPanInput : Prop :=
  AnalyticNumberTheory.Sieve.WeightedPanCondition (fun N : ℕ => (N : ℝ))
    correctedChenBoundingSieve (fun d => (3 : ℝ) ^ d.primeFactors.card)

/-- The corrected sieve's weighted Pan sum is the ant `weightedPanRemainder`:
the congruence-count error at `d` is exactly the `BoundingSieve` remainder
`rem d = multSum d − ν(d)·N/log N`. -/
theorem correctedChenPanSum_eq_weightedPanRemainder (N : ℕ) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
            correctedChenNu d * ((N : ℝ) / log (N : ℝ))|) =
      AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  unfold AnalyticNumberTheory.Sieve.weightedPanRemainder
  apply Finset.sum_congr rfl
  intro d hd
  have hrem : (correctedChenBoundingSieve N).rem d =
      ((correctedChenUnsiftedPrimeSupport N).filter (fun p => p ≡ N [MOD d])).card -
        correctedChenNu d * ((N : ℝ) / log (N : ℝ)) := by
    rw [correctedChenRem_eq_modEq_count]
    rfl
  rw [hrem]

/-- Consuming the ant weighted Pan-BV input: the corrected sieve's
distribution condition is **exactly** the ant `WeightedPanCondition`
instance. -/
theorem correctedChenDistributionCondition_iff_chenWeightedPanInput :
    CorrectedChenDistributionCondition ↔ ChenWeightedPanInput := by
  constructor
  · intro h A hA
    rcases h A hA with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN hEven
    rw [← correctedChenPanSum_eq_weightedPanRemainder N]
    exact hbound N hN hEven
  · intro h A hA
    rcases h A hA with ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro N hN hEven
    rw [correctedChenPanSum_eq_weightedPanRemainder N]
    exact hbound N hN hEven

/-- The counting-sieve `errSum` is bounded by the ant weighted Pan remainder:
the reusable ant seam `errSum_le_threeOmegaWeightedPanRemainder` at the
corrected Chen instance. -/
theorem correctedChenErrSum_le_weightedPanInput (N : ℕ) :
    (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      AnalyticNumberTheory.Sieve.weightedPanRemainder (correctedChenBoundingSieve N)
        (fun d => (3 : ℝ) ^ d.primeFactors.card) :=
  AnalyticNumberTheory.Sieve.errSum_le_threeOmegaWeightedPanRemainder

/-- Given the ant weighted Pan-BV input, the corrected sieve's `errSum` is
uniformly `O(N / log^A N)`: this closes the Chen `errSum` line on
[ant issue #7](https://github.com/UyNewNas/analytic-number-theory-lean/issues/7). -/
theorem correctedChenErrSum_uniform_of_weightedPanInput {A : ℝ} (hA : 0 < A)
    (N : ℕ) (hN : 1000 ≤ N) (hEven : Even N)
    (hinput : ChenWeightedPanInput) :
    ∃ C : ℝ, 0 < C ∧
      (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A := by
  rcases hinput A hA with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  exact le_trans (correctedChenErrSum_le_weightedPanInput N) (hbound N hN hEven)

/-- The corrected candidate count is at least the lower-sieve main term minus
the explicit `errSum`: the finite seam through which a uniform
Jurkat--Richert lower bound for `mainSum μ⁻` (with the closed `N / log N`
total mass) proves `CorrectedChenAnalyticPositivity`. -/
theorem correctedChenCandidates_card_ge_mainSum_sub_errSum (N : ℕ)
    (muMinus : ℕ → ℝ) (hmu : AnalyticNumberTheory.Sieve.IsLowerMoebius muMinus) :
    (correctedChenBoundingSieve N).totalMass *
        (correctedChenBoundingSieve N).mainSum muMinus -
      (correctedChenBoundingSieve N).errSum muMinus ≤
      (correctedChenCandidates N).card := by
  calc
    (correctedChenBoundingSieve N).totalMass *
          (correctedChenBoundingSieve N).mainSum muMinus -
        (correctedChenBoundingSieve N).errSum muMinus
        ≤ (correctedChenBoundingSieve N).siftedSum :=
          AnalyticNumberTheory.Sieve.mainSum_sub_errSum_le_siftedSum_of_lowerMoebius
            muMinus hmu
    _ = (correctedChenCandidates N).card :=
      correctedChenBoundingSieve_siftedSum_eq_card N

/-! ## 3.5 修正筛的基本引理级下界 (issue #5 的 chen 侧核心) -/

/-- 修正候选下界的核心观察: 普通 Möbius 函数就是下 Möbius 序列, 且等式成立.

`∑_{d | n} μ(d) = [n = 1]` (Möbius 反演, mathlib
`ArithmeticFunction.coe_zeta_mul_coe_moebius` + `coe_zeta_smul_apply`),
因此 `μ : ℕ → ℝ` 满足 `IsLowerMoebius`. -/
theorem moebius_real_isLowerMoebius :
    AnalyticNumberTheory.Sieve.IsLowerMoebius
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  intro n
  have hz : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) = (1 : ArithmeticFunction ℝ) := by
    simp
  have hzn : (ArithmeticFunction.zeta * ArithmeticFunction.moebius :
      ArithmeticFunction ℝ) n = (1 : ArithmeticFunction ℝ) n := by
    rw [hz]
  have hsum : (∑ i ∈ n.divisors,
      ((ArithmeticFunction.moebius i : ℤ) : ℝ)) =
      if n = 1 then (1 : ℝ) else 0 := by
    have hsmul : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) •
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
      rfl
    rw [hsmul, ArithmeticFunction.coe_zeta_smul_apply (R := ℝ)
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ))] at hzn
    rw [ArithmeticFunction.one_apply] at hzn
    exact hzn
  exact le_of_eq hsum

/-- |μ(d)| ≤ 1 (实值版本). -/
theorem abs_moebius_real_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

/-- 修正筛积 (chen 侧): V(N) = ∏_{p | 修正筛积} (1 - ν(p)), 其中
ν(p) = 1/(p-1). 与 ant 的 `sieveProductPrimeFactors` 相同; 在 ant PR #8
合并后可改为引用通用定义. -/
noncomputable def correctedChenSieveProduct (N : ℕ) : ℝ :=
  ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p)

/-- 普通 Möbius 的 Selberg 主项等于修正筛积 (精确恒等式).

`∑_{d | P} μ(d)·ν(d) = ∏_{p | P} (1 - ν(p))` — 乘法函数的"一减分解"
(mathlib `prodPrimeFactors_one_sub_of_squarefree`). 这是"JR 主项"在修正
候选上的精确形式: 主项就是 `V(N)`, 不需要任何筛函数渐近. -/
theorem mainSum_moebius_eq_correctedChenSieveProduct (N : ℕ) :
    (correctedChenBoundingSieve N).mainSum
        (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      correctedChenSieveProduct N := by
  rw [BoundingSieve.mainSum, correctedChenSieveProduct]
  change (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * correctedChenNu d) =
    ∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (1 - correctedChenNu p)
  rw [← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    correctedChenNu (AnalyticNumberTheory.Sieve.goldbachNu_isMultiplicative)
    (correctedChenSiftingProduct_squarefree N)]

/-- μ 的误差和被 1 系数误差和控制: |μ(d)| ≤ 1 ⇒ errSum(μ) ≤ errSum(1). -/
theorem correctedChenErrSum_moebius_le_errSum_one (N : ℕ) :
    (correctedChenBoundingSieve N).errSum
        (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)) ≤
      (correctedChenBoundingSieve N).errSum (fun _ => 1) := by
  unfold BoundingSieve.errSum
  apply Finset.sum_le_sum
  intro d hd
  have hmul : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
        |(correctedChenBoundingSieve N).rem d| ≤
      (1 : ℝ) * |(correctedChenBoundingSieve N).rem d| :=
    mul_le_mul_of_nonneg_right (abs_moebius_real_le_one d) (abs_nonneg _)
  simpa using hmul

/-- **修正候选的基本引理级下界 (chen 侧核心)**.

  `card(correctedChenCandidates N) ≥ X·V(N) − errSum(1)`

对**所有** `N` 无条件成立, 其中 `X = N/log N` 为总质量, `V(N)` 为修正
筛积, `errSum(1) = Σ_{d | P} |rem d|` 为显式除数误差和.

经典对应: 基本引理/线性筛下界 `S(A,z) ≥ X·V(z) − Σ_{d ≤ D} |R_d|`。
证明只用普通 Möbius 函数 (它本身就是精确的下 Möbius 序列), 因此主项是
精确的 `X·V(N)`, 不需要筛函数 `f(s)` 的任何渐近 —— 这正是修正候选定义
(只要求 `N-p` 无小于 `z` 的素因子) 与历史 W 候选 (多一个中区间素因子
条件) 的区别。剩下的解析输入只有:
  (1) `V(N)` 的 Mertens 型一致下界 (把主项放大到 `≫ N/log²N`);
  (2) `errSum(1)` 的加权 Pan 控制 (#7);
  (3) `correctedChenOmega` 的一致上界 (#6). -/
theorem correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum (N : ℕ) :
    (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N -
        (correctedChenBoundingSieve N).errSum (fun _ => 1) ≤
      (correctedChenCandidates N).card := by
  let mu : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
  have hseam := correctedChenCandidates_card_ge_mainSum_sub_errSum N mu
    moebius_real_isLowerMoebius
  have hmain : (correctedChenBoundingSieve N).mainSum mu = correctedChenSieveProduct N := by
    simpa [mu] using mainSum_moebius_eq_correctedChenSieveProduct N
  have herr : (correctedChenBoundingSieve N).errSum mu ≤
      (correctedChenBoundingSieve N).errSum (fun _ => 1) := by
    simpa [mu] using correctedChenErrSum_moebius_le_errSum_one N
  calc
    (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N -
        (correctedChenBoundingSieve N).errSum (fun _ => 1)
      ≤ (correctedChenBoundingSieve N).totalMass *
            (correctedChenBoundingSieve N).mainSum mu -
          (correctedChenBoundingSieve N).errSum mu := by
      rw [hmain]
      linarith
    _ ≤ (correctedChenCandidates N).card := hseam


/-- At a sieved prime `2 < p < z` with `p ∤ N`, the corrected Goldbach
density factor satisfies `(1 - ν(p))⁻¹ = (p-1)/(p-2)`. -/
theorem correctedChenNu_inv_prime {N p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    (1 - correctedChenNu p)⁻¹ = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime hp]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp [hpm1, hpm2]
  have hcancel : ((-2 : ℝ) + p) * ((-2 : ℝ) + p)⁻¹ = 1 := by
    convert mul_inv_cancel₀ hpm2 using 1
    ring
  ring_nf at hcancel ⊢
  exact hcancel

/-- At a sieved prime, the corrected density factor splits into the
Mertens-type `p/(p-1)` and the reciprocal singular-series local factor. -/
theorem correctedChenNu_inv_prime_localFactor {N p : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) (hpn : ¬ p ∣ N) :
    (1 - correctedChenNu p)⁻¹ =
      (p : ℝ) / (p - 1) * (AnalyticNumberTheory.Sieve.localFactor p N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hp hp2 hpn]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hrhs : (p : ℝ) / (p - 1) * ((p : ℝ) * (p - 2) / (p - 1) ^ 2)⁻¹ =
      (p - 1) / (p - 2) := by
    field_simp [hpm1, hpm2]
  rw [hrhs]
  exact correctedChenNu_inv_prime (N := N) hp hp2

/-- The corrected Selberg divisor sum splits into the Mertens-type prime
product over the sieved primes and the reciprocal of their singular-series
local-factor product.  This is the finite seam at which the exact Mertens
product formula and the singular series enter the main term. -/
theorem correctedChenSelbergSum_eq_mertens_mul_localFactor_inv (N : ℕ) :
    ∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d =
      (∏ p ∈ (correctedChenSiftingProduct N).primeFactors, (p : ℝ) / (p - 1)) *
      (∏ p ∈ (correctedChenSiftingProduct N).primeFactors,
          AnalyticNumberTheory.Sieve.localFactor p N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  rw [← Finset.prod_inv_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpcond := (prime_dvd_correctedChenSiftingProduct hp_prime).mp
    (Nat.dvd_of_mem_primeFactors hp)
  exact correctedChenNu_inv_prime_localFactor hp_prime hpcond.2.1 hpcond.2.2

/-! ## 4.6 主项渐近: Mertens 对接奇异级数 -/

/-- The corrected Selberg divisor sum factors as the product over the sieved
primes of `(1 - ν(p))⁻¹ = (p-1)/(p-2)`. -/
private theorem correctedChenSelbergSum_eq_prod_ratio (N : ℕ) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      ∏ p ∈ ((Finset.range (correctedChenZ N)).filter
        (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  simp only [correctedChenBoundingSieve]
  rw [correctedChenSiftingProduct_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpz, hpP, hp2, hpn⟩
  exact correctedChenNu_inv_prime (N := N) hpP hp2

/-- The Mertens-type factor `p/(p-1)` (real subtraction). -/
private noncomputable def mertensTypeFactor (p : ℕ) : ℝ :=
  (p : ℝ) / ((p : ℝ) - 1)

/-- Partition of the primes `< z` into `p = 2`, `2 < p ∧ p | N`, and
`2 < p ∧ ¬ p | N`. -/
private theorem sievedPrimePartition (N : ℕ) :
    ((Finset.range (correctedChenZ N)).filter Nat.Prime) =
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  ext p
  simp only [mem_filter, mem_union, mem_range]
  constructor
  · intro hp
    rcases hp with ⟨hpz, hpp⟩
    rcases eq_or_lt_of_le hpp.two_le with hpeq | hplt
    · exact Or.inl (Or.inl ⟨hpz, hpp, hpeq.symm⟩)
    · by_cases hpd : p ∣ N
      · exact Or.inl (Or.inr ⟨hpz, hpp, hplt, hpd⟩)
      · exact Or.inr ⟨hpz, hpp, hplt, hpd⟩
  · intro hp
    rcases hp with hpA | hpBC
    · rcases hpA with ⟨hpz, hpp, _⟩ | ⟨hpz, hpp, _, _⟩ <;> exact ⟨hpz, hpp⟩
    · rcases hpBC with ⟨hpz, hpp, _, _⟩
      exact ⟨hpz, hpp⟩

/-- The `p = 2` slice and the `p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_a_b (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, hpeq⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
  omega

/-- The `p = 2` slice and the `¬ p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_a_c (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, hpeq⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
  omega

/-- The `p | N` slice and the `¬ p | N` slice are disjoint. -/
private theorem sievedPrimeDisjoint_b_c (N : ℕ) :
    Disjoint ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_filter.mp hp1 with ⟨_, _, _, hpd⟩
  rcases Finset.mem_filter.mp hp2 with ⟨_, _, _, hpn⟩
  exact hpn hpd

/-- The union of the first two slices is disjoint from the `¬ p | N` slice. -/
private theorem sievedPrimeDisjoint_ab_c (N : ℕ) :
    Disjoint (((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ p = 2)) ∪
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)))
      ((Finset.range (correctedChenZ N)).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rcases Finset.mem_union.mp hp1 with hpa | hpb
  · rcases Finset.mem_filter.mp hpa with ⟨_, _, hpeq⟩
    rcases Finset.mem_filter.mp hp2 with ⟨_, _, hplt, _⟩
    omega
  · rcases Finset.mem_filter.mp hpb with ⟨_, _, _, hpd⟩
    rcases Finset.mem_filter.mp hp2 with ⟨_, _, _, hpn⟩
    exact hpn hpd

/-- Local factor at `p = 2` equals `p/(p-1)` for even `N`. -/
private theorem localFactor_eq_mertensTypeFactor_p2 (N : ℕ) (hN : Even N) :
    AnalyticNumberTheory.Sieve.localFactor 2 N = mertensTypeFactor 2 := by
  rw [AnalyticNumberTheory.Sieve.localFactor_two hN]
  norm_num [mertensTypeFactor]

/-- Local factor at a dividing odd prime equals `p/(p-1)`. -/
private theorem localFactor_eq_mertensTypeFactor_dvd {N p : ℕ} (hp : p.Prime)
    (hlt : 2 < p) (hpd : p ∣ N) :
    AnalyticNumberTheory.Sieve.localFactor p N = mertensTypeFactor p := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_dvd hp hlt hpd]
  rfl

/-- At a non-dividing odd prime, `(p-1)/(p-2)` times the local factor equals
`p/(p-1)`. -/
private theorem localFactor_ratio_not_dvd {N p : ℕ} (hp : p.Prime) (hlt : 2 < p)
    (hpn : ¬ p ∣ N) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N =
      mertensTypeFactor p := by
  rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hp hlt hpn]
  have hp1 : (2 : ℝ) < p := by exact_mod_cast hlt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  unfold mertensTypeFactor
  field_simp [hpm1, hpm2]

/-- The corrected Selberg divisor sum times the truncated singular series at
`z - 1` is exactly the full Mertens-type prime product `∏_{p<z} p/(p-1)`.
This is the exact seam that restores the excluded `p = 2` and `p | N` local
factors back into `singularSeriesTruncated`. -/
private theorem correctedChenSelbergSum_mul_singularSeries_eq_mertensProd
    (N : ℕ) (hN : Even N) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      ∏ p ∈ ((Finset.range (correctedChenZ N)).filter Nat.Prime), mertensTypeFactor p := by
  let z := correctedChenZ N
  let R : Finset ℕ := (Finset.range z).filter Nat.Prime
  let A : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ p = 2)
  let B : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ p ∣ N)
  let C : Finset ℕ := (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ ¬ p ∣ N)
  have hz : 1 ≤ correctedChenZ N := by
    unfold correctedChenZ
    omega
  have hrange : (Finset.range ((correctedChenZ N - 1) + 1)).filter Nat.Prime =
      (Finset.range (correctedChenZ N)).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz]
  have hR : R = A ∪ B ∪ C := by
    dsimp [R, A, B, C, z]
    exact sievedPrimePartition N
  have hS : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      ∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    dsimp [C, z]
    exact correctedChenSelbergSum_eq_prod_ratio N
  have hSplit : (∏ p ∈ R, AnalyticNumberTheory.Sieve.localFactor p N) =
      (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
      (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
      (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N) := by
    rw [hR]
    rw [Finset.prod_union (sievedPrimeDisjoint_ab_c N)]
    rw [Finset.prod_union (sievedPrimeDisjoint_a_b N)]
  have h𝔖 : AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      ∏ p ∈ R, AnalyticNumberTheory.Sieve.localFactor p N := by
    simp [AnalyticNumberTheory.Sieve.singularSeriesTruncated, R, z, hrange]
  have hSplitMf : (∏ p ∈ R, mertensTypeFactor p) =
      (∏ p ∈ A, mertensTypeFactor p) * (∏ p ∈ B, mertensTypeFactor p) *
      (∏ p ∈ C, mertensTypeFactor p) := by
    rw [hR]
    rw [Finset.prod_union (sievedPrimeDisjoint_ab_c N)]
    rw [Finset.prod_union (sievedPrimeDisjoint_a_b N)]
  have hA : (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) = (∏ p ∈ A, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, _, hpeq⟩
    subst p
    exact localFactor_eq_mertensTypeFactor_p2 N hN
  have hB : (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) = (∏ p ∈ B, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpP, hlt, hpd⟩
    exact localFactor_eq_mertensTypeFactor_dvd hpP hlt hpd
  have hC : (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N) =
      (∏ p ∈ C, mertensTypeFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hpP, hlt, hpn⟩
    exact localFactor_ratio_not_dvd hpP hlt hpn
  calc
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1)
        = (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
          (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
          (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N) := by
          rw [hS, h𝔖, hSplit]
          ring
    _ = (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
        ((∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
          (∏ p ∈ C, AnalyticNumberTheory.Sieve.localFactor p N)) := by ring
    _ = (∏ p ∈ A, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ B, AnalyticNumberTheory.Sieve.localFactor p N) *
        (∏ p ∈ C, ((p : ℝ) - 1) / ((p : ℝ) - 2) * AnalyticNumberTheory.Sieve.localFactor p N) := by
        rw [← Finset.prod_mul_distrib]
    _ = (∏ p ∈ A, mertensTypeFactor p) * (∏ p ∈ B, mertensTypeFactor p) *
        (∏ p ∈ C, mertensTypeFactor p) := by
        rw [hA, hB, hC]
    _ = ∏ p ∈ R, mertensTypeFactor p := by
        rw [← hSplitMf]

/-- The full Mertens-type product `∏_{p<z} p/(p-1)` equals the reciprocal of
the exact Mertens `primeProduct (z - 1)`. -/
private theorem mertensProd_eq_primeProduct_inv (N : ℕ) :
    (∏ p ∈ ((Finset.range (correctedChenZ N)).filter Nat.Prime), mertensTypeFactor p) =
      (MertensTheorem.primeProduct (correctedChenZ N - 1))⁻¹ := by
  have hz : 1 ≤ correctedChenZ N := by
    unfold correctedChenZ
    omega
  have hrange : (Finset.range ((correctedChenZ N - 1) + 1)).filter Nat.Prime =
      (Finset.range (correctedChenZ N)).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz]
  unfold mertensTypeFactor MertensTheorem.primeProduct
  rw [hrange]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP : p.Prime := (Finset.mem_filter.mp hp).2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpP.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    linarith
  field_simp [hp0, hp1]

/-- **主项恒等式 (Mertens 对接奇异级数)**: the corrected Selberg divisor sum
times the truncated singular series at `z - 1` equals the reciprocal of the
exact Mertens `primeProduct (z - 1)`.

This is the exact seam at which the main term connects the Mertens product
formula to the singular series: it restores the excluded `p = 2` and `p | N`
local factors (back into `singularSeriesTruncated`) and reduces the sieved
Selberg product to the full Mertens-type prime product `∏_{p<z} p/(p-1)`. -/
theorem correctedChenSelbergSum_mul_singularSeriesTruncated (N : ℕ) (hN : Even N) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) *
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) =
      (MertensTheorem.primeProduct (correctedChenZ N - 1))⁻¹ := by
  rw [correctedChenSelbergSum_mul_singularSeries_eq_mertensProd N hN]
  exact mertensProd_eq_primeProduct_inv N

/-! ## 4.7 主项下界: 奇异级数连接与一致主项 (issue #5 的解析核心) -/

/-- Mertens 素数乘积为正: `∏_{p ≤ x}(1 - 1/p) > 0`. -/
theorem primeProduct_pos (x : ℕ) : 0 < MertensTheorem.primeProduct x := by
  unfold MertensTheorem.primeProduct
  exact Finset.prod_pos (fun p hp => by
    have hpP : p.Prime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    have hle : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have hlt1 : 1 / (p : ℝ) < 1 := (div_lt_iff₀ hp0).mpr (by simpa using hle)
    linarith)

/-- `selbergSum = 1 / V(N)`: Selberg 除数和的"一减分解"取倒数. -/
theorem correctedChenSelbergSum_eq_sieveProduct_inv (N : ℕ) :
    (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
      (correctedChenBoundingSieve N).selbergTerms d) =
      (correctedChenSieveProduct N)⁻¹ := by
  rw [AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv]
  change (∏ p ∈ (correctedChenSiftingProduct N).primeFactors,
      (1 - correctedChenNu p)⁻¹) = (correctedChenSieveProduct N)⁻¹
  rw [correctedChenSieveProduct]
  rw [← Finset.prod_inv_distrib]

/-- **主项恒等式 (奇异级数连接)**: 修正筛积等于截断奇异级数乘以精确
Mertens 积:

  V(N) = 𝔖_trunc(N, z-1) · primeProduct(z-1)

这是把 `X·V(N)` 变成 `X·𝔖·primeProduct(z-1)` 型主项的精确接缝: 由
`correctedChenSelbergSum_mul_singularSeriesTruncated`
(`selbergSum·𝔖 = primeProduct⁻¹`) 与 `selbergSum = V⁻¹` 取倒数即得. -/
theorem correctedChenSieveProduct_eq_singularSeries_mul_primeProduct (N : ℕ) (hN : Even N) :
    correctedChenSieveProduct N =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
  have h1 := correctedChenSelbergSum_mul_singularSeriesTruncated N hN
  have hsel := correctedChenSelbergSum_eq_sieveProduct_inv N
  rw [hsel] at h1
  have hVnz : correctedChenSieveProduct N ≠ 0 := by
    unfold correctedChenSieveProduct
    exact ne_of_gt (Finset.prod_pos (fun p hp => by
      have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpcond := (prime_dvd_correctedChenSiftingProduct hpP).mp
        (Nat.dvd_of_mem_primeFactors hp)
      have hlt : correctedChenNu p < 1 :=
        AnalyticNumberTheory.Sieve.goldbachNu_lt_one_of_prime hpP hpcond.2.1
      linarith))
  have h𝔖nz : AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) ≠ 0 := by
    apply ne_of_gt
    apply AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos
    unfold correctedChenZ
    have hmax : 2 ≤ max 2 (Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))) := le_max_left _ _
    omega
  have hppnz : MertensTheorem.primeProduct (correctedChenZ N - 1) ≠ 0 :=
    ne_of_gt (primeProduct_pos (correctedChenZ N - 1))
  have h3 : (correctedChenSieveProduct N)⁻¹ =
      (MertensTheorem.primeProduct (correctedChenZ N - 1) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹ := by
    have h := congrArg (fun t : ℝ =>
        t * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹) h1
    rw [mul_assoc, mul_inv_cancel₀ h𝔖nz, mul_one] at h
    -- h : V⁻¹ = primeProduct⁻¹ * 𝔖⁻¹ ; 目标: V⁻¹ = (primeProduct * 𝔖)⁻¹
    rw [mul_inv]
    ring_nf
    exact h
  calc
    correctedChenSieveProduct N
        = ((correctedChenSieveProduct N)⁻¹)⁻¹ := by simp
    _ = (MertensTheorem.primeProduct (correctedChenZ N - 1) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))⁻¹⁻¹ := by
          rw [h3]
    _ = MertensTheorem.primeProduct (correctedChenZ N - 1) *
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
          simp
    _ = AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
          ring

/-- **一致主项下界 (chen 侧)**: 存在 `c > 0` 与阈值 `N₀`, 使得对所有
`N ≥ N₀` 的偶数 `N`, `X·V(N) ≥ c·N/log²N`.

量词顺序: `c`、`N₀` 先于 `∀ N` (一致版本, 常数不得依赖 `N`). 由
`correctedChenMainTerm_lower_of_estimates` 从三个标准解析输入推出:
(1) `𝔖_trunc` 的一致下界; (2) `primeProduct` 的 Mertens 下界;
(3) `log(z-1) ≤ C·log N` 的参数估计. -/
def CorrectedChenMainTermLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      c * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
        (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N

/-- **主项下界 (逐点组装)**: 给定 (1) 截断奇异级数下界 `c𝔖 ≤ 𝔖_trunc`,
(2) Mertens 下界 `cpp/log(z-1) ≤ primeProduct(z-1)`, (3) 参数估计
`log(z-1) ≤ Clog·log N`, 则

  `c𝔖·cpp/Clog · N/log²N ≤ X·V(N)`.

证明只用 `V = 𝔖_trunc·primeProduct(z-1)` 精确恒等式与正性/倒数算术. -/
theorem correctedChenMainTerm_lower_of_estimates (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N)
    (hz : 2 ≤ correctedChenZ N - 1)
    {c𝔖 cpp Clog : ℝ} (hc𝔖 : 0 < c𝔖) (hcpp : 0 < cpp) (hClog : 0 < Clog)
    (h𝔖 : c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1))
    (hpp : cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤
      MertensTheorem.primeProduct (correctedChenZ N - 1))
    (hlog : log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ Clog * log (N : ℝ)) :
    c𝔖 * cpp / Clog * (N : ℝ) / (log (N : ℝ)) ^ 2 ≤
      (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
  have hV : correctedChenSieveProduct N =
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) :=
    correctedChenSieveProduct_eq_singularSeries_mul_primeProduct N hN
  have hlogN : 0 < log (N : ℝ) := by
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact Real.log_pos this
  have hlogz : 0 < log ((correctedChenZ N - 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) < (correctedChenZ N - 1 : ℕ) := by exact_mod_cast (by omega : 1 < correctedChenZ N - 1)
    exact Real.log_pos this
  have h𝔖pos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N (correctedChenZ N - 1) (by omega)
  have hX : (correctedChenBoundingSieve N).totalMass = (N : ℝ) / log (N : ℝ) := rfl
  have h𝔖pp : c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) ≤
      AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
        MertensTheorem.primeProduct (correctedChenZ N - 1) := by
    exact mul_le_mul h𝔖 hpp (le_of_lt (div_pos hcpp hlogz)) (le_of_lt h𝔖pos)
  have hle : c𝔖 * cpp / (Clog * log (N : ℝ)) ≤
      c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) := by
    have hone : (Clog * log (N : ℝ))⁻¹ ≤ (log ((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹ :=
      (inv_le_inv₀ (mul_pos hClog hlogN) hlogz).mpr hlog
    have hnonneg : 0 ≤ c𝔖 * cpp := mul_nonneg (le_of_lt hc𝔖) (le_of_lt hcpp)
    calc
      c𝔖 * cpp / (Clog * log (N : ℝ)) =
          c𝔖 * cpp * (Clog * log (N : ℝ))⁻¹ := by
            field_simp [ne_of_gt (mul_pos hClog hlogN)]
      _ ≤ c𝔖 * cpp * (log ((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹ := by
            exact mul_le_mul_of_nonneg_left hone hnonneg
      _ = c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ)) := by
            field_simp [hlogz.ne']
  calc
    c𝔖 * cpp / Clog * (N : ℝ) / (log (N : ℝ)) ^ 2
        = (N : ℝ) / log (N : ℝ) * (c𝔖 * cpp / (Clog * log (N : ℝ))) := by
          field_simp [hlogN.ne']
    _ ≤ (N : ℝ) / log (N : ℝ) * (c𝔖 * (cpp / log ((correctedChenZ N - 1 : ℕ) : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hle (div_nonneg (by positivity) (le_of_lt hlogN))
    _ ≤ (correctedChenBoundingSieve N).totalMass *
          (AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) *
            MertensTheorem.primeProduct (correctedChenZ N - 1)) := by
          rw [hX]
          exact mul_le_mul_of_nonneg_left h𝔖pp (div_nonneg (by positivity) (le_of_lt hlogN))
    _ = (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N := by
          rw [hV]

/-- 三个一致解析输入打包成 `CorrectedChenMainTermLower`:
(1) `𝔖_trunc` 一致下界; (2) `primeProduct` 的 Mertens 一致下界;
(3) `log(z-1) ≤ Clog·log N` 参数估计; 外加 (4) 参数条件
(`2 ≤ N`、`2 ≤ z-1`、`M₀ ≤ z-1`). -/
theorem CorrectedChenMainTermLower_of_uniform_estimates
    {c𝔖 cpp Clog : ℝ} {M₀ N₀'' : ℕ}
    (hc𝔖 : 0 < c𝔖) (hcpp : 0 < cpp) (hClog : 0 < Clog)
    (h𝔖 : ∀ N : ℕ, ∀ z : ℕ, 2 ≤ z →
      c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z)
    (hpp : ∀ m : ℕ, M₀ ≤ m → 2 ≤ m →
      cpp / log (m : ℝ) ≤ MertensTheorem.primeProduct m)
    (hlog : ∀ N : ℕ, 2 ≤ N →
      log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ Clog * log (N : ℝ))
    (hparams : ∀ N : ℕ, N₀'' ≤ N →
      2 ≤ N ∧ 2 ≤ correctedChenZ N - 1 ∧ M₀ ≤ correctedChenZ N - 1) :
    CorrectedChenMainTermLower := by
  refine ⟨c𝔖 * cpp / Clog, ?_, ⟨N₀'', ?_⟩⟩
  · positivity
  · intro N hN hEven
    rcases hparams N hN with ⟨hN2, hz, hM⟩
    exact correctedChenMainTerm_lower_of_estimates N hEven hN2 hz hc𝔖 hcpp hClog
      (h𝔖 N (correctedChenZ N - 1) hz)
      (hpp (correctedChenZ N - 1) hM hz)
      (hlog N hN2)

/-! ## 4.8 参数估计与 Mertens/奇异级数接线 -/

/-- 参数估计 1: 修正筛水平满足 `z - 1 ≤ N` (实数). -/
theorem correctedChenZ_sub_one_le_N {N : ℕ} (hN : 1 ≤ N) :
    ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ N := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
  by_cases hf : 2 ≤ Nat.floor x
  · have hz : correctedChenZ N = Nat.floor x := by
      unfold correctedChenZ
      exact max_eq_right hf
    have hxle : x ≤ (N : ℝ) := by
      have hx1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      have hpow := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 10 : ℝ) ≤ 1)
      -- hpow : N^(1/10) ≤ N^1
      simpa [x] using hpow
    calc
      ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ (correctedChenZ N : ℝ) := by
        exact_mod_cast (Nat.sub_le (correctedChenZ N) 1)
      _ = (Nat.floor x : ℝ) := by rw [hz]
      _ ≤ x := Nat.floor_le hx0
      _ ≤ (N : ℝ) := hxle
  · have hz : correctedChenZ N = 2 := by
      unfold correctedChenZ
      change max 2 (Nat.floor x) = 2
      exact max_eq_left (by omega)
    rw [hz]
    norm_num
    exact_mod_cast hN

/-- 参数估计 2: 对 `N ≥ 3^10 = 59049`, 修正筛水平满足 `2 ≤ z - 1`. -/
theorem correctedChenZ_sub_one_ge_two_of_large {N : ℕ} (hN : 59049 ≤ N) :
    2 ≤ correctedChenZ N - 1 := by
  let x : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  have h3le : (3 : ℝ) ≤ x := by
    dsimp [x]
    -- 3 = (3^10)^(1/10) ≤ N^(1/10)
    have h310 : (3 : ℝ) ^ (10 : ℝ) ≤ (N : ℝ) := by
      have hnat : (3 : ℝ) ^ 10 ≤ (N : ℝ) := by
        norm_num at hN ⊢
        exact_mod_cast hN
      simpa [Real.rpow_natCast] using hnat
    have hstep := Real.rpow_le_rpow (by positivity : 0 ≤ (3 : ℝ) ^ (10 : ℝ)) h310
      (by norm_num : 0 ≤ (1 / 10 : ℝ))
    -- hstep : ((3:ℝ)^(10:ℝ))^(1/10:ℝ) ≤ x ; LHS 化简为 3
    have hrew : ((3 : ℝ) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) = (3 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
      norm_num
    rwa [hrew] at hstep
  have hfloor : 3 ≤ Nat.floor x := Nat.le_floor h3le
  have hz : correctedChenZ N = Nat.floor x := by
    unfold correctedChenZ
    change max 2 (Nat.floor x) = Nat.floor x
    exact max_eq_right (le_trans (by norm_num : (2 : ℕ) ≤ 3) hfloor)
  rw [hz]
  omega

/-- 参数估计 3: `log(z - 1) ≤ log N` (即 `Clog = 1` 的参数估计). -/
theorem correctedChenZ_log_le_logN {N : ℕ} (hN : 2 ≤ N) :
    log ((correctedChenZ N - 1 : ℕ) : ℝ) ≤ log (N : ℝ) := by
  have hle := correctedChenZ_sub_one_le_N (by omega : 1 ≤ N)
  have hpos : 0 < (correctedChenZ N - 1 : ℕ) := by
    have hz2 : 2 ≤ correctedChenZ N := by
      unfold correctedChenZ
      exact le_max_left _ _
    omega
  exact Real.log_le_log (by exact_mod_cast hpos) hle

/-- 一致主项下界由两个标准输入推出: (1) `𝔖_trunc` 的一致下界 `h𝔖`
(C₂ 级, 待证), (2) Mertens 积的 `primeProduct_asymptotic_order` (已证)
加参数估计 (已证). 剩余唯一解析输入是 `h𝔖`. -/
theorem CorrectedChenMainTermLower_of_singularSeries_bound
    {c𝔖 : ℝ} (hc𝔖 : 0 < c𝔖)
    (h𝔖 : ∀ N : ℕ, ∀ z : ℕ, 2 ≤ z →
      c𝔖 ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z) :
    CorrectedChenMainTermLower := by
  obtain ⟨c₁₀, c₂₀, hc₁₀, hPP⟩ := MertensTheorem.primeProduct_asymptotic_order
  exact CorrectedChenMainTermLower_of_uniform_estimates
    (c𝔖 := c𝔖) (cpp := c₁₀) (Clog := 1) (M₀ := 2) (N₀'' := 59049)
    hc𝔖 hc₁₀ (by norm_num)
    h𝔖
    (fun m _hm h2 => (hPP m h2).1)
    (fun N hN => by
      have hlog := correctedChenZ_log_le_logN hN
      simpa using hlog)
    (fun N hN => by
      refine ⟨by omega, ?_, ?_⟩
      · exact correctedChenZ_sub_one_ge_two_of_large hN
      · exact correctedChenZ_sub_one_ge_two_of_large hN)

/-- **截断奇异级数的一致下界** (issue #5 的最后一个解析输入).

对任意 `N` 与 `z ≥ 2`: `1/2 ≤ 𝔖_trunc(N, z)`. 经典证明 (孪生素数常数
`C₂ ≈ 0.66` 级):

  𝔖_trunc(N,z) ≥ ∏_{2<p≤z}(1 − 1/(p−1)²) ≥ 1 − Σ_{p>2} 1/(p−1)²
                  ≥ 1 − (1/4)·Σ_{k≥1} 1/k² ≥ 1/2,

其中第二步行由 `∏(1−x_i) ≥ 1−Σx_i`, 第三行用 `p−1` 为偶数的子集包含
(素数 > 2 均为奇数), 最后一行用望远镜求和 `Σ_{k≥1}1/k² ≤ 2`. 该命题
的证明 = 纯有限组合/实数引理, 已精确陈述; 由它经
`CorrectedChenMainTermLower_of_singularSeries_lower` 直接闭合主项下界. -/
def SingularSeriesTruncatedLowerBound : Prop :=
  ∀ N z : ℕ, 2 ≤ z → (1 / 2 : ℝ) ≤
    AnalyticNumberTheory.Sieve.singularSeriesTruncated N z

/-- 截断奇异级数一致下界 (取 `c𝔖 = 1/2`) 推出 `CorrectedChenMainTermLower`. -/
theorem CorrectedChenMainTermLower_of_singularSeries_lower
    (h𝔖 : SingularSeriesTruncatedLowerBound) :
    CorrectedChenMainTermLower := by
  exact CorrectedChenMainTermLower_of_singularSeries_bound (c𝔖 := 1 / 2) (by norm_num)
    (fun N z hz => h𝔖 N z hz)

/-! ## 4.9 截断奇异级数一致下界 (sub-issue #3 的解析核心)

以下引理是通用解析事实 (与具体筛问题无关), 按边界规则应迁入
`analytic-number-theory-lean` 的 `AnalyticNumberTheory/Sieve/SingularSeries.lean`;
在 ant PR #8 合并前先在本文件证明 (迁移注记). -/

/-- 有限集合上 `∏(1 - x_i) ≥ 1 - Σ x_i` (0 ≤ x_i ≤ 1). -/
theorem prod_one_sub_ge_one_sub_sum {s : Finset ℕ} {x : ℕ → ℝ}
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hx0s : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
      have hx1s : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
      have hx0a : 0 ≤ x a := hx0 a (by simp)
      have hx1a : x a ≤ 1 := hx1 a (by simp)
      have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx0s
      rw [Finset.sum_insert ha]
      calc
        1 - (x a + ∑ i ∈ s, x i) ≤ (1 - x a) * (1 - ∑ i ∈ s, x i) := by
          nlinarith [mul_nonneg hx0a hS]
        _ ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) := by
          exact mul_le_mul_of_nonneg_left (ih hx0s hx1s) (sub_nonneg.mpr hx1a)
        _ = ∏ i ∈ insert a s, (1 - x i) := by
          rw [Finset.prod_insert ha]

/-- `Σ_{p 素数, 2 < p ≤ z} 1/(p−1)² ≤ 1/2`.

素数 > 2 均为奇数, 故 `p−1 = 2k` 为偶数; 经注入 `p ↦ (p−1)/2` 化到
`Σ_{k} 1/(2k)² = (1/4)Σ_k 1/k²`, 再用望远镜求和
`Σ_{k≥1} 1/k² ≤ 1 + Σ_{k≥2} 1/((k−1)k) ≤ 2`. -/
theorem sum_sq_recip_primes_ge_three_le_half (z : ℕ) :
    (∑ p ∈ (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p),
      1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤ (1 / 2 : ℝ) := by
  let S : Finset ℕ := (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)
  have hinj : Set.InjOn (fun p : ℕ => (p - 1) / 2) ↑S := by
    intro a ha b hb hab
    rcases Finset.mem_filter.mp ha with ⟨ha1, ha2⟩
    rcases Finset.mem_filter.mp hb with ⟨hb1, hb2⟩
    have hodd_a : Odd a := ha2.1.odd_of_ne_two (by omega : a ≠ 2)
    have hodd_b : Odd b := hb2.1.odd_of_ne_two (by omega : b ≠ 2)
    rcases hodd_a with ⟨ka, hka⟩
    rcases hodd_b with ⟨kb, hkb⟩
    have ha' : a - 1 = 2 * ka := by omega
    have hb' : b - 1 = 2 * kb := by omega
    have hka' : (a - 1) / 2 = ka := by
      rw [ha']
      exact Nat.mul_div_right ka (by norm_num : 0 < 2)
    have hkb' : (b - 1) / 2 = kb := by
      rw [hb']
      exact Nat.mul_div_right kb (by norm_num : 0 < 2)
    change (a - 1) / 2 = (b - 1) / 2 at hab
    have hk : ka = kb := by rwa [hka', hkb'] at hab
    omega
  have himg := Finset.sum_image (f := fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2)
    (g := fun p : ℕ => (p - 1) / 2) (s := S) hinj
  have hcong : (∑ p ∈ S, 1 / ((2 * ((p - 1) / 2) : ℕ) : ℝ) ^ 2) =
      ∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
    have hodd : Odd p := hp2.1.odd_of_ne_two (by omega : p ≠ 2)
    rcases hodd with ⟨k, hk⟩
    have hsub : p - 1 = 2 * k := by omega
    have hdiv : 2 ∣ p - 1 := ⟨k, by rw [hsub]⟩
    have hmul : (p - 1) / 2 * 2 = p - 1 := Nat.div_mul_cancel hdiv
    rw [show (2 * ((p - 1) / 2) : ℕ) = p - 1 by rw [mul_comm, hmul]]
  have hsubset : S.image (fun p : ℕ => (p - 1) / 2) ⊆ Finset.range (z + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
    rw [Finset.mem_range]
    have hple : p ≤ z := by
      rcases Finset.mem_range.mp hp1 with h
      omega
    omega
  have hle1 : (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤
      ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
    calc
      (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
          = ∑ k ∈ S.image (fun p : ℕ => (p - 1) / 2), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
            rw [← hcong]
            exact himg.symm
      _ ≤ ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (fun k hk hknot => by positivity)
  have hfour : (∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have h2k : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
    rw [h2k]
    field_simp
    ring
  have htel : (∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) ≤ 1 := by
    have h := Finset.sum_range_sub' (f := fun i : ℕ => 1 / ((i : ℝ) + 1)) (n := z)
    -- h : Σ_{i ∈ range z} (1/((i:ℝ)+1) − 1/((i:ℝ)+2)) = 1 − 1/((z:ℝ)+1)
    have hrew : (∑ i ∈ Finset.range z,
        1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) =
        ∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
      have h2 : ((i + 2 : ℕ) : ℝ) = (i : ℝ) + 2 := by norm_num
      rw [h1, h2]
      field_simp
      ring
    rw [hrew]
    have hval : (∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) =
        ∑ i ∈ Finset.range z, (1 / ((i : ℝ) + 1) - 1 / (((i + 1 : ℕ) : ℝ) + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [hval, h]
    have hc : 1 / ((0 : ℝ) + 1) = 1 := by norm_num
    have hpos : 0 ≤ 1 / ((z : ℝ) + 1) := by positivity
    linarith
  -- 平方倒数上界: Σ_{k=0}^{z} 1/k² ≤ 2
  have hsq : (∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2) ≤ 2 := by
    let A : Finset ℕ := (Finset.range (z + 1)).filter (fun k => k ≤ 1)
    let B : Finset ℕ := (Finset.range (z + 1)).filter (fun k => 2 ≤ k)
    have hpart : A ∪ B = Finset.range (z + 1) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, A, B]
      omega
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro k hk1 hk2
      omega
    have hA : (∑ k ∈ A, 1 / (k : ℝ) ^ 2) ≤ 1 := by
      have hsub : A ⊆ ({0, 1} : Finset ℕ) := by
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      calc
        (∑ k ∈ A, 1 / (k : ℝ) ^ 2) ≤ ∑ k ∈ ({0, 1} : Finset ℕ), 1 / (k : ℝ) ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hknot => by positivity)
        _ = 1 := by norm_num
    have hB : (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤
        ∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
      have hle : (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤
          ∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        have hpos1 : 0 < ((k - 1 : ℕ) : ℝ) := by
          have hkm1 : (1 : ℕ) ≤ k - 1 := by omega
          exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hkm1)
        have hpos2 : 0 < (k : ℝ) := by
          have : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
          linarith
        have hleprod : ((k - 1 : ℕ) : ℝ) * (k : ℝ) ≤ (k : ℝ) ^ 2 := by
          have hsub : (k - 1 : ℕ) ≤ k := Nat.sub_le _ _
          nlinarith [show ((k - 1 : ℕ) : ℝ) ≤ k by exact_mod_cast hsub]
        exact one_div_le_one_div_of_le (mul_pos hpos1 hpos2) hleprod
      have hinj2 : Set.InjOn (fun k : ℕ => k - 2) ↑B := by
        intro a ha b hb hab
        change a ∈ B at ha
        rcases Finset.mem_filter.mp ha with ⟨_, ha2⟩
        change b ∈ B at hb
        rcases Finset.mem_filter.mp hb with ⟨_, hb2⟩
        have ha' : a = (a - 2) + 2 := by omega
        have hb' : b = (b - 2) + 2 := by omega
        change a - 2 = b - 2 at hab
        rw [ha', hb', hab]
      have himg2 := Finset.sum_image
        (f := fun i : ℕ => 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)))
        (g := fun k : ℕ => k - 2) (s := B) hinj2
      have hcong2 : (∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ))) =
          ∑ i ∈ B.image (fun k : ℕ => k - 2),
            1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
        rw [himg2]
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_filter.mp hk).2
        have hshift : (k - 2 : ℕ) + 1 = k - 1 := by omega
        have hshift2 : (k - 2 : ℕ) + 2 = k := by omega
        rw [hshift, hshift2]
      have hsub2 : B.image (fun k : ℕ => k - 2) ⊆ Finset.range z := by
        intro i hi
        rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
        rw [Finset.mem_range]
        rcases Finset.mem_filter.mp hk with ⟨hk1, hk2⟩
        rcases Finset.mem_range.mp hk1 with h
        omega
      calc
        (∑ k ∈ B, 1 / (k : ℝ) ^ 2) ≤ ∑ k ∈ B, 1 / (((k - 1 : ℕ) : ℝ) * (k : ℝ)) := hle
        _ = ∑ i ∈ B.image (fun k : ℕ => k - 2),
            1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := hcong2
        _ ≤ ∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ)) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun i hi hnot => by positivity)
    calc
      (∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2)
          = (∑ k ∈ A, 1 / (k : ℝ) ^ 2) + (∑ k ∈ B, 1 / (k : ℝ) ^ 2) := by
            rw [← hpart, Finset.sum_union hdisj]
      _ ≤ 1 + (∑ i ∈ Finset.range z, 1 / (((i + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ))) := by
            exact add_le_add hA hB
      _ ≤ 1 + 1 := by
            exact add_le_add (le_refl (1 : ℝ)) htel
      _ = 2 := by norm_num
  calc
    (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
        ≤ (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := by
          calc
            (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2)
                ≤ ∑ k ∈ Finset.range (z + 1), 1 / ((2 * k : ℕ) : ℝ) ^ 2 := hle1
            _ = (1 / 4 : ℝ) * ∑ k ∈ Finset.range (z + 1), 1 / (k : ℝ) ^ 2 := hfour
    _ ≤ (1 / 4 : ℝ) * 2 := by
          exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 / 2 := by norm_num

/-- **截断奇异级数一致下界**: 对任意 `N` 与 `z ≥ 2`, `1/2 ≤ 𝔖_trunc(N, z)`.

经典路线 (孪生素数常数 `C₂` 级): 局部因子按 `p=2`、`p|N`、`p∤N` 分类,
`𝔖_trunc ≥ ∏_{2<p≤z}(1 − 1/(p−1)²)`, 再由
`∏(1−x_i) ≥ 1−Σx_i` 与 `Σ_{p>2}1/(p−1)² ≤ 1/2` 得到下界. -/
theorem singularSeriesTruncated_ge_half {N z : ℕ} (hz : 2 ≤ z) :
    (1 / 2 : ℝ) ≤ AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := by
  let S : Finset ℕ := (Finset.range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)
  have hsplit : (Finset.range (z + 1)).filter Nat.Prime = insert 2 S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, S]
    constructor
    · intro hp
      rcases hp with ⟨hpz, hpp⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨hpz, hpp, lt_of_le_of_ne hpp.two_le (Ne.symm hp2)⟩
    · intro hp
      rcases hp with hpeq | hpS
      · subst p
        exact ⟨by omega, Nat.prime_two⟩
      · rcases hpS with ⟨hpz, hpp, hp2⟩
        exact ⟨hpz, hpp⟩
  have hlf2 : (1 : ℝ) ≤ AnalyticNumberTheory.Sieve.localFactor 2 N := by
    unfold AnalyticNumberTheory.Sieve.localFactor
    by_cases h2dvd : 2 ∣ N
    · simp [h2dvd]
    · simp [h2dvd]
  have hprod_le : (∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2)) ≤
      ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
    apply Finset.prod_le_prod
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpm1 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        have hp3n : (2 : ℕ) ≤ p - 1 := by omega
        exact_mod_cast hp3n
      have hx2 : (4 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((p - 1 : ℕ) : ℝ) - 2)]
      have h14 : 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
        exact one_div_le_one_div_of_le (by norm_num : 0 < (4 : ℝ)) hx2
      -- 0 ≤ 1 − 1/(p−1)²
      have hpos : 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by positivity
      linarith
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpp : p.Prime := hp2.1
      have hp2p : 2 < p := hp2.2
      by_cases hpdvd : p ∣ N
      · rw [AnalyticNumberTheory.Sieve.localFactor_of_dvd hpp hp2p hpdvd]
        have hle1 : 1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
          have hpos : 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by positivity
          linarith
        have hle2 : (1 : ℝ) ≤ (p : ℝ) / (p - 1) := by
          have hp1 : 0 < (p : ℝ) - 1 := by
            have : (2 : ℝ) < p := by exact_mod_cast hp2p
            linarith
          rw [le_div_iff₀ hp1]
          linarith
        linarith
      · rw [AnalyticNumberTheory.Sieve.localFactor_of_not_dvd hpp hp2p hpdvd]
        have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ p))
        have hp1 : (p : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) < p := by exact_mod_cast hp2p
          linarith
        have heq : 1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2 =
            (p : ℝ) * (p - 2) / ((p - 1 : ℕ) : ℝ) ^ 2 := by
          rw [hcast]
          field_simp [hp1]
          ring
        rw [heq, hcast]
  have h𝔖 : AnalyticNumberTheory.Sieve.singularSeriesTruncated N z =
      AnalyticNumberTheory.Sieve.localFactor 2 N *
        ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
    unfold AnalyticNumberTheory.Sieve.singularSeriesTruncated
    rw [hsplit]
    rw [Finset.prod_insert]
    · intro h2S
      rcases Finset.mem_filter.mp h2S with ⟨h1, h2⟩
      omega
  have hprod_ge : (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by
    have hx0 : ∀ p ∈ S, 0 ≤ 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
      intro p hp
      positivity
    have hx1 : ∀ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
      have hpm1 : (2 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        have hp3n : (2 : ℕ) ≤ p - 1 := by omega
        exact_mod_cast hp3n
      have hx2 : (4 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((p - 1 : ℕ) : ℝ) - 2)]
      have h14 : 1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
        exact one_div_le_one_div_of_le (by norm_num : 0 < (4 : ℝ)) hx2
      calc
        1 / ((p - 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := h14
        _ ≤ 1 := by norm_num
    calc
      (1 / 2 : ℝ) ≤ 1 - ∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2 := by
        have hle := sum_sq_recip_primes_ge_three_le_half z
        have hleS : (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ) ^ 2) ≤ 1 / 2 := by
          simpa [S] using hle
        linarith
      _ ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := by
            exact prod_one_sub_ge_one_sub_sum hx0 hx1
  calc
    (1 / 2 : ℝ) ≤ ∏ p ∈ S, (1 - 1 / ((p - 1 : ℕ) : ℝ) ^ 2) := hprod_ge
    _ ≤ ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := hprod_le
    _ ≤ AnalyticNumberTheory.Sieve.localFactor 2 N *
        ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
          have hnonneg : 0 ≤ ∏ p ∈ S, AnalyticNumberTheory.Sieve.localFactor p N := by
            apply Finset.prod_nonneg
            intro p hp
            rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
            exact le_of_lt (AnalyticNumberTheory.Sieve.localFactor_pos hp2.1)
          exact le_mul_of_one_le_left hnonneg hlf2
    _ = AnalyticNumberTheory.Sieve.singularSeriesTruncated N z := h𝔖.symm

/-- 实例化: `SingularSeriesTruncatedLowerBound` 成立 (子 issue #3 闭合). -/
theorem singularSeriesTruncatedLowerBound_ge_half : SingularSeriesTruncatedLowerBound := by
  intro N z hz
  exact singularSeriesTruncated_ge_half hz

/-- `𝔖_trunc` 一致下界 ⇒ 一致主项下界: 主项侧现在完全闭合 (无剩余解析输入). -/
theorem CorrectedChenMainTermLower_of_singularSeries_lower_bound :
    CorrectedChenMainTermLower := by
  exact CorrectedChenMainTermLower_of_singularSeries_lower singularSeriesTruncatedLowerBound_ge_half

/-- **主项渐近阶**: the corrected Selberg divisor sum for the corrected sieve
is `Θ(log (z-1) / 𝔖(N, z-1))`.

This applies the exact Mertens product formula
(`primeProduct_asymptotic_order`) to the seam
`SelbergSum · 𝔖 = 1 / primeProduct (z-1)`. -/
theorem correctedChenSelbergSum_asymptotic_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ N : ℕ, Even N → 4 ≤ N → 3 ≤ correctedChenZ N →
      c₁ * log ((correctedChenZ N - 1 : ℕ) : ℝ) /
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) ≤
        (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
          (correctedChenBoundingSieve N).selbergTerms d) ∧
      (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
          (correctedChenBoundingSieve N).selbergTerms d) ≤
        c₂ * log ((correctedChenZ N - 1 : ℕ) : ℝ) /
        AnalyticNumberTheory.Sieve.singularSeriesTruncated N (correctedChenZ N - 1) := by
  obtain ⟨c₁₀, c₂₀, hc₁₀, hPP⟩ := MertensTheorem.primeProduct_asymptotic_order
  have hP2 : MertensTheorem.primeProduct 2 = (1 / 2 : ℝ) := by
    unfold MertensTheorem.primeProduct
    have hf : (Finset.range 3).filter Nat.Prime = {2} := by
      ext p
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · intro hp
        rcases hp with ⟨hp3, hpp⟩
        interval_cases p
        · exact absurd hpp Nat.not_prime_zero
        · exact absurd hpp Nat.not_prime_one
        · rfl
      · intro hp
        subst p
        simp [Nat.prime_two]
    rw [hf]
    norm_num
  have hc₂₀ : 0 < c₂₀ := by
    have hb := hPP 2 (by norm_num)
    have hP2pos : 0 < MertensTheorem.primeProduct 2 := by
      rw [hP2]
      norm_num
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hpos : 0 < c₂₀ / log 2 := lt_of_lt_of_le hP2pos hb.2
    have hmul : 0 < (c₂₀ / log 2) * log 2 := mul_pos hpos hlog2
    have hcancel : (c₂₀ / log 2) * log 2 = c₂₀ := by field_simp [hlog2.ne']
    rwa [hcancel] at hmul
  refine ⟨1 / c₂₀, 1 / c₁₀, one_div_pos.mpr hc₂₀, ?_⟩
  intro N hN _hN4 hz3
  let z := correctedChenZ N
  let x := z - 1
  have hz1 : 1 ≤ z := by omega
  have hx1 : 1 ≤ x := by omega
  have hx2 : 2 ≤ x := by omega
  have hlog : 0 < log (x : ℝ) := by
    have : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
    exact Real.log_pos this
  have hSpos : 0 < AnalyticNumberTheory.Sieve.singularSeriesTruncated N x :=
    AnalyticNumberTheory.Sieve.singularSeriesTruncated_pos N x hx1
  have hSne : AnalyticNumberTheory.Sieve.singularSeriesTruncated N x ≠ 0 := ne_of_gt hSpos
  have hP := hPP x hx2
  have hPpos : 0 < MertensTheorem.primeProduct x := by
    unfold MertensTheorem.primeProduct
    exact Finset.prod_pos (fun p hp => by
      have hpP : p.Prime := (Finset.mem_filter.mp hp).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      have hle : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
      have hlt1 : 1 / (p : ℝ) < 1 := (div_lt_iff₀ hp0).mpr (by simpa using hle)
      linarith)
  have hid := correctedChenSelbergSum_mul_singularSeriesTruncated N hN
  have hSel : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) =
      (MertensTheorem.primeProduct x)⁻¹ *
        (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ := by
    have h := congrArg (fun t : ℝ => t * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹) hid
    rw [mul_assoc, mul_inv_cancel₀ hSne, mul_one] at h
    exact h
  have hrec_lo : log (x : ℝ) / c₂₀ ≤ (MertensTheorem.primeProduct x)⁻¹ := by
    have h1 : (c₂₀ / log (x : ℝ))⁻¹ ≤ (MertensTheorem.primeProduct x)⁻¹ :=
      (inv_le_inv₀ (div_pos hc₂₀ hlog) hPpos).mpr hP.2
    have hrew : (c₂₀ / log (x : ℝ))⁻¹ = log (x : ℝ) / c₂₀ := by
      field_simp [hc₂₀.ne', hlog.ne']
    rwa [hrew] at h1
  have hrec_up : (MertensTheorem.primeProduct x)⁻¹ ≤ log (x : ℝ) / c₁₀ := by
    have h1 : (MertensTheorem.primeProduct x)⁻¹ ≤ (c₁₀ / log (x : ℝ))⁻¹ :=
      (inv_le_inv₀ hPpos (div_pos hc₁₀ hlog)).mpr hP.1
    have hrew : (c₁₀ / log (x : ℝ))⁻¹ = log (x : ℝ) / c₁₀ := by
      field_simp [hc₁₀.ne', hlog.ne']
    rwa [hrew] at h1
  have hA : log (x : ℝ) / c₂₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ ≤
      (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) := by
    rw [hSel]
    exact mul_le_mul_of_nonneg_right hrec_lo (inv_nonneg.mpr (le_of_lt hSpos))
  have hB : (∑ d ∈ (correctedChenBoundingSieve N).prodPrimes.divisors,
        (correctedChenBoundingSieve N).selbergTerms d) ≤
      log (x : ℝ) / c₁₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ := by
    rw [hSel]
    exact mul_le_mul_of_nonneg_right hrec_up (inv_nonneg.mpr (le_of_lt hSpos))
  have hnormA : log (x : ℝ) / c₂₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ =
      (1 / c₂₀) * log (x : ℝ) / AnalyticNumberTheory.Sieve.singularSeriesTruncated N x := by
    field_simp [hSne, hc₂₀.ne']
  have hnormB : log (x : ℝ) / c₁₀ * (AnalyticNumberTheory.Sieve.singularSeriesTruncated N x)⁻¹ =
      (1 / c₁₀) * log (x : ℝ) / AnalyticNumberTheory.Sieve.singularSeriesTruncated N x := by
    field_simp [hSne, hc₁₀.ne']
  constructor
  · rw [← hnormA]
    exact hA
  · rw [← hnormB]
    exact hB

/-- The historical lower-sieve candidates transfer safely to the corrected
candidate set once the unit boundary is removed.  This is a finite inclusion:
it carries no historical switching or Omega estimate. -/
theorem chenWCandidate_mem_corrected_of_two_le {N p : ℕ}
    (hp : p ∈ chenWCandidates N) (hcomp : 2 ≤ N - p) :
    p ∈ correctedChenCandidates N := by
  simp only [chenWCandidates, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hp_prime, hsmall, -⟩ := hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp_lt, hp_prime, hcomp, ?_⟩
  intro r hr_prime hr_lt
  let z := Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ))
  by_cases hz_small : z ≤ 2
  · have hmax : max 2 z = 2 := max_eq_left hz_small
    have hr_lt_two : r < 2 := by
      simpa only [correctedChenZ, z, hmax] using hr_lt
    exfalso
    exact (not_lt_of_ge hr_prime.two_le) hr_lt_two
  · have hz_two : 2 < z := by omega
    have hmax : max 2 z = z := max_eq_right (by omega)
    apply hsmall r hr_prime
    have hr_lt_z : r < z := by
      simpa only [correctedChenZ, z, hmax] using hr_lt
    omega

/-- Historical lower-sieve candidates away from the unit boundary. -/
noncomputable def chenWNonUnitCandidates (N : ℕ) : Finset ℕ :=
  (chenWCandidates N).filter (fun p => 2 ≤ N - p)

/-- The non-unit historical lower-sieve fibre is contained in the corrected
candidate set. -/
theorem chenWNonUnitCandidates_subset_correctedChenCandidates (N : ℕ) :
    chenWNonUnitCandidates N ⊆ correctedChenCandidates N := by
  intro p hp
  exact chenWCandidate_mem_corrected_of_two_le
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-- The historical W-count differs from a corrected-candidate lower bound by
at most its explicitly isolated unit fibre. -/
theorem chenWCandidates_card_le_correctedChenCandidates_card_add_one (N : ℕ) :
    (chenWCandidates N).card ≤ (correctedChenCandidates N).card + 1 := by
  have hcover : chenWCandidates N ⊆ chenWNonUnitCandidates N ∪ chenUnitCandidates N := by
    intro p hp
    have hp_range : p < N := by
      simpa only [chenWCandidates, Finset.mem_filter, Finset.mem_range] using
        (Finset.mem_filter.mp hp).1
    have hcomp_pos : 0 < N - p := by omega
    by_cases hunit : N - p = 1
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hunit⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  calc
    (chenWCandidates N).card ≤ (chenWNonUnitCandidates N ∪ chenUnitCandidates N).card :=
      Finset.card_le_card hcover
    _ ≤ (chenWNonUnitCandidates N).card + (chenUnitCandidates N).card :=
      Finset.card_union_le _ _
    _ ≤ (correctedChenCandidates N).card + 1 :=
      Nat.add_le_add
        (Finset.card_le_card (chenWNonUnitCandidates_subset_correctedChenCandidates N))
        (chenUnitCandidates_card_le_one N)

/-- Corrected candidates that already give a prime-plus-at-most-two-almost-
prime representation. -/
noncomputable def correctedChenGoodCandidates (N : ℕ) : Finset ℕ :=
  (correctedChenCandidates N).filter
    (fun p => Nat.IsAtMostAlmostPrime 2 (N - p))

/-- The bad fibre of the corrected candidate set.  The planned replacement
Omega must supply a multiplicity-correct penalty for every member of this
set. -/
noncomputable def correctedChenBadCandidates (N : ℕ) : Finset ℕ :=
  (correctedChenCandidates N).filter
    (fun p => ¬ Nat.IsAtMostAlmostPrime 2 (N - p))

/-- The explicit penalty attached to a corrected candidate.  It records both
prime-factor multiplicities in the medium interval and canonical
medium/large/large triple witnesses. -/
noncomputable def correctedChenPenalty (N p : ℕ) : ℝ :=
  primePowerSum (N - p) (correctedChenZ N) (correctedChenY N) +
    tripleFactorCount (N - p) (correctedChenZ N) (correctedChenY N)

/-- The replacement switching sum associated with the corrected candidates.
Unlike the historical `chenOmega`, its factor multiplicity is explicit.  No
analytic upper bound or counting bridge is claimed for it yet. -/
noncomputable def correctedChenOmega (N : ℕ) : ℝ :=
  (correctedChenCandidates N).sum (correctedChenPenalty N)

/-- 由下界接缝得到正性的最终化简: 只要主项 `X·V(N)` 严格大于
`errSum(1) + Ω/2`, 修正计数就是正的.

这正是 `CorrectedChenAnalyticPositivity` 的完整下界侧化简: 三个解析输入
(`V(N)` 的 Mertens 下界、#7 的 errSum 控制、#6 的 Ω 上界) 最终都只用于
验证这一条显式实数不等式. -/
theorem correctedChenPositivity_of_mainTerm_beats_error (N : ℕ)
    (hV : (correctedChenBoundingSieve N).errSum (fun _ => 1) +
        correctedChenOmega N / 2 <
      (correctedChenBoundingSieve N).totalMass * correctedChenSieveProduct N) :
    0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 := by
  have hlow := correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum N
  linarith

/-- The corrected penalty is exactly the amount subtracted by the existing
Chen weight.  This gives a concrete interpretation to the future `/ 2` in a
switching bridge. -/
theorem chenWeight_eq_one_sub_correctedChenPenalty (N p : ℕ) :
    chenWeight (N - p) (correctedChenZ N) (correctedChenY N) =
      1 - correctedChenPenalty N p / 2 := by
  unfold chenWeight correctedChenPenalty
  ring

/-- A bad corrected candidate has penalty at least two, provided the cutoff
parameters cover its complementary number below the cube scale.  This is the
finite multiplicity fact that will justify `/ 2` in the replacement switching
bridge. -/
theorem correctedChenBad_penalty_ge_two {N p : ℕ}
    (hp : p ∈ correctedChenBadCandidates N)
    (hzy : correctedChenZ N < correctedChenY N)
    (hcube : (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3) :
    (2 : ℝ) ≤ correctedChenPenalty N p := by
  rcases Finset.mem_filter.mp hp with ⟨hcandidate, hbad⟩
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hcandidate
  obtain ⟨hp_lt, _, hq_two, hcoprime⟩ := hcandidate
  have hcube' : ((N - p : ℕ) : ℝ) < (correctedChenY N : ℝ) ^ 3 := by
    rw [Nat.cast_sub (by omega : p ≤ N)]
    exact hcube
  have hz : 2 ≤ correctedChenZ N := by
    simp only [correctedChenZ]
    exact le_max_left _ _
  by_contra hpen
  have hpen_lt : correctedChenPenalty N p < 2 := by linarith
  have hweight :
      0 < chenWeight (N - p) (correctedChenZ N) (correctedChenY N) := by
    rw [chenWeight_eq_one_sub_correctedChenPenalty]
    linarith
  rcases chenWeight_pos_implies_semiprime (N - p)
      (correctedChenZ N) (correctedChenY N) hz hzy (by omega) hcube' hcoprime hweight with
    hunit | hprime | ⟨a, b, ha, hb, -, -, hproduct⟩
  · omega
  · exact hbad (hprime.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2))
  · apply hbad
    rw [hproduct]
    exact ha.mul_isAlmostPrime_two hb |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-- The corrected finite switching bridge, conditional only on the elementary
cutoff facts needed by the weight lemma.  Its `/ 2` is justified by the
explicit bad-fibre penalty, not by the obsolete historical Omega count. -/
theorem corrected_counting_bridge (N : ℕ)
    (hzy : correctedChenZ N < correctedChenY N)
    (hcube : ∀ p ∈ correctedChenCandidates N,
      (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((correctedChenGoodCandidates N).card : ℝ) := by
  let C := correctedChenCandidates N
  let G := correctedChenGoodCandidates N
  let B := correctedChenBadCandidates N
  have hpoint : ∀ p ∈ C,
      chenWeight (N - p) (correctedChenZ N) (correctedChenY N) ≤
        if p ∈ G then 1 else 0 := by
    intro p hp
    by_cases hgood : p ∈ G
    · simp only [hgood, ite_true]
      rw [chenWeight_eq_one_sub_correctedChenPenalty]
      have hpen : 0 ≤ correctedChenPenalty N p := by
        unfold correctedChenPenalty primePowerSum tripleFactorCount
        apply add_nonneg
        · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
        · exact Nat.cast_nonneg _
      linarith
    · simp only [hgood, ite_false]
      have hbad : p ∈ B := by
        apply Finset.mem_filter.mpr
        refine ⟨hp, ?_⟩
        intro halmost
        apply hgood
        exact Finset.mem_filter.mpr ⟨hp, halmost⟩
      have hpen : (2 : ℝ) ≤ correctedChenPenalty N p := by
        simpa only [B, C] using correctedChenBad_penalty_ge_two hbad hzy (hcube p hp)
      rw [chenWeight_eq_one_sub_correctedChenPenalty]
      linarith
  have hsum := Finset.sum_le_sum (fun p hp => hpoint p hp)
  have hfilter : C.filter (fun p => p ∈ G) = G := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact hp.2
    · intro hp
      exact ⟨Finset.filter_subset _ _ hp, hp⟩
  have hgood_sum : C.sum (fun p => if p ∈ G then (1 : ℝ) else 0) = G.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hweight_sum :
      C.sum (fun p => chenWeight (N - p) (correctedChenZ N) (correctedChenY N)) =
        (C.card : ℝ) - correctedChenOmega N / 2 := by
    simp only [chenWeight_eq_one_sub_correctedChenPenalty]
    rw [Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    simp [C, correctedChenOmega]
  rw [hweight_sum] at hsum
  simpa only [hgood_sum] using hsum

/-- Every corrected candidate lies in exactly one of the good and bad fibres.
This is the finite partition on which the replacement counting bridge will be
built. -/
theorem mem_correctedChenGood_or_bad {N p : ℕ}
    (hp : p ∈ correctedChenCandidates N) :
    p ∈ correctedChenGoodCandidates N ∨ p ∈ correctedChenBadCandidates N := by
  by_cases hgood : Nat.IsAtMostAlmostPrime 2 (N - p)
  · exact Or.inl <| Finset.mem_filter.mpr ⟨hp, hgood⟩
  · exact Or.inr <| Finset.mem_filter.mpr ⟨hp, hgood⟩

/-- Corrected good candidates are genuine good representations in the public
Chen statement. -/
theorem correctedChenGoodCandidates_subset_goodRepresentations (N : ℕ) :
    correctedChenGoodCandidates N ⊆ chenGoodRepresentations N := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hcandidate, halmost⟩
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hcandidate
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range]
  exact ⟨hcandidate.1, hcandidate.2.1, hcandidate.2.2.1, halmost⟩

/-- The two elementary scale facts required by the corrected finite switching
bridge.  Keeping them as a named predicate cleanly separates rounding/cutoff
analysis from the purely finite multiplicity argument. -/
def CorrectedChenCutoffValid (N : ℕ) : Prop :=
  correctedChenZ N < correctedChenY N ∧
    (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3

/-- Ceiling rounding alone supplies the cube-scale half of the corrected
cutoff predicate, for every natural input. -/
theorem correctedChen_cube_scale (N : ℕ) :
    (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3 := by
  have hceil : (N : ℝ) ^ (1 / 3 : ℝ) ≤ (correctedChenY N : ℝ) := by
    simpa only [correctedChenY] using Nat.le_ceil ((N : ℝ) ^ (1 / 3 : ℝ))
  have hbase : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    (N : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    _ ≤ (correctedChenY N : ℝ) ^ 3 := pow_le_pow_left₀ hbase hceil 3

/-- Apart from the harmless `max 2`, the lower cutoff is strictly below the
upper cutoff as soon as the base exceeds one. -/
theorem correctedChen_floorZ_lt_y {N : ℕ} (hN : 1 < (N : ℝ)) :
    Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) < correctedChenY N := by
  have hpow : (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hN
    norm_num
  simpa only [correctedChenY] using
    Nat.floor_lt_ceil_of_lt_of_pos hpow
      (Real.rpow_pos_of_pos (by linarith : 0 < (N : ℝ)) _)

/-- The corrected cutoff predicate follows from a single concrete lower-root
condition.  The remaining threshold task is therefore the elementary claim
`2 < N^(1/3)`, rather than any switching-counting statement. -/
theorem correctedChen_cutoffValid_of_root_gt_two {N : ℕ}
    (hroot : (2 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ)) :
    CorrectedChenCutoffValid N := by
  have hN : 1 < (N : ℝ) := by
    have hroot_pos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) := by linarith
    by_contra h
    have hN_nonpos : (N : ℝ) ≤ 1 := le_of_not_gt h
    have hpow_le : (N : ℝ) ^ (1 / 3 : ℝ) ≤ 1 :=
      Real.rpow_le_one (Nat.cast_nonneg N) hN_nonpos (by norm_num)
    linarith
  refine ⟨?_, correctedChen_cube_scale N⟩
  unfold correctedChenZ
  apply max_lt
  · simpa only [correctedChenY] using (Nat.lt_ceil.mpr hroot)
  · exact correctedChen_floorZ_lt_y hN

/-- The remaining lower-root condition is already valid from the concrete
threshold `N ≥ 9`.  Consequently the corrected finite counting bridge has no
unproved cutoff side condition in the range relevant to Chen's theorem. -/
theorem correctedChen_cutoffValid_of_nine_le {N : ℕ} (hN : 9 ≤ N) :
    CorrectedChenCutoffValid N := by
  apply correctedChen_cutoffValid_of_root_gt_two
  have hbase : (8 : ℝ) < N := by exact_mod_cast (show 8 < N by omega)
  have hpow := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 8) hbase
    (by norm_num : (0 : ℝ) < 1 / 3)
  have h8root : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    calc
      (8 : ℝ) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by norm_num
      _ = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast 2 3).symm
      _ = (2 : ℝ) ^ ((3 : ℝ) * (1 / 3 : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = 2 := by norm_num
  linarith

/-- The global cube-scale part of `CorrectedChenCutoffValid` supplies the
strict complementary bound for every corrected candidate, because its prime
component is positive. -/
theorem correctedChen_candidate_complement_lt_cube {N p : ℕ}
    (hscale : (N : ℝ) ≤ (correctedChenY N : ℝ) ^ 3)
    (hp : p ∈ correctedChenCandidates N) :
    (N - p : ℝ) < (correctedChenY N : ℝ) ^ 3 := by
  simp only [correctedChenCandidates, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hp_lt, hp_prime, -, -⟩ := hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
  linarith

/-- The corrected bridge in the public Chen representation space.  It is a
fully kernel-checked replacement for the refuted historical counting bridge,
conditional only on the cutoff predicate whose eventual validity remains an
explicit analytic/rounding task. -/
theorem corrected_counting_bridge_public {N : ℕ}
    (hcutoff : CorrectedChenCutoffValid N) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((chenGoodRepresentations N).card : ℝ) := by
  have hbridge :
      ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
        ((correctedChenGoodCandidates N).card : ℝ) :=
    corrected_counting_bridge N hcutoff.1
      (fun p hp => correctedChen_candidate_complement_lt_cube hcutoff.2 hp)
  exact hbridge.trans (by
    exact_mod_cast Finset.card_le_card
      (correctedChenGoodCandidates_subset_goodRepresentations N))

/-- The corrected finite bridge in the public representation space, with its
cutoffs discharged for every `N ≥ 9`. -/
theorem corrected_counting_bridge_public_of_nine_le {N : ℕ} (hN : 9 ≤ N) :
    ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2 ≤
      ((chenGoodRepresentations N).card : ℝ) :=
  corrected_counting_bridge_public (correctedChen_cutoffValid_of_nine_le hN)

/-- A positive corrected sieve difference already yields a genuine Chen
representation.  All finite switching, rounding, and boundary-fibre work is
internal to this theorem; the only future input is an analytic proof that its
left-hand side is positive. -/
theorem corrected_key_inequality_implies_chen_at {N : ℕ} (hN : 9 ≤ N)
    (hkey : 0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2) :
    ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
      Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  have hpos : 0 < ((chenGoodRepresentations N).card : ℝ) :=
    lt_of_lt_of_le hkey (corrected_counting_bridge_public_of_nine_le hN)
  have hcard : 0 < (chenGoodRepresentations N).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpprime, hq2, hqalmost⟩ := hp
  exact ⟨p, N - p, hpprime, hq2, hqalmost, by omega⟩

/-- The corrected analytic target implies Chen's theorem at the conventional
threshold.  This replaces the historical `ChenCountingBridge` assumption by
a single honest analytic positivity obligation for the new objects. -/
theorem corrected_key_inequality_implies_chen
    (hkey : ∀ N : ℕ, Even N → 1000 ≤ N →
      0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  refine ⟨1000, ?_⟩
  intro N hN_large hN_even
  exact corrected_key_inequality_implies_chen_at (by omega) (hkey N hN_even hN_large)

/-- The sole active analytic obligation for the corrected Chen development.
It deliberately speaks only about the new candidate and penalty objects; no
constant or bound from the refuted historical switching model is imported. -/
def CorrectedChenAnalyticPositivity : Prop :=
  ∀ N : ℕ, Even N → 1000 ≤ N →
    0 < ((correctedChenCandidates N).card : ℝ) - correctedChenOmega N / 2

/-- Conditional Chen theorem for the corrected development.  Its unique
assumption is precisely `CorrectedChenAnalyticPositivity`; the finite bridge
and representation extraction have been discharged above. -/
theorem corrected_chens_theorem (h : CorrectedChenAnalyticPositivity) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q :=
  corrected_key_inequality_implies_chen h

/-- Historical conditional counting bridge for the present `chenW`/`Ω`.

This proposition is retained so the conditional theorem has a stable, explicit
interface, but it is not an open proof obligation: finite evaluation refutes
it for the current definitions (see `CHEN_PROOF_ATLAS.md`).  A future
unconditional development must replace both this statement and, where needed,
the counting objects with a multiplicity-corrected switching bridge. -/
def ChenCountingBridge : Prop :=
  ∀ N : ℕ, Even N → 1000 ≤ N →
    chenW N - chenOmega N / 2 ≤ ((chenGoodRepresentations N).card : ℝ)

/-- 关键不等式在精确计数桥接下蕴含陈氏定理.

W(N) - Ω/2 > 0 意味着至少存在一个表示 N = p + q,
其中 p 素数, q = N - p 满足筛法条件 (至多两个素因子). -/
theorem key_inequality_implies_chen
    (h_bridge : ChenCountingBridge)
    (h_key : ∀ N : ℕ, Even N → N ≥ 1000 →
      chenW N - chenOmega N / 2 > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → Even N →
      ∃ p q : ℕ, p.Prime ∧ q ≥ 2 ∧
        Nat.IsAtMostAlmostPrime 2 q ∧ N = p + q := by
  -- The Lean proof below uses `ChenCountingBridge` directly.  The following
  -- numbered discussion is a classical switching-argument sketch only; it is
  -- not a formal proof of the missing bridge.
  --
  -- 证明策略 (完整证明需要 W(N) 和 Ω 的精确关系及计数论证):
  --
  -- 取 N₀ = 1000. 对任意偶数 N ≥ 1000:
  --
  -- 步骤 1: 由 h_key, chenW N - chenOmega N / 2 > 0, 故 chenW N > 0.
  --
  -- 步骤 2: chenW N > 0 意味着存在素数 p < N 满足 chenW 的筛法条件:
  --   (a) N - p 无 ≤ z = N^(1/10) 的素因子
  --   (b) N - p 在 (z, y] (y = N^(1/3)) 中至多一个素因子
  --   即 W(N) 的 filter 非空.
  --
  -- 步骤 3: 设 q = N - p. 由条件 (a) 和 (b):
  --   - q 无 ≤ z 的素因子 (由条件 a)
  --   - q 在 (z, y] 中至多一个素因子 (由条件 b)
  --   - q 的所有素因子要么 > y, 要么在 (z, y] 中 (至多一个)
  --
  -- 步骤 4: 需证明 q 至多两个素因子 (即 Nat.IsAtMostAlmostPrime 2 q).
  --   反证: 假设 q 有 3 个或更多素因子.
  --   由条件 (a), q 无 ≤ z 的素因子, 故所有素因子 > z.
  --   若 q 有 3 个素因子 p₁ ≤ p₂ ≤ p₃ (都 > z):
  --     - 若 p₁ ≤ y: 则 p₁ ∈ (z, y], 由条件 (b), (z, y] 中至多一个素因子,
  --       故 p₂, p₃ > y. 但此时 p₁*p₂*p₃ ≤ q = N - p < N,
  --       且 p₁ ∈ (z, y], p₂, p₃ ≥ y, 满足 tripleFactorCount 的条件,
  --       故 tripleFactorCount ≥ 1, 这意味着 Ω 计数了此情形.
  --     - 若 p₁ > y: 则 q ≥ p₁*p₂*p₃ > y³ = N (因 y = N^(1/3)),
  --       但 q = N - p < N, 矛盾.
  --
  -- 步骤 5: 将三因子情形从 W(N) 中排除.
  --   W(N) 计数满足筛法条件的 p, 其中可能包含 N - p 恰好三个素因子的情形.
  --   Ω 计数这些三因子情形 (通过切换和).
  --   由 h_key: W(N) > Ω/2, 即 W(N) - Ω/2 > 0.
  --   由于 Ω/2 ≤ (W(N) 中三因子情形数) (由切换等式 switching_identity),
  --   故 W(N) - Ω/2 > 0 意味着 W(N) 中存在非三因子情形的 p,
  --   即存在 p 使 q = N - p 至多两个素因子.
  --
  -- 步骤 6: q ≥ 2.
  --   由 q = N - p, p < N (因 p ∈ range N), 且 N ≥ 1000 > 2, p 为素数 ≥ 2,
  --   故 q = N - p ≥ N - (N-1) = 1. 需进一步排除 q = 1:
  --   若 q = 1, 则 N = p + 1, 但 N 为偶数且 ≥ 1000, p = N - 1 为奇数 ≥ 999.
  --   此时 q = 1 无素因子, 满足筛法条件, 但 Ω 不计数此情形 (因 Ω 仅计数三因子).
  --   实际上, q = 1 时 w(q) = 1 > 0, 且 q < y³, 由 chenWeight_pos_implies_semiprime,
  --   q = 1, 但 q ≥ 2 不满足. 需要额外论证排除 q = 1:
  --   当 N 充分大时, W(N) 远大于 Ω/2 (因 W(N) ~ N/log²N, Ω/2 ~ N/log²N,
  --   但系数 W > Ω/2), 故存在 p 使 q = N - p ≥ 2 且至多两个素因子.
  --   (严格论证需要更精细的计数.)
  --
  -- 步骤 7: Nat.IsAtMostAlmostPrime 2 q.
  --   由步骤 4-5, q 至多两个素因子, 即 Ω(q) ≤ 2.
  --   结合 q ≥ 2, 有 Nat.IsAtMostAlmostPrime 2 q.
  --
  -- 形式化难点:
  --   1. chenW N > 0 → 存在满足筛法条件的 p (需展开 chenW 的 Finset.card 定义)
  --   2. 筛法条件 → q 至多两个素因子 (需 chenWeight_pos_implies_semiprime,
  --      需验证 hn_lt : q < y³, 即 N - p < N, 这由 p ≥ 2 和 y = N^(1/3) 给出)
  --   3. W(N) - Ω/2 > 0 → 存在非三因子情形 (需 switching_identity 和计数论证)
  --   4. q ≥ 2 的论证 (需排除 q = 1 的边界情况)
  refine ⟨1000, ?_⟩
  intro N hN_large hN_even
  have hpos : 0 < ((chenGoodRepresentations N).card : ℝ) :=
    lt_of_lt_of_le (h_key N hN_even hN_large) (h_bridge N hN_even hN_large)
  have hcard : 0 < (chenGoodRepresentations N).card := by exact_mod_cast hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  simp only [chenGoodRepresentations, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpprime, hq2, hqalmost⟩ := hp
  refine ⟨p, N - p, hpprime, hq2, hqalmost, ?_⟩
  omega

/-! ## 5. 数值常数 -/

/-- W(N) 下界系数: 2.6408 -/
noncomputable def chenW_coefficient : ℝ := 2.6408

/-- Ω 上界系数: 3.9404 -/
noncomputable def chenOmega_coefficient : ℝ := 3.9404

/-- 关键差: W(N) - Ω/2 ≥ (2.6408 - 3.9404/2) 𝔖(N) N/log²N = 0.6706 𝔖(N) N/log²N -/
noncomputable def chen_difference_coefficient : ℝ :=
  chenW_coefficient - chenOmega_coefficient / 2

/-- 关键差为正: 0.6706 > 0 -/
theorem chen_difference_pos : 0 < chen_difference_coefficient := by
  unfold chen_difference_coefficient chenW_coefficient chenOmega_coefficient
  norm_num

/-- f(5) 的工作表达式: 2e^γ · log(5/2) / 5 ≈ 0.6528 -/
noncomputable def sieveF_at_5 : ℝ :=
  2 * exp Real.eulerMascheroniConstant * log (5/2) / 5

/-- W(N) 系数的来源: 10 · e^(-γ) · f(5) = 4 · log(5/2) ≈ 3.665...

注: 完整的 W(N) 系数 2.6408 来自 Jurkat-Richert 筛函数 f(5) 的精确计算,
涉及筛函数 F(s)/f(s) 的显式公式, 非简单的代数化简.
此处仅验证 e^γ · e^(-γ) = 1 的消去. -/
theorem chenW_coefficient_simplification :
    sieveF_at_5 * exp (-Real.eulerMascheroniConstant) =
      2 * log (5/2) / 5 := by
  unfold sieveF_at_5
  have h_exp : exp Real.eulerMascheroniConstant * exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]
    have h_sum : Real.eulerMascheroniConstant + (-Real.eulerMascheroniConstant) = 0 := by linarith
    rw [h_sum, Real.exp_zero]
  have h_rearr : (2 * exp Real.eulerMascheroniConstant * log (5/2)) / 5 * exp (-Real.eulerMascheroniConstant) =
        (2 * log (5/2) * (exp Real.eulerMascheroniConstant * exp (-Real.eulerMascheroniConstant))) / 5 := by ring
  rw [h_rearr, h_exp]
  ring

/-- M₁ 系数的来源: 8 · 0.49254 = 3.94032 -/
theorem chenOmega_coefficient_derivation :
    (8 : ℝ) * 0.49254 = 3.94032 := by
  -- 由 Lemma 3: Σ λ_{d₁} λ_{d₂} / φ([d₁,d₂]) ≈ 8 𝔖(N) / log N
  -- 由 Lemma 4: Σ f(a) / (a log(N/a)) ≤ 0.49254 / log N
  -- 故 M₁ ≤ 8 · 0.49254 · 𝔖(N) N / log²N = 3.94032 𝔖(N) N / log²N
  norm_num

/-! ## 6. 切换原理的直观解释 -/

/-
**切换原理的直观解释**:

1. **目标**: 证明存在 p 素数, q 半素数, 使 N = p + q

2. **第一步 (W(N) 下界)**: 对集合 A = {N - p : p 素数} 应用 Jurkat-Richert 筛法
   - 筛去 N-p 中 ≤ N^(1/10) 的素因子
   - 得到 W(N): N-p 无小素因子且中大范围至多一个素因子
   - W(N) ≥ 2.6408 𝔖(N) N/log²N

3. **第二步 (W(N) 中的三因子情形)**: W(N) 中的 p 可能对应
   N - p = p₁p₂p₃ (恰好三个素因子), 需要排除这些情形
   - 三因子情形满足: N^(1/10) < p₁ ≤ N^(1/3) < p₂ < p₃
   - 由对称性, Ω/2 给出三因子情形的上界

4. **第三步 (Ω 上界)**: 对切换集 B = {N - p₁p₂p₃} 应用 Selberg 筛
   - 切换: 不再直接筛 N-p, 而是筛 "N - ap₃ 素数" 中的 a
   - Selberg 筛给出 Ω ≤ 3.9404 𝔖(N) N/log²N

5. **结论**: W(N) - Ω/2 > 0 → 存在 p 使 N-p 至多两个素因子
-/

/-! ## 7. 切换集 B 的定义 -/

/-- **切换集 B**: `N - p₁p₂p₃`, 其中
`z ≤ p₁ < y ≤ p₂ ≤ p₃`, `p₁p₂p₃ < N`, `(p₁p₂p₃, N) = 1`。

这不是 `tripleFactorCount` 所用的三因子对象：这里额外要求与 `N` 互素及乘积小于
`N`，并且由 `p₂ < p₃` 排除重复因子 `p₂ = p₃`。二者的精确关系仍是待形式化的
切换桥的一部分。 -/
noncomputable def switchedSet (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n =>
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ < p₂ ∧ p₂ < p₃ ∧
      p₁ * p₂ * p₃ < N ∧
      Nat.gcd (p₁ * p₂ * p₃) N = 1 ∧
      n = N - p₁ * p₂ * p₃)

/-- 切换集 B 上的筛函数 S(B, P, y). -/
noncomputable def switchedSieveSum (N z y : ℕ) : ℝ :=
  (switchedSet N z y).sum (fun n =>
    if (∀ p : ℕ, p.Prime → p < y → ¬ p ∣ n) then 1 else 0)

/-- **切换等式的无条件粗界**: 第三项 = (1/2) S(B, P, y) + C,
其中 `|C| ≤ N+1`。

原陈述声称 `O(N^(1/3))`，但当前两个有限集定义之间尚无形式化的切换对应，无法推出
该精细误差。这里记录由二者均为 `range (N+1)` 的子计数直接得到的诚实粗界；
立方根误差仍是后续需要单独形式化的切换原理。 -/
theorem switching_identity (N z y : ℕ) (_hz : 2 ≤ z) (_hy : y ≤ N) :
    ∃ C : ℝ,
      (1/2 : ℝ) * ((Finset.range (N + 1)).filter (fun n =>
        (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
        ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card
      = (1/2 : ℝ) * switchedSieveSum N z y + C ∧
      |C| ≤ (N : ℝ) + 1 := by
  let A : ℝ := (((Finset.range (N + 1)).filter (fun n =>
    (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
      z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card : ℝ)
  let S : ℝ := switchedSieveSum N z y
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAle : A ≤ (N : ℝ) + 1 := by
    dsimp [A]
    have hnat : ((Finset.range (N + 1)).filter (fun n =>
        (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
        ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
          z ≤ p₁ ∧ p₁ < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ n = p₁ * p₂ * p₃)).card ≤ N + 1 := by
      calc
        _ ≤ (Finset.range (N + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = N + 1 := Finset.card_range _
    exact_mod_cast hnat
  have hS0 : 0 ≤ S := by
    dsimp [S, switchedSieveSum]
    apply Finset.sum_nonneg
    intro n hn
    split <;> norm_num
  have hSlecard : S ≤ ((switchedSet N z y).card : ℝ) := by
    dsimp [S, switchedSieveSum]
    calc
      (switchedSet N z y).sum (fun n =>
          if (∀ p : ℕ, p.Prime → p < y → ¬ p ∣ n) then 1 else 0) ≤
          (switchedSet N z y).sum (fun _ => (1 : ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            split <;> norm_num
      _ = ((switchedSet N z y).card : ℝ) := by simp
  have hScard : ((switchedSet N z y).card : ℝ) ≤ (N : ℝ) + 1 := by
    have hnat : (switchedSet N z y).card ≤ N + 1 := by
      unfold switchedSet
      calc
        _ ≤ (Finset.range (N + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = N + 1 := Finset.card_range _
    exact_mod_cast hnat
  have hSle : S ≤ (N : ℝ) + 1 := hSlecard.trans hScard
  refine ⟨A / 2 - S / 2, ?_, ?_⟩
  · change (1 / 2 : ℝ) * A = (1 / 2 : ℝ) * S + (A / 2 - S / 2)
    ring
  · rw [abs_le]
    constructor <;> nlinarith

/-! ## 8. 完整证明结构 -/

/-
**陈氏定理完整证明结构**:

  chens_theorem
  └── key_inequality_implies_chen (逻辑推导)
      └── chen_key_inequality: W(N) - Ω/2 > 0
          ├── W(N) ≥ 2.6408 𝔖(N) N/log²N
          │   ├── jurkat_richert_lower_bound (LinearSieve.lean)
          │   │   ├── SieveProblem 设置 (Goldbach 型)
          │   │   ├── 分布条件 (Bombieri-Vinogradov)
          │   │   ├── V(z) ≈ 𝔖(N) e^(-γ)/log z (Mertens)
          │   │   └── f(5) = 2e^γ log(5/2)/5 (筛函数)
          │   └── 𝔖(N) > 0 (AnalyticNumberTheory.Sieve.lean)
          └── Ω ≤ 3.9404 𝔖(N) N/log²N
              ├── Selberg 筛上界 (SelbergUpperBound.lean)
              │   ├── Lemma 3: Σ λ²/φ([d₁,d₂]) ≈ 8 𝔖(N)/log N
              │   └── Lemma 4: Σ f(a)/(a log(N/a)) ≤ 0.49254/log N
              ├── Pan 均值定理 (BombieriVinogradov.lean)
              │   └── R ≪ N/log^A N (误差项)
              └── 𝔖(N) > 0 (AnalyticNumberTheory.Sieve.lean)

**模块依赖关系**:
  - AnalyticNumberTheory.Sieve.lean: 𝔖(N) 定义和正性
  - LinearSieve.lean: Jurkat-Richert 定理, F(s)/f(s)
  - MertensTheorem.lean: V(z) 渐近, Mertens 定理
  - BombieriVinogradov.lean: 分布条件, Pan 均值定理
  - SwitchingPrinciple.lean: W(N), Ω, 切换原理 (本文件)
  - SelbergUpperBound.lean: Selberg 筛上界 (Ω 估计)
-/

end MathlibNt.SieveTheory.SwitchingPrinciple
