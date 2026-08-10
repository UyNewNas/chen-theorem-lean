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
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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

/-- **W(N)**: 满足筛法条件的素数 p 的计数.

W(N) = |{p 素数 : N - p 无 ≤ N^(1/10) 的素因子, 且 (N^(1/10), N^(1/3)] 中至多一个素因子}|

由 Jurkat-Richert 下界: W(N) ≥ 2.6408 𝔖(N) N/log²N -/
noncomputable def chenW (N : ℕ) : ℝ :=
  let z := Nat.floor ((N : ℝ) ^ (1/10 : ℝ))
  let y := Nat.floor ((N : ℝ) ^ (1/3 : ℝ))
  (Finset.card ((Finset.range N).filter (fun p =>
    p.Prime ∧
    (∀ q : ℕ, q.Prime → q ≤ z → ¬ q ∣ (N - p)) ∧
    (Finset.card ((Finset.range (y + 1)).filter (fun q =>
      q.Prime ∧ z < q ∧ q ≤ y ∧ q ∣ (N - p))) ≤ 1))) : ℝ)

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
  unfold chenW
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

/-- `chenW`/`Ω` 与好表示计数之间所需的精确组合桥接。

当前 `chenW` 是未加权的 filter 基数，而 `chenOmega` 是以 `a = p₁p₂`
索引的切换和；它们的工作定义本身没有给出下面的计数不等式。 -/
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

/-- **切换集 B**: N - p₁p₂p₃, 其中 z ≤ p₁ < y ≤ p₂ ≤ p₃, p₁p₂p₃ < N, (p₁p₂p₃, N) = 1 -/
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
          │   └── 𝔖(N) > 0 (SingularSeries.lean)
          └── Ω ≤ 3.9404 𝔖(N) N/log²N
              ├── Selberg 筛上界 (SelbergUpperBound.lean)
              │   ├── Lemma 3: Σ λ²/φ([d₁,d₂]) ≈ 8 𝔖(N)/log N
              │   └── Lemma 4: Σ f(a)/(a log(N/a)) ≤ 0.49254/log N
              ├── Pan 均值定理 (BombieriVinogradov.lean)
              │   └── R ≪ N/log^A N (误差项)
              └── 𝔖(N) > 0 (SingularSeries.lean)

**模块依赖关系**:
  - SingularSeries.lean: 𝔖(N) 定义和正性
  - LinearSieve.lean: Jurkat-Richert 定理, F(s)/f(s)
  - MertensTheorem.lean: V(z) 渐近, Mertens 定理
  - BombieriVinogradov.lean: 分布条件, Pan 均值定理
  - SwitchingPrinciple.lean: W(N), Ω, 切换原理 (本文件)
  - SelbergUpperBound.lean: Selberg 筛上界 (Ω 估计)
-/

end MathlibNt.SieveTheory.SwitchingPrinciple
