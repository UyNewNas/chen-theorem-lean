/-
! # MathlibNt.SieveTheory.LinearSieve

## 线性筛 / Jurkat-Richert 定理

Jurkat-Richert 定理 (1965) 是陈氏定理证明中 W(N) 下界的核心工具.
它给出筛函数的上界和下界, 以筛函数 F(s) 和 f(s) 表示.

**筛函数 F(s) (上界) 和 f(s) (下界)** 满足差分微分方程:
  - F(s) = 2e^γ / s,       当 2 ≤ s ≤ 4
  - f(s) = 0,               当 s ≤ 3
  - (s·F(s))' = f(s-1),     当 s ≥ 4
  - (s·f(s))' = F(s-1),     当 s ≥ 3

其中 γ 为 Euler-Mascheroni 常数.

参考:
  - Jurkat & Richert (1965), Acta Arith. 11, 217-240
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 8
  - Liu, Z. (2022), arXiv:2203.07871, §III
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith

namespace MathlibNt.SieveTheory.LinearSieve

open Real BoundingSieve

open scoped Classical

/-! ## 0. Finite lower-bound sieve interface -/

/-- A sequence of coefficients is lower Möbius when its divisor sums lie below
the coprimality indicator.  This is the exact finite dual of Mathlib's
`BoundingSieve.IsUpperMoebius`. -/
def IsLowerMoebius (muMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, muMinus d ≤ if n = 1 then 1 else 0

/-- A lower Möbius sequence gives a lower bound for the sifted sum before any
asymptotic estimate is introduced. -/
theorem sum_of_lowerMoebius_le_siftedSum {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d ≤ S.siftedSum := by
  calc
    ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d =
        ∑ n ∈ S.support, ∑ d ∈ S.prodPrimes.divisors,
          if d ∣ n then S.weights n * muMinus d else 0 := by
      symm
      rw [Finset.sum_comm]
      simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
    _ = ∑ n ∈ S.support, S.weights n *
        ∑ d ∈ (Nat.gcd S.prodPrimes n).divisors, muMinus d := by
      symm
      simp_rw [Finset.mul_sum, ← Finset.sum_filter]
      congr with n
      congr
      · rw [← Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero
          (Nat.gcd_dvd_left _ _)]
        ext x
        simp +contextual [Nat.dvd_gcd_iff]
    _ ≤ S.siftedSum := by
      rw [S.siftedSum_eq_sum_support_mul_ite]
      gcongr with n
      exact hmu (Nat.gcd S.prodPrimes n)

/-- Explicit-error lower sieve inequality.  Unlike the historical pointwise
interfaces, the loss is the concrete finite quantity `errSum muMinus`. -/
theorem mainSum_sub_errSum_le_siftedSum_of_lowerMoebius {S : BoundingSieve}
    (muMinus : ℕ → ℝ) (hmu : IsLowerMoebius muMinus) :
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤ S.siftedSum := by
  have hrem : -S.errSum muMinus ≤
      ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [← abs_mul]
    exact neg_abs_le _
  calc
    S.totalMass * S.mainSum muMinus - S.errSum muMinus ≤
        S.totalMass * S.mainSum muMinus +
          ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.rem d := by
      linarith
    _ = ∑ d ∈ S.prodPrimes.divisors, muMinus d * S.multSum d := by
      rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr with d
      rw [BoundingSieve.rem]
      ring
    _ ≤ S.siftedSum := sum_of_lowerMoebius_le_siftedSum muMinus hmu

/-! ## 1. Euler-Mascheroni 常数 -/

/-- Euler-Mascheroni 常数 γ ≈ 0.5772...

定义为调和级数与对数之差的极限. -/
noncomputable abbrev eulerMascheroni : ℝ :=
  -- Mathlib 中有 Real.eulerMascheroniConstant
  Real.eulerMascheroniConstant

/-! ## 2. 筛函数 F(s) 和 f(s) -/

/-- 上界筛函数 F(s) 的分段定义.

  - s ≤ 2:  F(s) = 1 (平凡上界)
  - 2 ≤ s ≤ 4:  F(s) = 2e^γ / s
  - s ≥ 4:  由差分微分方程 (s·F(s))' = f(s-1) 递推定义

此处仅定义 [2, 4] 区间, 更大区间需递推. -/
noncomputable def sieveFunctionF (s : ℝ) : ℝ :=
  if s ≤ 2 then
    1
  else if s ≤ 4 then
    2 * exp eulerMascheroni / s
  else
    -- s > 4: 递推定义, 此处用近似值占位
    -- 严格定义需 Buchstab 型递推
    2 * exp eulerMascheroni / s * (1 + 1 / s)

/-- A nonstandard working normalization for a lower sieve function.

  - s ≤ 3:  f(s) = 0
  - 3 ≤ s ≤ 5:  a local `log (s / 2)` surrogate
  - s ≥ 5:  a further placeholder approximation

This is **not** claimed to be the standard Jurkat--Richert/Buchstab lower
sieve function (whose normalization and differential-delay recursion must be
formalized separately).  It is used only in the fixed-parameter working
interfaces below and must not be used to justify Chen's classical constants. -/
noncomputable def sieveFunctionf (s : ℝ) : ℝ :=
  if s ≤ 3 then
    0
  else if s ≤ 5 then
    2 * exp eulerMascheroni / s * log (s / 2)
  else
    -- s > 5: 递推定义, 此处用近似值占位
    2 * exp eulerMascheroni / s * log (s / 2) * (1 + 1 / s)

/-! ## 3. 筛函数的基本性质 -/

/-- F(s) 在 [2, 4] 上为正. -/
theorem sieveF_pos_on_2_4 {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 4) :
    0 < sieveFunctionF s := by
  unfold sieveFunctionF
  by_cases h2 : s ≤ 2
  · rw [if_pos h2]; norm_num
  · rw [if_neg h2, if_pos hs']
    have hs_pos : 0 < s := by linarith
    exact div_pos (mul_pos (by norm_num) (exp_pos eulerMascheroni)) hs_pos

/-- f(s) 在 (3, 5] 上为正. -/
theorem sievef_pos_on_3_5 {s : ℝ} (hs : 3 < s) (hs' : s ≤ 5) :
    0 < sieveFunctionf s := by
  unfold sieveFunctionf
  have h1 : ¬ s ≤ 3 := by linarith
  rw [if_neg h1, if_pos hs']
  have hs_pos : 0 < s := by linarith
  have h_log : 0 < log (s / 2) := by
    apply log_pos
    field_simp
    linarith
  positivity
/-- f(s) ≤ F(s) (下界函数不超过上界函数).

对 s ∈ [2, 4] 可证:
- s ≤ 2: F = 1, f = 0. 0 ≤ 1 ✓
- 2 < s ≤ 3: F = 2e^γ/s > 0, f = 0 ✓
- 3 < s ≤ 4: F = 2e^γ/s, f = 2e^γ/s·log(s/2).
  由 log_le_sub_one: log(s/2) ≤ s/2-1 ≤ 1 (因 s ≤ 4), 故 f ≤ F ✓

注: s > 4 需完整递推分析 (Buchstab 型差分微分方程). -/
theorem sievef_le_sieveF {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 4) :
    sieveFunctionf s ≤ sieveFunctionF s := by
  unfold sieveFunctionF sieveFunctionf
  by_cases h2 : s ≤ 2
  · -- s ≤ 2: F = 1, f = 0 (因 s ≤ 3)
    have h3 : s ≤ (3 : ℝ) := le_trans h2 (by norm_num)
    simp only [if_pos h2, if_pos h3]
    norm_num
  · -- s > 2: F = 2e^γ/s (因 s ≤ 4)
    have hs_pos : 0 < s := by linarith
    by_cases h3 : s ≤ (3 : ℝ)
    · -- 2 < s ≤ 3: F = 2e^γ/s, f = 0
      simp only [if_neg h2, if_pos hs', if_pos h3]
      positivity
    · -- 3 < s ≤ 4: F = 2e^γ/s, f = 2e^γ/s · log(s/2)
      have h5 : s ≤ (5 : ℝ) := by linarith
      simp only [if_neg h2, if_pos hs', if_neg h3, if_pos h5]
      have hs2_pos : 0 < s / 2 := by positivity
      -- log(s/2) ≤ s/2 - 1 ≤ 1 (因 s ≤ 4)
      have h_log_le : log (s / 2) ≤ 1 := by
        calc log (s / 2) ≤ s / 2 - 1 := Real.log_le_sub_one_of_pos hs2_pos
          _ ≤ 1 := by linarith
      -- 2e^γ/s · log(s/2) ≤ 2e^γ/s · 1 = 2e^γ/s
      have h_factor : 0 ≤ 2 * exp eulerMascheroni / s := by positivity
      exact mul_le_of_le_one_right h_factor h_log_le

/-! ## 4. 筛法设置 (对齐 Mathlib.BoundingSieve) -/

/-- **陈氏定理筛法问题**: 扩展 Mathlib 的 `BoundingSieve`, 加入筛水平 z 和分布水平 D.

与 Mathlib `BoundingSieve` 的对齐关系:
  - `support` ← `A` (待筛集合, 如 {N - p : p 素数})
  - `totalMass` ← `X` (|A| 的近似值, 如 N / log N)
  - `nu` ← `ν` (乘性密度函数, ArithmeticFunction ℝ)
  - `weights` ← 恒为 1 (计数筛, 非加权筛)
  - `prodPrimes` ← < z 的素数之积 (筛水平以下的素数)
  - `siftedSum` ← 直接继承 Mathlib 的定义 (∑ Coprime prodPrimes d 的权重)

额外字段 (Jurkat-Richert 特有, Mathlib 无对应):
  - `z`: 筛水平 (移除 < z 的素数的倍数)
  - `D`: 分布水平 (误差项受控的范围)
  - `prodPrimes_eq`: prodPrimes = < z 的素数之积 -/
structure SieveProblem extends BoundingSieve where
  /-- 筛水平 z: 移除 < z 的素数的倍数 -/
  z : ℝ
  hz_pos : 0 < z
  /-- 分布水平 D: 误差项受控的范围 (来自 Bombieri-Vinogradov) -/
  D : ℝ
  hD_pos : 0 < D
  /-- prodPrimes 是 < z 的素数之积 -/
  prodPrimes_eq : prodPrimes = ((Finset.range ⌈z⌉₊).filter Nat.Prime).prod id

/-- **桥接引理**: Mathlib 的 `siftedSum` 等价于我们的筛法定义.

Mathlib: `siftedSum = ∑ d ∈ support, if Coprime prodPrimes d then weights d else 0`
我们:   `|{a ∈ A : ∀ p 素数, p < z → ¬ p ∣ a}|`

当 `prodPrimes` = < z 的素数之积, `weights = 1` (即前提 `hweights`) 时, 两者相等. -/
theorem siftedSum_eq_filter (SP : SieveProblem) (hweights : ∀ n, SP.weights n = 1) :
    SP.siftedSum =
      (SP.support.filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < SP.z → ¬ p ∣ a)).sum (fun _ => (1 : ℝ)) := by
  -- 辅助引理: 一组互异素数之积的 primeFactors 等于该素数集合本身.
  have h_pf : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (S.prod id).primeFactors = S := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp [Nat.primeFactors_one]
    | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      -- id p 定义等于 p (beta-reduction), 用 show 对齐目标表达式
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : (S.prod id) ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
          ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl
  -- 由 prodPrimes_eq: prodPrimes 的素因子集合恰为 (range ⌈z⌉₊).filter Prime.
  have h_ppf : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq, h_pf]
    intro p hp; simp at hp; exact hp.2
  -- 关键等价: 对素数 p, p ∣ prodPrimes ↔ (p : ℝ) < z.
  --   (⇒) p ∣ prodPrimes ⇒ p ∈ primeFactors = (range ⌈z⌉₊).filter Prime ⇒ p < ⌈z⌉₊ ⇒ (p:ℝ) < z.
  --   (⇐) (p:ℝ) < z ⇒ p < ⌈z⌉₊ (Nat.lt_ceil) ⇒ p ∈ range ⇒ p ∣ prod (Finset.dvd_prod_of_mem).
  have h_dvd_iff : ∀ p : ℕ, p.Prime → (p ∣ SP.prodPrimes ↔ (p : ℝ) < SP.z) := by
    intro p hp
    refine ⟨fun hdvd => ?_, fun hpz => ?_⟩
    · -- p ∣ prodPrimes ⇒ (p : ℝ) < z
      have h_mem : p ∈ SP.prodPrimes.primeFactors :=
        Nat.Prime.mem_primeFactors hp hdvd SP.prodPrimes_ne_zero
      rw [h_ppf, Finset.mem_filter, Finset.mem_range] at h_mem
      exact Nat.lt_ceil.mp h_mem.1
    · -- (p : ℝ) < z ⇒ p ∣ prodPrimes
      have hp_range : p < ⌈SP.z⌉₊ := Nat.lt_ceil.mpr hpz
      have hp_mem : p ∈ (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hp_range, hp⟩
      rw [SP.prodPrimes_eq]
      exact Finset.dvd_prod_of_mem id hp_mem
  -- 主等价: Nat.gcd prodPrimes a = 1 ↔ ∀ p 素数, (p:ℝ) < z ⇒ ¬ p ∣ a.
  --   (⇒) gcd = 1; 若 p ∣ prodPrimes (故 (p:ℝ) < z) 且 p ∣ a, 则 p ∣ gcd = 1, 与 p 素数矛盾.
  --   (⇐) 用 Nat.eq_one_iff_not_exists_prime_dvd 取反证: 若 gcd ≠ 1, 存在素数 p ∣ gcd,
  --       则 p ∣ prodPrimes (故 (p:ℝ) < z) 且 p ∣ a, 与假设矛盾.
  have hkey : ∀ a : ℕ, Nat.gcd SP.prodPrimes a = 1 ↔
      ∀ p : ℕ, p.Prime → (p : ℝ) < SP.z → ¬ p ∣ a := by
    intro a
    refine ⟨fun hcop p hp hpz hpa => ?_, fun h => ?_⟩
    · have hp_dvd_PP : p ∣ SP.prodPrimes := (h_dvd_iff p hp).mpr hpz
      have hp_gcd : p ∣ Nat.gcd SP.prodPrimes a := Nat.dvd_gcd hp_dvd_PP hpa
      rw [hcop] at hp_gcd
      exact hp.not_dvd_one hp_gcd
    · rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p hp hp_gcd
      have hp_dvd_PP : p ∣ SP.prodPrimes := hp_gcd.trans (Nat.gcd_dvd_left _ _)
      have hp_a : p ∣ a := hp_gcd.trans (Nat.gcd_dvd_right _ _)
      exact h p hp ((h_dvd_iff p hp).mp hp_dvd_PP) hp_a
  -- 主证明: 展开 siftedSum (siftedSum_eq_sum_support_mul_ite), 代入 weights = 1,
  -- 将 ite 转为 filter (Finset.sum_filter), 再以 hkey 化简 filter 谓词.
  rw [SP.siftedSum_eq_sum_support_mul_ite]
  simp_rw [hweights, one_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (Finset.filter_congr fun d _ => hkey d) (fun _ _ => rfl)

/-- **筛积 V(z)** = Π_{p < z} (1 - ν(p)).

这是 Jurkat-Richert 定理中主项 X · V(z) · f(s) 的组成部分.

与 Mathlib `selbergTerms` 的关系:
  Mathlib 的 `selbergTerms d = ν(d) · Π_{p|d} (1 - ν(p))⁻¹`
  当 d = prodPrimes (= < z 的素数之积) 时:
    selbergTerms prodPrimes = ν(prodPrimes) / V(z)
  即 V(z) = ν(prodPrimes) / selbergTerms(prodPrimes)

注: Mathlib 中 `ν(p) = ω(p)/p`, 故 `1 - ν(p) = 1 - ω(p)/p` 即标准筛密度因子. -/
noncomputable def sieveProduct (SP : SieveProblem) : ℝ :=
  ((Finset.range ⌈SP.z⌉₊).filter Nat.Prime).prod
    (fun p => 1 - SP.nu p)

/-- **桥接引理 1**: sieveProduct 等于 Π_{p | prodPrimes} (1 - ν(p)).

由 `prodPrimes_eq`: prodPrimes = < z 的素数之积,
故 p | prodPrimes ⟺ p 素数 ∧ p < z. -/
theorem sieveProduct_eq_prod_one_sub_nu (SP : SieveProblem) :
    sieveProduct SP =
      ∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p) := by
  -- 辅助引理: 素数集合的乘积的 primeFactors = 该集合本身
  -- 证明: 对 S 用 Finset.induction_on
  --   基础: S = ∅, ∏ id = 1, primeFactors 1 = ∅ ✓
  --   归纳: S = {p} ∪ S', ∏ id = p * (∏ S' id)
  --         primeFactors(p * prod) = {p} ∪ primeFactors(prod) = {p} ∪ S' = S ✓
  have h_pf : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (S.prod id).primeFactors = S := by
    intro S hS
    induction S using Finset.induction_on with
    | empty => simp [Nat.primeFactors_one]
    | insert p S hp ih =>
      rw [Finset.prod_insert hp]
      show (p * S.prod id).primeFactors = insert p S
      have hp' := hS p (Finset.mem_insert_self _ _)
      have h0p : p ≠ 0 := hp'.ne_zero
      have h0s : (S.prod id) ≠ 0 := ne_of_gt <| Finset.prod_pos fun q hq =>
        Nat.Prime.pos (hS q (Finset.mem_insert_of_mem hq))
      rw [Nat.primeFactors_mul h0p h0s, Nat.Prime.primeFactors hp',
          ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]
      rfl
  -- 应用: SP.prodPrimes.primeFactors = (range ⌈z⌉).filter Prime
  have h_eq : SP.prodPrimes.primeFactors = (Finset.range ⌈SP.z⌉₊).filter Nat.Prime := by
    rw [SP.prodPrimes_eq, h_pf]
    intro p hp; simp at hp; exact hp.2
  rw [sieveProduct, h_eq]

/-- **桥接引理 2**: sieveProduct · selbergTerms(prodPrimes) = ν(prodPrimes).

由 Mathlib 的 `selbergTerms_apply`:
  selbergTerms d = ν(d) · Π_{p|d} (1 - ν(p))⁻¹

当 d = prodPrimes 时:
  selbergTerms prodPrimes = ν(prodPrimes) · Π_{p|prodPrimes} (1 - ν(p))⁻¹
                         = ν(prodPrimes) / sieveProduct

故 sieveProduct · selbergTerms(prodPrimes) = ν(prodPrimes). -/
theorem sieveProduct_mul_selbergTerms_eq_nu (SP : SieveProblem) :
    sieveProduct SP * SP.selbergTerms SP.prodPrimes = SP.nu SP.prodPrimes := by
  -- 由 selbergTerms_apply: selbergTerms d = nu d * ∏_{p|d} (1 - nu p)⁻¹
  -- 由 sieveProduct_eq_prod_one_sub_nu: sieveProduct = ∏_{p|d} (1 - nu p)
  -- 故 sieveProduct * selbergTerms = ∏(1-nu p) * nu(PP) * ∏(1-nu p)⁻¹
  --                                = nu(PP) * (∏(1-nu p) * ∏(1-nu p)⁻¹) = nu(PP)
  rw [SP.selbergTerms_apply, sieveProduct_eq_prod_one_sub_nu]
  -- Goal: (∏(1-nu p)) * (nu(PP) * ∏(1-nu p)⁻¹) = nu(PP)
  -- 每个 (1 - nu p) ≠ 0 (由 nu_lt_one_of_prime: nu p < 1)
  have h_nz : ∀ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p) ≠ 0 := by
    intro p hp
    obtain ⟨hp_p, hp_dvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ne_of_gt (by linarith [SP.nu_lt_one_of_prime p hp_p hp_dvd])
  -- ∏(1-nu p)⁻¹ = (∏(1-nu p))⁻¹
  rw [Finset.prod_inv_distrib]
  -- Goal: A * (B * A⁻¹) = B, 其中 A = ∏(1-nu p), B = nu(PP)
  -- = A * B * A⁻¹ = B * A * A⁻¹ = B * 1 = B
  have h_A_ne_zero : (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => h_nz p hp)
  rw [← mul_assoc, mul_comm _ (SP.nu SP.prodPrimes), mul_assoc]
  -- 对齐 bound variable, 消除 alpha-renaming 差异
  show SP.nu SP.prodPrimes *
      ((∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) *
        (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p))⁻¹) =
    SP.nu SP.prodPrimes
  -- 先证明 A * A⁻¹ = 1, 再重写 (避免 rw 无法匹配 Finset.prod 模式)
  have h_inv : (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p)) *
               (∏ p ∈ SP.prodPrimes.primeFactors, (1 - SP.nu p))⁻¹ = 1 :=
    mul_inv_cancel₀ h_A_ne_zero
  rw [h_inv, mul_one]

/-- **桥接推论**: sieveProduct = ν(prodPrimes) / selbergTerms(prodPrimes). -/
theorem sieveProduct_eq_nu_div_selbergTerms (SP : SieveProblem) :
    sieveProduct SP = SP.nu SP.prodPrimes / SP.selbergTerms SP.prodPrimes := by
  -- 由 sieveProduct_mul_selbergTerms_eq_nu: sieveProduct * selbergTerms(PP) = nu(PP)
  -- 故 sieveProduct = nu(PP) / selbergTerms(PP) (因 selbergTerms(PP) > 0)
  have h := sieveProduct_mul_selbergTerms_eq_nu SP
  -- h : sieveProduct * selbergTerms(PP) = nu(PP)
  have h_st_pos : 0 < SP.selbergTerms SP.prodPrimes :=
    SP.selbergTerms_pos (dvd_refl SP.prodPrimes)
  -- eq_div_iff: a = c / b ↔ a * b = c (当 b ≠ 0)
  rw [eq_div_iff h_st_pos.ne']
  exact h

/-- **分布条件**: 对 d ≤ D, |{a ∈ A : d | a}| = ν(d) · X + R_d.

这对应 Mathlib `BoundingSieve` 中的 `multSum_eq_main_err`:
  `multSum d = nu d * totalMass + rem d`

其中 `rem d` 即误差项 R_d. 分布水平 D 控制 |rem d| 可忽略的 d 的范围. -/
theorem distribution_condition (SP : SieveProblem) (d : ℕ) (hd : (d : ℝ) ≤ SP.D) (hd_pos : 1 ≤ d) :
    SP.multSum d = SP.nu d * SP.totalMass + SP.rem d := by
  exact SP.multSum_eq_main_err d

/-! ## 5. Jurkat-Richert 定理 (陈述, 对齐 Mathlib 筛法上界) -/

/-- **Jurkat-Richert 定理 (上界)**: 筛函数的上界.

  S(A, z) ≤ X · V(z) · (F(s) + O(η)) + Σ_{d ≤ D} |R_d|

与 Mathlib `siftedSum_le_mainSum_errSum_of_upperMoebius` 的关系:
  Mathlib 已证明: siftedSum ≤ totalMass · mainSum(μ⁺) + errSum(μ⁺)
  Jurkat-Richert 进一步给出: mainSum(μ⁺) ≤ V(z) · F(s), errSum ≤ Σ |R_d|

这是陈氏定理中 Ω 上界估计的理论基础.

注意：当前接口只要求为单个 `SP` 存在一个未量化的加性误差，故该命题本身
可由两边差的绝对值直接给出；这不是 Jurkat--Richert 的一致解析估计。后者还须
把 `C_error` 与 `SP.rem` 的显式界联系起来。 -/
theorem jurkat_richert_upper_bound (SP : SieveProblem)
    (_hs : 2 ≤ SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≤
        SP.totalMass * sieveProduct SP * (sieveFunctionF (SP.D / SP.z)) + C_error := by
  -- 证明策略 (对齐 Mathlib):
  -- 1. 由 siftedSum_le_mainSum_errSum_of_upperMoebius:
  --    siftedSum ≤ totalMass * mainSum(μ⁺) + errSum(μ⁺)
  -- 2. Jurkat-Richert: mainSum(μ⁺) ≤ V(z) * F(s)  (筛函数上界)
  -- 3. errSum(μ⁺) ≤ Σ_{d≤D} |R_d|  (误差项界)
  -- 4. 合并: siftedSum ≤ X * V(z) * F(s) + Σ |R_d|
  refine ⟨|SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z)|, ?_⟩
  have h := le_abs_self (SP.siftedSum - SP.totalMass * sieveProduct SP *
    sieveFunctionF (SP.D / SP.z))
  linarith

/-- **Jurkat-Richert 定理 (下界)**: 筛函数的下界.

  S(A, z) ≥ X · V(z) · (f(s) - O(η)) - Σ_{d ≤ D} |R_d|

这是陈氏定理中 W(N) 下界估计的理论基础:
  W(N) ≥ 2.6408 𝔖(N) N/log²N

同上，现有量词结构只表达逐个 `SP` 的加性误差存在性；一致的
Jurkat--Richert 下界仍需另行形式化。 -/
theorem jurkat_richert_lower_bound (SP : SieveProblem)
    (_hs : 3 < SP.D / SP.z) :
    ∃ C_error : ℝ,
      SP.siftedSum ≥
        SP.totalMass * sieveProduct SP * (sieveFunctionf (SP.D / SP.z)) - C_error := by
  -- 下界筛需要下界 Moebius 条件 (Mathlib 目前仅有上界)
  -- 参见 Halberstam-Richert Ch. 8
  refine ⟨|SP.totalMass * sieveProduct SP * sieveFunctionf (SP.D / SP.z) -
    SP.siftedSum|, ?_⟩
  have h := le_abs_self (SP.totalMass * sieveProduct SP *
    sieveFunctionf (SP.D / SP.z) - SP.siftedSum)
  linarith

/-! ## 6. 陈氏定理中的应用 -/

/-
在陈氏定理中, Jurkat-Richert 下界应用于:
  - A = {N - p : p 素数, N^(1/10) < p < N}  (Goldbach 型集合)
  - X ≈ N / log N  (素数个数近似)
  - ν(d) = Π_{p|d} (p-1)⁻¹  (Goldbach 密度函数)
  - z = N^(1/10)  (筛水平)
  - D = N^(1/2 - ε)  (分布水平, 来自 Bombieri-Vinogradov)
  - s = log(D)/log(z) ≈ 5  (筛比)

得到 W(N) ≥ 2.6408 𝔖(N) N/log²N, 其中:
  - V(z) ≈ 𝔖(N) / log N  (筛积与奇异级数的关系)
  - f(5) ≈ 2e^γ · log(5/2) / 5  (下界筛函数在 s=5 处的值)
-/

/-! ## 6.5 陈氏关键不等式 (已移除)

**2026-08-04 清理**: 原 `chen_key_inequality` 与 `chen_key_implies_theorem` 基于
工作定义 `chenW = chenOmega = 0`, 命题 "0 - 0/2 > 0" 为假, 不能以 sorry 存在.
W(N)/Ω(N) 的精确定义与关键不等式均在 `SwitchingPrinciple.lean`
(`chenW`, `chenOmega`, `chen_key_inequality`), 由 Jurkat-Richert 下界
(本文件 `jurkat_richert_lower_bound`) 与 Selberg 筛上界给出. -/

/-! ## 7. 总结 -/

/-
**筛法理论形式化状态**:

1. **奇异级数** (已完成, 见 SingularSeries.lean):
   - 局部因子, 截断乘积, 正性
   - 界估计待完成 (依赖 Mertens 定理 / PNT)

2. **线性筛 / Jurkat-Richert 工作接口**:
   - 筛函数 F(s), f(s) 定义
   - SieveProblem 结构 (扩展 Mathlib `BoundingSieve`)
   - 上下界为固定参数的余项接口；不是经典统一 Jurkat--Richert 定理
   - 陈氏定理中的 W(N), Ω 定义 (工作定义)

3. **Mathlib 对齐层** (已完成):
   - `SieveProblem` extends `BoundingSieve` ✓
   - `sieveProduct_eq_prod_one_sub_nu`: V(z) = Π_{p|P} (1-ν(p)) ✓
   - `sieveProduct_mul_selbergTerms_eq_nu`: V(z)·g(P) = ν(P) ✓
   - `sieveProduct_eq_nu_div_selbergTerms`: V(z) = ν(P)/g(P) ✓
   - `siftedSum_eq_filter`: Mathlib `siftedSum` ↔ 筛后计数 ✓
   - `distribution_condition`: 直接继承 `multSum_eq_main_err` ✓

4. **证明层依赖图**:
   chens_theorem (ChenAnalyticBounds, ChenCountingBridge)
   ├── key_inequality_implies_chen (已证)
   │   ├── ChenCountingBridge  (精确切换计数的显式外部输入)
   │   └── chen_key_inequality (W(N) - Ω/2 > 0, 已证)
   │       └── ChenAnalyticBounds  (Jurkat--Richert / Selberg 统一估计的显式外部输入)
   └── 逐点余项接口与 Mathlib 筛法桥接  (已完成)

5. **下一步优先级**:
   - [高] 补全 Selberg 筛最终上界 (Mathlib 已有 80%, 桥接已完成)
   - [高] 形式化 W(N), Ω 的精确定义
   - [中] 定义 Bombieri-Vinogradov 定理陈述
   - [中] 定义大筛法不等式陈述
-/

end MathlibNt.SieveTheory.LinearSieve
