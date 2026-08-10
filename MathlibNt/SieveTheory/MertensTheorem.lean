/-
! # MathlibNt.SieveTheory.MertensTheorem

## Mertens 定理 (Mertens' Theorems)

Mertens 定理是陈氏定理证明中筛积 V(z) 估计和奇异级数 𝔖(N) 界估计的基础.

**Mertens 第二定理**: 存在常数 B₁ 使得
  Σ_{p ≤ x} 1/p = log log x + B₁ + O(1/log x)

**Mertens 乘积公式**:
  Π_{p ≤ x} (1 - 1/p) ~ e^(-γ) / log x

其中 γ 为 Euler-Mascheroni 常数.

在陈氏定理中的应用:
  - V(z) = Π_{p < z, p ∤ N} (1 - ν(p)/p) ≈ 𝔖(N) · e^(-γ) / log z
  - 𝔖(N) 的有界性依赖于 Π_{p > 2} (1 - 1/(p-1)²) 的收敛性 (孪生素数常数)

参考:
  - Chen, J.R. (1973), Sci. Sinica 16, 157-176
  - Liu, Z. (2022), arXiv:2203.07871, Lemma 1
  - Nathanson, "Additive Number Theory", GTM 164
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import AnalyticNumberTheory
import MathlibNt.SieveTheory.SingularSeries

namespace MathlibNt.SieveTheory.MertensTheorem

open Real Finset

/-! ## 1. Mertens 第二定理 (陈述) -/

/-- 素数倒数和: Σ_{p ≤ x} 1/p -/
noncomputable def primeReciprocalSum (x : ℕ) : ℝ :=
  ((range (x + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ))

/-- **Mertens 第二定理**: 存在常数 B₁ 使得
  Σ_{p ≤ x} 1/p = log log x + B₁ + O(1/log x)

这是陈氏定理证明中 Lemma 1 的理论基础.
一条可采用的证明路线是 PNT 加 Abel 分部求和；这不是必要条件，
Mertens 定理也有初等证明。 -/
theorem mertens_second_theorem :
    ∃ B₁ : ℝ, ∃ C : ℝ,
      ∀ x : ℕ, 2 ≤ x →
        |primeReciprocalSum x - (log (log x) + B₁)| ≤ C / log x := by
  -- 计划路线：由 PNT: π(x) ~ x/log x 加 Abel 分部求和导出。
  -- 这只是充分路线；也存在不使用 PNT 的初等证明。
  sorry

/-! ## 2. Mertens 乘积公式 (陈述) -/

/-- 素数乘积: Π_{p ≤ x} (1 - 1/p) -/
noncomputable def primeProduct (x : ℕ) : ℝ :=
  ((range (x + 1)).filter Nat.Prime).prod (fun p => 1 - 1 / (p : ℝ))

/-- **Mertens 乘积公式**: Π_{p ≤ x} (1 - 1/p) ~ e^(-γ) / log x

即存在常数 C 使得 |Π_{p ≤ x} (1 - 1/p) - e^(-γ) / log x| ≤ C / (log x)²

这是筛积 V(z) 估计的核心工具. -/
theorem mertens_product_formula :
    ∃ C : ℝ,
      ∀ x : ℕ, 2 ≤ x →
        |primeProduct x - exp (-eulerMascheroniConstant) / log x| ≤
          C / (log x) ^ 2 := by
  -- 证明依赖 Mertens 第二定理及对数变换
  sorry

/-- 一般局部对数修正: 对 0 < t ≤ 1/2, |log(1 - t) + t| ≤ 2t².

由 `log x ≤ x - 1` 给出上界 log(1-t) ≤ -t, 由 `log(1/(1-t)) ≤ t/(1-t)`
(即 `log(1-t) ≥ -t/(1-t)`) 结合 t ≤ 1/2 给出下界. -/
private lemma log_one_sub_bound {t : ℝ} (ht0 : 0 < t) (htle : t ≤ 1 / 2) :
    |log (1 - t) + t| ≤ 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hne : 1 - t ≠ 0 := ne_of_gt hpos
  -- 上界: log(1 - t) ≤ -t
  have hub : log (1 - t) ≤ -t := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  -- 下界: log(1 - t) ≥ -t - 2t²
  have hlb : -t - 2 * t ^ 2 ≤ log (1 - t) := by
    have hrec : 0 < 1 / (1 - t) := by positivity
    have hle := Real.log_le_sub_one_of_pos hrec
    -- log(1/(1-t)) ≤ t/(1-t), 且 log(1/(1-t)) = -log(1-t)
    have hloginv : log (1 / (1 - t)) = -log (1 - t) := by
      rw [one_div, Real.log_inv]
    have hle' : -log (1 - t) ≤ t / (1 - t) := by
      have hstep : 1 / (1 - t) - 1 = t / (1 - t) := by
        field_simp [hne]
        ring
      rwa [hloginv, hstep] at hle
    have hsame : -(t / (1 - t)) = -t / (1 - t) := by
      rw [div_eq_mul_inv, ← neg_mul, ← div_eq_mul_inv]
    have hge0 : -t / (1 - t) ≤ log (1 - t) := by
      have h := neg_le_neg hle'
      simpa [hsame] using h
    -- 1/(1-t) ≤ 1 + 2t (当 t ≤ 1/2)
    have hrec2 : 1 / (1 - t) ≤ 1 + 2 * t := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hmul : t / (1 - t) ≤ t * (1 + 2 * t) := by
      have hx := mul_le_mul_of_nonneg_left hrec2 (le_of_lt ht0)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hx
    have hneg : -t - 2 * t ^ 2 ≤ -t / (1 - t) := by
      calc -t - 2 * t ^ 2 ≤ -t * (1 + 2 * t) := by
            have hx : t * (1 + 2 * t) = t + 2 * t ^ 2 := by ring
            linarith
        _ ≤ -t / (1 - t) := by
          have h := neg_le_neg_iff.mpr hmul
          have hsame1 : -(t * (1 + 2 * t)) = -t * (1 + 2 * t) := by
            rw [← neg_mul]
          rwa [hsame1, hsame] at h
    linarith
  -- 组合: |log(1-t) + t| ≤ 2t²
  have hge : -2 * t ^ 2 ≤ log (1 - t) + t := by nlinarith [hlb]
  have hle0 : log (1 - t) + t ≤ 0 := by linarith [hub]
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- 每个素数 p ≥ 2 的局部对数修正: |log(1 - 1/p) + 1/p| ≤ 2/p². -/
private lemma log_one_sub_prime_bound {p : ℕ} (hp : p.Prime) :
    |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
  let t : ℝ := 1 / (p : ℝ)
  have ht0 : 0 < t := by
    unfold t
    exact div_pos one_pos (by exact_mod_cast hp.pos)
  have htle : t ≤ 1 / 2 := by
    unfold t
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hp.two_le)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsubst : |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| = |log (1 - t) + t| := by
    simp [t]
  have hrhs : 2 * t ^ 2 = 2 / (p : ℝ) ^ 2 := by
    unfold t
    field_simp [hp0]
  rw [hsubst, ← hrhs]
  exact log_one_sub_bound ht0 htle

/-- **Mertens 乘积公式 (阶形式)**: primeProduct x = Θ(1/log x), 即存在常数
  c₁, c₂ > 0 使得 c₁/log x ≤ Π_{p ≤ x}(1 - 1/p) ≤ c₂/log x.

这是 `mertens_product_formula` (精确常数 e^{-γ}) 的弱化版本: 由 Mertens 第二定理
(-log Π = Σ 1/p + O(1)) 直接推出, 不需要 Euler-Mascheroni 常数恒等式.
证明要点:
  1. log Π = Σ log(1 - 1/p), 且 |log(1 - 1/p) + 1/p| ≤ 2/p²;
  2. 故 -log Π = Σ 1/p + E(x), 其中 |E(x)| ≤ Σ 2/p² ≤ 2·Σ_{n} 1/n² < ∞;
  3. 由 Mertens 第二定理, Σ 1/p = log log x + B₁ + O(1/log x);
  4. Π = exp(-B₁ - δ - E)/log x, 其中 |δ|, |E| 有界, 故 Π = Θ(1/log x). -/
theorem primeProduct_asymptotic_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ x : ℕ, 2 ≤ x →
      c₁ / log x ≤ primeProduct x ∧ primeProduct x ≤ c₂ / log x := by
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- Σ_{n ≥ 1} 1/n² 收敛, 故素数部分 2/p² 之和有界
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  have hbound : ∃ T : ℝ, 0 ≤ T ∧
      ∀ s : Finset ℕ, s.sum (fun p => 2 / (p : ℝ) ^ 2) ≤ T := by
    refine ⟨2 * ∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), ?_, ?_⟩
    · exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by positivity))
    · intro s
      calc
        s.sum (fun p => 2 / (p : ℝ) ^ 2) = 2 * s.sum (fun p => 1 / (p : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
          congr 1
          ext p
          ring
        _ ≤ 2 * (∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (Summable.sum_le_tsum s (fun n _hn => by positivity) hsum2) (by norm_num)
  obtain ⟨T, hT0, hbound⟩ := hbound
  -- 局部对数修正 (每个素数)
  have hlocal : ∀ p : ℕ, p.Prime →
      |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 :=
    by
    intro p hp
    exact log_one_sub_prime_bound hp
  refine ⟨exp (-B₁ - T - C₁ / log 2), exp (-B₁ + T + C₁ / log 2), ?_, ?_⟩
  · exact Real.exp_pos _
  · intro x hx
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
    have hlogxpos : 0 < log x := Real.log_pos hx1
    have hprod_pos : 0 < primeProduct x := by
      unfold primeProduct
      exact Finset.prod_pos (fun p hp => by
        have hp' : p.Prime := (mem_filter.mp hp).2
        have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
        have hdiv : 1 / (p : ℝ) < 1 := by
          rw [div_lt_iff₀ (by positivity : 0 < (p : ℝ))]
          nlinarith
        linarith)
    -- log Π = Σ log(1 - 1/p)
    have hlogprod : log (primeProduct x) =
        ((range (x + 1)).filter Nat.Prime).sum (fun p => log (1 - 1 / (p : ℝ))) := by
      unfold primeProduct
      rw [Real.log_prod]
      intro p hp
      have hp' : p.Prime := (mem_filter.mp hp).2
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
      have hdiv : 1 / (p : ℝ) < 1 := by
        rw [div_lt_iff₀ (by positivity : 0 < (p : ℝ))]
        nlinarith
      linarith
    -- E(x) := Σ_{p ≤ x} (-log(1-1/p) - 1/p), |E(x)| ≤ T
    let E : ℝ := ((range (x + 1)).filter Nat.Prime).sum
      (fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))
    have hneglog : -log (primeProduct x) = primeReciprocalSum x + E := by
      unfold E primeReciprocalSum
      rw [hlogprod]
      rw [← Finset.sum_neg_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have hEabs : |E| ≤ T := by
      unfold E
      calc
        |((range (x + 1)).filter Nat.Prime).sum
            (fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))|
            ≤ ((range (x + 1)).filter Nat.Prime).sum
              (fun p => |(-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ))|) :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ((range (x + 1)).filter Nat.Prime).sum (fun p => 2 / (p : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2
            have h := hlocal p hp'
            rw [← abs_neg] at h
            rwa [show (-(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
                -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) by ring] at h
        _ ≤ T := hbound _
    -- δ := S(x) - (log log x + B₁), |δ| ≤ C₁/log x
    let δ : ℝ := primeReciprocalSum x - (log (log x) + B₁)
    have hδ_le : |δ| ≤ C₁ / log x := by
      simpa [δ] using (hM x hx)
    have hδ_le2 : |δ| ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log x :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < x))).2 (by exact_mod_cast hx)
      exact le_trans hδ_le (div_le_div_of_nonneg_left hC1 hlog2 hlelog)
    -- Π = exp(-B₁ - δ - E) / log x
    have hlogP : log (primeProduct x) = -(log (log x) + B₁ + δ + E) := by
      have h1 : -log (primeProduct x) = log (log x) + B₁ + δ + E := by
        rw [hneglog]
        unfold δ
        ring
      linarith
    have hP' : primeProduct x = exp (-B₁ - δ - E) / log x := by
      rw [← Real.exp_log hprod_pos]
      have hsplit : -(log (log x) + B₁ + δ + E) = -log (log x) + (-B₁ - δ - E) := by ring
      rw [hlogP, hsplit, Real.exp_add, Real.exp_neg, Real.exp_log (by positivity : 0 < log x)]
      rw [div_eq_mul_inv]
      ring
    -- 界: exp(-B₁ - T - C₁/log2) ≤ exp(-B₁-δ-E) ≤ exp(-B₁ + T + C₁/log2)
    have hlower : -B₁ - T - C₁ / log 2 ≤ -B₁ - δ - E := by
      have hδ : δ ≤ |δ| := le_abs_self _
      have hE : E ≤ |E| := le_abs_self _
      nlinarith [hδ, hE, hδ_le2, hEabs, hT0]
    have hupper : -B₁ - δ - E ≤ -B₁ + T + C₁ / log 2 := by
      have hδ' : -δ ≤ |δ| := neg_le_abs δ
      have hE' : -E ≤ |E| := neg_le_abs E
      nlinarith [hδ', hE', hδ_le2, hEabs, hT0]
    have hP_low : exp (-B₁ - T - C₁ / log 2) ≤ exp (-B₁ - δ - E) :=
      Real.exp_le_exp.mpr hlower
    have hP_up : exp (-B₁ - δ - E) ≤ exp (-B₁ + T + C₁ / log 2) :=
      Real.exp_le_exp.mpr hupper
    rw [hP']
    constructor
    · exact div_le_div_of_nonneg_right hP_low (le_of_lt hlogxpos)
    · exact div_le_div_of_nonneg_right hP_up (le_of_lt hlogxpos)

/-! ## 3. 应用: 素数倒数和的有界性 (Lemma 1) -/

/-- `primeReciprocalSum` 单调: x ≤ y ⟹ Σ_{p ≤ x} 1/p ≤ Σ_{p ≤ y} 1/p. -/
private lemma primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro a b hab
  unfold primeReciprocalSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hfn
  · intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p _hp _hnot
    exact div_nonneg zero_le_one (by positivity)

/-- 当 u ≤ 1 时 S(u) = 0 (无素数 ≤ 1). -/
private lemma primeReciprocalSum_zero_of_le_one {u : ℕ} (hu : u ≤ 1) :
    primeReciprocalSum u = 0 := by
  unfold primeReciprocalSum
  interval_cases u
  · rw [Finset.sum_filter]
    norm_num [Finset.sum_range_succ]
  · rw [Finset.sum_filter]
    norm_num [Finset.sum_range_succ, Nat.not_prime_one]

/-- **Lemma 1 (Liu 2022)**: 对固定 0 < α < β, 和 Σ_{x^α < p ≤ x^β} 1/p 有界.

证明: 由 Mertens 第二定理,
  Σ_{x^α < p ≤ x^β} 1/p = (log log x^β + B₁ + O(1/log x)) - (log log x^α + B₁ + O(1/log x))
                       = log(β/α) + O(1/log x)

故该和有界. -/
theorem prime_reciprocal_sum_bounded (α β : ℝ) (hα : 0 < α) (_hβ : α < β) :
    ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
      |((range (x + 1)).filter (fun p => Nat.Prime p ∧
        ((x : ℝ) ^ α < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ β))).sum
        (fun p => 1 / (p : ℝ))| ≤ C := by
  obtain ⟨_B₁, C₁, hM⟩ := mertens_second_theorem
  -- C₁ ≥ 0 (由 x = 2 处的界推出)
  have hC1 : 0 ≤ C₁ := by
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- x₀: 当 x^α < 2 时 x ≤ x₀; K: log(2/α) 与 0 的较大者
  let x₀ : ℕ := ⌊(2 : ℝ) ^ (1 / α)⌋₊
  let K : ℝ := max (log (2 / α)) 0
  refine ⟨max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2), ?_⟩
  intro x hx
  let T : Finset ℕ := (range (x + 1)).filter (fun p => Nat.Prime p ∧
    ((x : ℝ) ^ α < (p : ℝ) ∧ (p : ℝ) ≤ (x : ℝ) ^ β))
  let U : Finset ℕ := (range (x + 1)).filter (fun p => Nat.Prime p ∧
    (x : ℝ) ^ α < (p : ℝ))
  let u : ℕ := ⌊(x : ℝ) ^ α⌋₊
  have hxα0 : 0 ≤ (x : ℝ) ^ α :=
    Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ x)) α
  -- T ⊆ U: 丢掉 β 条件 (p ≤ x^β 蕴含于 p ≤ x 或由子集论证)
  have hTsub : T ⊆ U := by
    intro p hp
    simp only [T, U, mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hTnonneg : 0 ≤ T.sum (fun p => 1 / (p : ℝ)) := by
    exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
  -- 核心估计: U 的和 ≤ max (S x₀) (K + 2C₁/log 2)
  have hUbound : U.sum (fun p => 1 / (p : ℝ)) ≤
      max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := by
    by_cases hux : u ≤ x
    · -- U = {p ≤ x 素数} \ {p ≤ u 素数}, 故 U.sum = S x - S u
      have hUeq : U.sum (fun p => 1 / (p : ℝ)) =
          primeReciprocalSum x - primeReciprocalSum u := by
        have hsub2 : (range (u + 1)).filter Nat.Prime ⊆
            (range (x + 1)).filter Nat.Prime := by
          intro p hp
          simp only [mem_filter, mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
        have hUsdiff : U = (range (x + 1)).filter Nat.Prime \
            (range (u + 1)).filter Nat.Prime := by
          ext p
          simp only [U, mem_filter, mem_sdiff, mem_range]
          constructor
          · rintro ⟨hpx, hpP, hxp⟩
            refine ⟨⟨hpx, hpP⟩, ?_⟩
            intro hpu
            have hu_lt_p' : ⌊(x : ℝ) ^ α⌋₊ < p := (Nat.floor_lt hxα0).mpr hxp
            have hu_lt_p : u < p := by
              simpa [u] using hu_lt_p'
            omega
          · rintro ⟨⟨hpx, hpP⟩, hnot⟩
            refine ⟨hpx, hpP, ?_⟩
            have hup : u < p := by
              by_contra h
              have hp_le_u : p ≤ u := le_of_not_gt h
              have hp_lt_u1 : p < u + 1 := by omega
              exact hnot ⟨hp_lt_u1, hpP⟩
            have hup' : ⌊(x : ℝ) ^ α⌋₊ < p := by simpa [u] using hup
            exact (Nat.floor_lt hxα0).mp hup'
        rw [hUsdiff]
        exact eq_sub_of_add_eq (Finset.sum_sdiff (s₁ := (range (u + 1)).filter Nat.Prime)
          (s₂ := (range (x + 1)).filter Nat.Prime) hsub2)
      by_cases hu2 : 2 ≤ u
      · -- 主情形: 两个 Mertens 界相减
        have hlogxpos : 0 < log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
        have hlogupos : 0 < log u := Real.log_pos (by exact_mod_cast (by omega : 1 < u))
        have hlog2pos : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have hMx := hM x hx
        have hMu := hM u hu2
        have hLx : primeReciprocalSum x - (log (log x) + _B₁) ≤ C₁ / log x :=
          (abs_le.mp hMx).2
        have hLu : (log (log u) + _B₁) - primeReciprocalSum u ≤ C₁ / log u := by
          have h := (abs_le.mp hMu).1
          linarith
        -- log x / log u ≤ 2 / α
        have hlogratio : log x / log u ≤ 2 / α := by
          have hα0 : α ≠ 0 := ne_of_gt hα
          by_cases hbig : (2 * log 2 / α) ≤ log x
          · -- log u ≥ α·log x - log 2 ≥ (α/2)·log x
            have hcross : 2 * log 2 ≤ α * log x := by
              have := (div_le_iff₀ hα).mp hbig
              nlinarith
            have hden : 0 < α * log x - log 2 := by
              nlinarith [hcross, hlog2pos]
            have hxα2 : (2 : ℝ) ≤ (x : ℝ) ^ α := by
              have hu_le : (u : ℝ) ≤ (x : ℝ) ^ α := Nat.floor_le hxα0
              have hu2' : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
              nlinarith
            have hfl : (x : ℝ) ^ α / 2 ≤ u := by
              have hlt := Nat.lt_floor_add_one (a := (x : ℝ) ^ α)
              nlinarith [hlt, hxα2]
            have hlogu_ge : α * log x - log 2 ≤ log u := by
              have hpos1 : 0 < (x : ℝ) ^ α / 2 := by positivity
              have hpos2 : 0 < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
              calc
                α * log x - log 2 = log ((x : ℝ) ^ α / 2) := by
                  rw [Real.log_div (by positivity : (x : ℝ) ^ α ≠ 0)
                    (by norm_num : (2 : ℝ) ≠ 0)]
                  rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < x))]
              _ ≤ log u := (Real.log_le_log_iff hpos1 hpos2).2 hfl
            have hfrac : log x / (α * log x - log 2) ≤ 2 / α := by
              rw [div_le_iff₀ hden]
              field_simp [hα0, hden.ne']
              nlinarith [hcross]
            calc
              log x / log u ≤ log x / (α * log x - log 2) :=
                div_le_div_of_nonneg_left (le_of_lt hlogxpos) hden hlogu_ge
              _ ≤ 2 / α := hfrac
          · -- log x < 2·log 2/α: log x/log u ≤ log x/log 2 ≤ 2/α
            have hlt : log x < 2 * log 2 / α := lt_of_not_ge hbig
            have hle1 : log x / log u ≤ log x / log 2 := by
              have hlog2_le_logu : log 2 ≤ log u :=
                (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
                  (by exact_mod_cast (by omega : 0 < u))).2 (by exact_mod_cast hu2)
              exact div_le_div_of_nonneg_left (le_of_lt hlogxpos) hlog2pos hlog2_le_logu
            have hcross2 : α * log x < 2 * log 2 := by
              have := (lt_div_iff₀ hα).mp hlt
              nlinarith
            have hle2 : log x / log 2 ≤ 2 / α := by
              rw [div_le_iff₀ hlog2pos]
              field_simp [hα0]
              nlinarith [hcross2]
            exact hle1.trans hle2
        -- log(log x) - log(log u) = log(log x / log u) ≤ log(2/α)
        have hLdiff : log (log x) - log (log u) ≤ log (2 / α) := by
          have hdivpos : 0 < log x / log u := div_pos hlogxpos hlogupos
          have h2a : 0 < 2 / α := div_pos (by norm_num) hα
          calc
            log (log x) - log (log u) = log (log x / log u) := by
              rw [← Real.log_div (ne_of_gt hlogxpos) (ne_of_gt hlogupos)]
          _ ≤ log (2 / α) := (Real.log_le_log_iff hdivpos h2a).2 hlogratio
        -- 合并差分
        have hdiff : primeReciprocalSum x - primeReciprocalSum u ≤
            (log (log x) - log (log u)) + C₁ / log x + C₁ / log u := by
          nlinarith [hLx, hLu]
        have hlelog : log 2 ≤ log x :=
          (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
            (by exact_mod_cast (by omega : 0 < x))).2 (by exact_mod_cast hx)
        have hlelogu : log 2 ≤ log u :=
          (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
            (by exact_mod_cast (by omega : 0 < u))).2 (by exact_mod_cast hu2)
        have hc1x : C₁ / log x ≤ C₁ / log 2 :=
          div_le_div_of_nonneg_left hC1 hlog2pos hlelog
        have hc1u : C₁ / log u ≤ C₁ / log 2 :=
          div_le_div_of_nonneg_left hC1 hlog2pos hlelogu
        have hK1 : log (2 / α) ≤ K := by
          unfold K
          exact le_max_left _ _
        have h2div : 2 * C₁ / log 2 = C₁ / log 2 + C₁ / log 2 := by
          field_simp [hlog2pos.ne']
          ring
        have hfinal : primeReciprocalSum x - primeReciprocalSum u ≤ K + 2 * C₁ / log 2 := by
          calc
            primeReciprocalSum x - primeReciprocalSum u
                ≤ (log (log x) - log (log u)) + C₁ / log x + C₁ / log u := hdiff
            _ ≤ log (2 / α) + C₁ / log 2 + C₁ / log 2 := by
                nlinarith [hLdiff, hc1x, hc1u]
            _ ≤ K + 2 * C₁ / log 2 := by
                rw [h2div]
                nlinarith [hK1]
        rw [hUeq]
        exact hfinal.trans (le_max_right _ _)
      · -- u ≤ 1: x 有界, S x ≤ S x₀
        have hu1 : u ≤ 1 := by omega
        have hUzero : primeReciprocalSum u = 0 := primeReciprocalSum_zero_of_le_one hu1
        have hxlt : (x : ℝ) < (2 : ℝ) ^ (1 / α) := by
          have hu2' : u < 2 := by omega
          have hxαlt2 : (x : ℝ) ^ α < 2 := by
            simpa [u] using (Nat.floor_lt hxα0).mp hu2'
          have hxpos : 0 < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
          have hpow := Real.rpow_lt_rpow hxα0 hxαlt2 (by positivity : 0 < 1 / α)
          have hα0 : α ≠ 0 := ne_of_gt hα
          have hmul : ((x : ℝ) ^ α) ^ (1 / α) = (x : ℝ) := by
            rw [← Real.rpow_mul (le_of_lt hxpos)]
            have hαmul : α * (1 / α) = 1 := by
              field_simp [hα0]
            rw [hαmul, Real.rpow_one]
          rwa [hmul] at hpow
        have hxle0 : x ≤ x₀ := by
          have hxle : (x : ℝ) ≤ (2 : ℝ) ^ (1 / α) := le_of_lt hxlt
          exact (Nat.le_floor_iff (by positivity : 0 ≤ (2 : ℝ) ^ (1 / α))).2 hxle
        have hSx : primeReciprocalSum x ≤ primeReciprocalSum x₀ :=
          primeReciprocalSum_mono hxle0
        have hS0 : primeReciprocalSum x₀ ≤
            max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) :=
          le_max_left _ _
        rw [hUeq, hUzero, sub_zero]
        exact hSx.trans hS0
    · -- u > x: U 为空
      have hxltu : x < u := lt_of_not_ge hux
      have hUempty : U.sum (fun p => 1 / (p : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp only [U, mem_filter, mem_range] at hp
        obtain ⟨hpx, _hp, hxp⟩ := hp
        have hp_lt_u : p < u := by omega
        have hu_lt_p' : ⌊(x : ℝ) ^ α⌋₊ < p := (Nat.floor_lt hxα0).mpr hxp
        have hu_lt_p : u < p := by
          simpa [u] using hu_lt_p'
        omega
      have hCnonneg : 0 ≤ max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := by
        have hSx0 : 0 ≤ primeReciprocalSum x₀ := by
          unfold primeReciprocalSum
          exact Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
        exact le_max_of_le_left hSx0
      rw [hUempty]
      exact hCnonneg
  -- 组合: |T.sum| = T.sum ≤ U.sum ≤ C
  calc
    |T.sum (fun p => 1 / (p : ℝ))| = T.sum (fun p => 1 / (p : ℝ)) := abs_of_nonneg hTnonneg
    _ ≤ U.sum (fun p => 1 / (p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub
        (fun p _hp _hnot => div_nonneg zero_le_one (by positivity))
    _ ≤ max (primeReciprocalSum x₀) (K + 2 * C₁ / log 2) := hUbound

/-! ## 4. 应用: 筛积 V(z) 的渐近公式 -/

/-- Goldbach 筛积 V(z, N) = Π_{p < z, p ∤ N} (1 - 1/(p-1)) -/
noncomputable def goldbachSieveProduct (N z : ℕ) : ℝ :=
  ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1))

/-- 奇素数 p ≥ 3 的局部对数修正: |log(1 - 1/(p-1)) + 1/(p-1)| ≤ 2/(p-1)². -/
private lemma log_one_sub_prime_odd_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    |log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1)| ≤ 2 / ((p : ℝ) - 1) ^ 2 := by
  let t : ℝ := 1 / ((p : ℝ) - 1)
  have hp3 : 3 ≤ p := by
    have h2lt : 2 < p := by
      have h2le : 2 ≤ p := hp.two_le
      omega
    omega
  have ht0 : 0 < t := by
    unfold t
    have hpos : 0 < (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    exact div_pos one_pos hpos
  have htle : t ≤ 1 / 2 := by
    unfold t
    have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have : 0 < (p : ℝ) - 1 := by linarith
    exact ne_of_gt this
  have hsubst : |log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1)| =
      |log (1 - t) + t| := by
    simp [t]
  have hrhs : 2 * t ^ 2 = 2 / ((p : ℝ) - 1) ^ 2 := by
    unfold t
    field_simp [hp1]
  rw [hsubst, ← hrhs]
  exact log_one_sub_bound ht0 htle

/-- **筛积下界**: 存在 c₁ > 0, 对任意偶数 N ≥ 4 与 z ≥ 2,
  c₁ / log z ≤ V(z, N) = Π_{p < z, p ∤ N}(1 - 1/(p-1)).

证明要点:
  1. N 偶数 ⟹ p = 2 不在筛积中, 且排除 p|N 只增不减, 故
     V ≥ W(z) := Π_{p < z, p > 2}(1 - 1/(p-1));
  2. 局部对数修正 |log(1 - 1/(p-1)) + 1/(p-1)| ≤ 2/(p-1)²;
  3. -log W = Σ_{p<z,p>2} 1/(p-1) + O(1) ≤ log log z + O(1) (Mertens 第二定理);
  4. W = exp(-log W) ≥ e^{-C}/log z.

这是筛积渐近 V ≈ 𝔖(N)·e^{-γ}/log z 的下界部分 (Jurkat-Richert 主项所需). -/
theorem goldbachSieveProduct_lower_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ N z : ℕ, 2 ≤ z → Even N → 4 ≤ N →
      c₁ / log z ≤ goldbachSieveProduct N z := by
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  -- Σ_{p} 1/p² 有界
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  have hK : ∃ K : ℝ, 0 ≤ K ∧
      ∀ z : ℕ, ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) ≤ K := by
    refine ⟨∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), tsum_nonneg (fun n => by positivity), ?_⟩
    intro z
    exact Summable.sum_le_tsum ((range z).filter Nat.Prime)
      (fun n _hn => by positivity) hsum2
  obtain ⟨K, hK0, hK⟩ := hK
  let Ctotal : ℝ := B₁ + C₁ / log 2 + 12 * K
  refine ⟨exp (-Ctotal), by exact Real.exp_pos _, ?_⟩
  intro N z hz hN hN4
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (by omega : 1 < z)
  have hlogzpos : 0 < log z := Real.log_pos hz1
  let W : ℝ := ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1))
  -- V ≥ W: V 的筛集是 W 的筛集的子集, 因子 ∈ (0, 1]
  have hVsub : ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)) ⊆
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    rcases hp with ⟨hpz, hpP, hpndvd⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      have h2dvd : 2 ∣ N := by
        rcases hN with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        rw [hk]
        omega
      exact hpndvd (by simpa [hp2] using h2dvd)
    exact ⟨hpz, hpP, hpne2⟩
  have hVgeW : W ≤ goldbachSieveProduct N z := by
    unfold W goldbachSieveProduct
    refine Finset.prod_le_prod_of_subset_of_le_one hVsub ?_ ?_
    · intro p hp
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      -- 0 ≤ 1 - 1/(p-1)
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
        have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
      linarith
    · intro p hp _hnot
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
        div_nonneg zero_le_one (le_of_lt hpos)
      exact sub_le_self (a := (1 : ℝ)) hnonneg
  -- log W = Σ log(1 - 1/(p-1))
  have hlogW : log W = ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
      (fun p => log (1 - 1 / ((p : ℝ) - 1))) := by
    unfold W
    rw [Real.log_prod]
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
    have hp3 : 3 ≤ p := by
      have h2lt : 2 < p := by
        have h2le : 2 ≤ p := hp'.two_le
        omega
      omega
    have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
    have hlt : 1 / ((p : ℝ) - 1) < 1 := by
      have h12 : (1 / 2 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt hle h12
    have hfac : (1 - 1 / ((p : ℝ) - 1)) ≠ 0 := by linarith
    exact hfac
  -- E(z) := Σ_{p<z,p>2} (-log(1-1/(p-1)) - 1/(p-1)), |E| ≤ 8K
  let E : ℝ := ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
    (fun p => -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))
  have hneglog : -log W =
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
        (fun p => 1 / ((p : ℝ) - 1)) + E := by
    unfold E
    rw [hlogW]
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hEabs : |E| ≤ 8 * K := by
    unfold E
    calc
      |((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
          (fun p => -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))|
          ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => |(-log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1))|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 2 / ((p : ℝ) - 1) ^ 2) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' : p.Prime := (mem_filter.mp hp).2.1
          have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
          have h := log_one_sub_prime_odd_bound hp' hp2
          rw [← abs_neg] at h
          rwa [show (-(log (1 - 1 / ((p : ℝ) - 1)) + 1 / ((p : ℝ) - 1))) =
              -log (1 - 1 / ((p : ℝ) - 1)) - 1 / ((p : ℝ) - 1) by ring] at h
      _ ≤ ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2) := by
          calc
            ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                (fun p => 2 / ((p : ℝ) - 1) ^ 2)
              ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                  (fun p => 8 / (p : ℝ) ^ 2) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  have hp' : p.Prime := (mem_filter.mp hp).2.1
                  have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
                  have hp3 : 3 ≤ p := by
                    have h2lt : 2 < p := by
                      have h2le : 2 ≤ p := hp'.two_le
                      omega
                    omega
                  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
                  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
                    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                    have : 0 < (p : ℝ) - 1 := by linarith
                    exact ne_of_gt this
                  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                  have hpos1 : 0 < (p : ℝ) - 1 := by
                    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                    linarith
                  have hpos2 : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos (by linarith : 0 < (p : ℝ))
                  rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
                  nlinarith
            _ ≤ ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2) := by
                  exact Finset.sum_le_sum_of_subset_of_nonneg
                    (by
                      intro p hp
                      simp only [mem_filter, mem_range] at hp ⊢
                      exact ⟨by omega, hp.2.1⟩)
                    (fun p _hp _hnot => by positivity)
      _ ≤ 8 * K := by
          calc
            ((range z).filter Nat.Prime).sum (fun p => 8 / (p : ℝ) ^ 2)
                = 8 * ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                  rw [Finset.mul_sum]
                  congr 1
                  ext p
                  ring
            _ ≤ 8 * K := mul_le_mul_of_nonneg_left (hK z) (by norm_num)
  -- Σ_{p<z,p>2} 1/(p-1) ≤ S(z) + 4K
  have hsum_le : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ primeReciprocalSum z + 4 * K := by
    calc
      ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
          (fun p => 1 / ((p : ℝ) - 1))
          ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2.1
            have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
            have hp3 : 3 ≤ p := by
              have h2lt : 2 < p := by
                have h2le : 2 ≤ p := hp'.two_le
                omega
              omega
            -- 1/(p-1) = 1/p + 1/(p(p-1)) ≤ 1/p + 1/(p-1)²
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
            have hpm1 : (p : ℝ) - 1 ≠ 0 := by
              have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
              have : 0 < (p : ℝ) - 1 := by linarith
              exact ne_of_gt this
            have hle : 1 / ((p : ℝ) - 1) ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2 := by
              -- 1/(p-1) - 1/(p-1)² = (p-2)/(p-1)² ≤ 1/p
              have hpos1 : 0 < (p : ℝ) - 1 := by
                have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                linarith
              have hpos2 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
              have hstep : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 =
                  ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
                field_simp [hpm1]
                ring
              have hle' : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
                rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
                nlinarith
              have hsub : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
                rwa [hstep]
              nlinarith
            exact hle
      _ = ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 1 / (p : ℝ)) +
          ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
            (fun p => 1 / ((p : ℝ) - 1) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ ≤ primeReciprocalSum z + 4 * K := by
          -- Σ_{p<z,p>2} 1/p ≤ S(z); Σ_{p<z,p>2} 1/(p-1)² ≤ 4K
          have h1 : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / (p : ℝ)) ≤ primeReciprocalSum z := by
            unfold primeReciprocalSum
            -- 子集和
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro p hp; simp only [mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2.1⟩)
              (fun p _hp _hnot => by positivity)
          have h2 : ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
              (fun p => 1 / ((p : ℝ) - 1) ^ 2) ≤ 4 * K := by
            calc
              ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                  (fun p => 1 / ((p : ℝ) - 1) ^ 2)
                  ≤ ((range z).filter (fun p => Nat.Prime p ∧ p ≠ 2)).sum
                      (fun p => 4 / (p : ℝ) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro p hp
                    have hp' : p.Prime := (mem_filter.mp hp).2.1
                    have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
                    have hp3 : 3 ≤ p := by
                      have h2lt : 2 < p := by
                        have h2le : 2 ≤ p := hp'.two_le
                        omega
                      omega
                    have hpos1 : 0 < (p : ℝ) - 1 := by
                      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
                      linarith
                    have hpos2 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
                    rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) (sq_pos_of_pos hpos2)]
                    have hp3' : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
                    nlinarith
              _ ≤ ((range z).filter Nat.Prime).sum (fun p => 4 / (p : ℝ) ^ 2) := by
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (by
                        intro p hp
                        simp only [mem_filter, mem_range] at hp ⊢
                        exact ⟨by omega, hp.2.1⟩)
                      (fun p _hp _hnot => by positivity)
              _ = 4 * ((range z).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext p
                    ring
              _ ≤ 4 * K := mul_le_mul_of_nonneg_left (hK z) (by norm_num)
          nlinarith
  -- -log W ≤ log log z + Ctotal
  have hS : primeReciprocalSum z ≤ log (log z) + B₁ + C₁ / log 2 := by
    have hMz := hM z hz
    have h1 : primeReciprocalSum z ≤ log (log z) + B₁ + C₁ / log z := by
      have h := (abs_le.mp hMz).2
      linarith
    have h2 : C₁ / log z ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log z :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < z))).2 (by exact_mod_cast hz)
      exact div_le_div_of_nonneg_left hC1 hlog2 hlelog
    nlinarith
  have hneg_le : -log W ≤ log (log z) + Ctotal := by
    have hE : E ≤ |E| := le_abs_self _
    have h1 : -log W ≤ (primeReciprocalSum z + 4 * K) + 8 * K := by
      nlinarith [hneglog, hE, hEabs, hsum_le]
    unfold Ctotal
    nlinarith [h1, hS]
  -- W ≥ e^{-Ctotal}/log z
  have hWpos : 0 < W := by
    unfold W
    exact Finset.prod_pos (fun p hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : p ≠ 2 := (mem_filter.mp hp).2.2
      have hp3 : 3 ≤ p := by
        have h2lt : 2 < p := by
          have h2le : 2 ≤ p := hp'.two_le
          omega
        omega
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
        have h2le : (2 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
          linarith
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2le
      have hlt : 1 / ((p : ℝ) - 1) < 1 := by
        have h12 : (1 / 2 : ℝ) < 1 := by norm_num
        exact lt_of_le_of_lt hle h12
      linarith)
  have hW_low : exp (-Ctotal) / log z ≤ W := by
    have hlogW_ge : -log (log z) - Ctotal ≤ log W := by linarith [hneg_le]
    have h1 : exp (-log (log z) - Ctotal) ≤ exp (log W) :=
      Real.exp_le_exp.mpr hlogW_ge
    have hWexp : exp (log W) = W := Real.exp_log hWpos
    have h2 : exp (-log (log z) - Ctotal) = exp (-Ctotal) / log z := by
      rw [show -log (log z) - Ctotal = -log (log z) + (-Ctotal) by ring, Real.exp_add]
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < log z)]
      rw [div_eq_mul_inv]
      ring
    rw [hWexp] at h1
    rwa [h2] at h1
  exact hW_low.trans hVgeW

/-- 筛积上界: V(z, N) ≤ 1 (每个因子 ∈ (0, 1]). -/
theorem goldbachSieveProduct_le_one (N z : ℕ) :
    goldbachSieveProduct N z ≤ 1 := by
  unfold goldbachSieveProduct
  exact Finset.prod_le_one
    (fun (p : ℕ) hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : 2 ≤ p := hp'.two_le
      have hle : 1 / ((p : ℝ) - 1) ≤ 1 := by
        have hpos : 0 < (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        rw [div_le_iff₀ hpos]
        have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          linarith
        nlinarith
      linarith)
    (fun (p : ℕ) hp => by
      have hp' : p.Prime := (mem_filter.mp hp).2.1
      have hp2 : 2 ≤ p := hp'.two_le
      have hpos : 0 < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        linarith
      have hnonneg : 0 ≤ 1 / ((p : ℝ) - 1) :=
        div_nonneg zero_le_one (le_of_lt hpos)
      exact sub_le_self (a := (1 : ℝ)) hnonneg)

/-- **筛积恒等式**: V(z,N) = Π_{p<z}(1-1/p) · 𝔖(N,z-1).

证明: 每个因子分解 (1-1/(p-1)) = (1-1/p)(1-1/(p-1)²), 且
  - p ∤ N (含 p=2 被排除): (1-1/p)·localFactor(p,N) = 1-1/(p-1);
  - p | N (包括 p=2, 因 N 偶): (1-1/p)·localFactor(p,N) = 1.
故 Π_{p<z}(1-1/p)·𝔖(N,z-1) = Π_{p<z}[(1-1/p)·localFactor(p,N)] = V.

这是筛积渐近 V ≈ 𝔖(N)·e^{-γ}/log z 的精确骨架. -/
theorem sieveProduct_identity (N z : ℕ) (hz : 2 ≤ z) (hN : Even N) :
    goldbachSieveProduct N z =
      primeProduct (z - 1) * SingularSeries.singularSeriesTruncated N (z - 1) := by
  have hz1 : 1 ≤ z := by omega
  have h2dvd : 2 ∣ N := by
    rcases hN with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  have hrangeP : (range (z - 1 + 1)).filter Nat.Prime = (range z).filter Nat.Prime := by
    rw [Nat.sub_add_cancel hz1]
  unfold goldbachSieveProduct primeProduct SingularSeries.singularSeriesTruncated
  rw [hrangeP]
  -- 目标: ∏_{p<z,p∤N}(1-1/(p-1)) = ∏_{p<z}(1-1/p) · ∏_{p<z} localFactor p N
  rw [← Finset.prod_mul_distrib]
  -- 分割: 按 p|N / p∤N
  have hpart : ((range z).filter Nat.Prime) =
      ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)) ∪
      ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)) := by
    ext p
    simp only [mem_filter, mem_union, mem_range]
    by_cases hp : p ∣ N <;> simp [hp]
  have hdisj : Disjoint ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N))
      ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [mem_filter] at hp1 hp2
    exact hp1.2.2 hp2.2.2
  rw [hpart, Finset.prod_union hdisj]
  -- 每因子: p ∤ N ⟹ (1-1/p)·localFactor = 1-1/(p-1)
  have hF_pnd : ∀ p ∈ (range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N),
      1 - 1 / ((p : ℝ) - 1) =
        (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N := by
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hpnd : ¬ p ∣ N := (mem_filter.mp hp).2.2
    have hpne2 : p ≠ 2 := by
      intro hp2
      exact hpnd (by simpa [hp2] using h2dvd)
    unfold SingularSeries.localFactor
    rw [if_neg hpne2, if_neg hpnd]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
      have : 0 < (p : ℝ) - 1 := by linarith
      exact ne_of_gt this
    field_simp [hp0, hpm1]
    ring
  -- 每因子: p | N ⟹ (1-1/p)·localFactor = 1
  have hF_pd : ∀ p ∈ (range z).filter (fun p => Nat.Prime p ∧ p ∣ N),
      (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N = 1 := by
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2.1
    have hpd : p ∣ N := (mem_filter.mp hp).2.2
    unfold SingularSeries.localFactor
    by_cases hp2 : p = 2
    · subst hp2
      rw [if_pos rfl, if_pos h2dvd]
      norm_num
    · rw [if_neg hp2, if_pos hpd]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
        have : 0 < (p : ℝ) - 1 := by linarith
        exact ne_of_gt this
      field_simp [hp0, hpm1]
  -- 组装
  have hLHS : ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
        (fun p => 1 - 1 / ((p : ℝ) - 1)) =
      ((range z).filter (fun p => Nat.Prime p ∧ ¬ p ∣ N)).prod
        (fun p => (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N) :=
    Finset.prod_congr rfl hF_pnd
  have hRHS : ((range z).filter (fun p => Nat.Prime p ∧ p ∣ N)).prod
        (fun p => (1 - 1 / (p : ℝ)) * SingularSeries.localFactor p N) = 1 :=
    Finset.prod_eq_one hF_pd
  rw [hLHS, hRHS, mul_one]

/-- **筛积的阶**: 存在 c₁, c₂ > 0, 对任意偶数 N ≥ 4 与 z ≥ 3,
  c₁·𝔖(N,z-1)/log z ≤ V(z,N) ≤ c₂·𝔖(N,z-1)/log z.

由恒等式 V = Π_{p<z}(1-1/p)·𝔖(N,z-1) 与 `primeProduct_asymptotic_order`
(Π_{p<z}(1-1/p) = Θ(1/log z)) 直接推出. -/
theorem sieveProduct_order :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ N z : ℕ, 3 ≤ z → Even N → 4 ≤ N →
      c₁ * SingularSeries.singularSeriesTruncated N (z - 1) / log z ≤
        goldbachSieveProduct N z ∧
      goldbachSieveProduct N z ≤
        c₂ * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
  obtain ⟨c₁0, c₂0, hc₁0, hPP⟩ := primeProduct_asymptotic_order
  refine ⟨c₁0, 2 * c₂0, hc₁0, ?_⟩
  intro N z hz hN hN4
  have h1z : 1 ≤ z := by omega
  have hz2 : 2 ≤ z - 1 := by omega
  have hz1 : 1 ≤ z - 1 := by omega
  have hz3 : (3 : ℝ) ≤ z := by exact_mod_cast (by omega : 3 ≤ z)
  have hlogz : 0 < log z := Real.log_pos (by linarith : (1 : ℝ) < z)
  have hz1r : (1 : ℝ) < (z : ℝ) - 1 := by linarith
  have hcast : ((z - 1 : ℕ) : ℝ) = (z : ℝ) - 1 :=
    by simpa using (Nat.cast_sub h1z)
  have hlogz1 : 0 < log (z - 1) := by
    exact Real.log_pos hz1r
  have h𝔖 : 0 < SingularSeries.singularSeriesTruncated N (z - 1) :=
    SingularSeries.singularSeriesTruncated_pos N (z - 1) hz1
  have hP := hPP (z - 1) hz2
  have hlelog1 : log (z - 1) ≤ log z := by
    have hpos1 : 0 < (z : ℝ) - 1 := by linarith
    have hle1 : (z : ℝ) - 1 ≤ (z : ℝ) := by linarith
    exact (Real.log_le_log_iff hpos1 (by linarith : 0 < (z : ℝ))).2 hle1
  have hlog_ratio : (1 / 2 : ℝ) * log z ≤ log (z - 1) := by
    have hsqrt : Real.sqrt z ≤ (z : ℝ) - 1 := by
      have hz1pos : 0 ≤ (z : ℝ) - 1 := by linarith
      have hsq : (z : ℝ) ≤ ((z : ℝ) - 1) ^ 2 := by
        have hdiff : ((z : ℝ) - 1) ^ 2 - (z : ℝ) =
            ((z : ℝ) - 2) ^ 2 + ((z : ℝ) - 3) := by ring
        have hnonneg : 0 ≤ ((z : ℝ) - 1) ^ 2 - (z : ℝ) := by
          rw [hdiff]
          have h1 : 0 ≤ ((z : ℝ) - 2) ^ 2 := sq_nonneg _
          have h2 : 0 ≤ (z : ℝ) - 3 := by linarith
          nlinarith
        linarith
      exact (Real.sqrt_le_iff).2 ⟨hz1pos, hsq⟩
    have hlogsqrt : log (Real.sqrt z) = (1 / 2 : ℝ) * log z := by
      rw [Real.log_sqrt (by exact_mod_cast (by omega : 0 ≤ z))]
      ring
    have hle : log (Real.sqrt z) ≤ log (z - 1) := by
      have hpos1 : 0 < Real.sqrt z :=
        Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < z))
      have hpos2 : 0 < (z : ℝ) - 1 := by linarith
      exact (Real.log_le_log_iff hpos1 hpos2).2 hsqrt
    rwa [hlogsqrt] at hle
  have hid := sieveProduct_identity N z (by omega) hN
  have hV_low : c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) ≤
      goldbachSieveProduct N z := by
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hP.1 (le_of_lt h𝔖)
    -- hmul : c₁0/log(z-1) · 𝔖 ≤ P·𝔖 — 规范化
    simpa [div_eq_mul_inv, hcast, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hV_up : goldbachSieveProduct N z ≤
      c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) := by
    rw [hid]
    have hmul := mul_le_mul_of_nonneg_right hP.2 (le_of_lt h𝔖)
    simpa [div_eq_mul_inv, hcast, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- 换成 log z
  have hA : c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log z ≤
      c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) := by
    have hnonneg : 0 ≤ c₁0 * SingularSeries.singularSeriesTruncated N (z - 1) :=
      mul_nonneg (le_of_lt hc₁0) (le_of_lt h𝔖)
    exact div_le_div_of_nonneg_left hnonneg hlogz1 hlelog1
  have hB : c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) / log (z - 1) ≤
      (2 * c₂0) * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
    -- 1/log(z-1) ≤ 2/log z
    have hnonneg : 0 ≤ c₂0 * SingularSeries.singularSeriesTruncated N (z - 1) := by
      -- c₂0 ≥ 0 (由 primeProduct 上界推出)
      have hc20 : 0 ≤ c₂0 := by
        have hb := hPP 2 (by norm_num)
        have hle1 : (0 : ℝ) ≤ primeProduct 2 := by
          unfold primeProduct
          have hf : (range 3).filter Nat.Prime = {2} := by
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
              subst hp
              simp [Nat.prime_two]
          rw [hf]
          norm_num
        have hle2 : primeProduct 2 ≤ c₂0 / log 2 := hb.2
        have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        have : (0 : ℝ) ≤ c₂0 / log 2 := le_trans hle1 hle2
        simpa using (le_div_iff₀ hlog2).mp this
      exact mul_nonneg hc20 (le_of_lt h𝔖)
    -- 需要: c₂0·𝔖/log(z-1) ≤ 2·c₂0·𝔖/log z ⟺ 1/log(z-1) ≤ 2/log z ⟸ log z ≤ 2·log(z-1)
    have hdiv : (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / log (z - 1) ≤
        (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / (log z / 2) := by
      have hle : log z / 2 ≤ log (z - 1) := by linarith [hlog_ratio]
      exact div_le_div_of_nonneg_left hnonneg (by linarith : 0 < log z / 2) hle
    have hnorm : (c₂0 * SingularSeries.singularSeriesTruncated N (z - 1)) / (log z / 2) =
        (2 * c₂0) * SingularSeries.singularSeriesTruncated N (z - 1) / log z := by
      field_simp [hlogz.ne']
    exact hdiv.trans (le_of_eq hnorm)
  constructor
  · exact hA.trans hV_low
  · exact hV_up.trans hB

/-! ## 4.5 素数倒数 (p-1) 求和引理 (Selberg Lemma 2 的基础) -/

/-- Σ_{p ≤ y} 1/p² 有界 (常数只依赖 Σ_{n≥1} 1/n²). -/
theorem prime_inv_sq_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℕ, ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / (p : ℝ) ^ 2) ≤ K := by
  have hsum2 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)
  refine ⟨∑' n : ℕ, (1 / (n : ℝ) ^ 2 : ℝ), tsum_nonneg (fun n => by positivity), ?_⟩
  intro y
  exact Summable.sum_le_tsum ((range (y + 1)).filter Nat.Prime) (fun n _hn => by positivity) hsum2

/-- Σ_{p ≤ y} 1/(p-1) ≤ log(log y) + C 对 y ≥ 3 (Mertens 第二定理 + 分解). -/
theorem prime_inv_pminus1_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ, 3 ≤ y →
      ((range (y + 1)).filter Nat.Prime).sum
        (fun p => 1 / ((p : ℝ) - 1)) ≤ log (log y) + C := by
  obtain ⟨B₁, C₁, hM⟩ := mertens_second_theorem
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_bound
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC1 : 0 ≤ C₁ := by
    have hb := hM 2 (by norm_num)
    have hnonneg : 0 ≤ C₁ / log 2 := le_trans (abs_nonneg _) hb
    simpa using (le_div_iff₀ hlog2).mp hnonneg
  refine ⟨max (B₁ + C₁ / log 2 + 4 * K) 0, le_max_right _ _, ?_⟩
  intro y hy
  have hlogy : 0 < log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- Σ 1/p ≤ log(log y) + B₁ + C₁/log 2
  have hS : primeReciprocalSum y ≤ log (log y) + B₁ + C₁ / log 2 := by
    have hMz := hM y (by omega : 2 ≤ y)
    have h1 : primeReciprocalSum y ≤ log (log y) + B₁ + C₁ / log y := by
      have h := (abs_le.mp hMz).2
      linarith
    have h2 : C₁ / log y ≤ C₁ / log 2 := by
      have hlelog : log 2 ≤ log y :=
        (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast (by omega : 0 < y))).2 (by exact_mod_cast (by omega : 2 ≤ y))
      exact div_le_div_of_nonneg_left hC1 hlog2 hlelog
    nlinarith
  -- Σ 1/(p-1) ≤ Σ(1/p + 1/(p-1)²) ≤ S + 4K
  have hsum : ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ primeReciprocalSum y + 4 * K := by
    calc
      ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1))
          ≤ ((range (y + 1)).filter Nat.Prime).sum
              (fun p => 1 / (p : ℝ) + 1 / ((p : ℝ) - 1) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp' : p.Prime := (mem_filter.mp hp).2
            have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
            have hpm1 : (p : ℝ) - 1 ≠ 0 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
              have : 0 < (p : ℝ) - 1 := by linarith
              exact ne_of_gt this
            have hpos1 : 0 < (p : ℝ) - 1 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
              linarith
            have hpos2 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
            have hstep : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 =
                ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 := by
              field_simp [hpm1]
              ring
            have hle' : ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
              rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) hpos2]
              nlinarith
            have hsub : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / (p : ℝ) := by
              rwa [hstep]
            nlinarith
      _ = ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ)) +
          ((range (y + 1)).filter Nat.Prime).sum
            (fun p => 1 / ((p : ℝ) - 1) ^ 2) := by
            rw [Finset.sum_add_distrib]
      _ ≤ primeReciprocalSum y + 4 * K := by
          have h1 : ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ)) ≤
              primeReciprocalSum y := by
            unfold primeReciprocalSum
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by intro p hp; simp only [mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩)
              (fun p _hp _hnot => by positivity)
          have h2 : ((range (y + 1)).filter Nat.Prime).sum
              (fun p => 1 / ((p : ℝ) - 1) ^ 2) ≤ 4 * K := by
            calc
              ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1) ^ 2)
                  ≤ ((range (y + 1)).filter Nat.Prime).sum (fun p => 4 / (p : ℝ) ^ 2) := by
                    apply Finset.sum_le_sum
                    intro p hp
                    have hp' : p.Prime := (mem_filter.mp hp).2
                    have hpos1 : 0 < (p : ℝ) - 1 := by
                      have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                      linarith
                    have hpos2 : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
                    rw [div_le_div_iff₀ (sq_pos_of_pos hpos1) (sq_pos_of_pos hpos2)]
                    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
                    nlinarith
              _ = 4 * ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / (p : ℝ) ^ 2) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext p
                    ring
              _ ≤ 4 * K := mul_le_mul_of_nonneg_left (hK y) (by norm_num)
          nlinarith
  -- 组合
  have hle : ((range (y + 1)).filter Nat.Prime).sum
      (fun p => 1 / ((p : ℝ) - 1)) ≤ log (log y) + (B₁ + C₁ / log 2 + 4 * K) := by
    nlinarith [hS, hsum]
  have hmax : B₁ + C₁ / log 2 + 4 * K ≤ max (B₁ + C₁ / log 2 + 4 * K) 0 :=
    le_max_left _ _
  linarith

/-- **筛积渐近公式** (修正): V(z, N) ≈ 𝔖(N, z-1) · e^(-γ) / log(z-1)

其中 𝔖(N, z) = Π_{p ≤ z, p.Prime} localFactor(p, N) 为截断奇异级数
(`SingularSeries.singularSeriesTruncated`).

**2026-08-04 修正**: 原陈述漏掉奇异级数因子, 对含多个小奇素因子的 N 是假命题
(V 依赖 N 通过局部因子 p/(p-1), 无界). 正确渐近为 V ≈ 𝔖(N)·e^{-γ}/log z,
来自恒等式 (1 - 1/(p-1)) = (1 - 1/p)·(1 - 1/(p-1)²) 与 Mertens 乘积公式.
这是 Jurkat-Richert 定理中主项 X · V(z) 的计算基础.

误差也必须乘以截断奇异级数；否则无法从 Mertens 乘积公式对任意 `N` 一致推出。
`z - 1` 则精确对应 `goldbachSieveProduct` 中的范围 `p < z`. -/
theorem sieve_product_asymptotic :
    ∃ C : ℝ,
      ∀ N z : ℕ, 3 ≤ z → Even N → 4 ≤ N →
        |goldbachSieveProduct N z -
          SingularSeries.singularSeriesTruncated N (z - 1) *
            exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ)| ≤
          C * SingularSeries.singularSeriesTruncated N (z - 1) /
            (log ((z - 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C, hC⟩ := mertens_product_formula
  refine ⟨C, ?_⟩
  intro N z hz hN _hN4
  have hz2 : 2 ≤ z - 1 := by omega
  have hz1 : 1 ≤ z - 1 := by omega
  have hP := hC (z - 1) hz2
  have hSpos : 0 < SingularSeries.singularSeriesTruncated N (z - 1) :=
    SingularSeries.singularSeriesTruncated_pos N (z - 1) hz1
  rw [sieveProduct_identity N z (by omega) hN]
  have hmul := mul_le_mul_of_nonneg_right hP (le_of_lt hSpos)
  calc
    |primeProduct (z - 1) * SingularSeries.singularSeriesTruncated N (z - 1) -
        SingularSeries.singularSeriesTruncated N (z - 1) *
          exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ)| =
        |primeProduct (z - 1) - exp (-eulerMascheroniConstant) /
          log ((z - 1 : ℕ) : ℝ)| *
          SingularSeries.singularSeriesTruncated N (z - 1) := by
            rw [show primeProduct (z - 1) *
                SingularSeries.singularSeriesTruncated N (z - 1) -
              SingularSeries.singularSeriesTruncated N (z - 1) *
                exp (-eulerMascheroniConstant) / log ((z - 1 : ℕ) : ℝ) =
              (primeProduct (z - 1) - exp (-eulerMascheroniConstant) /
                log ((z - 1 : ℕ) : ℝ)) *
                SingularSeries.singularSeriesTruncated N (z - 1) by ring,
              abs_mul, abs_of_pos hSpos]
    _ ≤ C / (log ((z - 1 : ℕ) : ℝ)) ^ 2 *
          SingularSeries.singularSeriesTruncated N (z - 1) := hmul
    _ = C * SingularSeries.singularSeriesTruncated N (z - 1) /
          (log ((z - 1 : ℕ) : ℝ)) ^ 2 := by ring

/-! ## 5. 辅助引理: 素数计数函数 -/

/-- 素数计数函数 π(x) = |{p ≤ x : p 素数}| -/
def primeCount (x : ℕ) : ℕ :=
  ((range (x + 1)).filter Nat.Prime).card

/-- The project's finite prime count agrees definitionally with mathlib's
`Nat.primeCounting`.  This is the normalization needed when importing a PNT
stated using mathlib's standard counting function. -/
theorem primeCount_eq_primeCounting (x : ℕ) :
    primeCount x = Nat.primeCounting x := by
  simp only [primeCount, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- A prime-counting PNT in the normal form exported by PNTAnd's `pi_alt`.

This is kept as a separate interface: adapting an external proof to the
project toolchain only has to establish this proposition. -/
def PrimeCountingPNT : Prop :=
  ∃ c : ℕ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℕ, (primeCount x : ℝ) = (1 + c x) * (x : ℝ) / log x

/-- The `pi_alt` normal form implies the epsilon formulation used by the
project's PNT declaration. -/
theorem primeCountingPNT_implies_prime_number_theorem (hPNT : PrimeCountingPNT) :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ,
      ∀ x : ℕ, x₀ ≤ x →
        |(primeCount x : ℝ) - (x : ℝ) / log x| ≤
          ε * (x : ℝ) / log x := by
  obtain ⟨c, hc, hcount⟩ := hPNT
  rw [Asymptotics.isLittleO_iff] at hc
  intro ε hε
  specialize hc (c := ε) hε
  rw [Filter.eventually_atTop] at hc
  obtain ⟨x₀, hx₀⟩ := hc
  refine ⟨max 2 x₀, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hcx : |c x| ≤ ε := by
    have := hx₀ x (le_trans (le_max_right _ _) hx)
    simpa using this
  have hlog : 0 < log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hscale : 0 ≤ (x : ℝ) / log x := by positivity
  rw [hcount x]
  have hrewrite :
      (1 + c x) * (x : ℝ) / log x - (x : ℝ) / log x =
        c x * ((x : ℝ) / log x) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg hscale]
  calc
    |c x| * ((x : ℝ) / log x) ≤ ε * ((x : ℝ) / log x) :=
      mul_le_mul_of_nonneg_right hcx hscale
    _ = ε * (x : ℝ) / log x := by ring

/-- π(x) ≥ 1 当 x ≥ 2 (至少有素数 2) -/
theorem primeCount_pos (x : ℕ) (hx : 2 ≤ x) : 0 < primeCount x := by
  unfold primeCount
  apply Finset.card_pos.mpr
  use 2
  simp [mem_filter, mem_range, hx, Nat.prime_two]

/-- **素数定理 (PNT)**: π(x) ~ x / log x

即 |π(x) - x/log x| / (x/log x) → 0 当 x → ∞.
这是 Mertens 定理的证明基础. -/
theorem prime_number_theorem :
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ,
      ∀ x : ℕ, x₀ ≤ x →
        |(primeCount x : ℝ) - (x : ℝ) / log x| ≤
          ε * (x : ℝ) / log x := by
  apply primeCountingPNT_implies_prime_number_theorem
  obtain ⟨c, hc, hcount⟩ :=
    AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
  refine ⟨c, hc, ?_⟩
  intro x
  rw [primeCount_eq_primeCounting]
  exact hcount x

/-! ## 6. 孪生素数常数 -/

/-- 孪生素数常数 C₂ = Π_{p > 2} (1 - 1/(p-1)²) ≈ 0.66016...

该常数的收敛性是奇异级数 𝔖(N) 有界性的关键. -/
noncomputable def twinPrimeConstant : ℝ :=
  -- 截断乘积的极限, 严格定义需无穷乘积收敛理论
  -- 此处用截断作为工作定义 (范围缩小以加速编译, 证明不依赖具体大小)
  ((range 100).filter (fun p => Nat.Prime p ∧ 2 < p)).prod
    (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- 孪生素数常数为正 (每个因子为正, 且乘积收敛). -/
theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  -- 每个因子 1 - 1/(p-1)² > 0 (因 p ≥ 3, (p-1)² ≥ 4 > 1)
  -- 且 Π (1 - 1/(p-1)²) 收敛 (因 Σ 1/(p-1)² ≤ Σ 1/p² < ∞)
  unfold twinPrimeConstant
  apply Finset.prod_pos
  intro p hp
  simp only [mem_filter, mem_range] at hp
  obtain ⟨_, hp_prime, hp2⟩ := hp
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have h_sq : 1 < (p - 1 : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ p - 1 := by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    nlinarith
  have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
    have h_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
    rw [div_lt_iff₀ h_pos, one_mul]
    exact h_sq
  linarith

/-- 每个因子 1 - 1/(p-1)² < 1 (因 p ≥ 3, (p-1)² ≥ 4 > 1, 故 1/(p-1)² > 0). -/
private lemma twinPrimeConstant_factor_lt_one {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    linarith
  have h_sq_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
  have : 0 < 1 / ((p : ℝ) - 1) ^ 2 := div_pos one_pos h_sq_pos
  linarith

/-- 每个因子 1 - 1/(p-1)² ≤ 1. -/
private lemma twinPrimeConstant_factor_le_one {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
  exact le_of_lt (twinPrimeConstant_factor_lt_one hp hp2)

/-- 每个因子为正. -/
private lemma twinPrimeConstant_factor_pos {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp3 : 3 ≤ p := by omega
  have hp1_pos : (0 : ℝ) < p - 1 := by
    have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    linarith
  have h_sq : 1 < ((p : ℝ) - 1) ^ 2 := by
    have : (2 : ℝ) ≤ p - 1 := by
      have : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
      linarith
    nlinarith
  have h_pos : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos hp1_pos
  have : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
    rw [div_lt_iff₀ h_pos, one_mul]
    exact h_sq
  linarith

/-- 孪生素数常数 < 1 (每个因子 ∈ (0,1), 且至少含 p = 3 的因子 = 3/4 < 1). -/
theorem twinPrimeConstant_lt_one : twinPrimeConstant < 1 := by
  -- 策略: 分离 p=3 的因子, 其余因子之积 ≤ 1
  -- product = factor(3) * prod(rest), factor(3) = 3/4, prod(rest) ≤ 1
  -- 故 product ≤ 3/4 < 1
  unfold twinPrimeConstant
  set S := (range 100).filter (fun p => Nat.Prime p ∧ 2 < p) with hS_def
  -- p = 3 在集合中
  have h_3_mem : 3 ∈ S := by
    rw [hS_def]
    simp [mem_filter, mem_range, Nat.prime_three]
  -- 分离 p=3
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h_3_mem]
  -- factor(3) = 3/4
  have h_3_val : 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 = 3 / 4 := by norm_num
  -- 其余因子之积 ≤ 1 (所有因子 ∈ (0, 1])
  have h_rest_le : (S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      simp only [mem_sdiff, mem_singleton] at hp
      obtain ⟨hp_mem, hp_ne⟩ := hp
      simp only [hS_def, mem_filter, mem_range] at hp_mem
      obtain ⟨_, hp_prime, hp2⟩ := hp_mem
      exact le_of_lt (twinPrimeConstant_factor_pos hp_prime hp2)
    · intro p hp
      simp only [mem_sdiff, mem_singleton] at hp
      obtain ⟨hp_mem, hp_ne⟩ := hp
      simp only [hS_def, mem_filter, mem_range] at hp_mem
      obtain ⟨_, hp_prime, hp2⟩ := hp_mem
      exact twinPrimeConstant_factor_le_one hp_prime hp2
  -- factor(3) ≥ 0
  have h_3_nonneg : 0 ≤ 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 := by linarith [h_3_val]
  -- product ≤ 3/4 * 1 = 3/4 < 1
  have h_prod_le : (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) *
      ((S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤ 3 / 4 := by
    calc (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) *
          ((S \ {3}).prod (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1) ^ 2))
        ≤ (1 - 1 / ((↑3 : ℝ) - 1) ^ 2) * 1 := mul_le_mul_of_nonneg_left h_rest_le h_3_nonneg
      _ = 1 - 1 / ((↑3 : ℝ) - 1) ^ 2 := mul_one _
      _ = 3 / 4 := h_3_val
  linarith

/-! ## 7. 总结 -/

/-
**Mertens 定理形式化状态**:

1. **陈述层** (已完成):
   - `mertens_second_theorem`: Mertens 第二定理 (Σ 1/p = log log x + B₁ + O(1/log x))
   - `mertens_product_formula`: Mertens 乘积公式 (Π (1-1/p) ~ e^(-γ)/log x)
   - `prime_number_theorem`: 素数定理 (π(x) ~ x/log x)

2. **应用层** (陈述已完成):
   - `prime_reciprocal_sum_bounded`: Lemma 1 (素数倒数和有界)
   - `sieve_product_asymptotic`: 筛积渐近公式 V(z) ≈ 𝔖(N) e^(-γ)/log z

3. **孪生素数常数** (已完成):
   - `twinPrimeConstant`: C₂ = Π_{p>2} (1 - 1/(p-1)²) 的截断定义
   - `twinPrimeConstant_pos`: C₂ > 0 (正性)
   - `twinPrimeConstant_lt_one`: C₂ < 1

4. **证明层** (待完成):
   - 所有主要定理的证明依赖素数定理 PNT
   - PNT 的完整形式化需要 ζ 函数理论 (数百页)
   - 当前作为公理声明 (sorry), 后续可逐步补全
-/

end MathlibNt.SieveTheory.MertensTheorem
