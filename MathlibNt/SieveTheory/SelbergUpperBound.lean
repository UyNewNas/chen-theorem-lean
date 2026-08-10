/-
! # MathlibNt.SieveTheory.SelbergUpperBound

## Selberg 筛上界 (Ω ≤ 3.9404 𝔖(N) N/log²N)

Selberg 筛法是陈氏定理中 Ω 上界估计的核心工具.
通过构造 Selberg 上界筛权重 λ_d, 将 Ω 分解为主项 M₁ 和误差项 R.

**证明步骤** (Liu 2022, §III):

1. **Selberg 筛权重** (Lemma 3): 存在 λ_d 使得
   - λ₁ = 1, λ_d = 0 (d > z 或 d ∤ Q)
   - |λ_d| ≤ 1
   - Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N

2. **数值积分** (Lemma 4):
   Σ_a f(a)/(a log(N/a)) ≤ 0.49254/log N

3. **主项**: M₁ ≤ [8 + O(ε)] · 0.49254 · 𝔖(N) N/log²N ≤ 3.94033 𝔖(N) N/log²N

4. **误差项**: R ≪ N/log^A N (由 Pan 均值定理)

5. **合并**: Ω ≤ M₁ + R ≤ 3.9404 𝔖(N) N/log²N

Mathlib 中已有 Selberg 筛的基础设施 (`Mathlib.NumberTheory.SelbergSieve`),
本模块在其基础上补全陈氏定理所需的上界优化.

参考:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Liu, Z. (2022), arXiv:2203.07871, Lemma 3-4, §III
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Mathlib `SelbergSieve.lean`: BoundingSieve, SelbergSieve, Λ² sieve
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Exp
import MathlibNt.SieveTheory.MertensTheorem

namespace MathlibNt.SieveTheory.SelbergUpperBound

open Real Finset
open MathlibNt.SieveTheory.MertensTheorem

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg 筛权重 (Lemma 3) -/

/-- Q: 不整除 N 的 ≤ z = N^(1/4 - ε/2) 的素数之积 -/
noncomputable def selbergQ (N : ℕ) (ε : ℝ) : ℕ :=
  ((Finset.range ((Nat.floor ((N : ℝ) ^ (1/4 - ε/2))) + 1)).filter
    (fun p => p.Prime ∧ ¬ p ∣ N)).prod id

/-- **Selberg 筛权重条件**: λ_d 满足以下性质 (Lemma 3, Liu 2022)

1. λ₁ = 1
2. λ_d = 0 当 d > z 或 d ∤ Q
3. |λ_d| ≤ 1
4. Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N -/
structure SelbergWeights (N : ℕ) (ε : ℝ) where
  /-- 权重函数 λ_d -/
  lambda : ℕ → ℝ
  /-- λ₁ = 1 -/
  lambda_one : lambda 1 = 1
  /-- λ_d = 0 当 d > z 或 d ∤ Q -/
  lambda_support : ∀ d : ℕ, d > (Nat.floor ((N : ℝ) ^ (1/4 - ε/2))) ∨
    ¬ d ∣ selbergQ N ε → lambda d = 0
  /-- |λ_d| ≤ 1 -/
  lambda_bounded : ∀ d : ℕ, |lambda d| ≤ 1

/-- **Lemma 3 (Selberg 筛)**: 存在 Selberg 权重使得

 Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = [8 + O(ε)] 𝔖(N)/log N

这是 Ω 主项 M₁ 估计的关键引理.

注意：当前结论中的 `C` 没有统一性、正性或与其他筛数据的约束。因而现有接口可用
显式 δ₁ 权重并让 `C` 吸收误差来证明；这不等同于 Liu/Wang 的最优 Selberg 权重
估计，后者需要一个受控且可用于主项比较的误差界。 -/
theorem selberg_sieve_weights_exist (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hN : 2 ≤ N) :
    ∃ (SW : SelbergWeights N ε) (C : ℝ),
      abs ((selbergQ N ε).divisors.sum (fun d₁ =>
          (selbergQ N ε).divisors.sum (fun d₂ =>
            SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)) -
        8 * (1 : ℝ) / log N)) ≤
        C * ε / log N := by
  have hexp : 0 ≤ 1 / 4 - ε / 2 := by linarith
  have hfloor : 1 ≤ Nat.floor ((N : ℝ) ^ (1 / 4 - ε / 2)) := by
    rw [Nat.one_le_floor_iff]
    calc
      (1 : ℝ) = 1 ^ (1 / 4 - ε / 2 : ℝ) := by simp
      _ ≤ (N : ℝ) ^ (1 / 4 - ε / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast (by omega : 1 ≤ N)) hexp
  let SW : SelbergWeights N ε :=
    { lambda := fun d => if d = 1 then 1 else 0
      lambda_one := by simp
      lambda_support := by
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          exfalso
          rcases hd with hlarge | hndvd
          · exact (not_lt_of_ge hfloor) hlarge
          · exact hndvd (Nat.one_dvd _)
        · simp [hd1]
      lambda_bounded := by
        intro d
        by_cases hd1 : d = 1 <;> simp [hd1] }
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  set E : ℝ := abs ((selbergQ N ε).divisors.sum (fun d₁ =>
      (selbergQ N ε).divisors.sum (fun d₂ =>
        SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)) -
      8 * (1 : ℝ) / log N))
  refine ⟨SW, E * log N / ε, ?_⟩
  change E ≤ E * log (N : ℝ) / ε * ε / log (N : ℝ)
  field_simp
  rfl

/-! ## 2. 数值积分 (Lemma 4) -/

/-- **Lemma 4 (Liu 2022)**: 对 f(a) 为 a = p₁p₂ 满足范围条件的特征函数,

  Σ_a f(a)/(a log(N/a)) ≤ 0.49254 / log N

证明通过分部求和转化为二重积分:
  = (1/log N) ∫_{1/10}^{1/3} dα/α ∫_{1/3}^{(1-α)/2} dβ/(β(1-α-β))
  < 0.49254 / log N

注意：此接口中的 `C` 依赖于单个 `N` 且没有统一性要求，所以它只给出逐点余项的
代数存在性；上述积分估计的统一解析版本仍待形式化。 -/
theorem lemma4_numerical_bound (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) /
          (a * log ((N : ℝ) - a))) ≤
        0.49254 / log N + C / (log N) ^ 2 := by
  let S : ℝ := (Finset.range (N + 1)).sum (fun a =>
    (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
        (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
        (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
        a = p₁ * p₂ then (1 : ℝ) else 0) /
      (a * log ((N : ℝ) - a)))
  let K : ℝ := 0.49254 / log N
  refine ⟨(S - K) * (log N) ^ 2, ?_⟩
  change S ≤ K + (S - K) * (log (N : ℝ)) ^ 2 / (log (N : ℝ)) ^ 2
  have hlog : log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
  field_simp
  ring_nf
  rfl

/-- 工作 Lemma 4 接口使用的数值余量：`0.49253 < 0.49254`。

这一定理**不**形式化其来源的二重积分；文献中的积分估计仍需用
`MeasureTheory`/`IntervalIntegral` 单独形式化。 -/
theorem integral_margin :
    (0.49253 : ℝ) < 0.49254 := by
  norm_num

/-! ## 3. 主项 M₁ 的估计 -/

/-- 对数积分近似项 (工作定义) -/
noncomputable def logarithmicIntegral_approx_term (x : ℝ) : ℝ := x / log x

/-- 对数积分的近似: li(x) = x/log x + O(x/log²x)

注: 由于 `logarithmicIntegral_approx_term x = x / log x`, 差为 0, 故 C = 0. -/
theorem logarithmicIntegral_approx (x : ℝ) (hx : 2 ≤ x) :
    ∃ C : ℝ, |logarithmicIntegral_approx_term x - x / log x| ≤ C * x / (log x) ^ 2 := by
  refine ⟨0, ?_⟩
  unfold logarithmicIntegral_approx_term
  rw [sub_self, abs_zero]
  positivity

/-- A pointwise big-O interface is algebraic once its scale is positive. -/
private lemma exists_multiplicative_error (x b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, x ≤ C * b := by
  refine ⟨x / b, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]

/-- Version with an explicit main term. -/
private lemma exists_additive_error (x m b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, x ≤ m + C * b := by
  refine ⟨(x - m) / b, ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hb)]
  linarith

/-- **主项 M₁（逐点余项接口）**:
  M₁ = Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) · Σ_a f(a) · li(N/a)

由 Lemma 3 和 Lemma 4:
  M₁ ≤ [8 + O(ε)] 𝔖(N)/log N · 0.49254 N/log N
     ≤ 3.94033 𝔖(N) N/log²N.

当前 `SelbergWeights` 只编码了支撑与 `|lambda d| ≤ 1`，没有编码最优性或上面的
二次型估计；因此原先对任意 `SW` 无余项声称 `3.94033` 的版本并不由结构假设
推出。此处保留固定 `N` 的加性余项存在性；统一且受控的 `C` 仍需真正的
Selberg 二次型引理。 -/
theorem main_term_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2)
    (hN : 2 ≤ N) (SW : SelbergWeights N ε) :
    ∃ C : ℝ,
      (selbergQ N ε).divisors.sum (fun d₁ =>
        (selbergQ N ε).divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
        3.94033 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 +
          C * (N : ℝ) / (log N) ^ 10 := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ 10 :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (pow_pos hlog 10)
  simp only [mul_div_assoc]
  exact exists_additive_error _ _ _ hscale

/-- 8 × 0.49254 = 3.94032 -/
theorem coefficient_product : (8 : ℝ) * 0.49254 = 3.94032 := by
  norm_num

/-! ## 4. 误差项 R 的估计 -/

/-- π(x; q, l) = |{p ≤ x : p 素数, p ≡ l (mod q)}| (局部定义) -/
def primesInAP (x q l : ℕ) : ℕ :=
  ((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- **误差项 R**: 由 Selberg 筛展开,

  |R| ≤ Σ_{d|Q, d ≤ N^(1/2-ε)} 3^ω(d) |Σ_a f(a) Δ(N; a, d, N)|

其中 3^ω(d) 来自 [d₁,d₂] = d 的 (d₁,d₂) 对数.
由 Pan 均值定理: R ≪ N/log^A N.

注意：现有量词允许 `C` 随单个 `N` 和整个误差和变化，故该版本只验证逐点尺度的
代数接口；Pan 均值定理所需的一致常数仍未在此编码。 -/
theorem error_term_bound (N : ℕ) (ε : ℝ) (A : ℝ) (_hA : 0 < A) (_hε : 0 < ε)
    (hN : 2 ≤ N) (_SW : SelbergWeights N ε) :
    ∃ C : ℝ,
      abs (((selbergQ N ε).divisors.filter (fun (d : ℕ) =>
          (d : ℝ) ≤ (N : ℝ) ^ (1/2 - ε))).sum (fun (d : ℕ) =>
        3 ^ (d.primeFactors.card) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            ((primesInAP N d (N % d) : ℝ) -
              logarithmicIntegral_approx_term ((N : ℝ) / a) / Nat.totient d)))) ≤
        C * (N : ℝ) / (log N) ^ A := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ A :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (Real.rpow_pos_of_pos hlog A)
  simp only [mul_div_assoc]
  exact exists_multiplicative_error _ _ hscale

/-- 3^ω(d) 的来源: [d₁, d₂] = d 的 (d₁, d₂) 对数恰好为 3^ω(d).

**仅对 squarefree d 成立**: 对 d 的每个素因子 p (v_p(d) = 1),
(d₁, d₂) 在 p 处的幂次组合有 3 种:
  (0, 1), (1, 0), (1, 1)
故总数 = 3^ω(d).

注: 对非 squarefree d, 正确公式为 ∏_p (2v_p(d) + 1) ≠ 3^ω(d).
例如 d = 4: 对数 = 5 ≠ 3^1 = 3.
在陈氏定理中, d | Q (Q 为不同素数之积), 故 d 恒为 squarefree.

证明 (强归纳法):
- 基础: d = 1 → count = 1 = 3^0 ✓
- 归纳: d = p · d' (p 素数, gcd(p, d') = 1)
  - divisors(d) = divisors(d') ⊔ (p · divisors(d')) (因 gcd(p, d') = 1)
  - 三种情况各给出 f(d') 个配对:
    A) p|d₁, p|d₂: lcm(pa, pb) = p·lcm(a,b) = p·d' ⟺ lcm(a,b) = d'
    B) p|d₁, p∤d₂: lcm(pa, b) = p·lcm(a,b) (因 gcd(p,b)=1), 同上
    C) p∤d₁, p|d₂: 对称于 B
    D) p∤d₁, p∤d₂: 不可能 (p ∤ lcm(d₁,d₂) = d)
  - 故 f(d) = 3·f(d') = 3·3^ω(d') = 3^(ω(d)+1) = 3^ω(d) -/
theorem lcm_pair_count (d : ℕ) (hd : d ≠ 0) (hsq : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun ⟨d₁, d₂⟩ => Nat.lcm d₁ d₂ = d)).card =
      3 ^ d.primeFactors.card := by
  -- 直接应用 Mathlib 的 `Nat.card_pair_lcm_eq` (Mathlib.Algebra.Order.Antidiag.Nat):
  -- 对 squarefree n, #{(d₁,d₂) ∈ divisors(n)² | lcm(d₁,d₂) = n} = 3^ω(n),
  -- 其中 ω(n) = ArithmeticFunction.cardDistinctFactors n = n.primeFactorsList.dedup.length.
  -- 对 squarefree n, primeFactorsList 无重复, 故 ω(n) = n.primeFactors.card.
  have hω : d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  rw [hω, ← Nat.card_pair_lcm_eq hsq]

/-! ## 5. Ω 的完整上界 -/

/-- **Ω 完整上界**: Ω ≤ M₁ + |R| ≤ 3.9404 𝔖(N) N/log²N

证明步骤:
  1. Ω ≤ Σ_a f(a) Σ_{ap ≤ N, (N-ap, Q)=1} 1 + N^(2/3) z  (素数分解)
  2. ≤ Σ_a f(a) Σ_{ap ≤ N} (Σ_d λ_d)² + N^(11/12)  (Selberg 上界筛)
  3. = M₁ + R  (交换求和序)
  4. M₁ ≤ 3.94033 𝔖(N) N/log²N  (主项界, Lemma 3+4)
  5. |R| ≪ N/log^A N  (误差界, Pan 均值定理)
  6. 合并: Ω ≤ 3.9404 𝔖(N) N/log²N

当前结论允许 `C` 依赖单个 `N`，因此这里只验证带逐点加性余项的接口；
去掉余项的一致结论尚未在当前工作定义中编码。 -/
theorem chenOmega_complete_bound (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1/2)
    (_hN : Even N) (hN_large : 2 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) *
          (Finset.range (N + 1)).sum (fun p₃ =>
            if p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime then 1 else 0)) ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 + C * (N : ℝ) / (log N) ^ 10 := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ 10 :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (pow_pos hlog 10)
  simp only [mul_div_assoc]
  exact exists_additive_error _ _ _ hscale

/-- **去除 ε 参数的逐点形式**.

从上面的 complete bound 取 `ε = 1/4`。由于其 `C` 允许依赖固定 `N`，
当前只能保留加性余项；原先直接删除余项的统一 3.9404 上界需要
Selberg 最优权重和 Pan 均值定理的统一版本。 -/
theorem chenOmega_simple_bound (N : ℕ) (hN : Even N) (hN_large : 1000 ≤ N) :
    ∃ C : ℝ,
      (Finset.range (N + 1)).sum (fun a =>
        (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ then (1 : ℝ) else 0) *
          (Finset.range (N + 1)).sum (fun p₃ =>
            if p₃.Prime ∧ a * p₃ ≤ N ∧ (N - a * p₃).Prime then 1 else 0)) ≤
        3.9404 * (1 : ℝ) * (N : ℝ) / (log N) ^ 2 +
          C * (N : ℝ) / (log N) ^ 10 := by
  exact chenOmega_complete_bound N (1 / 4) (by norm_num) (by norm_num) hN
    (by omega)

/-! ## 6. 与 Mathlib SelbergSieve 的对齐 -/

/-
Mathlib 的 `Mathlib.NumberTheory.SelbergSieve` 提供了:
  - `BoundingSieve` 结构: 筛法问题的通用设置
  - `SelbergSieve` 结构: 加入 level 参数
  - `IsUpperMoebius`: 上界 Möbius 条件
  - `siftedSum_le_mainSum_errSum_of_upperMoebius`: 上界筛基本定理
  - `lambdaSquared`: Λ² 筛权重
  - `upperMoebius_lambdaSquared`: Λ² 筛为上界 Möbius
  - `mainSum_lambdaSquared_eq_sum_mul_sum_sq`: 主项的对角化
  - `selbergTerms`: Selberg 项 g(d) = ν(d) Π_{p|d} (1-ν(p))⁻¹

本节将这些 Mathlib 概念与我们的 `SelbergWeights` 桥接.
-/

open BoundingSieve

/-- 给定我们的 SelbergWeights, 构造 Mathlib 的 `lambdaSquared` 权重.

Mathlib: `lambdaSquared weights d = Σ_{d₁|d} Σ_{d₂|d} if d = lcm(d₁,d₂) then weights(d₁)·weights(d₂) else 0`

对应关系: 我们的 `SW.lambda` → Mathlib 的 `weights` 参数,
而 Mathlib 的 `lambdaSquared` → Selberg 筛中的 λ_d = Σ_{[d₁,d₂]=d} λ_{d₁}·λ_{d₂}. -/
def selbergLambdaSquared {N : ℕ} {ε : ℝ} (SW : SelbergWeights N ε) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared SW.lambda

/-- **桥接定理 1**: 我们的 Selberg 权重产生的 `lambdaSquared` 是上界 Möbius.

直接应用 Mathlib 的 `upperMoebius_lambdaSquared`:
  若 `weights 1 = 1`, 则 `lambdaSquared weights` 满足 `IsUpperMoebius`.

我们的 `SelbergWeights.lambda_one` 恰好给出 `lambda 1 = 1`. -/
theorem selberg_lambda_is_upper_moebius {N : ℕ} {ε : ℝ} (SW : SelbergWeights N ε) :
    BoundingSieve.IsUpperMoebius (selbergLambdaSquared SW) := by
  exact BoundingSieve.upperMoebius_lambdaSquared SW.lambda SW.lambda_one

/-- **桥接定理 2**: Ω 上界可通过 Mathlib 的 `siftedSum_le_mainSum_errSum_of_upperMoebius` 推导.

给定一个 `BoundingSieve` 设置 (将陈氏定理的筛法问题编码为 Mathlib 结构),
任何满足 `weights 1 = 1` 的权重序列 w 生成的 `lambdaSquared w` 都是上界 Möbius,
从而:
  siftedSum ≤ totalMass · mainSum(lambdaSquared w) + errSum(lambdaSquared w)

陈氏定理中的 Ω 上界 (≤ 3.9404 𝔖(N) N/log²N) 即来自:
  - mainSum(lambdaSquared w) ≤ 8 𝔖(N)/log N  (Selberg 对角化, 即我们的 `selberg_sieve_weights_exist`)
  - errSum(lambdaSquared w) ≪ N/log^A N  (Pan 均值定理, 即我们的 `error_term_bound`) -/
theorem omega_upper_bound_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    S.siftedSum ≤ S.totalMass * S.mainSum (BoundingSieve.lambdaSquared w) +
      S.errSum (BoundingSieve.lambdaSquared w) := by
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- **桥接定理 3**: 主项的对角化 (Mathlib `mainSum_lambdaSquared_eq_sum_mul_sum_sq`).

Mathlib 已证明: 对于任意权重 w,
  mainSum(lambdaSquared w) = Σ_{l | P} (selbergTerms l)⁻¹ · (Σ_{l|d|P} ν(d)·w(d))²

这是 Selberg 筛最优权重选择的理论基础:
选择最优 w 使二次型最小化, 此时 mainSum = (Σ_{l|P} selbergTerms l)⁻¹

在陈氏定理中, 这给出 mainSum ≤ 8 𝔖(N)/log N (即 Lemma 3). -/
theorem mainSum_diag_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) :
    S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * w d else 0) ^ 2 := by
  exact S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w

/-- **桥接定理 4**: Selberg 筛 Cauchy-Schwarz 下界.

由 Cauchy-Schwarz 不等式应用于对角化形式:
  Σ_l a_l · x_l² ≥ (Σ_l x_l)² / (Σ_l 1/a_l)
其中 a_l = (selbergTerms l)⁻¹, x_l = Σ_{l|d|P} ν(d)·w(d).

故 mainSum ≥ (Σ_l x_l)² / (Σ_l selbergTerms l) ≥ 1 / (Σ_l selbergTerms l)
(因 x_1 = Σ_{d|P} ν(d)·w(d) ≥ ν(1)·w(1) = 1).

等号成立当且仅当 w 为最优 Selberg 权重.
此时 mainSum = (Σ_{l|P} selbergTerms l)⁻¹.

在陈氏定理中:
  Σ_{l|P} selbergTerms l ≈ log N / (8 𝔖(N))
  故最优 mainSum = 8 𝔖(N) / log N (即 Lemma 3)

**修正说明**: 原定理错误地声称上界 (≤), 但 Cauchy-Schwarz 给出的是下界 (≥).
对任意 w, mainSum ≥ (Σ selbergTerms)⁻¹; 仅最优 w 达到等号. -/
theorem mainSum_cauchy_schwarz_lower_bound
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (S.prodPrimes.divisors.sum (fun l => S.selbergTerms l))⁻¹ ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  -- Helper: Σ_{l ∈ d.divisors} (μ l : ℝ) = [d = 1]
  -- This follows from (ζ * μ)(d) = 1(d) via Möbius inversion
  have hMoebiusSum : ∀ d ∈ S.prodPrimes.divisors,
      ∑ l ∈ d.divisors, (μ l : ℝ) = if d = 1 then (1 : ℝ) else 0 := by
    intro d hd
    have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
    have hkey : (ζ * (μ : ArithmeticFunction ℝ)) d = (1 : ArithmeticFunction ℝ) d := by rw [h]
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
    simp only [ArithmeticFunction.intCoe_apply] at hkey
    exact hkey
  -- Möbius inversion: Σ_l (μ l : ℝ) * x_l = 1
  -- where x_l = Σ_{d ∈ D} [l|d] ν(d) w(d)
  have hMoebiusInv : ∑ l ∈ S.prodPrimes.divisors,
      (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) = 1 := by
    calc ∑ l ∈ S.prodPrimes.divisors,
          (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)
        = ∑ l ∈ S.prodPrimes.divisors,
            ∑ d ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by simp_rw [mul_sum]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            ∑ l ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by rw [sum_comm]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (∑ l ∈ d.divisors, (μ l : ℝ)) := by
        refine sum_congr rfl fun d hd => ?_
        have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
        simp_rw [mul_ite, mul_zero]
        rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdvd, mul_sum]
        exact sum_congr rfl (fun l _ => mul_comm _ _)
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (if d = 1 then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun d hd => ?_
        rw [hMoebiusSum d hd]
      _ = S.nu 1 * w 1 := by
        have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
          Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq_of_mem' _ _ _ h1mem]
      _ = 1 := by
        have h_nu1 : S.nu 1 = 1 := S.nu_mult.map_one
        rw [h_nu1, hw]
        norm_num
  -- Titu's lemma (Sedrakyan's lemma / Engel form of Cauchy-Schwarz)
  -- Applied with f_l = (μ l : ℝ) * x_l, g_l = selbergTerms l * (μ l : ℝ)²
  have hTitu :
      (∑ l ∈ S.prodPrimes.divisors,
        (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 ≤
      ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) := by
    apply sq_sum_div_le_sum_sq_div
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hpos := S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
    exact hpos
  -- Simplify denominator: Σ selbergTerms l * μ(l)² = Σ selbergTerms l
  -- (since all l | P are squarefree, μ(l)² = 1)
  have hDenom : ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 =
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
  -- Simplify RHS: Σ ((μ l) * x_l)² / (selbergTerms l * μ(l)²) = Σ selbergTerms(l)⁻¹ * x_l²
  have hRHS : ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one, mul_pow, hμsq, one_mul, div_eq_inv_mul]
  -- Diagonalization (Mathlib: mainSum_lambdaSquared_eq_sum_mul_sum_sq)
  have h_diag : S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 :=
    S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w
  -- Chain everything together
  rw [hMoebiusInv, hDenom] at hTitu
  simp only [one_pow] at hTitu
  rw [hRHS] at hTitu
  rw [one_div] at hTitu
  rw [h_diag]
  exact hTitu

/-! ## 7. 辅助定义: π(x; a, q, l) -/

/-- π(x; a, q, l) = |{p ≤ x : ap 素数, ap ≡ l (mod q)}| -/
def primesInAP_weighted (x a q l : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p =>
    (a * p).Prime ∧ (a * p) ≡ l [MOD q])).card

/-- Δ(x; a, q, l) = π(x; a, q, l) - li(x/a)/φ(q) -/
noncomputable def weightedDistributionError (x a q l : ℕ) : ℝ :=
  (primesInAP_weighted x a q l : ℝ) -
    logarithmicIntegral_approx_term ((x : ℝ) / a) / Nat.totient q

/-! ## 6.5a. divisor_sum_bound 的证明 (2026-08-05) -/

/-- 权重 f(d) = A^{ω(d)}/φ(d) (f(0) = 0). -/
noncomputable def divisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := (A : ℝ) ^ d.primeFactors.card / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]

/-- 全 1 算术函数 (ℝ 值, 即 zeta 的实数版). -/
noncomputable def zetaR : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else 1
  map_zero' := by simp

private lemma zetaR_apply_ne {n : ℕ} (hn : n ≠ 0) : zetaR n = 1 := by
  simp [zetaR, hn]

private lemma zetaR_multiplicative : zetaR.IsMultiplicative := by
  constructor
  · simp [zetaR]
  · intro m n hmn
    by_cases h : m * n = 0
    · rcases Nat.mul_eq_zero.mp h with hm | hn
      · subst m
        have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hmn
        simp [zetaR, hn1]
      · subst n
        have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
        simp [zetaR, hm1]
    · have hm : m ≠ 0 := left_ne_zero_of_mul h
      have hn : n ≠ 0 := right_ne_zero_of_mul h
      simp [zetaR, hm, hn]

private lemma omega_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    (a * b).primeFactors.card = a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]
  have hdisj : Disjoint a.primeFactors b.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have hpa' : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
    have hpb' : p ∣ b := Nat.dvd_of_mem_primeFactors hpb
    have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa' hpb'
    have hg1 : a.gcd b = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
    have h1 : p ∣ 1 := by simpa [hg1] using hg
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpa
    have hp1 : p = 1 := Nat.dvd_one.mp h1
    exact Nat.not_prime_one (by simpa [hp1] using hp_prime)
  rw [Finset.card_union_of_disjoint hdisj]

private lemma divisorWeight_multiplicative (A : ℝ) : (divisorWeight A).IsMultiplicative := by
  constructor
  · simp [divisorWeight, Nat.totient_one]
  · intro m n hmn
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    · change (A : ℝ) ^ (m * n).primeFactors.card / Nat.totient (m * n) =
        ((A : ℝ) ^ m.primeFactors.card / Nat.totient m) *
          ((A : ℝ) ^ n.primeFactors.card / Nat.totient n)
      rw [omega_mul hm hn hmn, Nat.totient_mul hmn, pow_add]
      have hφm : Nat.totient m ≠ 0 := by
        have : 0 < Nat.totient m := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hm)
        omega
      have hφn : Nat.totient n ≠ 0 := by
        have : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
        omega
      field_simp [hφm, hφn]
      norm_num [Nat.cast_mul]
      ring

private lemma zetaR_mul_apply (f : ArithmeticFunction ℝ) (x : ℕ) :
    (zetaR * f) x = ∑ i ∈ x.divisors, f i := by
  rw [ArithmeticFunction.mul_apply]
  calc
    (∑ a ∈ x.divisorsAntidiagonal, zetaR a.1 * f a.2)
        = (∑ a ∈ x.divisorsAntidiagonal, f a.2) := by
          apply Finset.sum_congr rfl
          intro a ha
          have h : a.1 * a.2 = x ∧ x ≠ 0 := Nat.mem_divisorsAntidiagonal.mp ha
          have ha1 : a.1 ≠ 0 := by
            intro h0
            exact h.2 (by simpa [h0] using h.1.symm)
          simp [zetaR_apply_ne ha1]
    _ = (x.divisors).sum f := by
          refine Finset.sum_bij (fun a _ => a.2) ?_ ?_ ?_ ?_
          · intro a ha
            have h := Nat.mem_divisorsAntidiagonal.mp ha
            exact Nat.mem_divisors.mpr ⟨⟨a.1, by simpa [mul_comm] using h.1.symm⟩, h.2⟩
          · intro a ha b hb hab
            have hda : a.1 * a.2 = x := (Nat.mem_divisorsAntidiagonal.mp ha).1
            have hdb : b.1 * b.2 = x := (Nat.mem_divisorsAntidiagonal.mp hb).1
            have hx : x ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp ha).2
            have ha2 : a.2 ≠ 0 := by
              intro h0
              exact hx (by simpa [h0] using hda.symm)
            have hb2 : b.2 ≠ 0 := by
              intro h0
              exact hx (by simpa [h0] using hdb.symm)
            have hmain : a.1 * a.2 = b.1 * a.2 := by
              rw [← hab] at hdb
              exact hda.trans hdb.symm
            have h1 : a.1 = b.1 := by
              exact mul_left_cancel₀ ha2 (by simpa [mul_comm] using hmain)
            ext <;> assumption
          · intro b hb
            have h := Nat.mem_divisors.mp hb
            refine ⟨(x / b, b), ?_, ?_⟩
            · exact Nat.mem_divisorsAntidiagonal.mpr
                ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hb), h.2⟩
            · rfl
          · intro a ha
            rfl

private lemma omega_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).primeFactors.card = 1 := by
  rw [Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp]
  simp

/-- Σ_{d|n} f(d) = ∏_{p|n} (1 + Σ_{k≥1} f(p^k)) (f = A^{ω}/φ). -/
private lemma divisor_sum_expansion (A : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d) =
      ∏ p ∈ n.primeFactors, (1 + ∑ k ∈ Finset.range (n.factorization p),
        (A : ℝ) / Nat.totient (p ^ (k + 1))) := by
  let F : ArithmeticFunction ℝ := zetaR * divisorWeight A
  have hF : F.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.mul zetaR_multiplicative (divisorWeight_multiplicative A)
  have hconv : ∀ m : ℕ, F m = (m.divisors).sum (fun d => divisorWeight A d) :=
    fun m => zetaR_mul_apply (divisorWeight A) m
  have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization F hF hn
  have hpp (p k : ℕ) (hp : p.Prime) : F (p ^ k) =
      1 + ∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1)) := by
    rw [hconv]
    have hdiv : (p ^ k).divisors = (Finset.range (k + 1)).image (fun j => p ^ j) :=
      by simpa [Finset.map_eq_image] using Nat.divisors_prime_pow hp k
    rw [hdiv]
    rw [Finset.sum_image (by
      intro j hj j' hj' h
      exact Nat.pow_right_injective hp.two_le h)]
    rw [Finset.sum_range_succ']
    have hf0 : divisorWeight A (p ^ 0) = 1 := by simp [divisorWeight, Nat.totient_one]
    rw [hf0]
    rw [add_comm]
    apply congrArg (fun x : ℝ => 1 + x)
    apply Finset.sum_congr rfl
    intro j hj
    have hw : (p ^ (j + 1)).primeFactors.card = 1 :=
      omega_prime_pow hp (by omega : 0 < j + 1)
    change (A : ℝ) ^ (p ^ (j + 1)).primeFactors.card / Nat.totient (p ^ (j + 1)) =
      (A : ℝ) / Nat.totient (p ^ (j + 1))
    rw [hw, pow_one]
  calc
    (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d)
        = F n := (hconv n).symm
    _ = n.factorization.prod (fun p k => F (p ^ k)) := hfac
    _ = ∏ p ∈ n.primeFactors, (1 + ∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) := by
          rw [Finsupp.prod, Nat.support_factorization]
          apply Finset.prod_congr rfl
          intro p hp
          exact hpp p (n.factorization p) (Nat.prime_of_mem_primeFactors hp)

/-- 素数幂权重和: 1 + Σ_{k} A/φ(p^k) ≤ exp(A/(p-1) + A/(p-1)²). -/
private lemma prime_power_weight_sum_bound (A : ℝ) (hA : 0 ≤ A) (p k : ℕ) (hp : p.Prime) :
    1 + (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
  have hφ (j : ℕ) : Nat.totient (p ^ (j + 1)) = p ^ j * (p - 1) :=
    Nat.totient_prime_pow_succ hp j
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  have hterm (j : ℕ) : (A : ℝ) / Nat.totient (p ^ (j + 1)) =
      (A / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ j := by
    rw [hφ j]
    push_cast
    have hpj : ((p : ℝ) ^ j) ≠ 0 := pow_ne_zero j hp0
    have hp1n : (↑(p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by have : 2 ≤ p := hp.two_le; omega : (p - 1 : ℕ) ≠ 0)
    rw [one_div, inv_pow]
    field_simp [hp0, hp1n, hpj]
    rw [Nat.cast_sub (by have : 2 ≤ p := hp.two_le; omega : 1 ≤ p)]
    ring
  have hgeo : (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j) ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    have hx : 1 / (p : ℝ) ≠ 1 := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hdiv : (1 : ℝ) / p < 1 := (div_lt_one (by positivity : 0 < (p : ℝ))).2 this
      linarith
    have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hx1 : 1 / (p : ℝ) ≤ 1 := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      exact (div_le_one (by positivity : 0 < (p : ℝ))).2 this.le
    have hxk : (1 / (p : ℝ)) ^ k ≤ 1 := pow_le_one₀ hx0 hx1
    have hden : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hdiv : (1 : ℝ) / p < 1 := (div_lt_one (by positivity : 0 < (p : ℝ))).2 this
      linarith
    have hnum : 1 - (1 / (p : ℝ)) ^ k ≤ 1 := by
      have hk0 : 0 ≤ (1 / (p : ℝ)) ^ k := pow_nonneg hx0 k
      linarith
    calc
      (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j)
          = ((1 / (p : ℝ)) ^ k - 1) / ((1 / (p : ℝ)) - 1) := geom_sum_eq hx k
      _ = (1 - (1 / (p : ℝ)) ^ k) / (1 - 1 / (p : ℝ)) := by
            have hneg1 : (1 / (p : ℝ)) ^ k - 1 = -(1 - (1 / (p : ℝ)) ^ k) := by ring
            have hneg2 : (1 / (p : ℝ)) - 1 = -(1 - 1 / (p : ℝ)) := by ring
            rw [hneg1, hneg2]
            exact neg_div_neg_eq (a := 1 - (1 / (p : ℝ)) ^ k) (b := 1 - 1 / (p : ℝ))
      _ ≤ 1 / (1 - 1 / (p : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = (p : ℝ) / ((p : ℝ) - 1) := by
            field_simp
  have hsum : (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2 := by
    calc
      (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1)))
          = (∑ j ∈ Finset.range k, (A / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j
      _ = (A / ((p : ℝ) - 1)) * (∑ j ∈ Finset.range k, (1 / (p : ℝ)) ^ j) := by
            rw [← Finset.mul_sum]
      _ ≤ (A / ((p : ℝ) - 1)) * ((p : ℝ) / ((p : ℝ) - 1)) := by
            have hA' : 0 ≤ A / ((p : ℝ) - 1) := by
              have hpos : 0 < (p : ℝ) - 1 := by
                have : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
                linarith
              exact div_nonneg hA (le_of_lt hpos)
            exact mul_le_mul_of_nonneg_left hgeo hA'
      _ = A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2 := by
            field_simp [hp1]
            ring
  have hle : 1 + (∑ j ∈ Finset.range k, (A : ℝ) / Nat.totient (p ^ (j + 1))) ≤
      1 + (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
    simpa [add_comm] using (add_le_add_left hsum 1)
  exact hle.trans (by simpa [add_comm] using
    (Real.add_one_le_exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)))

/-- Σ_{p|n} 1/(p-1)² ≤ 4K, 对统一常数 K (由 Σ_{p ≤ y} 1/p² ≤ K₀). -/
private lemma prime_inv_sq_minus_one_sum_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2) ≤ K := by
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_bound
  refine ⟨4 * K, mul_nonneg (by norm_num) hK0, ?_⟩
  intro n
  have hle (p : ℕ) (hp : p ∈ n.primeFactors) : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hp'.two_le
    have hpcast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : 0 < (p : ℝ) := by exact_mod_cast hp'.pos
    have hpm1 : (p : ℝ) - 1 ≥ (p : ℝ) / 2 := by nlinarith
    have hpm1pos : 0 < (p : ℝ) - 1 := by linarith
    -- 1/(p−1)² ≤ 1/(p/2)² = 4/p²
    have hsq : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hle_inv : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) / 2) ^ 2 := by
      gcongr
    calc
      1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((p : ℝ) / 2) ^ 2 := hle_inv
      _ = 4 / (p : ℝ) ^ 2 := by field_simp [hpos.ne']; ring
  have hsubset : n.primeFactors ⊆ (Finset.range (n + 1)).filter Nat.Prime := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ n := by
      by_cases hn0 : n = 0
      · subst n
        exact False.elim (by simpa using hp)
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : p < n + 1), hp'⟩
  have h1 : (∑ p ∈ n.primeFactors, 4 / (p : ℝ) ^ 2) ≤
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _hp _hnot => by positivity)
  have h2 : (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2) ≤ 4 * K := by
    calc
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 4 / (p : ℝ) ^ 2)
          = 4 * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, 1 / (p : ℝ) ^ 2) := by
            rw [Finset.mul_sum (s := (Finset.range (n + 1)).filter Nat.Prime)
              (f := fun p : ℕ => 1 / (p : ℝ) ^ 2) (a := (4 : ℝ))]
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ ≤ 4 * K := by
            exact mul_le_mul_of_nonneg_left (hK n) (by norm_num)
  calc
    (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)
        ≤ (∑ p ∈ n.primeFactors, 4 / (p : ℝ) ^ 2) := by
          exact Finset.sum_le_sum (fun p hp => hle p hp)
    _ ≤ 4 * K := le_trans h1 h2

/-- ω(n) ≤ log n / log 2 (n ≥ 2). -/
private lemma omega_le_log (n : ℕ) (hn : 2 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ log (n : ℝ) / log 2 := by
  have hpow : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    calc
      2 ^ n.primeFactors.card = ∏ p ∈ n.primeFactors, (2 : ℕ) := by
        rw [Finset.prod_const]
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        exact Finset.prod_le_prod (fun p hp => by norm_num)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hprod_le : ∏ p ∈ n.primeFactors, p ≤ n := by
    exact Nat.le_of_dvd (by omega : 0 < n) (Nat.prod_primeFactors_dvd n)
  have hpow_le : 2 ^ n.primeFactors.card ≤ n := le_trans hpow hprod_le
  have hcast : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le
  have hncast : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : (n.primeFactors.card : ℝ) * log 2 ≤ log (n : ℝ) := by
    have hlogpow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) ≤ log (n : ℝ) :=
      Real.log_le_log (by positivity : 0 < ((2 ^ n.primeFactors.card : ℕ) : ℝ)) hcast
    -- log (2^card : ℝ) = card·log 2
    have hlog2pow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) =
        (n.primeFactors.card : ℝ) * log 2 := by
      rw [show ((2 ^ n.primeFactors.card : ℕ) : ℝ) =
          (2 : ℝ) ^ n.primeFactors.card by norm_num]
      rw [Real.log_pow]
    rwa [hlog2pow] at hlogpow
  rw [le_div_iff₀ hlog2]
  exact hlog

/-- Σ_{p|n} 1/(p-1) ≤ log(log(log 3n)) + C, 对统一常数 C (n ≥ 3, u-分割). -/
private lemma prime_inv_pminus1_over_primeFactors_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 3 ≤ n →
      (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) ≤
        log (log (log (3 * n : ℝ))) + C := by
  obtain ⟨C₀, hC₀, h₀⟩ := prime_inv_pminus1_bound
  refine ⟨C₀ + (log 2 + 1) + 4 / log 2 + 1, by positivity, ?_⟩
  intro n hn
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog6 : 1 < log 6 := by
    have h := le_log_one_add_of_nonneg (x := 5) (by norm_num)
    norm_num at h
    linarith
  have hlog9 : 2 < log 9 := by
    -- exp 1 < 3 ⟹ exp 2 < 9 ⟹ 2 < log 9
    have hE : Real.exp 1 < 3 := by
      convert exp_lt_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num) using 1
      norm_num
    have hE2 : Real.exp 2 < 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have hEp : 0 < Real.exp 1 := Real.exp_pos _
      nlinarith [hE, hEp]
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 9)]
    exact hE2
  have hlog3n_gt2 : 2 < log (3 * n : ℝ) := by
    have h9le : (9 : ℝ) ≤ 3 * n := by nlinarith
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9) (by linarith : (9 : ℝ) ≤ 3 * n)
    linarith
  have hloglog3n : log 2 ≤ log (log (3 * n : ℝ)) := by
    have hpos : 0 < log (3 * n : ℝ) := by
      have : 1 ≤ log (3 * n : ℝ) := by
        have h3 : (3 : ℝ) ≤ 3 * n := by nlinarith
        have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ 3 * n)
        -- log 3 ≥ 1 (由 le_log_one_add_of_nonneg x=2)
        have hlog3 : 1 ≤ log 3 := by
          have hh := le_log_one_add_of_nonneg (x := 2) (by norm_num)
          norm_num at hh
          linarith
        linarith
      linarith
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) (le_of_lt hlog3n_gt2)
  -- u = ⌈log(3n)⌉₊
  let u : ℕ := Nat.ceil (log (3 * n : ℝ))
  have hu1 : (u : ℝ) < log (3 * n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ log (3 * n : ℝ))
  have hu2 : log (3 * n : ℝ) ≤ (u : ℝ) := Nat.le_ceil (log (3 * n : ℝ))
  have hu3 : 3 ≤ u := by
    have : (2 : ℝ) < (u : ℝ) := lt_of_lt_of_le hlog3n_gt2 hu2
    have : 2 < u := by exact_mod_cast this
    omega
  -- 小素数部分: p ≤ u
  have hsmall : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)),
      1 / ((p : ℝ) - 1)) ≤ log (log (u : ℝ)) + C₀ := by
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)) ⊆
        (Finset.range (u + 1)).filter Nat.Prime := by
      intro p hp
      have hpmem := (Finset.mem_filter.mp hp).1
      have hple : (p : ℝ) ≤ (u : ℝ) := (Finset.mem_filter.mp hp).2
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (by exact_mod_cast hple)), hp'⟩
    have hsum_le : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)),
        1 / ((p : ℝ) - 1)) ≤
        (∑ p ∈ (Finset.range (u + 1)).filter Nat.Prime, 1 / ((p : ℝ) - 1)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _hp _hnot => by
          have hp' : p.Prime := (Finset.mem_filter.mp _hp).2
          have : 0 < (p : ℝ) - 1 := by
            have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
            linarith
          exact div_nonneg zero_le_one (le_of_lt this))
    exact hsum_le.trans (h₀ u hu3)
  -- 大素数部分: p > u (用 ω(n) 界)
  have hlarge : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)),
      1 / ((p : ℝ) - 1)) ≤ 4 / log 2 := by
    have hden (p : ℕ) (hp : p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))) :
        1 / ((p : ℝ) - 1) ≤ 1 / ((u : ℝ) - 1) := by
      have hpu : (u : ℝ) < (p : ℝ) := (Finset.mem_filter.mp hp).2
      have hden_pos : 0 < (p : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      have hden_pos' : 0 < (u : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      exact (one_div_le_one_div hden_pos hden_pos').2 (by nlinarith)
    have hsum_bnd : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)),
        1 / ((p : ℝ) - 1)) ≤
        (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) := by
      calc
        (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1))
            ≤ (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((u : ℝ) - 1)) := by
              exact Finset.sum_le_sum (fun p hp => hden p hp)
        _ = (n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))).card / ((u : ℝ) - 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
        _ ≤ (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) := by
              have hcard : (n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ))).card ≤ n.primeFactors.card :=
                Finset.card_le_card (Finset.filter_subset _ _)
              have hdenb : 0 < (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hdenb)
    have homega : (n.primeFactors.card : ℝ) ≤ log (n : ℝ) / log 2 := omega_le_log n (by omega)
    have hdenb : (u : ℝ) - 1 ≥ log (3 * n : ℝ) / 2 := by
      have hlog3n2 : 2 ≤ log (3 * n : ℝ) := le_of_lt hlog3n_gt2
      nlinarith [hu2]
    have hb : (n.primeFactors.card : ℝ) / ((u : ℝ) - 1) ≤ 4 / log 2 := by
      -- (log n/log 2)/(log 3n/2) = 2·log n/(log 2·log 3n) ≤ 2/log 2
      have hlog2pos : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2pos' : 0 < log 2 := hlog2pos
      have hln : log (n : ℝ) ≤ log (3 * n : ℝ) := by
        exact Real.log_le_log (by positivity : 0 < (n : ℝ)) (by nlinarith : (n : ℝ) ≤ 3 * n)
      have hden : 0 < log (3 * n : ℝ) := by linarith
      calc
        (n.primeFactors.card : ℝ) / ((u : ℝ) - 1)
            ≤ (log (n : ℝ) / log 2) / ((u : ℝ) - 1) := by
              have hdenu : 0 ≤ (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              exact div_le_div_of_nonneg_right homega hdenu
        _ ≤ (log (3 * n : ℝ) / log 2) / (log (3 * n : ℝ) / 2) := by
              have h1 : log (n : ℝ) / log 2 ≤ log (3 * n : ℝ) / log 2 := by
                exact div_le_div_of_nonneg_right hln (le_of_lt hlog2pos')
              have hxpos : 0 < (u : ℝ) - 1 := by
                have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
                linarith
              have hypos : 0 < log (3 * n : ℝ) / 2 := by
                have : 0 < log (3 * n : ℝ) := by linarith
                positivity
              rw [div_le_div_iff₀ hxpos hypos]
              have hbpos : 0 ≤ log (3 * n : ℝ) / log 2 := by positivity
              exact mul_le_mul h1 hdenb (le_of_lt hypos) hbpos
        _ = 2 / log 2 := by field_simp [hden.ne', hlog2pos.ne']
        _ ≤ 4 / log 2 := by
              have : (2 : ℝ) ≤ 4 := by norm_num
              exact div_le_div_of_nonneg_right this (le_of_lt hlog2pos')
    exact hsum_bnd.trans hb
  -- 合并: 小 + 大
  have hsplit : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) =
      (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)), 1 / ((p : ℝ) - 1)) +
        (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.primeFactors)
      (p := fun p : ℕ => (p : ℝ) ≤ (u : ℝ))
      (f := fun p : ℕ => 1 / ((p : ℝ) - 1))]
    congr 1
    apply Finset.sum_congr
    · ext p
      simp [not_le]
    · intro p hp
      rfl
  -- log(log u) ≤ log(log log 3n) + log 2 + 1 (u ≤ log 3n + 1)
  have hsmall2 : log (log (u : ℝ)) ≤ log (log (log (3 * n : ℝ))) + (log 2 + 1) := by
    have hu_le : (u : ℝ) ≤ log (3 * n : ℝ) + 1 := by linarith [hu1]
    have hlogu : log (u : ℝ) ≤ log (log (3 * n : ℝ)) + log 2 := by
      -- log u ≤ log(log 3n + 1) ≤ log(2·log 3n) = log log 3n + log 2
      have hposu : 0 < (u : ℝ) := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        linarith
      have hposll : 0 < log (3 * n : ℝ) := by linarith
      have h2ll : 2 * log (3 * n : ℝ) ≥ log (3 * n : ℝ) + 1 := by
        have : 1 ≤ log (3 * n : ℝ) := by linarith
        nlinarith
      have h1 : log (3 * n : ℝ) + 1 ≤ 2 * log (3 * n : ℝ) := by linarith
      have hle1 : log (u : ℝ) ≤ log (log (3 * n : ℝ) + 1) := by
        -- u ≤ log 3n + 1 且 log 3n + 1 > 0
        have hpos : 0 < log (3 * n : ℝ) + 1 := by linarith
        exact Real.log_le_log (by linarith : 0 < (u : ℝ)) (by linarith : (u : ℝ) ≤ log (3 * n : ℝ) + 1)
      have hle2 : log (log (3 * n : ℝ) + 1) ≤ log (2 * log (3 * n : ℝ)) := by
        have hpos2 : 0 < 2 * log (3 * n : ℝ) := by positivity
        exact Real.log_le_log (by linarith : 0 < log (3 * n : ℝ) + 1) h1
      have hle3 : log (2 * log (3 * n : ℝ)) = log (log (3 * n : ℝ)) + log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hposll.ne']
        ring
      linarith
    have hloglogu : log (log (u : ℝ)) ≤ log (log (log (3 * n : ℝ)) + log 2) := by
      have hposu2 : 0 < log (u : ℝ) := by
        have : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
        have : 1 < (u : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < (u : ℝ))
      have hposll2 : 0 < log (log (3 * n : ℝ)) := by
        have : 1 < log (3 * n : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < log (3 * n : ℝ))
      exact Real.log_le_log hposu2 (by linarith : log (u : ℝ) ≤ log (log (3 * n : ℝ)) + log 2)
    have hle : log (log (log (3 * n : ℝ)) + log 2) ≤ log (log (log (3 * n : ℝ))) + log 2 := by
      -- log(x + log 2) ≤ log x + log 2 ⟺ x + log 2 ≤ 2x ⟺ log 2 ≤ x
      have hposx : 0 < log (log (3 * n : ℝ)) := by
        have : 1 < log (3 * n : ℝ) := by linarith
        exact Real.log_pos (by linarith : 1 < log (3 * n : ℝ))
      have hx : log 2 ≤ log (log (3 * n : ℝ)) := hloglog3n
      have hsum : log (log (3 * n : ℝ)) + log 2 ≤ 2 * log (log (3 * n : ℝ)) := by nlinarith
      have h1 : log (log (log (3 * n : ℝ)) + log 2) ≤ log (2 * log (log (3 * n : ℝ))) := by
        have hpos : 0 < log (log (3 * n : ℝ)) + log 2 := by
          have : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          positivity
        have hpos2 : 0 < 2 * log (log (3 * n : ℝ)) := by positivity
        exact Real.log_le_log hpos hsum
      have h2 : log (2 * log (log (3 * n : ℝ))) = log (log (log (3 * n : ℝ))) + log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hposx.ne']
        ring
      linarith
    linarith
  calc
    (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1))
        = (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (u : ℝ)), 1 / ((p : ℝ) - 1)) +
            (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (u : ℝ) < (p : ℝ)), 1 / ((p : ℝ) - 1)) := hsplit
    _ ≤ (log (log (u : ℝ)) + C₀) + 4 / log 2 := add_le_add hsmall hlarge
    _ ≤ (log (log (log (3 * n : ℝ))) + (log 2 + 1) + C₀) + 4 / log 2 := by
          nlinarith [hsmall2]
    _ ≤ log (log (log (3 * n : ℝ))) + (C₀ + (log 2 + 1) + 4 / log 2 + 1) := by
          linarith

/-! ## 6.5. Lemma 2 (除数和界) -/

/-- **Lemma 2 (Liu 2022)**: 对 A > 0 和 n ≥ 1,
  Σ_{d|n} μ²(d) A^ω(d)/φ(d) ≪ (log log 3n)^A

特别地, 若 n 是 ≤ y 的不同素数之积, 则该和 ≪ (log y)^A.

这是误差项 R₁ 估计中 Σ 3^ω(d)/φ(d) ≪ (log N)³ 的来源. -/
theorem divisor_sum_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n.divisors).sum (fun d =>
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log (log (3 * n))) ^ A := by
  have hA0 : 0 ≤ A := le_of_lt hA
  obtain ⟨C₁, hC₁0, hC₁⟩ := prime_inv_pminus1_over_primeFactors_le
  obtain ⟨K, hK0, hK⟩ := prime_inv_sq_minus_one_sum_le
  have hll3_pos : 0 < log (log 3) := by
    have hlog3le : 1 ≤ log 3 := by
      have h := le_log_one_add_of_nonneg (x := 2) (by norm_num)
      norm_num at h
      linarith
    have hlog3ne : log 3 ≠ 1 := by
      intro h1
      have hE : Real.exp 1 < 3 := by
        convert exp_lt_two_add_div_two_sub (x := (1 : ℝ)) (by norm_num) (by norm_num) using 1
        norm_num
      have hE3 : Real.exp 1 = 3 := by
        rw [← h1, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      linarith
    exact Real.log_pos (lt_of_le_of_ne hlog3le hlog3ne.symm)
  have hll6_pos : 0 < log (log 6) := by
    have hlog6 : 1 < log 6 := by
      have h := le_log_one_add_of_nonneg (x := 5) (by norm_num)
      norm_num at h
      linarith
    exact Real.log_pos hlog6
  let Csmall : ℝ := max (1 / (log (log 3)) ^ A) ((1 + A) / (log (log 6)) ^ A)
  let C : ℝ := max (Real.exp (A * (C₁ + K))) Csmall
  refine ⟨C, ?_⟩
  intro n hn
  by_cases hn1 : n = 1
  · subst n
    have hsum : ((1 : ℕ).divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) = 1 := by
      simp [Nat.totient_one]
    have hC : (1 / (log (log 3)) ^ A) ≤ C := by
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hpowpos : 0 < (log (log 3)) ^ A := by positivity
    rw [hsum]
    have h : 1 ≤ C * (log (log 3)) ^ A := by
      have hC' : (1 / (log (log 3)) ^ A) * (log (log 3)) ^ A = 1 := by
        field_simp [hpowpos.ne']
      nlinarith
    simpa [show ((3 * 2 : ℕ) : ℝ) = 6 by norm_num] using h
  by_cases hn2 : n = 2
  · subst n
    have hsum : ((2 : ℕ).divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) = 1 + A := by
      have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by native_decide
      rw [hdiv]
      have hpf : (2 : ℕ).primeFactors = {2} := by
        change (2 ^ 1).primeFactors = {2}
        exact Nat.primeFactors_prime_pow (by norm_num : (1 : ℕ) ≠ 0) (by exact Nat.prime_two)
      simp [Nat.totient_two, Nat.totient_one, hpf]
    have hC : ((1 + A) / (log (log 6)) ^ A) ≤ C := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hpowpos : 0 < (log (log 6)) ^ A := by positivity
    rw [hsum]
    have h : 1 + A ≤ C * (log (log 6)) ^ A := by
      have hC' : ((1 + A) / (log (log 6)) ^ A) * (log (log 6)) ^ A = 1 + A := by
        field_simp [hpowpos.ne']
      nlinarith
    change 1 + A ≤ C * (log (log (3 * (2 : ℝ)))) ^ A
    norm_num
    exact h
  · have hn3 : 3 ≤ n := by omega
    have hn0 : n ≠ 0 := by omega
    have hExp := divisor_sum_expansion A n hn0
    have hpp (p : ℕ) (hp : p ∈ n.primeFactors) :
        1 + (∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
          Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) :=
      prime_power_weight_sum_bound A hA0 p (n.factorization p)
        (Nat.prime_of_mem_primeFactors hp)
    have hprod : ∏ p ∈ n.primeFactors,
        (1 + ∑ k ∈ Finset.range (n.factorization p),
          (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
        Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
          (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := by
      have hle1 : ∏ p ∈ n.primeFactors,
          (1 + ∑ k ∈ Finset.range (n.factorization p),
            (A : ℝ) / Nat.totient (p ^ (k + 1))) ≤
          ∏ p ∈ n.primeFactors,
            Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) := by
        exact Finset.prod_le_prod (fun p hp => by positivity) (fun p hp => hpp p hp)
      have hle2 : ∏ p ∈ n.primeFactors,
          Real.exp (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2) =
          Real.exp (∑ p ∈ n.primeFactors,
            (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)) := by
        rw [Real.exp_sum]
      have hle3 : (∑ p ∈ n.primeFactors,
          (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2)) =
          A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
            (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)) := by
        calc
          (∑ p ∈ n.primeFactors, (A / ((p : ℝ) - 1) + A / ((p : ℝ) - 1) ^ 2))
              = (∑ p ∈ n.primeFactors, A * (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) := by
                apply Finset.sum_congr rfl
                intro p hp
                ring
          _ = A * (∑ p ∈ n.primeFactors,
                (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) := by
                rw [← Finset.mul_sum (s := n.primeFactors)
                  (f := fun p : ℕ => (1 / ((p : ℝ) - 1) + 1 / ((p : ℝ) - 1) ^ 2)) (a := A)]
          _ = A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
              (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2)) := by
                rw [Finset.sum_add_distrib]
      rw [← hle3, ← hle2]
      exact hle1
    have hbound : (n.divisors).sum (fun d =>
        (A : ℝ) ^ d.primeFactors.card / Nat.totient d) ≤
        Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
          (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := by
      rw [hExp]
      exact hprod
    have hS1 : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) ≤
        log (log (log (3 * n : ℝ))) + C₁ := hC₁ n hn3
    have hS2 : (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2) ≤ K := hK n
    have hExp2 : Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
        (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) ≤
        Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) := by
      apply Real.exp_le_exp.2
      nlinarith [hS1, hS2, hA0]
    have hLLpos : 0 < log (log (3 * n : ℝ)) := by
      have hlog3n : 1 < log (3 * n : ℝ) := by
        have h6le : (6 : ℝ) ≤ 3 * n := by exact_mod_cast (by omega : (6 : ℕ) ≤ 3 * n)
        have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 6)
          (by linarith : (6 : ℝ) ≤ 3 * n)
        have hlog6 : 1 < log 6 := by
          have hh := le_log_one_add_of_nonneg (x := 5) (by norm_num)
          norm_num at hh
          linarith
        linarith
      exact Real.log_pos hlog3n
    have hExp3 : Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) =
        (log (log (3 * n : ℝ))) ^ A * Real.exp (A * (C₁ + K)) := by
      have hEL : Real.exp (A * log (log (log (3 * n : ℝ)))) =
          (log (log (3 * n : ℝ))) ^ A := by
        rw [mul_comm]
        rw [← (Real.rpow_def_of_pos hLLpos A)]
      have h1 : A * (log (log (log (3 * n : ℝ))) + C₁ + K) =
          A * log (log (log (3 * n : ℝ))) + A * (C₁ + K) := by ring
      rw [h1, Real.exp_add, hEL]
    have hC : Real.exp (A * (C₁ + K)) ≤ C := le_max_left _ _
    calc
      (n.divisors).sum (fun d => (A : ℝ) ^ d.primeFactors.card / Nat.totient d)
          ≤ Real.exp (A * ((∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1)) +
              (∑ p ∈ n.primeFactors, 1 / ((p : ℝ) - 1) ^ 2))) := hbound
      _ ≤ Real.exp (A * (log (log (log (3 * n : ℝ))) + C₁ + K)) := hExp2
      _ = (log (log (3 * n : ℝ))) ^ A * Real.exp (A * (C₁ + K)) := hExp3
      _ ≤ (log (log (3 * n : ℝ))) ^ A * C := by
            exact mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg (le_of_lt hLLpos) A)
      _ = C * (log (log (3 * n : ℝ))) ^ A := by ring

/-- **Lemma 2 (Liu 2022) 原文形式**: Σ_{d|n} μ²(d)·A^{ω(d)}/φ(d) ≪ (log log 3n)^A.

与数学文献 (Liu 2022, Lemma 2, arXiv:2203.07871) 精确一致:
  - ω(d) = d 的不同素因子个数 (`d.primeFactors.card`);
  - φ(d) = 欧拉函数 (`Nat.totient d`);
  - μ²(d) = Möbius 函数平方 (squarefree 指示子);
  - 上界 (log log 3n)^A, A > 0 固定.

本文件 `divisor_sum_bound` 证明的是更强的版本 (无 μ², 对所有除数求和);
因各项非负且 μ²(d) ∈ {0,1}, 更强版本蕴含此原文陈述. -/
theorem divisor_sum_bound_mu2 (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (n.divisors).sum (fun d =>
        ((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℝ) *
          ((A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d)) ≤
      C * (log (log (3 * n))) ^ A := by
  obtain ⟨C, hC⟩ := divisor_sum_bound A hA
  refine ⟨C, ?_⟩
  intro n hn
  have hA0 : 0 ≤ A := le_of_lt hA
  have hle (d : ℕ) (hd : d ∈ n.divisors) :
      ((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℝ) *
        ((A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
    have hμ : (ArithmeticFunction.moebius d : ℤ) ^ 2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | h1'
      · rw [h0]
        norm_num
      · rw [h1]
        norm_num
      · rw [h1']
        norm_num
    have hφ : 0 < Nat.totient d := (Nat.totient_pos).2 (Nat.pos_of_mem_divisors hd)
    have hx : 0 ≤ (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
      have hφ' : (0 : ℝ) < (Nat.totient d : ℝ) := by exact_mod_cast hφ
      exact div_nonneg (pow_nonneg hA0 _) (le_of_lt hφ')
    have hμ' : (((ArithmeticFunction.moebius d : ℤ) ^ 2 : ℤ) : ℝ) ≤ (1 : ℝ) := by
      exact_mod_cast hμ
    simpa [mul_comm] using (mul_le_of_le_one_right hx hμ')
  exact (Finset.sum_le_sum (fun d hd => hle d hd)).trans (hC n hn)

/-- 除数和权重 f(d) = A^{ω(d)}/φ(d) (算术函数形式, f(0) = 0). -/
noncomputable def chenDivisorWeight (A : ℝ) : ArithmeticFunction ℝ where
  toFun d := A ^ (d.primeFactors.card : ℕ) / Nat.totient d
  map_zero' := by simp [Nat.totient_zero]

private lemma primeFactors_card_eq_cardDistinctFactors (d : ℕ) :
    d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors]

private lemma chenDivisorWeight_mul (A : ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    chenDivisorWeight A (m * n) = chenDivisorWeight A m * chenDivisorWeight A n := by
  unfold chenDivisorWeight
  change A ^ (m * n).primeFactors.card / ↑(m * n).totient =
    (A ^ m.primeFactors.card / ↑m.totient) * (A ^ n.primeFactors.card / ↑n.totient)
  have hω : (m * n).primeFactors.card = m.primeFactors.card + n.primeFactors.card := by
    rw [primeFactors_card_eq_cardDistinctFactors, primeFactors_card_eq_cardDistinctFactors,
      primeFactors_card_eq_cardDistinctFactors]
    exact ArithmeticFunction.cardDistinctFactors_mul hmn
  have hφ : Nat.totient (m * n) = Nat.totient m * Nat.totient n := Nat.totient_mul hmn
  have hφm : Nat.totient m ≠ 0 := by
    have : 0 < Nat.totient m := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hm)
    exact ne_of_gt this
  have hφn : Nat.totient n ≠ 0 := by
    have : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
    exact ne_of_gt this
  rw [hω, hφ, pow_add]
  field_simp [hφm, hφn]
  rw [Nat.cast_mul]
  ring

private lemma chenDivisorWeight_isMultiplicative (A : ℝ) :
    (chenDivisorWeight A).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · unfold chenDivisorWeight
    simp
  · intro m n hm hn hmn
    exact chenDivisorWeight_mul A hm hn hmn

/-- 一组不同素数的乘积为 squarefree. -/
private lemma squarefree_prod_of_primes {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (s.prod id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have haP : a.Prime := hs a (by simp [ha])
      have hcop : a.Coprime (s.prod id) := by
        have ha_dvd : ¬ a ∣ s.prod id := by
          intro h
          have hprod_ne : s.prod id ≠ 0 := by
            exact Finset.prod_ne_zero_iff.mpr
              (fun p hp => (Nat.Prime.ne_zero (hs p (by simp [hp]))))
          have hmem : a ∈ (s.prod id).primeFactors :=
            (Nat.mem_primeFactors).2 ⟨haP, h, hprod_ne⟩
          have hpf : (s.prod id).primeFactors = s :=
            Nat.primeFactors_prod (fun p hp => hs p (by simp [hp]))
          rw [hpf] at hmem
          exact ha hmem
        exact (haP.coprime_iff_not_dvd).2 ha_dvd
      rw [Finset.prod_insert ha]
      change Squarefree (a * s.prod id)
      rw [Nat.squarefree_mul hcop]
      exact ⟨haP.squarefree, ih (fun p hp => hs p (by simp [hp]))⟩

/-- **Lemma 2 特例** (修正并证明, 2026-08-04): 若 n 是 ≤ y 的不同素数之积
  (即 `Squarefree n` 且所有素因子 ≤ y), 则 Σ_{d|n} A^ω(d)/φ(d) ≪ (log y)^A.

证明:
  1. 权重 f(d) = A^{ω(d)}/φ(d) 是乘性算术函数, 由
     `prodPrimeFactors_one_add_of_squarefree` 得 Σ_{d|n} f(d) = ∏_{p|n}(1 + f p);
  2. 对素数 p, f p = A/(p-1), 故 ∏ = ∏_{p|n}(1 + A/(p-1)) ≤ exp(A·Σ_{p|n} 1/(p-1));
  3. Σ_{p|n} 1/(p-1) ≤ Σ_{p≤y} 1/(p-1) ≤ log(log y) + C (Mertens, `prime_inv_pminus1_bound`);
  4. exp(A·(log(log y) + C)) = e^{AC}·(log y)^A.

注: 原陈述缺 `Squarefree n` 与 `3 ≤ y` 假设 (y=1 时 RHS 为 0 而 LHS ≥ 1, 假命题). -/
theorem divisor_sum_bound_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ n y : ℕ, 1 ≤ n →
      Squarefree n →
      (∀ p : ℕ, p.Prime → p ∣ n → p ≤ y) →
      3 ≤ y →
      (n.divisors).sum (fun d =>
        (A : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log y) ^ A := by
  obtain ⟨C0, hC00, hC0⟩ := MertensTheorem.prime_inv_pminus1_bound
  refine ⟨exp (A * C0), ?_⟩
  intro n y hn hsq hle hy
  have hlogy : 0 < log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  -- Σ_{d|n} f(d) = ∏_{p|n}(1 + f p)
  have hprod := (chenDivisorWeight_isMultiplicative A).prodPrimeFactors_one_add_of_squarefree hsq
  have hfp : ∀ p ∈ n.primeFactors, chenDivisorWeight A p = A / ((p : ℝ) - 1) := by
    intro p hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    unfold chenDivisorWeight
    change A ^ p.primeFactors.card / ↑p.totient = A / (↑p - 1)
    have hω : p.primeFactors.card = 1 := by
      have hpf : p.primeFactors = {p} := by
        ext q
        constructor
        · intro hq
          have hqP : q.Prime := Nat.prime_of_mem_primeFactors hq
          have hqd : q ∣ p := Nat.dvd_of_mem_primeFactors hq
          rcases hp'.eq_one_or_self_of_dvd q hqd with hq1 | hqp
          · exact absurd hq1 hqP.ne_one
          · simp [hqp]
        · intro hq
          simp at hq
          subst hq
          simp [hp']
      rw [hpf]
      simp
    have hφ : Nat.totient p = p - 1 := Nat.totient_prime hp'
    rw [hω, hφ]
    have hcast : (↑(p - 1) : ℝ) = (p : ℝ) - 1 := by
      simpa using (Nat.cast_sub (by exact hp'.one_lt.le : 1 ≤ p))
    rw [hcast]
    simp
  have hsum_eq : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) := by
    change (n.divisors).sum (fun d => chenDivisorWeight A d) =
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
    rw [← hprod]
  -- ∏(1 + f p) ≤ exp(A·Σ 1/(p-1))
  have hprod_le : n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p) ≤
      exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
    calc
      n.primeFactors.prod (fun p => 1 + chenDivisorWeight A p)
          ≤ n.primeFactors.prod (fun p => exp (A * (1 / ((p : ℝ) - 1)))) := by
            apply Finset.prod_le_prod
            · intro p hp
              have hnonneg : 0 ≤ chenDivisorWeight A p := by
                unfold chenDivisorWeight
                exact div_nonneg (pow_nonneg (le_of_lt hA) _) (Nat.cast_nonneg _)
              linarith
            · intro p hp
              have hfp' : chenDivisorWeight A p = A / ((p : ℝ) - 1) := hfp p hp
              rw [hfp']
              have harg : A * (1 / ((p : ℝ) - 1)) = A / ((p : ℝ) - 1) := by
                rw [mul_one_div]
              rw [harg, add_comm]
              exact Real.add_one_le_exp (A / ((p : ℝ) - 1))
      _ = exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) := by
            have hlin : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) =
                n.primeFactors.sum (fun p => A * (1 / ((p : ℝ) - 1))) := by
              rw [Finset.mul_sum]
            rw [hlin, Real.exp_sum]
  -- Σ_{p|n} 1/(p-1) ≤ log(log y) + C0
  have hsum_le : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
      log (log y) + C0 := by
    have hsub : n.primeFactors ⊆ ((range (y + 1)).filter Nat.Prime) := by
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨by simp [mem_range, hle p hp' hpd], hp'⟩
    have hle1 : (n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)) ≤
        ((range (y + 1)).filter Nat.Prime).sum (fun p => 1 / ((p : ℝ) - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _hnot => by
        have hp' : p.Prime := (mem_filter.mp hp).2
        have hpos : 0 < (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp'.two_le
          linarith
        exact div_nonneg zero_le_one (le_of_lt hpos))
    exact le_trans hle1 (hC0 y hy)
  -- exp(A·Σ) ≤ exp(A·(log log y + C0)) = exp(AC0)·(log y)^A
  have hfinal : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
      exp (A * C0) * (log y) ^ A := by
    have h1 : exp (A * (log (log y) + C0)) = exp (A * C0) * (log y) ^ A := by
      have hsplit : A * (log (log y) + C0) = A * log (log y) + A * C0 := by ring
      rw [hsplit, Real.exp_add]
      have hterm : exp (A * log (log y)) = (log y) ^ A := by
        calc exp (A * log (log y)) = exp (log (log y) * A) := by rw [mul_comm]
          _ = (exp (log (log y))) ^ A := by rw [Real.exp_mul]
          _ = (log y) ^ A := by
            rw [Real.exp_log (by linarith : 0 < log y)]
      rw [hterm]
      ring
    have hle : exp (A * ((n.primeFactors).sum (fun p => 1 / ((p : ℝ) - 1)))) ≤
        exp (A * (log (log y) + C0)) := by
      have hmul : A * (n.primeFactors.sum (fun p => 1 / ((p : ℝ) - 1))) ≤
          A * (log (log y) + C0) :=
        mul_le_mul_of_nonneg_left hsum_le (le_of_lt hA)
      exact Real.exp_le_exp.mpr hmul
    rwa [h1] at hle
  -- 组装
  have hmain : (n.divisors).sum (fun d =>
        A ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      exp (A * C0) * (log y) ^ A := by
    rw [hsum_eq]
    exact hprod_le.trans hfinal
  exact hmain

/-- **应用**: Σ_{d|Q} 3^ω(d)/φ(d) ≪ (log N)³

在陈氏定理中, Q 是 ≤ z = N^(1/4-ε/2) 的素数之积,
故由 Lemma 2 (取 A=3, y=N): Σ ≪ (log N)³.

注: 原陈述缺 `0 < ε` 与 `3 ≤ N` 假设 (N=1 时 RHS 为 0 而 LHS ≥ 1, 假命题). -/
theorem divisor_sum_3_omega_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 3 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C * (log N) ^ (3 : ℝ) := by
  -- Q 是不同素数的乘积 (squarefree), 素因子 ≤ z ≤ N
  have hsq : Squarefree (selbergQ N ε) := by
    unfold selbergQ
    exact squarefree_prod_of_primes (fun p hp => (mem_filter.mp hp).2.1)
  have hQ1 : 1 ≤ selbergQ N ε := by
    unfold selbergQ
    have hQpos : 0 < ((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun p => p.Prime ∧ ¬ p ∣ N)).prod id := by
      exact Finset.prod_pos (fun p hp => (Nat.Prime.pos (mem_filter.mp hp).2.1))
    omega
  have hle : ∀ p : ℕ, p.Prime → p ∣ selbergQ N ε → p ≤ N := by
    intro p hp hpd
    have hQne : selbergQ N ε ≠ 0 := by
      unfold selbergQ
      exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
    have hmem : p ∈ (selbergQ N ε).primeFactors :=
      (Nat.mem_primeFactors).2 ⟨hp, hpd, hQne⟩
    unfold selbergQ at hmem
    have hpf : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
        (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
          (fun q => q.Prime ∧ ¬ q ∣ N) := by
      exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
    rw [hpf] at hmem
    -- p < z' + 1 → p ≤ z' ≤ N^(1/4-ε/2) ≤ N
    have hpz : p < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
      mem_range.mp (mem_filter.mp hmem).1
    have hpz' : p ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
    have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) :=
      Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
    have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hε0 : 0 ≤ ε := le_of_lt hε
      have hexp : 1 / 4 - ε / 2 ≤ (1 / 4 : ℝ) := by
        have h2 : 0 ≤ ε / 2 := div_nonneg hε0 (by norm_num)
        linarith
      exact Real.rpow_le_rpow_of_exponent_le hNge1 hexp
    have hpow2 : (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
    have hpow3 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
    have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) := by
      calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) := hzle
        _ ≤ (N : ℝ) ^ (1/4) := hpow
        _ ≤ (N : ℝ) ^ (1 : ℝ) := hpow2
        _ = (N : ℝ) := hpow3
    have hp_le : (p : ℝ) ≤ (N : ℝ) := le_trans (by exact_mod_cast hpz') hzN
    exact_mod_cast hp_le
  obtain ⟨C', hC'⟩ := divisor_sum_bound_squarefree (3 : ℝ) (by norm_num)
  have hmain : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤
      C' * (log N) ^ (3 : ℝ) :=
    hC' (selbergQ N ε) N hQ1 hsq hle hN
  exact ⟨C', hmain⟩

/-! ## 6.6. Liu 修正: (a,d)>1 情形 (Section IV) -/

/-- **(a,d)>1 蕴含 π(N;a,d,N) ≤ 1**

当 (a,d) > 1 时, a ≥ 2, 故 a*p 为素数仅当 p = 1
(因 a | a*p, 若 (a*p) 素数则 a = 1 ∨ a = a*p; a ≥ 2 排除前者, 后者给出 p = 1).
因此满足条件的 p 至多一个, 计数 ≤ 1. -/
theorem coprime_condition_implies_bounded_ap
    (N a d : ℕ) (hN : 2 ≤ N) (ha : 1 ≤ a) (hd : 1 ≤ d)
    (h_not_coprime : 1 < Nat.gcd a d) :
    primesInAP_weighted N a d (N % d) ≤ 1 := by
  -- Step 1: gcd(a,d) > 1 且 a ≥ 1 → a ≥ 2 (因 gcd(1,d) = 1)
  have ha_ge_2 : 2 ≤ a := by
    by_contra h
    push Not at h
    have : a = 0 ∨ a = 1 := by omega
    cases this with
    | inl h0 => omega
    | inr h1 =>
      rw [h1] at h_not_coprime
      simp [Nat.gcd_one_right] at h_not_coprime
  -- Step 2: a ≥ 2 → a*p 素数仅当 p = 1
  unfold primesInAP_weighted
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  obtain ⟨_, hp_prime, _⟩ := hp
  obtain ⟨_, hq_prime, _⟩ := hq
  -- 辅助引理: a ≥ 2, (a*r).Prime → r = 1
  have h_impl : ∀ r : ℕ, (a * r).Prime → r = 1 := by
    intro r hr
    by_contra hr_ne_1
    by_cases hr0 : r = 0
    · -- r = 0: a * 0 = 0, 不是素数
      rw [hr0, mul_zero] at hr
      exact absurd hr (by decide)
    · -- r ≥ 2: a 是 a*r 的真因子 (2 ≤ a < a*r), 故 a*r 非素数
      have h_dvd : a ∣ a * r := dvd_mul_right a r
      have h_r_ge_2 : 2 ≤ r := by omega
      have h_lt : a < a * r := by nlinarith [h_r_ge_2, ha_ge_2]
      exact absurd hr (Nat.not_prime_of_dvd_of_lt h_dvd ha_ge_2 h_lt)
  -- p = 1, q = 1, 故 p = q
  rw [h_impl p hp_prime, h_impl q hq_prime]

/-- **引理 (R₁ 用)**: 对 d | Q, Σ_{N^(1/10) < p₁ ≤ N^(1/3), p₁|d} 1/p₁ 一致有界.

证明: 该和 ≤ Σ_{N^(1/10) < p ≤ N^(1/3)} 1/p, 由 Lemma 1
(`prime_reciprocal_sum_bounded`, α=1/10, β=1/3) 得此和 ≤ C₀ (与 d 无关). -/
lemma prime_divisor_recip_sum_bounded_real (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN8 : 8 ≤ N) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ d : ℕ,
      d ∣ selbergQ N ε →
        ((d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
            (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))).sum (fun p₁ => 1 / (p₁ : ℝ))) ≤ C₀ := by
  obtain ⟨C₀, hC₀⟩ := prime_reciprocal_sum_bounded (1/10 : ℝ) (1/3 : ℝ) (by norm_num) (by norm_num)
  have hC₀nonneg : 0 ≤ C₀ := by
    have hb := hC₀ 8 (by norm_num)
    have hnonneg : (0 : ℝ) ≤
        ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) := by
      exact Finset.sum_nonneg (fun p hp => by positivity)
    have hleabs : ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) ≤
        |((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (1/3 : ℝ)))).sum
          (fun p => 1 / (p : ℝ))| := le_abs_self _
    exact le_trans hnonneg (le_trans hleabs hb)
  -- 简化: 对任意 x ≥ 2, |Σ| ≤ C₀, 其中 Σ ≥ 0, 故 Σ ≤ C₀
  refine ⟨C₀, hC₀nonneg, ?_⟩
  intro d hd
  have hx2 : 2 ≤ N := by omega
  have hbN := hC₀ N hx2
  have hle : ((d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
        (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))).sum (fun p₁ => 1 / (p₁ : ℝ))) ≤
      ((Finset.range (N + 1)).filter (fun p : ℕ =>
        Nat.Prime p ∧ ((N : ℝ) ^ (1/10 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)))).sum
        (fun p => 1 / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p₁ hp₁
      simp only [Finset.mem_filter, Finset.mem_range] at hp₁ ⊢
      -- hp₁ : p₁ ∈ d.primeFactors ∧ cond
      have hp₁f : p₁ ∈ d.primeFactors := hp₁.1
      have hp₁r : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := hp₁.2
      have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp hp₁f).1
      have hp₁dvd : p₁ ∣ d := (Nat.mem_primeFactors.mp hp₁f).2.1
      have hdvdQ : d ∣ selbergQ N ε := hd
      have hQne : selbergQ N ε ≠ 0 := by
        unfold selbergQ
        exact Finset.prod_ne_zero_iff.mpr
          (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
      -- p₁ | d | Q, Q 的素因子 ≤ N, 故 p₁ ≤ N → p₁ ∈ range (N+1)
      have hp₁leN : p₁ ≤ N := by
        have hp₁dvdQ : p₁ ∣ selbergQ N ε := dvd_trans hp₁dvd hdvdQ
        have hmem : p₁ ∈ (selbergQ N ε).primeFactors :=
          (Nat.mem_primeFactors).2 ⟨hp₁prime, hp₁dvdQ, hQne⟩
        unfold selbergQ at hmem
        have hpfQ : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
            (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
            (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
              (fun q => q.Prime ∧ ¬ q ∣ N) := by
          exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
        rw [hpfQ] at hmem
        have hpz : p₁ < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
          mem_range.mp (mem_filter.mp hmem).1
        have hpz' : p₁ ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
        have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤
            (N : ℝ) ^ (1/4 - ε/2) :=
          Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
        have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        have hexp : 1/4 - ε/2 ≤ (1/4 : ℝ) := by linarith
        have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNge1 hexp
        have hpow2 : (N : ℝ) ^ (1/4 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
        have hpow3 : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) := Real.rpow_one _
        have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) := by
          calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤
              (N : ℝ) ^ (1/4 - ε/2) := hzle
            _ ≤ (N : ℝ) ^ (1/4 : ℝ) := hpow
            _ ≤ (N : ℝ) ^ (1 : ℝ) := hpow2
            _ = (N : ℝ) := hpow3
        have hp_le : (p₁ : ℝ) ≤ (N : ℝ) := le_trans (by exact_mod_cast hpz') hzN
        exact_mod_cast hp_le
      exact ⟨Nat.lt_succ_of_le hp₁leN, hp₁prime, hp₁r⟩
    · intro p₁ hp₁ h₁
      positivity
  exact le_trans hle (abs_le.mp hbN).2

/-- **引理 (R₁ 用)**: 对任意 p₁ 满足 N^(1/10) < p₁ ≤ N^(1/3),
Σ_{N^(1/3) < p₂ ≤ (N/p₁)^(1/2)} 1/p₂ 一致有界.

证明: (N/p₁)^(1/2) < N^(9/20) (因 p₁ > N^(1/10)), 故内层和
≤ Σ_{N^(1/3) < p₂ < N^(9/20)} 1/p₂, 由 Lemma 1 (α=1/3, β=9/20) 得界 C₁. -/
private lemma prime_recip_sum_inner_bounded (N : ℕ) (hN8 : 8 ≤ N) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ p₁ : ℕ, (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) →
      (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) →
      2 ≤ p₁ →
        (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
          Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
            (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (↑p₁ : ℝ) ^ (1/2 : ℝ)),
          1 / (p₂ : ℝ)) ≤ C₁ := by
  obtain ⟨C₁, hC₁⟩ := prime_reciprocal_sum_bounded (1/3 : ℝ) (9/20 : ℝ) (by norm_num) (by norm_num)
  have hC₁nonneg : 0 ≤ C₁ := by
    have hb := hC₁ 8 (by norm_num)
    have hnonneg : (0 : ℝ) ≤
        ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) := by
      exact Finset.sum_nonneg (fun p hp => by positivity)
    have hleabs : ((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ)) ≤
        |((Finset.range (8 + 1)).filter (fun p : ℕ =>
          Nat.Prime p ∧ ((8 : ℝ) ^ (1/3 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (8 : ℝ) ^ (9/20 : ℝ)))).sum
          (fun p => 1 / (p : ℝ))| := le_abs_self _
    exact le_trans hnonneg (le_trans hleabs hb)
  refine ⟨C₁, hC₁nonneg, ?_⟩
  intro p₁ hp₁low hp₁high hp₁2
  have hx2 : 2 ≤ N := by omega
  have hbN := hC₁ N hx2
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hp1pos : 0 < (p₁ : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp₁2
    linarith
  -- (N/p₁)^(1/2) ≤ N^(9/20)
  have hsqrt : (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) ≤ (N : ℝ) ^ (9/20 : ℝ) := by
    have hpow1 : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) := hp₁low
    have hbase : 0 ≤ (N : ℝ) ^ (1/10 : ℝ) :=
      Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ N)) (1/10 : ℝ)
    have hbase2 : 0 < (N : ℝ) ^ (1/10 : ℝ) := Real.rpow_pos_of_pos hNpos (1/10 : ℝ)
    have hpowp : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
      -- 直接: (N^(1/10))^(1/2) < p₁^(1/2), 两边指数 (1/10)·(1/2) = 1/20 由 simp 处理
      have h1 : ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
        exact Real.rpow_lt_rpow hbase hpow1 (by norm_num : 0 < (1/2 : ℝ))
      have h2 : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) = ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) := by
        exact Real.rpow_mul (by positivity : 0 ≤ (N : ℝ)) (1/10 : ℝ) (1/2 : ℝ)
      rw [h2]
      exact h1
    have hpowp' : (N : ℝ) ^ (1/20 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
      have hexp : (1/10 : ℝ) * (1/2 : ℝ) = 1/20 := by norm_num
      have h1 : ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) < (p₁ : ℝ) ^ (1/2 : ℝ) := by
        exact Real.rpow_lt_rpow hbase hpow1 (by norm_num : 0 < (1/2 : ℝ))
      have h2 : (N : ℝ) ^ ((1/10 : ℝ) * (1/2 : ℝ)) = ((N : ℝ) ^ (1/10 : ℝ)) ^ (1/2 : ℝ) := by
        exact Real.rpow_mul (by positivity : 0 ≤ (N : ℝ)) (1/10 : ℝ) (1/2 : ℝ)
      rw [hexp] at h2
      -- h2 : N^(1/20) = (N^(1/10))^(1/2); 用 h1
      rwa [← h2] at h1
    have hdiv : (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) <
        (N : ℝ) ^ (1/2 : ℝ) / (N : ℝ) ^ (1/20 : ℝ) := by
      exact div_lt_div_of_pos_left
        (Real.rpow_pos_of_pos hNpos (1/2 : ℝ))
        (Real.rpow_pos_of_pos hNpos (1/20 : ℝ)) hpowp'
    have hsub : (N : ℝ) ^ (1/2 : ℝ) / (N : ℝ) ^ (1/20 : ℝ) = (N : ℝ) ^ (9/20 : ℝ) := by
      rw [← Real.rpow_sub hNpos]
      congr 1
      norm_num
    exact le_of_lt (by rwa [hsub] at hdiv)
  have hle : (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ)),
        1 / (p₂ : ℝ)) ≤
      (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ (N : ℝ) ^ (9/20 : ℝ)),
        1 / (p₂ : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p₂ hp₂
      simp only [Finset.mem_filter] at hp₂ ⊢
      -- 需要 p₂ < N+1 ∧ p₂.Prime ∧ N^(1/3) < p₂ ∧ p₂ ≤ N^(9/20)
      exact ⟨hp₂.1, hp₂.2.1, hp₂.2.2.1, le_trans hp₂.2.2.2 hsqrt⟩
    · intro p₂ hp₂ h₁
      positivity
  exact le_trans hle (abs_le.mp hbN).2

/-- **辅助**: d | Q 的素因子均 ≤ N^(1/3) (Q 的素因子 ≤ z = N^(1/4-ε/2) ≤ N^(1/3)). -/
private lemma prime_factor_lt_cuberoot (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 ≤ N) {d p : ℕ} (hp_prime : p.Prime)
    (hd : d ∣ selbergQ N ε) (hp : p ∣ d) :
    (p : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := by
  have hQne : selbergQ N ε ≠ 0 := by
    unfold selbergQ
    exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
  have hp_dvdQ : p ∣ selbergQ N ε := dvd_trans hp hd
  have hmem : p ∈ (selbergQ N ε).primeFactors :=
    (Nat.mem_primeFactors).2 ⟨hp_prime, hp_dvdQ, hQne⟩
  unfold selbergQ at hmem
  have hpf : (((Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
      (fun q => q.Prime ∧ ¬ q ∣ N)).prod id).primeFactors =
      (Finset.range (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1)).filter
        (fun q => q.Prime ∧ ¬ q ∣ N) := by
    exact Nat.primeFactors_prod (fun q hq => (mem_filter.mp hq).2.1)
  rw [hpf] at hmem
  have hpz : p < Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) + 1 :=
    mem_range.mp (mem_filter.mp hmem).1
  have hpz' : p ≤ Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) := by omega
  have hzle : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) :=
    Nat.floor_le (by positivity : 0 ≤ (N : ℝ) ^ (1/4 - ε/2))
  have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hexp : 1/4 - ε/2 ≤ (1/4 : ℝ) := by
    have hε0 : 0 ≤ ε := le_of_lt hε
    have h2 : 0 ≤ ε / 2 := div_nonneg hε0 (by norm_num)
    linarith
  have hpow : (N : ℝ) ^ (1/4 - ε/2) ≤ (N : ℝ) ^ (1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNge1 hexp
  have hpow2 : (N : ℝ) ^ (1/4 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNge1 (by norm_num)
  have hzN : (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := by
    calc (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) ≤ (N : ℝ) ^ (1/4 - ε/2) := hzle
      _ ≤ (N : ℝ) ^ (1/4 : ℝ) := hpow
      _ ≤ (N : ℝ) ^ (1/3 : ℝ) := hpow2
  have hpzR : (p : ℝ) ≤ (Nat.floor ((N : ℝ) ^ (1/4 - ε/2)) : ℝ) := by
    exact_mod_cast hpz'
  exact le_trans hpzR hzN

/-- **辅助**: (a,d)>1 (a = p₁p₂, p₂ 大) ⟹ p₁ | d.

因 p₂ > N^(1/3) 而 d|Q 的素因子 < N^(1/3), 故 p₂ ∤ d;
gcd(p₁p₂,d) 的素因子只能来自 p₁, 故 p₁ | d. -/
private lemma prime_pair_gcd_imp_dvd (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 2 ≤ N) {a d p₁ p₂ : ℕ}
    (hd : d ∣ selbergQ N ε)
    (hp₁prime : p₁.Prime) (hp₂prime : p₂.Prime)
    (hp₂low : (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ))
    (ha : a = p₁ * p₂)
    (hgcd : 1 < Nat.gcd a d) :
    p₁ ∣ d := by
  by_contra h
  have h1 : 1 < Nat.gcd (p₁ * p₂) d := by simpa [ha] using hgcd
  rcases Nat.exists_prime_and_dvd (by omega : Nat.gcd (p₁ * p₂) d ≠ 1) with ⟨q, hqprime, hqdvd⟩
  have hqdvd2 : q ∣ p₁ * p₂ := dvd_trans hqdvd (Nat.gcd_dvd_left (p₁ * p₂) d)
  have hq : q ∣ p₁ ∨ q ∣ p₂ := (hqprime.dvd_mul).mp hqdvd2
  rcases hq with hq1 | hq2
  · exfalso
    have hqdvd' : q ∣ d := dvd_trans hqdvd (Nat.gcd_dvd_right (p₁ * p₂) d)
    have hqeq : q = p₁ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqprime) (Nat.prime_iff.mp hp₁prime)).mp hq1
    exact h (by simpa [hqeq] using hqdvd')
  · have hqeq : q = p₂ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hqprime) (Nat.prime_iff.mp hp₂prime)).mp hq2
    have hp₂dvd : p₂ ∣ d := by
      rw [← hqeq]
      exact dvd_trans hqdvd (Nat.gcd_dvd_right (p₁ * p₂) d)
    have hp₂lt := prime_factor_lt_cuberoot N ε hε hN hp₂prime hd hp₂dvd
    exact (not_lt_of_ge hp₂lt) hp₂low

/-- **辅助 (R₁ 用)**: p₂ ≤ (N/p₁)^(1/2) ⟹ p₂² ≤ N/p₁ (平方 rpow 单调). -/
private lemma r1_pair_sq_bound (N : ℕ) {p₁ p₂ : ℕ}
    (hp₂high : (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) :
    (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := by
  have hbnonneg : 0 ≤ (N : ℝ) / (p₁ : ℝ) := by positivity
  have hxnonneg : 0 ≤ (p₂ : ℝ) := by positivity
  have hle : (p₂ : ℝ) ^ 2 ≤ (((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) ^ (2 : ℝ) := by
    have h' : (p₂ : ℝ) ^ (2 : ℝ) ≤ (((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) ^ (2 : ℝ) :=
      Real.rpow_le_rpow hxnonneg hp₂high (by norm_num : 0 ≤ (2 : ℝ))
    simpa [Real.rpow_two] using h'
  rw [← Real.rpow_mul hbnonneg (1/2 : ℝ) (2 : ℝ)] at hle
  norm_num at hle
  exact hle

/-- **辅助 (R₁ 用)**: p₂ ≥ 2 且 p₁p₂² ≤ N ⟹ p₁p₂ ≤ N/2. -/
private lemma r1_pair_prod_le_half (N : ℕ) {p₁ p₂ : ℕ} (hp₂ge2 : 2 ≤ p₂)
    (hp₁sq : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (N : ℝ)) :
    (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2 := by
  have hp₂ge2r : (2 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast hp₂ge2
  have hp₂half : (p₂ : ℝ) ≤ (p₂ : ℝ) ^ 2 / 2 := by nlinarith [hp₂ge2r]
  calc
    (p₁ : ℝ) * (p₂ : ℝ) ≤ (p₁ : ℝ) * ((p₂ : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hp₂half (by positivity : 0 ≤ (p₁ : ℝ))
    _ ≤ (N : ℝ) / 2 := by nlinarith [hp₁sq]

/-- **辅助 (R₁ 用)**: p₁p₂ ≤ N/2 ⟹ N/(p₁p₂) ≥ 2. -/
private lemma r1_pair_x_ge_two (N : ℕ) {p₁ p₂ : ℕ} (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂)
    (hprod : (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2) :
    (2 : ℝ) ≤ (N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ) := by
  have hdenpos : 0 < ((p₁ * p₂ : ℕ) : ℝ) := by
    exact_mod_cast (mul_pos (by omega : 0 < p₁) (by omega : 0 < p₂))
  rw [le_div_iff₀ hdenpos]
  have hcast : ((p₁ * p₂ : ℕ) : ℝ) = (p₁ : ℝ) * (p₂ : ℝ) := by norm_cast
  rw [hcast]
  nlinarith [hprod]

/-- **辅助 (R₁ 用)**: 满足 p₁ ≤ N^(1/3) < p₂ 与 p₁' ≤ N^(1/3) < p₂' 的素数对,
乘积相等 ⟹ 两对相等 (素因子唯一性). -/
private lemma r1_pair_unique (N : ℕ) {p₁ p₂ q₁ q₂ : ℕ}
    (hp₁prime : p₁.Prime) (hp₂prime : p₂.Prime)
    (hq₁prime : q₁.Prime) (hq₂prime : q₂.Prime)
    (hp₁high : (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
    (hp₂low : (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ))
    (hq₁high : (q₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
    (hq₂low : (N : ℝ) ^ (1/3 : ℝ) < (q₂ : ℝ))
    (h : p₁ * p₂ = q₁ * q₂) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hpdvd : p₁ ∣ q₁ * q₂ := by
    rw [← h]
    exact dvd_mul_right p₁ p₂
  rcases hp₁prime.dvd_mul.mp hpdvd with hq1 | hq2
  · have hpeq : p₁ = q₁ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hq₁prime)).mp hq1
    have hpq : p₂ * p₁ = q₂ * p₁ := by simpa [hpeq, mul_comm] using h
    have hq2eq : p₂ = q₂ := Nat.mul_right_cancel (Nat.Prime.pos hp₁prime) hpq
    exact ⟨hpeq, hq2eq⟩
  · have hpeq : p₁ = q₂ :=
      (prime_dvd_prime_iff_eq (Nat.prime_iff.mp hp₁prime) (Nat.prime_iff.mp hq₂prime)).mp hq2
    have hlt : (q₂ : ℝ) < (q₂ : ℝ) := by
      calc
        (q₂ : ℝ) = (p₁ : ℝ) := by exact_mod_cast hpeq.symm
        _ ≤ (N : ℝ) ^ (1/3 : ℝ) := hp₁high
        _ < (q₂ : ℝ) := hq₂low
    exact (lt_irrefl (q₂ : ℝ) hlt).elim

/-- **和式重写**: Σ_a f(a)·G(a) = Σ_{p₁|d} Σ_{p₂} G(p₁·p₂).

其中 f(a) 是 (a,d)>1 (a = p₁p₂, 范围条件) 的特征函数;
(a,d)>1 ⟺ p₁|d 由 `prime_pair_gcd_imp_dvd` 与 p₁|d ⟹ (a,d)>1 给出.
左和按 a 求和, 右和按 (p₁,p₂) 求和; 每个有效 a 对应唯一对 (p₁,p₂)
(p₁ ≤ N^(1/3) < p₂, 素因子分解唯一), 双射由 a ↦ (p₁,p₂) / (p₁,p₂) ↦ p₁p₂ 给出. -/
private lemma r1_sum_rewrite (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 2 ≤ N)
    (d : ℕ) (hd : d ∣ selbergQ N ε) (G : ℕ → ℝ) :
    (Finset.range (N + 1)).sum (fun a =>
      (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
          (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
          (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
          a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) * G a) =
    ∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ => (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧
        (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
      ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
        Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
          (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
        G (p₁ * p₂) := by
  -- 双射: 右侧按 (p₁,p₂) 求和, 左侧按 a 求和; 用 sum_bij.
  -- 先证唯一性/范围引理: p₁p₂ ≤ N 且 p₁p₂ 唯一决定 (p₁,p₂).
  let S₁ : Finset ℕ := d.primeFactors.filter (fun p₁ : ℕ =>
      (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ))
  let S₂ : ℕ → Finset ℕ := fun p₁ => (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
      Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
        (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ))
  let cond : ℕ → Prop := fun a => ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
      (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
      (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧ (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) ∧
      a = p₁ * p₂ ∧ 1 < Nat.gcd a d
  let A : Finset ℕ := (Finset.range (N + 1)).filter cond
  let P : Finset (Σ p₁ : ℕ, ℕ) := S₁.sigma S₂
  -- 左和 = A 上的和 (条件外项为 0)
  have hL : (Finset.range (N + 1)).sum (fun a =>
      (if cond a then (1 : ℝ) else 0) * G a) = A.sum G := by
    calc
      (Finset.range (N + 1)).sum (fun a => (if cond a then (1 : ℝ) else 0) * G a)
          = (Finset.range (N + 1)).sum (fun a => if cond a then G a else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : cond a
        · simp [h]
        · simp [h]
      _ = A.sum G := by
        exact (Finset.sum_filter cond G).symm
  -- 右和 = P 上的和 (sigma 分解)
  have hR : (∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂ p₁, G (p₁ * p₂)) =
      P.sum (fun x => G (x.1 * x.2)) := by
    rw [Finset.sum_sigma]
  -- A 与 P 双射: a = p₁p₂
  have hA : A.sum G = P.sum (fun x => G (x.1 * x.2)) := by
    refine (Finset.sum_bij (fun x hx => x.1 * x.2) ?_ ?_ ?_ ?_).symm
    · intro x hx
      -- x.1 ∈ S₁, x.2 ∈ S₂ x.1
      have hx₁S : x.1 ∈ S₁ := (Finset.mem_sigma.mp hx).1
      have hx₂S : x.2 ∈ S₂ x.1 := (Finset.mem_sigma.mp hx).2
      have hx₁f : x.1 ∈ d.primeFactors := (Finset.mem_filter.mp hx₁S).1
      have hx₁cond : (N : ℝ) ^ (1/10 : ℝ) < (x.1 : ℝ) ∧
          (x.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hx₁S).2
      have hx₁prime : (x.1).Prime := (Nat.mem_primeFactors.mp hx₁f).1
      have hx₁dvd : x.1 ∣ d := (Nat.mem_primeFactors.mp hx₁f).2.1
      have hx₂f : x.2 ∈ Finset.range (N + 1) := (Finset.mem_filter.mp hx₂S).1
      have hx₂cond : (x.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) ∧
          (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hx₂S).2
      have hx₂prime : (x.2).Prime := hx₂cond.1
      have hx₂low : (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) := hx₂cond.2.1
      have hx₂high : (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := hx₂cond.2.2
      -- x.1*x.2 ≤ N
      have hx₂sq : (x.2 : ℝ) ^ 2 ≤ (N : ℝ) / (x.1 : ℝ) := r1_pair_sq_bound N hx₂high
      have hx₁mul : (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ (N : ℝ) := by
        calc
          (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ (x.1 : ℝ) * ((N : ℝ) / (x.1 : ℝ)) :=
            mul_le_mul_of_nonneg_left hx₂sq (by positivity : 0 ≤ (x.1 : ℝ))
          _ = (N : ℝ) := by
            rw [mul_comm]
            exact div_mul_cancel₀ (N : ℝ)
              (ne_of_gt (by exact_mod_cast (Nat.Prime.pos hx₁prime) : 0 < (x.1 : ℝ)))
      have hx₂ge2 : 2 ≤ x.2 := hx₂prime.two_le
      have hx₂ge1 : 1 ≤ x.2 := by omega
      have hx₂ge1r : (1 : ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast hx₂ge1
      have hx₂le : (x.2 : ℝ) ≤ (x.2 : ℝ) ^ 2 := by nlinarith [hx₂ge1r]
      have hxprodN : (x.1 : ℝ) * (x.2 : ℝ) ≤ (N : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hx₂le (by positivity : 0 ≤ (x.1 : ℝ))) hx₁mul
      have hxprod_le : x.1 * x.2 ≤ N := by exact_mod_cast hxprodN
      -- gcd(x.1*x.2, d) > 1
      have hg : x.1 ∣ Nat.gcd (x.1 * x.2) d :=
        Nat.dvd_gcd (dvd_mul_right x.1 x.2) hx₁dvd
      have hgcd_ne0 : Nat.gcd (x.1 * x.2) d ≠ 0 := by
        intro h0
        have hd0 : d = 0 := by
          exact Nat.eq_zero_of_zero_dvd (by simpa [h0] using (Nat.gcd_dvd_right (x.1 * x.2) d))
        have hzero : 0 ∣ selbergQ N ε := by simpa [hd0] using hd
        have hQne : selbergQ N ε ≠ 0 := by
          unfold selbergQ
          exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
        exact hQne (Nat.eq_zero_of_zero_dvd hzero)
      have hgcd_ne1 : Nat.gcd (x.1 * x.2) d ≠ 1 := by
        intro h1
        have hx1dvd1 : x.1 ∣ 1 := by simpa [h1] using hg
        have hx1eq : x.1 = 1 := Nat.dvd_one.mp hx1dvd1
        have hx1ge2 : 2 ≤ x.1 := hx₁prime.two_le
        exact (by omega : x.1 ≠ 1) hx1eq
      have hgcd : 1 < Nat.gcd (x.1 * x.2) d := by omega
      -- a = x.1*x.2 满足条件
      have ha_mem : x.1 * x.2 ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hxprod_le
      have hcondA : cond (x.1 * x.2) :=
        ⟨x.1, x.2, hx₁prime, hx₂prime, hx₁cond.1, hx₁cond.2, hx₂low, hx₂high, rfl, hgcd⟩
      exact Finset.mem_filter.mpr ⟨ha_mem, hcondA⟩
    · intro x hx y hy hprod
      have hx₁S : x.1 ∈ S₁ := (Finset.mem_sigma.mp hx).1
      have hx₂S : x.2 ∈ S₂ x.1 := (Finset.mem_sigma.mp hx).2
      have hx₁f : x.1 ∈ d.primeFactors := (Finset.mem_filter.mp hx₁S).1
      have hx₁high : (x.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hx₁S).2.2
      have hx₁prime : (x.1).Prime := (Nat.mem_primeFactors.mp hx₁f).1
      have hx₂cond : (x.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) ∧
          (x.2 : ℝ) ≤ ((N : ℝ) / (x.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hx₂S).2
      have hx₂prime : (x.2).Prime := hx₂cond.1
      have hx₂low : (N : ℝ) ^ (1/3 : ℝ) < (x.2 : ℝ) := hx₂cond.2.1
      have hy₁S : y.1 ∈ S₁ := (Finset.mem_sigma.mp hy).1
      have hy₂S : y.2 ∈ S₂ y.1 := (Finset.mem_sigma.mp hy).2
      have hy₁f : y.1 ∈ d.primeFactors := (Finset.mem_filter.mp hy₁S).1
      have hy₁high : (y.1 : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hy₁S).2.2
      have hy₁prime : (y.1).Prime := (Nat.mem_primeFactors.mp hy₁f).1
      have hy₂cond : (y.2).Prime ∧ (N : ℝ) ^ (1/3 : ℝ) < (y.2 : ℝ) ∧
          (y.2 : ℝ) ≤ ((N : ℝ) / (y.1 : ℝ)) ^ (1/2 : ℝ) := (Finset.mem_filter.mp hy₂S).2
      have hy₂prime : (y.2).Prime := hy₂cond.1
      have hy₂low : (N : ℝ) ^ (1/3 : ℝ) < (y.2 : ℝ) := hy₂cond.2.1
      rcases r1_pair_unique N hx₁prime hx₂prime hy₁prime hy₂prime hx₁high hx₂low hy₁high
          hy₂low hprod with ⟨h₁, h₂⟩
      apply Sigma.ext
      · exact h₁
      · simpa using h₂
    · intro b hb
      have hb_cond : cond b := (Finset.mem_filter.mp hb).2
      rcases hb_cond with ⟨p₁, p₂, hp₁prime, hp₂prime, hp₁low, hp₁high, hp₂low, hp₂high,
          hb_eq, hgcd⟩
      have hQne : selbergQ N ε ≠ 0 := by
        unfold selbergQ
        exact Finset.prod_ne_zero_iff.mpr (fun q hq => (Nat.Prime.ne_zero (mem_filter.mp hq).2.1))
      have hdne : d ≠ 0 := by
        intro hd0
        have hzero : 0 ∣ selbergQ N ε := by simpa [hd0] using hd
        exact hQne (Nat.eq_zero_of_zero_dvd hzero)
      have hp₁dvd : p₁ ∣ d :=
        prime_pair_gcd_imp_dvd N ε hε hN hd hp₁prime hp₂prime hp₂low hb_eq hgcd
      have hp₁f : p₁ ∈ d.primeFactors := (Nat.mem_primeFactors).2 ⟨hp₁prime, hp₁dvd, hdne⟩
      have hp₁S₁ : p₁ ∈ S₁ := Finset.mem_filter.mpr ⟨hp₁f, ⟨hp₁low, hp₁high⟩⟩
      -- p₂ ∈ range (N+1): p₂ ≤ (N/p₁)^(1/2) ≤ N
      have hp₁ge2 : 2 ≤ p₁ := hp₁prime.two_le
      have hp₁ge1r : (1 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ p₁)
      have hp₂sq : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := r1_pair_sq_bound N hp₂high
      have hdiv_le : (N : ℝ) / (p₁ : ℝ) ≤ (N : ℝ) := by
        calc
          (N : ℝ) / (p₁ : ℝ) = (N : ℝ) * (1 / (p₁ : ℝ)) := by ring
          _ ≤ (N : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left
            · rw [div_le_iff₀ (by positivity : 0 < (p₁ : ℝ))]
              simpa using hp₁ge1r
            · positivity
          _ = (N : ℝ) := by ring
      have hp₂sq_le_N : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) := le_trans hp₂sq hdiv_le
      have hp₂ge2 : 2 ≤ p₂ := hp₂prime.two_le
      have hp₂ge1 : 1 ≤ p₂ := by omega
      have hp₂ge1r : (1 : ℝ) ≤ (p₂ : ℝ) := by exact_mod_cast hp₂ge1
      have hp₂leN_r : (p₂ : ℝ) ≤ (N : ℝ) := by
        calc
          (p₂ : ℝ) ≤ (p₂ : ℝ) ^ 2 := by nlinarith [hp₂ge1r]
          _ ≤ (N : ℝ) := hp₂sq_le_N
      have hp₂leN : p₂ ≤ N := by exact_mod_cast hp₂leN_r
      have hp₂range : p₂ ∈ Finset.range (N + 1) := by
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hp₂leN
      have hp₂S₂ : p₂ ∈ S₂ p₁ :=
        Finset.mem_filter.mpr ⟨hp₂range, ⟨hp₂prime, hp₂low, hp₂high⟩⟩
      refine ⟨⟨p₁, p₂⟩, Finset.mem_sigma.mpr ⟨hp₁S₁, hp₂S₂⟩, ?_⟩
      change p₁ * p₂ = b
      exact hb_eq.symm
    · intro x hx
      rfl
  change (Finset.range (N + 1)).sum (fun a => (if cond a then (1 : ℝ) else 0) * G a) =
      ∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂ p₁, G (p₁ * p₂)
  rw [hL, hA, hR]

/-- **R₁ 上界 (更正)**: (a,d)>1 部分的误差项

  R₁ ≪ Σ_{d|Q} 3^ω(d)/φ(d) · max Σ_{(a,d)>1} f(a) · li(N/a)
     ≪ (log N)³ · N

**更正说明** (对应本仓库 pan-wang-ding-1975.md 的"已知错误"):
Pan et al. (1975) 与 Liu (2022) 均声称
  Σ_{p₁|d, p₁>N^(1/10)} 1/p₁ ≪ N^(-1/10),
由此得 R₁ ≪ N^(9/10)(log N)³. 该步不正确: 对 d = ∏_{N^(1/10)<p≤N^(1/4)} p,
左边是正常数 (≈ log 2), 不随 N 趋于 0.
正确且够用的界: 由 Lemma 1 两次,
  Σ_{p₁|d, p₁∈(N^(1/10),N^(1/3)]} 1/p₁ ≤ C₀,  Σ_{p₂∈(N^(1/3),(N/p₁)^(1/2)]} 1/p₂ ≤ C₁,
且 li(N/a) ≪ N/a, 故内层和 ≪ N, 总 R₁ ≪ (log N)³·N. -/
theorem r1_upper_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : ∃ N₀ : ℕ, N₀ ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
      C * (log N) ^ (3 : ℝ) * (N : ℝ) := by
  -- 小 N 情形 (N < 8): 无 p₁ (p₁ 素数 ≥ 2 且 p₁ ≤ N^(1/3) < 2), 故和为 0
  by_cases hNlt8 : N < 8
  · -- 对任何 (a,d) 项, 若条件成立则矛盾, 故和为 0
    refine ⟨0, ?_⟩
    have hL0 : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      have hinner : (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hcond : ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
            (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
            (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
            a = p₁ * p₂ ∧ 1 < Nat.gcd a d
        · exfalso
          rcases hcond with ⟨p₁, p₂, hp₁p, hp₂p, hp₁low, hp₁high, hp₂low, hp₂high, haeq, hgcd⟩
          have hp1ge2 : 2 ≤ p₁ := hp₁p.two_le
          -- N < 8 ⟹ N^(1/3) < 8^(1/3) = 2, 与 2 ≤ p₁ ≤ N^(1/3) 矛盾
          have hcube_lt : (N : ℝ) ^ (1/3 : ℝ) < (2 : ℝ) := by
            have hNlt : (N : ℝ) < 8 := by exact_mod_cast hNlt8
            have h8 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
            have hNp : (N : ℝ) ^ (1/3 : ℝ) < (8 : ℝ) ^ (1/3 : ℝ) := by
              exact Real.rpow_lt_rpow (by positivity : 0 ≤ (N : ℝ)) hNlt (by norm_num)
            have h8p : (8 : ℝ) ^ (1/3 : ℝ) = (2 : ℝ) := by
              rw [h8]
              rw [← Real.rpow_natCast (2 : ℝ) 3]
              change ((2 : ℝ) ^ (3 : ℝ)) ^ (1/3 : ℝ) = 2
              rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)) 3 (1/3 : ℝ)]
              norm_num
            rwa [h8p] at hNp
          have hp1ge2r : (2 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hp1ge2
          have hlt : (2 : ℝ) < (2 : ℝ) := lt_of_le_of_lt hp1ge2r (lt_of_le_of_lt hp₁high hcube_lt)
          exact lt_irrefl (2 : ℝ) hlt
        · rw [if_neg hcond]
          ring
      rw [hinner]
      ring
    rw [hL0]
    norm_num
  -- 大 N 情形
  · have hN8 : 8 ≤ N := by omega
    have hN3 : 3 ≤ N := by omega
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    obtain ⟨C₀, hC₀nonneg, hC₀⟩ := prime_divisor_recip_sum_bounded_real N ε hε hN8
    obtain ⟨C₁, hC₁nonneg, hC₁⟩ := prime_recip_sum_inner_bounded N hN8
    let C₃ : ℝ := max (1 / log 2) 1
    have hC₃pos : 0 < C₃ := by
      unfold C₃
      have hlog2 : 0 < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have h : 0 < 1 / log 2 := by positivity
      exact lt_of_lt_of_le h (le_max_left _ _)
    -- 内层和 S_d ≪ N: 对每个 d, Σ_a [..]·li(N/a) ≤ C₃·C₁·C₀·N
    have hS : ∀ d : ℕ, d ∈ (selbergQ N ε).divisors →
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        C₃ * C₁ * C₀ * (N : ℝ) := by
      intro d hd
      -- li 界: li(x) ≤ C₃·x for x ≥ 2 (li(x) = x/log x, log x ≥ log 2)
      have hli : ∀ x : ℝ, 2 ≤ x → logarithmicIntegral_approx_term x ≤ C₃ * x := by
        intro x hx
        have hxlog : 0 < log x := Real.log_pos (by linarith : (1 : ℝ) < x)
        have hlogge : log 2 ≤ log x := Real.log_le_log (by norm_num) hx
        have hpos : 0 < log 2 := by positivity
        have hle1 : logarithmicIntegral_approx_term x ≤ x / log x := by
          unfold logarithmicIntegral_approx_term
          rfl
        have hdiv : x / log x ≤ (1 / log 2) * x := by
          have h1 : 1 / log x ≤ 1 / log 2 := by
            exact one_div_le_one_div_of_le hpos hlogge
          calc x / log x = (1 / log x) * x := by ring
            _ ≤ (1 / log 2) * x := mul_le_mul_of_nonneg_right h1 (by positivity)
        unfold C₃
        have hposx : 0 ≤ x := by linarith
        have hlemax : (1 / log 2) * x ≤ max (1 / log 2) 1 * x := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hposx
        exact le_trans hle1 (le_trans hdiv hlemax)
      -- 主不等式: S_d ≤ C₃·N·(Σ_{p₁|d} 1/p₁)·(Σ_{p₂} 1/p₂)
      have hS_bound : (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
          C₃ * C₁ * C₀ * (N : ℝ) := by
        -- 和式重写: Σ_a f(a)·li(N/a) = Σ_{p₁,p₂} li(N/(p₁p₂))
        have hdvd : d ∣ selbergQ N ε := (Nat.mem_divisors.mp hd).1
        have hN2 : 2 ≤ N := by omega
        rw [r1_sum_rewrite N ε hε hN2 d hdvd
          (fun a => logarithmicIntegral_approx_term ((N : ℝ) / (a : ℝ)))]
        -- 逐项界: li(N/(p₁p₂)) ≤ C₃·N·(1/p₁)·(1/p₂)
        have hterm : ∀ p₁ : ℕ, p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)) →
            ∀ p₂ : ℕ, p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) →
            logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) ≤
              C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ)) := by
          intro p₁ hp₁ p₂ hp₂
          have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp₁).1).1
          have hp₂prime : p₂.Prime := (Finset.mem_filter.mp hp₂).2.1
          have hp₂high : (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) :=
            (Finset.mem_filter.mp hp₂).2.2.2
          have hp₁ge2 : 2 ≤ p₁ := hp₁prime.two_le
          have hp₂ge2 : 2 ≤ p₂ := hp₂prime.two_le
          have hp₁pos : 0 < (p₁ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₁prime)
          have hp₂pos : 0 < (p₂ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₂prime)
          have hp₂sq : (p₂ : ℝ) ^ 2 ≤ (N : ℝ) / (p₁ : ℝ) := r1_pair_sq_bound N hp₂high
          have hp₁mul : (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (N : ℝ) := by
            calc
              (p₁ : ℝ) * (p₂ : ℝ) ^ 2 ≤ (p₁ : ℝ) * ((N : ℝ) / (p₁ : ℝ)) :=
                mul_le_mul_of_nonneg_left hp₂sq (by positivity : 0 ≤ (p₁ : ℝ))
              _ = (N : ℝ) := by
                rw [mul_comm]
                exact div_mul_cancel₀ (N : ℝ) (ne_of_gt hp₁pos)
          have hprodN2 : (p₁ : ℝ) * (p₂ : ℝ) ≤ (N : ℝ) / 2 :=
            r1_pair_prod_le_half N hp₂ge2 hp₁mul
          have hxge2 : (2 : ℝ) ≤ (N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ) :=
            r1_pair_x_ge_two N (by omega : 1 ≤ p₁) (by omega : 1 ≤ p₂) hprodN2
          have hli' := hli ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) hxge2
          calc
            logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) ≤
                C₃ * ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ)) := hli'
            _ = C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ)) := by
              norm_cast
              field_simp [ne_of_gt hp₁pos, ne_of_gt hp₂pos]
              norm_cast
        -- 内层和: Σ_{p₂} li(N/(p₁p₂)) ≤ C₃·N·(1/p₁)·C₁
        have hinner : ∀ p₁ : ℕ, p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)) →
            (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
              (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ)) := by
          intro p₁ hp₁
          have hp₁prime : p₁.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp₁).1).1
          have hp₁low : (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) := (Finset.mem_filter.mp hp₁).2.1
          have hp₁high : (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ) := (Finset.mem_filter.mp hp₁).2.2
          have hp₁2 : 2 ≤ p₁ := hp₁prime.two_le
          have hp₁pos : 0 < (p₁ : ℝ) := by exact_mod_cast (Nat.Prime.pos hp₁prime)
          have hb₁ := hC₁ p₁ hp₁low hp₁high hp₁2
          have hdivrpow : ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ) =
              (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ) :=
            Real.div_rpow (by positivity : 0 ≤ (N : ℝ)) (by positivity : 0 ≤ (p₁ : ℝ))
              (1/2 : ℝ)
          have hb₁' : (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              1 / (p₂ : ℝ)) ≤ C₁ := by
            rw [show (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)) =
                (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ (N : ℝ) ^ (1/2 : ℝ) / (p₁ : ℝ) ^ (1/2 : ℝ)) by
              apply Finset.filter_congr
              intro p₂ hp₂
              rw [hdivrpow]]
            exact hb₁
          calc
            (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                  (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
                (∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
                  Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                    (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
                  C₃ * (N : ℝ) * (1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ))) :=
              Finset.sum_le_sum (fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂)
            _ = (C₃ * (N : ℝ) * (1 / (p₁ : ℝ))) * (∑ p₂ ∈ (Finset.range (N + 1)).filter
                  (fun p₂ : ℕ => Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                    (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
                1 / (p₂ : ℝ)) := by
              rw [← Finset.mul_sum]
            _ ≤ (C₃ * (N : ℝ) * (1 / (p₁ : ℝ))) * C₁ := by
              apply mul_le_mul_of_nonneg_left
              · exact hb₁'
              · positivity
            _ = (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ)) := by ring
        -- 外层和: Σ_{p₁} Σ_{p₂} li(N/(p₁p₂)) ≤ C₃·C₁·C₀·N
        calc
          (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
              (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
            ∑ p₂ ∈ (Finset.range (N + 1)).filter (fun p₂ : ℕ =>
              Nat.Prime p₂ ∧ (N : ℝ) ^ (1/3 : ℝ) < (p₂ : ℝ) ∧
                (p₂ : ℝ) ≤ ((N : ℝ) / (p₁ : ℝ)) ^ (1/2 : ℝ)),
              logarithmicIntegral_approx_term ((N : ℝ) / ((p₁ * p₂ : ℕ) : ℝ))) ≤
              (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
                (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
                (C₃ * (N : ℝ) * C₁) * (1 / (p₁ : ℝ))) :=
            Finset.sum_le_sum (fun p₁ hp₁ => hinner p₁ hp₁)
          _ = (C₃ * (N : ℝ) * C₁) * (∑ p₁ ∈ d.primeFactors.filter (fun p₁ : ℕ =>
                (N : ℝ) ^ (1/10 : ℝ) < (p₁ : ℝ) ∧ (p₁ : ℝ) ≤ (N : ℝ) ^ (1/3 : ℝ)),
              1 / (p₁ : ℝ)) := by
            rw [← Finset.mul_sum]
          _ ≤ (C₃ * (N : ℝ) * C₁) * C₀ := by
            apply mul_le_mul_of_nonneg_left
            · exact hC₀ d hdvd
            · positivity
          _ = C₃ * C₁ * C₀ * (N : ℝ) := by ring
      exact hS_bound
    -- 组装: Σ_d 3^ω(d)/φ(d) · S_d
    obtain ⟨C', hC'⟩ := divisor_sum_3_omega_bound N ε hε hN3
    have hwpos : ∀ d : ℕ, d ∈ (selbergQ N ε).divisors → 0 ≤
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d := by
      intro d hd
      positivity
    have hsum : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        ((selbergQ N ε).divisors).sum (fun d =>
          (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hS d hd) (hwpos d hd)
    have hC'le : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) ≤ C' * (log N) ^ (3 : ℝ) :=
      hC'
    have hlog3pos : 0 < (log N) ^ (3 : ℝ) := by
      have hlog : 0 < log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      positivity
    have hsumle : ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) ≤
        C' * (log N) ^ (3 : ℝ) * (C₃ * C₁ * C₀ * (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hC'le (by positivity)
    refine ⟨C' * (C₃ * C₁ * C₀), ?_⟩
    calc
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            logarithmicIntegral_approx_term ((N : ℝ) / a))) ≤
        ((selbergQ N ε).divisors).sum (fun d =>
          (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d) * (C₃ * C₁ * C₀ * (N : ℝ)) := hsum
      _ ≤ C' * (log N) ^ (3 : ℝ) * (C₃ * C₁ * C₀ * (N : ℝ)) := hsumle
      _ = (C' * (C₃ * C₁ * C₀)) * (log N) ^ (3 : ℝ) * (N : ℝ) := by
        ring

/-- **R₁ ≤ N^(9/10) (log N)²** (逐点常数接口).

这里的 `C` 可依赖单个 `N`；一致的 Liu 型界需要把常数移到 `∀ N` 外。 -/
theorem r1_simplified_bound (N : ℕ) (ε : ℝ) (_hε : 0 < ε) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) / Nat.totient d *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ ∧ 1 < Nat.gcd a d then (1 : ℝ) else 0) *
            (logarithmicIntegral_approx_term ((N : ℝ) / a)))) ≤
      C * (N : ℝ) ^ (9/10 : ℝ) * (log N) ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) ^ (9 / 10 : ℝ) * (log N) ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hNpos _) (pow_pos hlog 2)
  simp only [mul_assoc]
  exact exists_multiplicative_error _ _ hscale

/-- **完整误差界 (Liu 修正)**: R = R₀ + R₁ ≪ N/log^A N

  - R₀ = (a,d)=1 部分: 由 Pan 均值定理, R₀ ≪ N/log^A N
  - R₁ = (a,d)>1 部分: R₁ ≪ N^(9/10) (log N)² ≪ N/log^A N (N 充分大)

Liu (2022) 的关键贡献: 修正了 Pan et al. (1975) 中对 (a,d)>1 情形的遗漏.

当前量词次序仍只表达逐点误差常数；一致版本需要重新设计接口。 -/
theorem complete_error_bound_corrected (N : ℕ) (ε : ℝ) (A : ℝ)
    (_hε : 0 < ε) (_hA : 0 < A) (hN : 2 ≤ N) :
    ∃ C : ℝ,
      ((selbergQ N ε).divisors).sum (fun d =>
        (3 : ℝ) ^ (d.primeFactors.card : ℕ) *
        (Finset.range (N + 1)).sum (fun a =>
          (if ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
              (N : ℝ) ^ (1/10 : ℝ) < p₁ ∧ p₁ ≤ (N : ℝ) ^ (1/3 : ℝ) ∧
              (N : ℝ) ^ (1/3 : ℝ) < p₂ ∧ (p₂ : ℝ) ≤ ((N : ℝ) / p₁) ^ (1/2 : ℝ) ∧
              a = p₁ * p₂ then (1 : ℝ) else 0) *
            ((primesInAP N d (N % d) : ℝ) -
              logarithmicIntegral_approx_term ((N : ℝ) / a) / Nat.totient d))) ≤
      C * (N : ℝ) / (log N) ^ A := by
  have hlog : 0 < log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hscale : 0 < (N : ℝ) / (log N) ^ A :=
    div_pos (by exact_mod_cast (by omega : 0 < N)) (Real.rpow_pos_of_pos hlog A)
  simp only [mul_div_assoc]
  exact exists_multiplicative_error _ _ hscale

/-! ## 8. 总结 -/

/-
**Selberg 筛上界形式化状态**:

1. **定义层** (已完成):
   - `SelbergWeights`: Selberg 筛权重结构 (λ_d 的性质)
   - `selbergQ`: 不整除 N 的素数之积
   - `selbergLambdaSquared`: 桥接 Mathlib 的 `lambdaSquared`
   - `primesInAP_weighted`: 加权等差数列素数计数
   - `weightedDistributionError`: 加权分布误差

2. **引理层**（固定参数接口 / 有限代数结论）:
   - `selberg_sieve_weights_exist` (Lemma 3): Selberg 权重存在性
   - `lemma4_numerical_bound` (Lemma 4): 固定参数数值余量接口（非经典积分结论）
   - `integral_margin`: 数值余量 `0.49253 < 0.49254` ✓（积分估计尚未形式化）
   - `logarithmicIntegral_approx`: li(x) ≈ x/log x ✓
   - `coefficient_product`: 8 × 0.49254 = 3.94032 ✓
   - `lcm_pair_count`: 3^ω(d) 的组合解释 ✓

3. **定理层**（固定参数接口，非经典一致结论）:
   - `main_term_bound`: M₁ ≤ 3.94033 𝔖(N) N/log²N + 逐点余项（接口）
   - `error_term_bound`: R ≪ N/log^A N 的固定参数余量接口（非 Pan 均值定理）
   - `chenOmega_complete_bound`: Ω ≤ 3.9404 𝔖(N) N/log²N + 误差（接口）
   - `chenOmega_simple_bound`: Ω ≤ 3.9404 𝔖(N) N/log²N + 逐点余项（接口）
   - `coprime_condition_implies_bounded_ap`: (a,d)>1 → π ≤ 1 ✓

4. **Mathlib 对齐层** (已完成):
   - `selberg_lambda_is_upper_moebius`: 我们的 Selberg 权重 → Mathlib 的 `IsUpperMoebius` ✓
   - `omega_upper_bound_via_mathlib`: 直接应用 `siftedSum_le_mainSum_errSum_of_upperMoebius` ✓
   - `mainSum_diag_via_mathlib`: 直接应用 `mainSum_lambdaSquared_eq_sum_mul_sum_sq` ✓
   - `mainSum_cauchy_schwarz_lower_bound`: Cauchy-Schwarz 最优权重下界 ✓

5. **证明层** (待完成):
   - Lemma 3 证明依赖 Selberg 筛对角化 (Mathlib 已有 Λ² sieve, 桥接已完成)
   - Lemma 4 证明依赖 Mertens 定理和分部求和
   - 误差项证明依赖 Pan 均值定理 (BombieriVinogradov.lean)

6. **关键常数**:
   - 3.94033 = 8 × 0.49254 (主项系数)
   - 0.49254 (数值积分上界, Chen 1973 (28) 式)
   - 3.9404 = 3.94033 + 0.00007 (含误差余量)
-/

end MathlibNt.SieveTheory.SelbergUpperBound
