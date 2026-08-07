/-
! # MathlibNt.ChensTheorem

## 陈氏定理 (Chen's Theorem)

**陈氏定理** (陈景润, 1966): 任何一个充分大的偶数都可以表示为一个素数
与一个半素数之和, 即存在常数 N, 使得对任意偶数 n ≥ N, 存在素数 p 和半素数 q,
使得 n = p + q.

半素数 (semiprime): 至多两个素数的乘积. 本文件使用 Mathlib 的
`Nat.IsAtMostAlmostPrime 2` 定义 (Ω(n) ≤ 2 且 n ≥ 2),
对应陈氏定理原文"至多两个素数的乘积".

Mathlib 中的 `Nat.IsSemiprime` 要求恰好 2 个素因子 (Ω = 2),
而陈氏定理允许 1 个 (素数本身) 或 2 个, 故使用 `IsAtMostAlmostPrime 2`.

参考:
  - Chen, J.R. "On the representation of a larger even integer as the sum
    of a prime and the product of at most two primes."
    Sci. Sinica 16 (1973), 157–176.
  - Mathlib `AlmostPrime.lean`: `Nat.IsAtMostAlmostPrime`, `Nat.IsAlmostPrime`
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.AlmostPrime
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.ChensTheorem

open scoped ArithmeticFunction.Omega

/-! ## 1. 半素数定义 (对齐 Mathlib) -/

/-- 半素数: 至多两个素数的乘积 (n ≥ 2).

定义为 `n ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 n`, 即:
- n ≥ 2 (排除 0 和 1)
- Ω(n) ≤ 2 (至多 2 个素因子, 计入重数)

这包含: 素数 (Ω = 1), 两素数乘积 (Ω = 2, 如 4=2·2, 6=2·3, 9=3·3). -/
def Semiprime (n : ℕ) : Prop :=
  n ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 n

/-! ## 2. 基本性质 (使用 Mathlib API) -/

/-- 素数是半素数 (Ω = 1 ≤ 2) -/
theorem prime_semiprime {p : ℕ} (hp : p.Prime) : Semiprime p := by
  refine ⟨hp.two_le, ?_⟩
  exact hp.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2)

/-- 两素数乘积是半素数 (Ω = 2 ≤ 2) -/
theorem mul_prime_semiprime {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    Semiprime (p₁ * p₂) := by
  refine ⟨?_, ?_⟩
  · have h1 : (2 : ℕ) ≤ p₁ := hp₁.two_le
    have h2 : (2 : ℕ) ≤ p₂ := hp₂.two_le
    nlinarith
  · exact hp₁.mul_isAlmostPrime_two hp₂ |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-- 4 = 2 * 2 是半素数 -/
theorem semiprime_four : Semiprime 4 := by
  have hp : Nat.Prime 2 := Nat.prime_two
  exact mul_prime_semiprime hp hp

/-- 6 = 2 * 3 是半素数 -/
theorem semiprime_six : Semiprime 6 := by
  have hp3 : Nat.Prime 3 := by decide
  exact mul_prime_semiprime Nat.prime_two hp3

/-- 9 = 3 * 3 是半素数 -/
theorem semiprime_nine : Semiprime 9 := by
  have hp3 : Nat.Prime 3 := by decide
  exact mul_prime_semiprime hp3 hp3

/-- 10 = 2 * 5 是半素数 -/
theorem semiprime_ten : Semiprime 10 := by
  have hp5 : Nat.Prime 5 := by decide
  exact mul_prime_semiprime Nat.prime_two hp5

/-- 15 = 3 * 5 是半素数 -/
theorem semiprime_fifteen : Semiprime 15 := by
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  exact mul_prime_semiprime hp3 hp5

/-- 1 不是半素数 (n ≥ 2 排除 1) -/
theorem not_semiprime_one : ¬ Semiprime 1 := by
  intro h
  exact absurd h.1 (by decide)

/-! ## 3. 构造性等价 -/

/-- 半素数的构造性刻画: n 为素数, 或 n 为两素数乘积. -/
theorem semiprime_iff :
    Semiprime n ↔ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ n = p₁ * p₂ := by
  constructor
  · -- Mathlib 定义 → 构造性定义
    intro h
    obtain ⟨hn2, hn⟩ := h
    obtain ⟨hn0, hΩ⟩ := hn
    -- n ≥ 2, 故 n ≠ 1, 存在素因子 p ∣ n
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hn1
    -- n = p * m
    obtain ⟨m, hm⟩ := exists_eq_mul_right_of_dvd hp_dvd
    -- p ≠ 0 (素数), m ≠ 0 (n ≠ 0 且 n = p * m)
    have hp0 : p ≠ 0 := hp.ne_zero
    have hm0 : m ≠ 0 := by
      intro heq; rw [heq, mul_zero] at hm; omega
    -- Ω(n) = Ω(p * m) = Ω(p) + Ω(m) = 1 + Ω(m)
    have hΩn : Ω n = 1 + Ω m := by
      rw [hm, ArithmeticFunction.cardFactors_mul hp0 hm0,
        ArithmeticFunction.cardFactors_apply_prime hp]
    -- Ω(m) ≤ 1
    have hΩm_le : Ω m ≤ 1 := by omega
    -- 分情况讨论 Ω(m)
    by_cases h0 : Ω m = 0
    · -- Ω(m) = 0 → m = 1 → n = p → 素数
      left
      have hm1 : m = 1 := by
        rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h | h
        · exact absurd h hm0
        · exact h
      rw [hm, hm1, mul_one]
      exact hp
    · -- Ω(m) = 1 → m 为素数 → n = p * m
      right
      have hm_prime : m.Prime :=
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
      exact ⟨p, m, hp, hm_prime, hm⟩
  · -- 构造性定义 → Mathlib 定义
    rintro (hn | ⟨p₁, p₂, hp₁, hp₂, hn⟩)
    · -- n 为素数: Ω(n) = 1 ≤ 2, n ≥ 2
      refine ⟨hn.two_le, ?_⟩
      exact hn.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2)
    · -- n = p₁ * p₂: Ω(n) = 2 ≤ 2, n ≥ 4 ≥ 2
      subst hn
      refine ⟨?_, ?_⟩
      · nlinarith [hp₁.two_le, hp₂.two_le]
      · exact hp₁.mul_isAlmostPrime_two hp₂ |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-! ## 4. 陈氏定理的形式化陈述 -/

/-- 陈氏定理在切换计数桥接下的形式 (Chen's Theorem, 1966):

存在一个常数 N, 使得对于所有偶数 n ≥ N, 存在素数 p 和半素数 q, 使得 n = p + q. -/
theorem chens_theorem
    (h_analytic : SieveTheory.SwitchingPrinciple.ChenAnalyticBounds)
    (h_bridge : SieveTheory.SwitchingPrinciple.ChenCountingBridge) :
    ∃ N : ℕ,
      ∀ n : ℕ,
        n ≥ N → Even n →
          ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q := by
  have h_key : ∀ n : ℕ, Even n → n ≥ 1000 →
      SieveTheory.SwitchingPrinciple.chenW n -
        SieveTheory.SwitchingPrinciple.chenOmega n / 2 > 0 := by
    intro n hn_even hn_large
    exact SieveTheory.SwitchingPrinciple.chen_key_inequality h_analytic n hn_even hn_large
  obtain ⟨N₀, hchen⟩ :=
    SieveTheory.SwitchingPrinciple.key_inequality_implies_chen h_bridge h_key
  refine ⟨N₀, ?_⟩
  intro n hn_large hn_even
  obtain ⟨p, q, hp, hq_two, hq_almost, hn⟩ := hchen n hn_large hn_even
  exact ⟨p, q, hp, ⟨hq_two, hq_almost⟩, hn⟩

/-! ## 5. 陈氏定理的弱化形式 -/

/-- 弱化陈氏定理: 对任意 N, 存在偶数 n ≥ N 可以表示为素数 + 半素数.

**证明思路**: 由欧几里得定理, 取素数 p ≥ max N 3, 令 n = p + 3.
p ≥ 3 故 p 为奇素数, n = p + 3 为偶数, q = 3 是素数 (从而半素数). -/
theorem chens_theorem_weak :
    ∀ N : ℕ, ∃ n : ℕ,
      n ≥ N ∧ Even n ∧ ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q := by
  intro N
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨p + 3, ?_, ?_, ?_⟩
  · have : N ≤ max N 3 := le_max_left N 3
    linarith
  · rcases hp_prime.eq_two_or_odd' with h2 | hodd
    · rw [h2] at hp_ge
      have : (3 : ℕ) ≤ max N 3 := le_max_right N 3
      linarith
    · exact hodd.add_odd (by decide : Odd 3)
  · exact ⟨p, 3, hp_prime, prime_semiprime (by decide), rfl⟩

/-! ## 6. 具体数值验证 -/

/-- 4 = 2 + 2 -/
theorem chen_example_four : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (4 : ℕ) = p + q := by
  use 2, 2
  refine ⟨Nat.prime_two, prime_semiprime Nat.prime_two, by decide⟩

/-- 6 = 3 + 3 -/
theorem chen_example_six : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (6 : ℕ) = p + q := by
  use 3, 3
  have hp : Nat.Prime 3 := by decide
  refine ⟨hp, prime_semiprime hp, by decide⟩

/-- 8 = 3 + 5 -/
theorem chen_example_eight : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (8 : ℕ) = p + q := by
  use 3, 5
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  refine ⟨hp3, prime_semiprime hp5, by decide⟩

/-- 10 = 3 + 7 -/
theorem chen_example_ten : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (10 : ℕ) = p + q := by
  use 3, 7
  have hp3 : Nat.Prime 3 := by decide
  have hp7 : Nat.Prime 7 := by decide
  refine ⟨hp3, prime_semiprime hp7, by decide⟩

/-- 10 = 5 + 5 -/
theorem chen_example_ten' : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (10 : ℕ) = p + q := by
  use 5, 5
  have hp : Nat.Prime 5 := by decide
  refine ⟨hp, prime_semiprime hp, by decide⟩

/-- 12 = 5 + 7 -/
theorem chen_example_twelve : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (12 : ℕ) = p + q := by
  use 5, 7
  have hp5 : Nat.Prime 5 := by decide
  have hp7 : Nat.Prime 7 := by decide
  refine ⟨hp5, prime_semiprime hp7, by decide⟩

/-- 14 = 3 + 11 -/
theorem chen_example_fourteen : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (14 : ℕ) = p + q := by
  use 3, 11
  have hp3 : Nat.Prime 3 := by decide
  have hp11 : Nat.Prime 11 := by decide
  refine ⟨hp3, prime_semiprime hp11, by decide⟩

/-- 22 = 3 + 19 -/
theorem chen_example_twenty_two : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (22 : ℕ) = p + q := by
  use 3, 19
  have hp3 : Nat.Prime 3 := by decide
  have hp19 : Nat.Prime 19 := by decide
  refine ⟨hp3, prime_semiprime hp19, by decide⟩

/-- 22 = 5 + 17 -/
theorem chen_example_twenty_two' : ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ (22 : ℕ) = p + q := by
  use 5, 17
  have hp5 : Nat.Prime 5 := by decide
  have hp17 : Nat.Prime 17 := by decide
  refine ⟨hp5, prime_semiprime hp17, by decide⟩

/-! ## 7. 与哥德巴赫猜想的关系 -/

/-- 哥德巴赫猜想蕴含陈氏定理 -/
theorem goldbach_implies_chen
    (h_goldbach : ∀ n : ℕ, n > 2 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) :
    ∃ N : ℕ,
      ∀ n : ℕ, n ≥ N → Even n →
        ∃ p q : ℕ, p.Prime ∧ Semiprime q ∧ n = p + q := by
  use 3
  intro n hn heven
  have hn2 : n > 2 := by linarith
  obtain ⟨p, q, hp, hq, hpq⟩ := h_goldbach n hn2 heven
  exact ⟨p, q, hp, prime_semiprime hq, hpq⟩

/-! ## 8. 辅助引理 -/

/-- 半素数至少为 2 (定义直接给出) -/
theorem semiprime_ge_two {n : ℕ} (h : Semiprime n) : n ≥ 2 := h.1

/-- 12 不是半素数: 12 = 2²·3, Ω(12) = 3 > 2. -/
theorem not_semiprime_twelve : ¬ Semiprime 12 := by
  intro h
  obtain ⟨_, hn⟩ := h
  obtain ⟨hn0, hΩ⟩ := hn
  -- 计算 Ω 12 = 3
  have hΩ12 : Ω 12 = 3 := by
    have h12_eq : (12 : ℕ) = 2 ^ 2 * 3 := by decide
    rw [h12_eq]
    rw [ArithmeticFunction.cardFactors_mul (by decide : (2 ^ 2 : ℕ) ≠ 0)
      (by decide : (3 : ℕ) ≠ 0)]
    have hΩ4 : Ω (2 ^ 2) = 2 :=
      ArithmeticFunction.cardFactors_apply_prime_pow (by decide : Nat.Prime 2)
    have hΩ3 : Ω 3 = 1 :=
      ArithmeticFunction.cardFactors_apply_prime (by decide : Nat.Prime 3)
    rw [hΩ4, hΩ3]
  rw [hΩ12] at hΩ
  omega

/-! ## 9. 与 Mathlib `Nat.IsSemiprime` 的关系 -/

/-- Mathlib 的 `IsSemiprime` 蕴含我们的 `Semiprime` -/
theorem isSemiprime_implies_semiprime {n : ℕ} (h : n.IsSemiprime) : Semiprime n := by
  have hΩ : Ω n = 2 := h.2
  have hn2 : 2 ≤ n := by
    have hΩpos : 0 < Ω n := hΩ ▸ (by decide : (0 : ℕ) < 2)
    have h1lt : 1 < n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp hΩpos
    omega
  refine ⟨hn2, ?_⟩
  exact h.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-! ## 10. 总结 -/

/-
**陈氏定理的形式化状态**:

1. **定义层** (已完成, 对齐 Mathlib):
   - `Semiprime n`: `n ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 n` (Ω(n) ≤ 2 且 n ≥ 2)
   - `prime_semiprime` / `mul_prime_semiprime`: 使用 Mathlib API 直接证明
   - `isSemiprime_implies_semiprime`: Mathlib `IsSemiprime` ⊆ `Semiprime`

2. **陈述层** (已完成):
   - `chens_theorem`: 在 `ChenAnalyticBounds` 与 `ChenCountingBridge` 下的定性陈述
   - `chens_theorem_weak`: 弱化形式 (无穷多偶数满足分解)

3. **证明层**:
   - `chens_theorem`: ✅ 条件形式已证明；统一解析估计和精确切换计数作为明示输入
   - `chens_theorem_weak`: ✅ 已证明 (利用欧几里得定理构造 n = p + 3)
   - `goldbach_implies_chen`: ✅ 已证明 (哥德巴赫猜想蕴含陈氏定理)
   - `not_semiprime_twelve`: ✅ 已证明 (Ω(12) = 3 > 2, 使用 cardFactors_mul)
   - `semiprime_iff` 反向: ✅ 已证明 (构造性定义 → Mathlib 定义)
   - `semiprime_iff` 正向: ✅ 已证明 (取素因子 p, 由 Ω(n) = 1 + Ω(m) ≤ 2 分情况)

4. **验证层** (已完成):
   - 9 个具体偶数的验证 (4, 6, 8, 10, 12, 14, 22)

**Mathlib 对齐说明**:
   - `Nat.IsAtMostAlmostPrime 2 n`: Ω(n) ≤ 2 (至多 2 个素因子) — 陈氏定理原文
   - `Nat.IsSemiprime n` = `IsAlmostPrime 2 n`: Ω(n) = 2 (恰好 2 个素因子) — Mathlib 定义
   - `Semiprime n` = `n ≥ 2 ∧ IsAtMostAlmostPrime 2 n`: 排除 1, 包含素数
-/

end MathlibNt.ChensTheorem
