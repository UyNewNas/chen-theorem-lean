import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# Pan truncation input structural reduction

Structural reduction of CorrectedChenPanTruncationInput: rem Moebius decomposition,
triangle inequality, reduction to two analytic steps (ChenPanTruncationSieveBound,
ChenPanTruncationMainTermBound). Zero sorry; analytic steps are explicit Props.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset Filter
open Asymptotics

open scoped Topology

open scoped Classical
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000
/-- **Pan 截断筛界 (解析台阶, chen #8)**: 分布误差部分 — 对所有 `d | P(N)`
与 `1 ≠ e | F(N)` 的 `lcm(d,e)` 模数, 以及截断外 (`¬(2 ≤ d ∧ d ≤ D)`) 模数上的
a=1 Pan 分布误差 `|Δ'(m)| = |panDistributionError (N−2) 1 m (N % m)|`, 加权
`3^{ω(d)}` 和 ≤ `C·N/log^A N`. 经典来源: Pan 1963 / Halberstam–Richert
Ch.10 支撑截断的分布型部分 (研究级输入, 与 `PanMeanValueUniform` 同级). -/
def ChenPanTruncationSieveBound : Prop :=
  ∀ A : ℝ, 0 < A → ∀ B : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
    ∀ N : ℕ, x₀ ≤ N → Even N →
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            |(μ e : ℝ)| *
              |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 (Nat.lcm d e) (N % Nat.lcm d e)|)) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors.filter (fun d =>
          ¬ (2 ≤ d ∧ d ≤ Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B))),
        (3 : ℝ) ^ d.primeFactors.card *
          |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A

/-- **Pan 截断主项 (解析台阶, chen #8)**: `li` 微差与 `|li(N−2)|` 的
`1/φ` 加权除数型和 — `|li(N−2) − li(N)|/φ(d)` 与
`Σ_{1≠e|F} |μ(e)|·|li(N−2)|/φ(lcm(d,e))` 的 `3^{ω(d)}` 加权和
≤ `C·N/log^A N` (li 主项微差, 标准解析估计). -/
def ChenPanTruncationMainTermBound : Prop :=
  ∀ A : ℝ, 0 < A → ∀ B : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
    ∀ N : ℕ, x₀ ≤ N → Even N →
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          (|AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
              AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)| /
            (Nat.totient d : ℝ))) +
      (∑ d ∈ (correctedChenSiftingProduct N).divisors,
        (3 : ℝ) ^ d.primeFactors.card *
          |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            (μ e : ℝ) * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|) ≤
        C * (N : ℝ) / (log (N : ℝ)) ^ A

/-- **`rem d − Δ'(d)` 的精确展开 (Möbius 校正)**: 由 `rem` 的 Möbius 分解
(`correctedChenRem_eq_moebiusBaseCount`) 与基计数分布误差恒等式
(`supportAPBaseCount_distributionError`), `e = 1` 项 `μ(1)·base(lcm(d,1)) = base(d)`
与 `Δ'(d)` 中的 `base(d)` 相消, 得
`rem d − Δ'(d) = (li(N−2) − li(N))/φ(d) + Σ_{1≠e|F} μ(e)·base(lcm(d,e))`,
其中 `li(x) = logarithmicIntegral x`, `base(q)` 是 `#{p < N : p 素数, 2 ≤ N−p,
p ≡ N [MOD q]}` 的实数值计数, `φ(q) = Nat.totient q`. -/
theorem correctedChenRem_sub_distributionError_eq (N d : ℕ)
    (hd : d ∣ correctedChenSiftingProduct N) (hN : 2 ≤ N) :
    (correctedChenBoundingSieve N).rem d -
        AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d) =
      (AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
          AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)) / (Nat.totient d : ℝ) +
        (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) := by
  classical
  rw [correctedChenRem_eq_moebiusBaseCount N d hd]
  rw [← supportAPBaseCount_distributionError N d hN]
  have hliN : (1 : ℝ) / (Nat.totient d : ℝ) * ((N : ℝ) / log (N : ℝ)) =
      AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ) / (Nat.totient d : ℝ) := by
    unfold AnalyticNumberTheory.Sieve.logarithmicIntegral
    ring
  rw [hliN]
  let f : ℕ → ℝ := fun e =>
    (μ e : ℝ) * (((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)
  have hsing : (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e = 1), f e) =
      (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d])).card : ℝ) := by
    rw [Finset.sum_eq_single (1 : ℕ)]
    · simp [f, ArithmeticFunction.moebius_apply_one]
    · intro b hb hbne
      exfalso
      rcases Finset.mem_filter.mp hb with ⟨_, hb1⟩
      exact hbne hb1
    · intro hnot
      exfalso
      exact hnot (Finset.mem_filter.mpr ⟨(Nat.mem_divisors.mpr ⟨Nat.one_dvd _, correctedChenForbiddenProduct_ne_zero N⟩), rfl⟩)
  rw [← Finset.sum_filter_add_sum_filter_not (correctedChenForbiddenProduct N).divisors
    (fun e => e = 1) f]
  rw [hsing]
  -- 化简: Σ_{e=1} f e + Σ_{e≠1} f e − li(N)/φ(d) − Δ'(d) = (li(N−2)−li(N))/φ(d) + Σ_{e≠1} f e
  -- 把求和项抽象为变量 (避免 ring 展开巨大求和), 再做线性化简
  let S : ℝ := ∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1), f e
  let base : ℝ := (((Finset.range N).filter (fun p =>
    p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD d])).card : ℝ)
  let liN : ℝ := AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)
  let liN2 : ℝ := AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)
  let phi : ℝ := (Nat.totient d : ℝ)
  -- 目标用这些变量重写后是纯线性等式:
  -- base + S − liN/phi − (base − liN2/phi) = (liN2 − liN)/phi + S
  have hphi_ne : phi ≠ 0 := by
    have hP0 : 0 < correctedChenSiftingProduct N :=
      Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
    change ((Nat.totient d : ℝ) ≠ 0)
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hd hP0)).ne'
  have hlin : base + S - liN / phi - (base - liN2 / phi) = (liN2 - liN) / phi + S := by
    field_simp [hphi_ne]
    ring
  -- 用 hlin 回代 (defeq 展开)
  simpa [S, base, liN, liN2, phi] using hlin

/-- **`|rem d − Δ'(d)|` 的三角不等式界**: 展开 (上一条) + `|Σ| ≤ Σ|·|`
(基计数非负) 得
`|rem d − Δ'(d)| ≤ |li(N−2) − li(N)|/φ(d) + Σ_{1≠e|F} |μ(e)|·base(lcm(d,e))`. -/
theorem abs_correctedChenRem_sub_distributionError_le (N d : ℕ)
    (hd : d ∣ correctedChenSiftingProduct N) (hN : 2 ≤ N) :
    |(correctedChenBoundingSieve N).rem d -
        AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)| ≤
      |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
          AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)| / (Nat.totient d : ℝ) +
        |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| := by
  classical
  have hA := correctedChenRem_sub_distributionError_eq N d hd hN
  have hφ0 : (0 : ℝ) < (Nat.totient d : ℝ) := by
    have hP0 : 0 < correctedChenSiftingProduct N :=
      Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hd hP0))
  have hφabs : |(Nat.totient d : ℝ)| = (Nat.totient d : ℝ) := abs_of_pos hφ0
  calc
    |(correctedChenBoundingSieve N).rem d -
        AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 d (N % d)|
        = |(AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
              AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)) / (Nat.totient d : ℝ) +
            (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
              (μ e : ℝ) * (((Finset.range N).filter (fun p =>
                p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ))| := by
          rw [hA]
    _ ≤ |(AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
            AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)) / (Nat.totient d : ℝ)| +
          |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            (μ e : ℝ) * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| := by
          exact abs_add_le _ _
    _ = |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
            AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)| / (Nat.totient d : ℝ) +
          |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            (μ e : ℝ) * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| := by
          rw [abs_div]
          rw [hφabs]
    _ ≤ |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
            AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)| / (Nat.totient d : ℝ) +
          |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            (μ e : ℝ) * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| := by
          exact le_rfl

/-- **基计数 ≤ 分布误差 + li 主项**: `base(q) = Δ'(q) + li(N−2)/φ(q)`
(`supportAPBaseCount_distributionError` 重排), 三角不等式得
`base(q) ≤ |Δ'(q)| + |li(N−2)|/φ(q)`. -/
theorem baseCount_le_distributionError_add_li (N q : ℕ) (hN : 2 ≤ N) (hq : 0 < q) :
    (((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD q])).card : ℝ) ≤
      |AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 q (N % q)| +
        |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| / (Nat.totient q : ℝ) := by
  classical
  have hφ0 : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hq)
  have h := supportAPBaseCount_distributionError N q hN
  -- h: base(q) − li(N−2)/φ(q) = Δ'(q), 故 base(q) = Δ'(q) + li(N−2)/φ(q)
  have hEq : (((Finset.range N).filter (fun p =>
      p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD q])).card : ℝ) =
      AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 q (N % q) +
        AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) / (Nat.totient q : ℝ) := by
    -- h: base − li/φ = Δ' ⟹ base = Δ' + li/φ (纯代数; rw ← h 后 ring 只处理原子 base)
    rw [← h]
    ring
  rw [hEq]
  exact add_le_add (le_abs_self _) (div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hφ0))

/-- **squarefree 除数和恒等式 (chen #39)**: 对 squarefree `m`, 除数加权和
`Σ_{d | m} 3^{ω(d)} = 4^{ω(m)}`.
证明: 双射 `d ↦ d.primeFactors` 把 `m.divisors` 映到 `m.primeFactors.powerset`
(逆 `S ↦ S.prod id`, 由 `prod_primeFactors_of_squarefree`/`primeFactors_prod`),
于是 `Σ_{d|m} 3^{ω(d)} = Σ_{S ⊆ m.primeFactors} 3^{|S|}`, 再由二项式定理
`Σ_{k=0}^{|s|} C(|s|,k)·3^k = (1+3)^{|s|} = 4^{|s|}` (`sum_powerset` +
`sum_powersetCard` + `add_pow`). 零 sorry, 纯初等. -/
lemma squarefree_divisorSum_three_pow_omega (m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, (3 : ℝ) ^ d.primeFactors.card) = (4 : ℝ) ^ m.primeFactors.card := by
  classical
  -- 双射: i : m.divisors → powerset, d ↦ d.primeFactors; j : powerset → m.divisors, S ↦ S.prod id
  have hbij : (∑ d ∈ m.divisors, (3 : ℝ) ^ d.primeFactors.card) =
      ∑ S ∈ m.primeFactors.powerset, (3 : ℝ) ^ S.card := by
    refine Finset.sum_bij' (fun d hd => d.primeFactors) (fun S hS => S.prod id) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono hdvd hm.ne_zero
    · intro S hS
      rw [Finset.mem_powerset] at hS
      rw [Nat.mem_divisors]
      constructor
      · rw [← Nat.prod_primeFactors_of_squarefree hm]
        exact Finset.prod_dvd_prod_of_subset _ _ _ hS
      · exact hm.ne_zero
    · intro d hd
      have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
      have hdsq : Squarefree d := hm.squarefree_of_dvd hdvd
      exact Nat.prod_primeFactors_of_squarefree hdsq
    · intro S hS
      rw [Finset.mem_powerset] at hS
      exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))
    · intro d hd
      rfl
  -- 幂集和 = 4^{#s}: Σ_{S ⊆ s} 3^{|S|} = Σ_k C(|s|,k)·3^k = (1+3)^{|s|}
  have hpow : (∑ S ∈ m.primeFactors.powerset, (3 : ℝ) ^ S.card) =
      (4 : ℝ) ^ m.primeFactors.card := by
    calc
      (∑ S ∈ m.primeFactors.powerset, (3 : ℝ) ^ S.card)
          = ∑ j ∈ range (m.primeFactors.card + 1),
              ∑ S ∈ powersetCard j m.primeFactors, (3 : ℝ) ^ S.card := by
              rw [← Finset.sum_powerset]
      _ = ∑ j ∈ range (m.primeFactors.card + 1),
              (3 : ℝ) ^ j * (m.primeFactors.card).choose j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hc := sum_powersetCard j m.primeFactors (fun n => (3 : ℝ) ^ n)
              rw [hc]
              rw [nsmul_eq_mul]
              ring
      _ = (3 + 1 : ℝ) ^ m.primeFactors.card := by
              rw [add_pow (3 : ℝ) (1 : ℝ) m.primeFactors.card]
              apply Finset.sum_congr rfl
              intro j hj
              have hone : (1 : ℝ) ^ (m.primeFactors.card - j) = 1 := by simp
              rw [hone]
              ring
      _ = (4 : ℝ) ^ m.primeFactors.card := by norm_num
  exact hbij.trans hpow


/-- **带符号 Möbius 基计数恒等式 (chen #39 修正核心)**: 对任意 `d`,
`Σ_{1≠e|F} μ(e)·base(lcm(d,e)) = −#{p < N : p 素数, 2 ≤ N−p, d | N−p, gcd(F, N−p) ≠ 1}`.
证明: 展开 base 为 p 指示和, 交换求和; 逐 p 用 lcm 合并
(`modEq_and_dvd_complement_iff_modEq_lcm`, 无需互素) 与 Möbius 互素指示
(`moebius_coprime_sum_forbidden` 减 e=1 项) 消去 e 和. -/
theorem moebiusBaseCount_signed_eq (N d : ℕ) (hN : 2 ≤ N) :
    (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
      (μ e : ℝ) * (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) =
    -(((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p)).card : ℝ) := by
  classical
  let F : ℕ := correctedChenForbiddenProduct N
  have hF0 : F ≠ 0 := correctedChenForbiddenProduct_ne_zero N
  -- 展开每个 base(lcm(d,e)) 为 p 指示和: (μ e)·card = Σ_p (if cond then μ e else 0)
  have hbase : ∀ e, (μ e : ℝ) * (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) =
      (∑ p ∈ Finset.range N,
        if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0) := by
    intro e
    rw [← Finset.sum_boole]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e]
    · simp [h]
    · simp [h]
  calc
    (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
      (μ e : ℝ) * (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ))
    = ∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
        (∑ p ∈ Finset.range N,
          if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hbase e
    _ = ∑ p ∈ Finset.range N,
        (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
          if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ = -(((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
        -- 逐 p: 内层 e 和 = if (base ∧ d | N−p ∧ ∃r..) then −1 else 0
        have hinner : ∀ p ∈ Finset.range N,
            (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
              if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0) =
            if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
              then -(1 : ℝ) else 0 := by
          intro p hp
          have hpN : p ≤ N := le_of_lt (Finset.mem_range.mp hp)
          have hde : ∀ e, (p ≡ N [MOD Nat.lcm d e]) ↔ (d ∣ N - p ∧ e ∣ N - p) := by
            intro e
            rw [← modEq_and_dvd_complement_iff_modEq_lcm (N := N) (p := p) (d := d) (e := e)
              (Finset.mem_range.mp hp)]
            rw [Nat.modEq_iff_dvd' (n := d) (a := p) (b := N) hpN]
          -- Möbius 互素指示减 e=1 项
          have hmoeb : (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                if e ∣ N - p then (μ e : ℝ) else 0) =
              if ¬ (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) then -(1 : ℝ) else 0 := by
            have hfull := moebius_coprime_sum_forbidden N (N - p)
            -- 全和减 e=1 项 (μ(1)·[1|N−p] = 1)
            have hsplit : (∑ e ∈ F.divisors,
                if e ∣ N - p then (μ e : ℝ) else 0) =
                (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                  if e ∣ N - p then (μ e : ℝ) else 0) +
                (∑ e ∈ F.divisors.filter (fun e => e = 1),
                  if e ∣ N - p then (μ e : ℝ) else 0) := by
              rw [← Finset.sum_filter_add_sum_filter_not F.divisors (fun e => e ≠ 1)
                (fun e => if e ∣ N - p then (μ e : ℝ) else 0)]
              have hf : F.divisors.filter (fun e => ¬ e ≠ 1) =
                  F.divisors.filter (fun e => e = 1) := by
                ext e
                by_cases h : e = 1 <;> simp [h]
              rw [hf]
            have hone : (∑ e ∈ F.divisors.filter (fun e => e = 1),
                if e ∣ N - p then (μ e : ℝ) else 0) = (1 : ℝ) := by
              rw [Finset.sum_eq_single (1 : ℕ)]
              · simp [ArithmeticFunction.moebius_apply_one]
              · intro b hb hbne
                exfalso
                rcases Finset.mem_filter.mp hb with ⟨_, hb1⟩
                exact hbne hb1
              · intro hnot
                exfalso
                exact hnot (Finset.mem_filter.mpr ⟨(Nat.mem_divisors.mpr ⟨Nat.one_dvd _, hF0⟩), rfl⟩)
            -- 分 ∀r 情形: S = full − one, full = if ∀r.. then 1 else 0, one = 1
            calc
              (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                if e ∣ N - p then (μ e : ℝ) else 0)
              = (∑ e ∈ F.divisors, if e ∣ N - p then (μ e : ℝ) else 0) -
                  (∑ e ∈ F.divisors.filter (fun e => e = 1),
                    if e ∣ N - p then (μ e : ℝ) else 0) := by
                  rw [hsplit]
                  ring
              _ = (if ∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ N - p
                    then (1 : ℝ) else 0) - 1 := by
                  rw [hone]
                  dsimp [F]
                  rw [hfull]
              _ = if ¬ (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) then -(1 : ℝ) else 0 := by
                  have hiff : (∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ N - p) ↔
                      (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) := by
                    constructor <;> intro h r hr <;> simpa [F] using h r hr
                  by_cases hcop : ∀ r : ℕ, r.Prime → r ∣ correctedChenForbiddenProduct N → ¬ r ∣ N - p
                  · rw [if_pos hcop]
                    have hF : (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) := hiff.1 hcop
                    rw [if_neg (by intro hnot; exact hnot hF)]
                    norm_num
                  · rw [if_neg hcop]
                    have hF : ¬ (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) := by
                      intro hnot
                      exact hcop (hiff.2 hnot)
                    rw [if_pos hF]
                    norm_num
          -- 用 hde 重写 lcm 条件, 提出 p 无关因子
          by_cases hb : p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p
          · have hcond : ∀ e, (p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e]) ↔
                (p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧ e ∣ N - p) := by
              intro e
              rw [hde e]
            calc
              (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0)
              = ∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                  if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧ e ∣ N - p then (μ e : ℝ) else 0 := by
                  apply Finset.sum_congr rfl
                  intro e he
                  by_cases h : p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e]
                  · rw [if_pos h]
                    rw [if_pos ((hcond e).1 h)]
                  · rw [if_neg h]
                    rw [if_neg (mt (hcond e).2 h)]
              _ = (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
                  if e ∣ N - p then (μ e : ℝ) else 0) := by
                  -- hb: p.Prime ∧ 2≤N−p ∧ d|N−p 恒真 ⟹ 条件 = e|N−p
                  apply Finset.sum_congr rfl
                  intro e he
                  rcases hb with ⟨hpp, h2, hd⟩
                  by_cases hep : e ∣ N - p
                  · simp [hpp, h2, hd, hep]
                  · simp [hpp, h2, hd, hep]
              _ = if (∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p) then -(1 : ℝ) else 0 := by
                  -- hmoeb + ∃↔¬∀ (push_neg)
                  have hex : (∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p) ↔
                      ¬ (∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p) := by
                    rw [not_forall]
                    apply exists_congr
                    intro r
                    tauto
                  rw [hmoeb]
                  by_cases he : ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
                  · rw [if_pos he, if_pos (hex.1 he)]
                  · rw [if_neg he, if_neg (mt hex.2 he)]
              _ = if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                    (∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)
                  then -(1 : ℝ) else 0 := by
                  by_cases he : ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
                  · rw [if_pos he]
                    rw [if_pos (by
                      rcases hb with ⟨hpp, h2, hd⟩
                      exact ⟨hpp, h2, hd, he⟩)]
                  · rw [if_neg he]
                    rw [if_neg (by
                      intro h
                      exact he h.2.2.2)]
          · -- ¬hb: RHS = 0, 且条件 (含 p≡N mod lcm) 恒假 ⟹ 和 = 0
            have hrhs : (if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                  (∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)
                then -(1 : ℝ) else 0) = 0 := by
              rw [if_neg (by
                intro h
                exact hb ⟨h.1, h.2.1, h.2.2.1⟩)]
            rw [hrhs]
            apply Finset.sum_eq_zero
            intro e he
            by_cases h : p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e]
            · exfalso
              rcases h with ⟨hpp, h2, hmod⟩
              rcases (hde e).1 hmod with ⟨hd, _⟩
              exact hb ⟨hpp, h2, hd⟩
            · simp [h]
        -- 装配: Σ_p inner = −#{...}
        calc
          (∑ p ∈ Finset.range N,
            (∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
              if p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e] then (μ e : ℝ) else 0))
          = ∑ p ∈ Finset.range N,
              if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                  ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
                then -(1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              exact hinner p hp
          _ = -(((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
              rw [← Finset.sum_boole]
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro p hp
              by_cases h : p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                  ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
              · simp [h]
              · simp [h]

/-- **带符号 Möbius 和每 d 界 (chen #39)**: 由 `moebiusBaseCount_signed_eq`,
`|Σ_{1≠e|F} μ(e)·base(lcm(d,e))| = #{p < N : p 素数, 2 ≤ N−p, d | N−p, ∃ r, r 素数, r|F, r|N−p}`.
右端每个 p 满足: r | N−p 且 r | F。r ≤ 2 或 r | N:
- r | N 时 r | N−p ∧ r | N ⟹ r | p ⟹ (p 素数) p = r ∈ primeFactors(F);
- r = 2 时 (N 偶) 2 | N−p ⟹ p 偶素数 ⟹ p = 2。
故计数 ≤ 1 + ω(F) (polylog, 与 d 无关)。-/
theorem abs_moebiusBaseCount_signed_le (N d : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
      (μ e : ℝ) * (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| ≤
      ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) := by
  classical
  let F : ℕ := correctedChenForbiddenProduct N
  have hEq := moebiusBaseCount_signed_eq N d hN
  have hF0 : F ≠ 0 := correctedChenForbiddenProduct_ne_zero N
  -- 左端 = #{p : p.Prime ∧ 2≤N−p ∧ d|N−p ∧ ∃r, r.Prime ∧ r|F ∧ r|N−p}
  have hcard : ((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card ≤
      1 + F.primeFactors.card := by
    -- 证明: 每个 p ∈ S 属于 {2} ∪ primeFactors(F)
    have hsub : ∀ p ∈ (Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p),
        p = 2 ∨ p ∈ F.primeFactors := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hprange, hcond⟩
      rcases hcond with ⟨hpp, htwo, hdvd, hex⟩
      rcases hex with ⟨r, hrprime, hrF, hrNp⟩
      have hp_le_N : p ≤ N := by omega
      -- r | F: r < z ∧ (r ≤ 2 ∨ r | N)
      have hrcond := (prime_dvd_correctedChenForbiddenProduct_iff hrprime).mp hrF
      rcases hrcond with ⟨hrz, hrzN⟩
      cases hrzN with
      | inl hrle2 =>
          -- r ≤ 2, r 素数 ⟹ r = 2; 2 | N−p, N 偶 ⟹ p 偶 ⟹ p = 2
          have hr2 : r = 2 := by
            have hrge2 : 2 ≤ r := hrprime.two_le
            omega
          subst r
          have h2dvdNp : 2 ∣ N - p := hrNp
          have h2dvdN : 2 ∣ N := by
            rcases hEven with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            rw [hk]
            ring
          have h2dvdp : 2 ∣ p := by
            -- p = N - (N-p), 2 | N 且 2 | N−p ⟹ 2 | p
            have hdvd : 2 ∣ N - (N - p) := Nat.dvd_sub h2dvdN h2dvdNp
            have hp_eq : N - (N - p) = p := by omega
            rwa [hp_eq] at hdvd
          left
          rcases (Nat.dvd_prime hpp).mp h2dvdp with h21 | h2p
          · exfalso
            norm_num at h21
          · exact h2p.symm
      | inr hrN =>
          -- r | N ∧ r | N−p ⟹ r | p; p, r 素数 ⟹ p = r; r | F ⟹ r ∈ primeFactors F
          have hrp : r ∣ p := by
            -- p = N - (N-p), r | N 且 r | N−p ⟹ r | p
            have hdvd : r ∣ N - (N - p) := Nat.dvd_sub hrN hrNp
            have hp_eq : N - (N - p) = p := by omega
            rwa [hp_eq] at hdvd
          have hrp_eq : r = p := by
            rcases (Nat.dvd_prime hpp).mp hrp with hr1 | hrp'
            · exfalso
              have hrge : 2 ≤ r := hrprime.two_le
              omega
            · exact hrp'
          right
          rw [← hrp_eq]
          exact (Nat.mem_primeFactors_of_ne_zero hF0).mpr ⟨hrprime, hrF⟩
    -- S ⊆ {2} ∪ primeFactors F 的计数 ≤ 1 + ω(F)
    calc
      ((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card
      ≤ (({2} : Finset ℕ) ∪ F.primeFactors).card := by
          -- 单调性: S ⊆ {2} ∪ primeFactors F
          exact Finset.card_le_card (by
            intro p hp
            have hmem : p = 2 ∨ p ∈ F.primeFactors := hsub p hp
            rw [Finset.mem_union]
            rcases hmem with h2 | hr
            · exact Or.inl (by simp [h2])
            · exact Or.inr hr)
      _ ≤ (({2} : Finset ℕ).card + F.primeFactors.card) := by
          exact Finset.card_union_le _ _
      _ = (1 + F.primeFactors.card) := by simp
  -- 装配: |Σ| = 右端计数 (由带符号恒等式: Σ = −(右端计数))
  have hEq' : |∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
        (μ e : ℝ) * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| =
      (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
    have hle : (0 : ℝ) ≤ (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p)).card : ℝ) := by positivity
    calc
      |∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|
      = (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p)).card : ℝ) := by
          -- 由带符号恒等式 (F 是 let, 定义性相等): Σ = −(计数)
          dsimp [F]
          rw [hEq]
          rw [abs_neg]
          exact abs_of_nonneg hle
      _ = (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
          -- 仅 F = correctedChenForbiddenProduct N 的展开差异 (F 是 let)
          rfl
  rw [hEq']
  exact_mod_cast hcard
/-- **除数加权和的点式 ω 界 (chen #39)**: 4^(ω(m)) ≤ 16^8·√m (m ≥ 1)。
初等证明 (无需素数计数下界): 16^(ω(m)) = ∏_{p|m} 16; 将 m.primeFactors
按 p < 16 拆分 — 小部分至多 16 个因子, 贡献 ≤ 16^16; 大部分逐点 16 ≤ p,
贡献 ≤ ∏_{p|m} p ≤ m (radical 整除 m); 故 16^ω ≤ 16^16·m,
对 ℝ 开方得 4^ω ≤ 16^8·√m。零 sorry, 纯初等。 -/
lemma four_pow_omega_le_sqrt (m : ℕ) (hm : 1 ≤ m) :
    (4 : ℝ) ^ m.primeFactors.card ≤ (16 ^ 8 : ℝ) * Real.sqrt (m : ℝ) := by
  classical
  -- 小部分: {p<16} 的因子至多 16 个, ∏ 16 ≤ 16^16
  have hsmall : (∏ p ∈ m.primeFactors.filter (fun p => p < 16), (16 : ℕ)) ≤ (16 : ℕ) ^ 16 := by
    calc
      (∏ p ∈ m.primeFactors.filter (fun p => p < 16), (16 : ℕ)) =
          (16 : ℕ) ^ (m.primeFactors.filter (fun p => p < 16)).card := by
        rw [Finset.prod_const]
      _ ≤ (16 : ℕ) ^ 16 := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 16)
        calc
          (m.primeFactors.filter (fun p => p < 16)).card ≤ (Finset.range 16).card := by
            exact Finset.card_le_card (by
              intro p hp
              rw [Finset.mem_filter] at hp
              exact Finset.mem_range.mpr hp.2)
          _ = 16 := by rw [Finset.card_range]
  -- 大部分: 逐点 16 ≤ p, 且 ∏_{p≥16} p ≤ ∏_{p|m} p ≤ m
  have hbig : (∏ p ∈ m.primeFactors.filter (fun p => 16 ≤ p), (16 : ℕ)) ≤
      ∏ p ∈ m.primeFactors.filter (fun p => 16 ≤ p), p := by
    exact Finset.prod_le_prod (fun p hp => by norm_num) (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact hp.2)
  have hbig_le : (∏ p ∈ m.primeFactors.filter (fun p => 16 ≤ p), p) ≤
      ∏ p ∈ m.primeFactors, p := by
    exact Finset.prod_le_prod_of_subset_of_one_le'
      (by intro p hp; rw [Finset.mem_filter] at hp; exact hp.1)
      (by intro p hp hnot; exact (Nat.prime_of_mem_primeFactors hp).one_le)
  have hrad_le : ∏ p ∈ m.primeFactors, p ≤ m := by
    exact Nat.le_of_dvd (by omega : 0 < m) (Nat.prod_primeFactors_dvd m)
  -- 16^ω = ∏ 16 = (∏_{p<16} 16)·(∏_{p≥16} 16) ≤ 16^16·m (ℕ)
  have h16n : (16 : ℕ) ^ m.primeFactors.card ≤ (16 : ℕ) ^ 16 * m := by
    calc
      (16 : ℕ) ^ m.primeFactors.card = ∏ p ∈ m.primeFactors, (16 : ℕ) := by
        rw [Finset.prod_const]
      _ = (∏ p ∈ m.primeFactors.filter (fun p => p < 16), (16 : ℕ)) *
          (∏ p ∈ m.primeFactors.filter (fun p => 16 ≤ p), (16 : ℕ)) := by
        have hflt : m.primeFactors.filter (fun p => 16 ≤ p) =
            m.primeFactors.filter (fun p => ¬ p < 16) := by
          apply Finset.filter_congr
          intro p hp
          exact not_lt.symm
        rw [hflt]
        rw [← Finset.prod_filter_mul_prod_filter_not
          (s := m.primeFactors) (p := fun p => p < 16) (f := fun p => (16 : ℕ))]
      _ ≤ (16 : ℕ) ^ 16 * (∏ p ∈ m.primeFactors.filter (fun p => 16 ≤ p), p) := by
        exact Nat.mul_le_mul hsmall hbig
      _ ≤ (16 : ℕ) ^ 16 * (∏ p ∈ m.primeFactors, p) := by
        exact Nat.mul_le_mul_left ((16 : ℕ) ^ 16) hbig_le
      _ ≤ (16 : ℕ) ^ 16 * m := by
        exact Nat.mul_le_mul_left ((16 : ℕ) ^ 16) hrad_le
  -- 转 ℝ 开方
  have h16R : ((16 : ℕ) ^ m.primeFactors.card : ℝ) ≤ (((16 : ℕ) ^ 16 * m : ℕ) : ℝ) := by
    exact_mod_cast h16n
  have hsqrt : Real.sqrt (((16 : ℕ) ^ m.primeFactors.card : ℝ)) ≤
      Real.sqrt (((16 : ℕ) ^ 16 * m : ℕ) : ℝ) := by
    exact Real.sqrt_le_sqrt h16R
  have hsqrt_lhs : Real.sqrt (((16 : ℕ) ^ m.primeFactors.card : ℝ)) =
      (4 : ℝ) ^ m.primeFactors.card := by
    have hEq : ((16 : ℕ) ^ m.primeFactors.card : ℝ) = ((4 : ℝ) ^ m.primeFactors.card) ^ 2 := by
      norm_num
      rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num]
      rw [← pow_mul (4 : ℝ) 2 m.primeFactors.card]
      rw [← pow_mul (4 : ℝ) m.primeFactors.card 2]
      rw [show 2 * m.primeFactors.card = m.primeFactors.card * 2 by omega]
    rw [hEq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hsqrt16 : Real.sqrt ((16 : ℝ) ^ 16) = (16 ^ 8 : ℝ) := by
    rw [show (16 : ℝ) ^ 16 = ((16 : ℝ) ^ 8) ^ 2 by
      rw [← pow_mul (16 : ℝ) 8 2]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hsqrt_rhs : Real.sqrt (((16 : ℕ) ^ 16 * m : ℕ) : ℝ) =
      (16 ^ 8 : ℝ) * Real.sqrt (m : ℝ) := by
    rw [show (((16 : ℕ) ^ 16 * m : ℕ) : ℝ) = (16 : ℝ) ^ 16 * (m : ℝ) by norm_num]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (16 : ℝ) ^ 16) (m : ℝ)]
    rw [hsqrt16]
  calc
    (4 : ℝ) ^ m.primeFactors.card = Real.sqrt (((16 : ℕ) ^ m.primeFactors.card : ℝ)) := hsqrt_lhs.symm
    _ ≤ Real.sqrt (((16 : ℕ) ^ 16 * m : ℕ) : ℝ) := hsqrt
    _ = (16 ^ 8 : ℝ) * Real.sqrt (m : ℝ) := hsqrt_rhs

/-- **除数加权和 (chen #39)**: 主项 MainB 的除数加权和 (交换后):
Σ_{p∈S} 4^{ω(gcd(P,N−p))} ≤ (1+ω(N))·16^8·√N。
其中 S = {p : p.Prime ∧ 2≤N−p ∧ ∃r, r.Prime ∧ r|F ∧ r|N−p} (F = correctedChenForbiddenProduct N)。
证明: 每项点式 4^{ω(gcd(P,N−p))} ≤ 16^8·√(gcd(P,N−p)) ≤ 16^8·√N
(four_pow_omega_le_sqrt + gcd ≤ N−p ≤ N), 求和后 |S| ≤ 1 + F.primeFactors.card
(hcard: S ⊆ {2} ∪ primeFactors F)。零 sorry。 -/
lemma divisorWeightedSum_le (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p),
      (4 : ℝ) ^ (Nat.gcd (correctedChenSiftingProduct N) (N - p)).primeFactors.card) ≤
      ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
  classical
  let F : ℕ := correctedChenForbiddenProduct N
  let P : ℕ := correctedChenSiftingProduct N
  let S : Finset ℕ := (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
    ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)
  -- |S| ≤ 1 + ω(F): S ⊆ {2} ∪ primeFactors F
  have hcardS : S.card ≤ 1 + F.primeFactors.card := by
    have hsub : ∀ p ∈ S, p = 2 ∨ p ∈ F.primeFactors := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hprange, hcond⟩
      rcases hcond with ⟨hpp, htwo, hex⟩
      rcases hex with ⟨r, hrprime, hrF, hrNp⟩
      have hrcond := (prime_dvd_correctedChenForbiddenProduct_iff hrprime).mp hrF
      rcases hrcond with ⟨hrz, hrzN⟩
      cases hrzN with
      | inl hrle2 =>
          have hr2 : r = 2 := by
            have hrge2 : 2 ≤ r := hrprime.two_le
            omega
          subst r
          have h2dvdNp : 2 ∣ N - p := hrNp
          have h2dvdN : 2 ∣ N := by
            rcases hEven with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            rw [hk]
            ring
          have h2dvdp : 2 ∣ p := by
            have hdvd : 2 ∣ N - (N - p) := Nat.dvd_sub h2dvdN h2dvdNp
            have hp_eq : N - (N - p) = p := by omega
            rwa [hp_eq] at hdvd
          left
          rcases (Nat.dvd_prime hpp).mp h2dvdp with h21 | h2p
          · exfalso
            norm_num at h21
          · exact h2p.symm
      | inr hrN =>
          have hrp : r ∣ p := by
            have hdvd : r ∣ N - (N - p) := Nat.dvd_sub hrN hrNp
            have hp_eq : N - (N - p) = p := by omega
            rwa [hp_eq] at hdvd
          have hrp_eq : r = p := by
            rcases (Nat.dvd_prime hpp).mp hrp with hr1 | hrp'
            · exfalso
              have hrge : 2 ≤ r := hrprime.two_le
              omega
            · exact hrp'
          right
          rw [← hrp_eq]
          exact (Nat.mem_primeFactors_of_ne_zero (correctedChenForbiddenProduct_ne_zero N)).mpr ⟨hrprime, hrF⟩
    calc
      S.card ≤ (({2} : Finset ℕ) ∪ F.primeFactors).card := by
          exact Finset.card_le_card (by
            intro p hp
            rw [Finset.mem_union]
            rcases hsub p hp with h2 | hr
            · exact Or.inl (by simp [h2])
            · exact Or.inr hr)
      _ ≤ (({2} : Finset ℕ).card + F.primeFactors.card) := by
          exact Finset.card_union_le _ _
      _ = (1 + F.primeFactors.card) := by simp
  -- 每项: 4^{ω(gcd(P,N−p))} ≤ 16^8·√N
  have hpoint : ∀ p ∈ S,
      (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card ≤ (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hprange, hcond⟩
    have hgcdpos : 1 ≤ Nat.gcd P (N - p) := by
      have hPpos : 0 < P := Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
      exact Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left (N - p) hPpos)
    have h1 := four_pow_omega_le_sqrt (Nat.gcd P (N - p)) hgcdpos
    have hgcd_le : Nat.gcd P (N - p) ≤ N - p := by
      exact Nat.le_of_dvd (by omega : 0 < N - p) (Nat.gcd_dvd_right P (N - p))
    have hNp_le : N - p ≤ N := by omega
    have hsqrt : Real.sqrt ((Nat.gcd P (N - p) : ℝ)) ≤ Real.sqrt (N : ℝ) := by
      have hle : (Nat.gcd P (N - p) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_trans hgcd_le hNp_le)
      exact Real.sqrt_le_sqrt hle
    calc
      (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card
          ≤ (16 ^ 8 : ℝ) * Real.sqrt ((Nat.gcd P (N - p) : ℝ)) := h1
      _ ≤ (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
  -- 求和: Σ_{p∈S} ≤ |S|·16^8·√N
  have hsum : (∑ p ∈ S, (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card) ≤
      S.card * ((16 ^ 8 : ℝ) * Real.sqrt (N : ℝ)) := by
    calc
      (∑ p ∈ S, (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card)
          ≤ ∑ p ∈ S, (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
            exact Finset.sum_le_sum hpoint
      _ = S.card * ((16 ^ 8 : ℝ) * Real.sqrt (N : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  -- 装配
  calc
    (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p),
      (4 : ℝ) ^ (Nat.gcd (correctedChenSiftingProduct N) (N - p)).primeFactors.card)
        ≤ S.card * ((16 ^ 8 : ℝ) * Real.sqrt (N : ℝ)) := by
          simpa [S, P, F] using hsum
    _ ≤ (1 + F.primeFactors.card) * ((16 ^ 8 : ℝ) * Real.sqrt (N : ℝ)) := by
          -- |S| ≤ 1+ω(F) (Nat), 两边乘正量 (ℝ cast)
          have hc : (S.card : ℝ) ≤ (1 + F.primeFactors.card : ℝ) := by exact_mod_cast hcardS
          have hpos : 0 ≤ (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right hc hpos
    _ = ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
          simp [F, mul_assoc]


/-- **交换恒等式 (chen #39)**: MainB' 的除数加权和等于按 `p` 的除数加权和:
`Σ_{d|P} 3^{ω(d)}·|Σ_{1≠e|F} μ(e)·base(lcm(d,e))| = Σ_{p∈S} 4^{ω(gcd(P,N−p))}`, 其中
`S = {p : p.Prime ∧ 2 ≤ N−p ∧ ∃r, r.Prime ∧ r|F ∧ r|N−p}` (`P`/`F` 为修正筛积与禁积).
证明: 由 `moebiusBaseCount_signed_eq`, 内层带符号和 = −count(d), 其中
`count(d) = #{p : p.Prime ∧ 2≤N−p ∧ d|N−p ∧ ∃r, r.Prime ∧ r|F ∧ r|N−p}`, 故绝对值 = count(d);
展开 count 为 p 指示和 (`sum_boole`), Fubini 交换求和 (`sum_comm` + `mul_sum`),
逐 p 提取条件并用 `divisors_filter_dvd_of_dvd` + `dvd_gcd_iff` 将 `{d|P, d|N−p}`
合并为 `gcd(P,N−p)` 的因子, 再应用 squarefree 除数和恒等式
(`gcd(P,N−p)` 为 squarefree, 因 `P` squarefree). 零 sorry. -/
lemma swap_weightedSum_eq (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|) =
    (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p),
      (4 : ℝ) ^ (Nat.gcd (correctedChenSiftingProduct N) (N - p)).primeFactors.card) := by
  classical
  let P : ℕ := correctedChenSiftingProduct N
  let F : ℕ := correctedChenForbiddenProduct N
  have hP0 : P ≠ 0 := correctedChenSiftingProduct_ne_zero N
  have hF0 : F ≠ 0 := correctedChenForbiddenProduct_ne_zero N
  have hPsq : Squarefree P := correctedChenSiftingProduct_squarefree N
  -- 步骤 1: 内层带符号和 = −count(d), 故绝对值 = count(d) (count ≥ 0)
  have hcount : ∀ d ∈ P.divisors,
      |∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
        (μ e : ℝ) * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| =
      (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
    intro d hd
    have hEq := moebiusBaseCount_signed_eq N d hN
    dsimp [F] at hEq
    rw [hEq]
    rw [abs_neg]
    exact abs_of_nonneg (by positivity)
  -- 步骤 2: LHS = Σ_{d|P} 3^{ω(d)}·count(d)
  have h1 : (∑ d ∈ P.divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |∑ e ∈ F.divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|) =
      ∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcount d hd]
  -- 步骤 3: count(d) = Σ_{p ∈ range N} [p.Prime ∧ 2≤N−p ∧ d|N−p ∧ ∃r, ...]
  have h2 : (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ)) =
      ∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (∑ p ∈ Finset.range N,
          if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
              ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_boole]
  -- 步骤 4: Fubini — Σ_d 3^{ω(d)}·Σ_p [cond] = Σ_p Σ_d 3^{ω(d)}·[cond]
  have h3 : (∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (∑ p ∈ Finset.range N,
          if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
              ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p then (1 : ℝ) else 0)) =
      ∑ p ∈ Finset.range N, ∑ d ∈ P.divisors,
        if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (3 : ℝ) ^ d.primeFactors.card else 0 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
    · simp [h]
    · simp [h]
  -- 步骤 5: 逐 p 提取条件; {d ∈ P.divisors | d | N−p} = gcd(P,N−p) 的因子
  have h4 : (∑ p ∈ Finset.range N, ∑ d ∈ P.divisors,
        if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (3 : ℝ) ^ d.primeFactors.card else 0) =
      ∑ p ∈ Finset.range N,
        (if p.Prime ∧ 2 ≤ N - p ∧ ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (∑ d ∈ (Nat.gcd P (N - p)).divisors,
            (3 : ℝ) ^ d.primeFactors.card) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpcond : p.Prime ∧ 2 ≤ N - p ∧ ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
    · -- hpcond 真: 条件简化为 d | N−p; 集合 = gcd(P,N−p).divisors
      have hinner : (∑ d ∈ P.divisors,
          if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
              ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
            then (3 : ℝ) ^ d.primeFactors.card else 0) =
          ∑ d ∈ (Nat.gcd P (N - p)).divisors, (3 : ℝ) ^ d.primeFactors.card := by
        have hred : (∑ d ∈ P.divisors,
            if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
              then (3 : ℝ) ^ d.primeFactors.card else 0) =
            ∑ d ∈ P.divisors, if d ∣ N - p then (3 : ℝ) ^ d.primeFactors.card else 0 := by
          rcases hpcond with ⟨hpp, h2, hr⟩
          rcases hr with ⟨r, hrprime, hrF, hrNp⟩
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdnp : d ∣ N - p
          · have hex : ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p := ⟨r, hrprime, hrF, hrNp⟩
            simp [hpp, h2, hdnp, hex]
          · simp [hpp, h2, hdnp]
        have hf : P.divisors.filter (fun d => d ∣ N - p) =
            (Nat.gcd P (N - p)).divisors := by
          ext d
          constructor
          · intro hd
            rw [Finset.mem_filter] at hd
            rcases hd with ⟨hdmem, hdNP⟩
            rw [Nat.mem_divisors] at hdmem
            rcases hdmem with ⟨hdvdP, hPne⟩
            rw [Nat.mem_divisors]
            refine ⟨Nat.dvd_gcd hdvdP hdNP, ?_⟩
            exact ne_of_gt (Nat.gcd_pos_of_pos_left (N - p) (Nat.pos_of_ne_zero hP0))
          · intro hd
            rw [Nat.mem_divisors] at hd
            rcases hd with ⟨hdgcd, hgcdne⟩
            rw [Finset.mem_filter]
            rw [Nat.mem_divisors]
            have hdvdP : d ∣ P := dvd_trans hdgcd (Nat.gcd_dvd_left P (N - p))
            have hdvdNP : d ∣ N - p := dvd_trans hdgcd (Nat.gcd_dvd_right P (N - p))
            refine ⟨⟨hdvdP, hP0⟩, hdvdNP⟩
        calc
          (∑ d ∈ P.divisors,
              if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
                  ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
                then (3 : ℝ) ^ d.primeFactors.card else 0)
              = ∑ d ∈ P.divisors, if d ∣ N - p then (3 : ℝ) ^ d.primeFactors.card else 0 := hred
          _ = ∑ d ∈ P.divisors.filter (fun d => d ∣ N - p), (3 : ℝ) ^ d.primeFactors.card := by
              rw [Finset.sum_filter]
          _ = ∑ d ∈ (Nat.gcd P (N - p)).divisors, (3 : ℝ) ^ d.primeFactors.card := by
              rw [hf]
      rw [if_pos hpcond]
      exact hinner
    · rw [if_neg hpcond]
      -- hpcond 假: 所有项条件含 p.Prime ∧ 2≤N−p ∧ ∃r... 为假 ⟹ 和 = 0
      apply Finset.sum_eq_zero
      intro d hd
      by_cases h : p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
      · exfalso
        rcases h with ⟨hpp, h2, hdnp, hr⟩
        exact hpcond ⟨hpp, h2, hr⟩
      · simp [h]
  -- 步骤 6: 应用 squarefree 除数和恒等式 (gcd(P,N−p) squarefree)
  have h5 : (∑ p ∈ Finset.range N,
        (if p.Prime ∧ 2 ≤ N - p ∧ ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (∑ d ∈ (Nat.gcd P (N - p)).divisors,
            (3 : ℝ) ^ d.primeFactors.card) else 0)) =
      ∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p),
        (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card := by
    rw [← Finset.sum_filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
        ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨hprange, hpcond⟩
    have hgcdpos : 1 ≤ Nat.gcd P (N - p) := by
      have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
      exact Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left (N - p) hPpos)
    have hsq : Squarefree (Nat.gcd P (N - p)) := hPsq.squarefree_of_dvd (Nat.gcd_dvd_left P (N - p))
    have hA := squarefree_divisorSum_three_pow_omega (Nat.gcd P (N - p)) hsq
    simpa [P, F] using hA

  -- 装配
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|)
    = ∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p)).card : ℝ) := by
        simpa [P, F] using h1
    _ = ∑ d ∈ P.divisors, (3 : ℝ) ^ d.primeFactors.card *
        (∑ p ∈ Finset.range N,
          if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
              ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p then (1 : ℝ) else 0) := by
        simpa [P, F] using h2
    _ = ∑ p ∈ Finset.range N, ∑ d ∈ P.divisors,
        if p.Prime ∧ 2 ≤ N - p ∧ d ∣ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (3 : ℝ) ^ d.primeFactors.card else 0 := by
        simpa [P, F] using h3
    _ = ∑ p ∈ Finset.range N,
        (if p.Prime ∧ 2 ≤ N - p ∧ ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p
          then (∑ d ∈ (Nat.gcd P (N - p)).divisors,
            (3 : ℝ) ^ d.primeFactors.card) else 0) := by
        simpa [P, F] using h4
    _ = ∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ F ∧ r ∣ N - p),
        (4 : ℝ) ^ (Nat.gcd P (N - p)).primeFactors.card := by
        simpa [P, F] using h5
    _ = (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
          ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p),
        (4 : ℝ) ^ (Nat.gcd (correctedChenSiftingProduct N) (N - p)).primeFactors.card) := by
        simp [P, F]

/-- **ω(n) ≤ log n / log 2 (n ≥ 2)** (初等界, chen #39):
`2^{ω(n)} = ∏_{p|n} 2 ≤ ∏_{p|n} p ≤ n` (素数 ≥ 2, radical 整除 n),
取 log 得 `ω(n)·log 2 ≤ log n`. 用于 MainTermBound 重写的 √N 吸收. -/
lemma omega_le_log_two (n : ℕ) (hn : 2 ≤ n) :
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
    have hlogpow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) ≤ log (n : ℝ) := by
      exact Real.log_le_log (by positivity : 0 < ((2 ^ n.primeFactors.card : ℕ) : ℝ)) hcast
    have hlog2pow : log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) =
        (n.primeFactors.card : ℝ) * log 2 := by
      rw [show ((2 ^ n.primeFactors.card : ℕ) : ℝ) =
          (2 : ℝ) ^ n.primeFactors.card by norm_num]
      rw [Real.log_pow]
    rwa [hlog2pow] at hlogpow
  have hdiv : (n.primeFactors.card : ℝ) ≤ log (n : ℝ) / log 2 := by
    rwa [le_div_iff₀ hlog2]
  exact hdiv

/-- **带符号 forbidden 计数除数加权和的最终界 (chen #39)**:
`Σ_{d|P} 3^{ω(d)}·|Σ_{1≠e|F} μ(e)·base(lcm(d,e))| ≤ (1+ω(F))·16^8·√N`.
由 swap 恒等式 (`swap_weightedSum_eq`) 把左端化为 `Σ_{p∈S} 4^{ω(gcd(P,N−p))}`,
再经 `divisorWeightedSum_le` 界为 `(1+ω(F))·16^8·√N`. 零 sorry. -/
lemma swapWeightedSum_le (N : ℕ) (hN : 2 ≤ N) (hEven : Even N) :
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|) ≤
      ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
  classical
  have hswap := swap_weightedSum_eq N hN
  have hdiv := divisorWeightedSum_le N hN hEven
  calc
    (∑ d ∈ (correctedChenSiftingProduct N).divisors,
      (3 : ℝ) ^ d.primeFactors.card *
        |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          (μ e : ℝ) * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|)
        = (∑ p ∈ (Finset.range N).filter (fun p => p.Prime ∧ 2 ≤ N - p ∧
            ∃ r : ℕ, r.Prime ∧ r ∣ correctedChenForbiddenProduct N ∧ r ∣ N - p),
          (4 : ℝ) ^ (Nat.gcd (correctedChenSiftingProduct N) (N - p)).primeFactors.card) := hswap
    _ ≤ ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := hdiv

/-- **√N·polylog 吸收 (chen #39)**: 对任意 `A`, 最终 `log^{A+1} N ≤ √N`.
证明: `isLittleO_log_rpow_atTop (1/(2(A+1)))` 给出最终 `log x ≤ x^{1/(2(A+1))}`,
离散化到 ℕ 后乘 `A+1` 次幂得 `log^{A+1} N ≤ N^{1/2} = √N`. 零 sorry. -/
lemma eventual_log_pow_le_sqrt (A : ℕ) :
    ∃ x₀ : ℕ, ∀ N : ℕ, x₀ ≤ N → (Real.log (N : ℝ)) ^ (A + 1) ≤ Real.sqrt (N : ℝ) := by
  let r : ℝ := 1 / (2 * ((A : ℝ) + 1))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hleR : ∀ᶠ x : ℝ in atTop, Real.log x ≤ x ^ r := by
    have hE := (isLittleO_log_rpow_atTop hr).eventuallyLE
    filter_upwards [hE, eventually_ge_atTop (1 : ℝ)] with x hxE hx1
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxrnn : 0 ≤ x ^ r := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognn, abs_of_nonneg hxrnn] using hxE
  -- eventually atTop on ℝ ⟹ ∃ M
  rcases (eventually_atTop.1 hleR) with ⟨M, hM⟩
  let x₀ : ℕ := Nat.ceil (max M 1)
  refine ⟨x₀, ?_⟩
  intro N hN
  have hNge : (max M 1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (x₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (max M 1 : ℝ) ≤ (x₀ : ℝ) := by
      dsimp [x₀]
      exact Nat.le_ceil _
    linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := (max_le_iff.mp hNge).2
  have hMle : M ≤ (N : ℝ) := (max_le_iff.mp hNge).1
  have hxle := hM (N : ℝ) hMle
  calc
    (Real.log (N : ℝ)) ^ (A + 1) ≤ ((N : ℝ) ^ r) ^ (A + 1) := by
      exact pow_le_pow_left₀ (Real.log_nonneg hN1) hxle (A + 1)
    _ = (N : ℝ) ^ (r * ((A : ℝ) + 1)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
      congr 1
      norm_num
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
      congr 1
      dsimp [r]
      field_simp
    _ = Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_eq_rpow]

/-- **ω(F(N)) ≤ 1 + ω(N)** (chen #39, N ≥ 2): F 的素因子 ⊆ `{2} ∪ {r | N, r 素数}`, 故
`ω(F) ≤ |{2}| + ω(N) = 1 + ω(N)`. 零 sorry. -/
lemma omega_forbidden_le (N : ℕ) (hN : 2 ≤ N) :
    (correctedChenForbiddenProduct N).primeFactors.card ≤ 1 + N.primeFactors.card := by
  classical
  let F : ℕ := correctedChenForbiddenProduct N
  -- F 的素因子 = {r < z : r.Prime ∧ (r ≤ 2 ∨ r | N)}
  have hFpf : F.primeFactors = (Finset.range (correctedChenZ N)).filter (fun r =>
      r.Prime ∧ (r ≤ 2 ∨ r ∣ N)) := by
    simpa [F] using correctedChenForbiddenProduct_primeFactors N
  -- F.primeFactors ⊆ {2} ∪ {r : r | N, r 素数}
  have hsub : F.primeFactors ⊆ ({2} : Finset ℕ) ∪
      (Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N) := by
    intro r hr
    rw [hFpf] at hr
    rw [Finset.mem_filter] at hr
    rcases hr with ⟨hrz, hcond⟩
    rcases hcond with ⟨hrprime, hcase⟩
    rw [Finset.mem_union]
    rcases hcase with hle2 | hdvd
    · left
      have hr2 : r = 2 := by
        have hrge : 2 ≤ r := hrprime.two_le
        omega
      simp [hr2]
    · right
      rw [Finset.mem_filter]
      exact ⟨hrz, hrprime, hdvd⟩
  -- {r : r|N, r 素数} ⊆ N.primeFactors
  have hsub2 : (Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N) ⊆
      N.primeFactors := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rcases hr with ⟨hrz, hcond⟩
    rcases hcond with ⟨hrprime, hdvd⟩
    have hN0 : N ≠ 0 := by omega
    exact (Nat.mem_primeFactors_of_ne_zero hN0).mpr ⟨hrprime, hdvd⟩
  -- 计数
  calc
    F.primeFactors.card ≤ (({2} : Finset ℕ) ∪
        (Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N)).card := by
      exact Finset.card_le_card hsub
    _ ≤ ({2} : Finset ℕ).card + ((Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N)).card := by
      exact Finset.card_union_le _ _
    _ = 1 + ((Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N)).card := by simp
    _ ≤ 1 + N.primeFactors.card := by
      have h : ((Finset.range (correctedChenZ N)).filter (fun r => r.Prime ∧ r ∣ N)).card ≤
          N.primeFactors.card := Finset.card_le_card hsub2
      omega

/-- **MainB 部分的最终 log^A 吸收 (chen #39, ℕ 指数版)**: 对任意 `A`, 最终
`(1 + ω(F(N)))·16^8·√N ≤ C·N/(log N)^A`.
证明链: `ω(F) ≤ 1 + ω(N)` (omega_forbidden_le) + `ω(N) ≤ log N/log 2`
(omega_le_log_two) ⟹ `1+ω(F) ≤ 2 + log N/log 2 ≤ (1+1/log 2)·log N` (2 ≤ log N);
`eventual_log_pow_le_sqrt` 给最终 `(log N)^(A+1) ≤ √N`, 故
`√N·log N·(log N)^A ≤ √N·(log N)^(A+1) ≤ N`; 组合得目标. 零 sorry. -/
lemma mainB_sqrt_absorbed (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ N : ℕ, x₀ ≤ N → (1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  rcases eventual_log_pow_le_sqrt A with ⟨x₀₁, hsqrt₁⟩
  have hlog1ev : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ Real.log x := by
    exact (Real.tendsto_log_atTop.eventually_ge_atTop 2)
  rcases (eventually_atTop.1 hlog1ev) with ⟨M₁, hM₁⟩
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let x₀ : ℕ := max x₀₁ (Nat.ceil (max M₁ 2))
  let C : ℝ := (16 ^ 8) * (1 + 1 / Real.log 2)
  refine ⟨C, ?_, x₀, ?_⟩
  · dsimp [C]
    positivity
  · intro N hN
    have hNx0₁ : x₀₁ ≤ N := by
      have h1 : x₀₁ ≤ x₀ := by dsimp [x₀]; exact Nat.le_max_left _ _
      exact le_trans h1 (by exact_mod_cast hN)
    have hNge : (max M₁ 2 : ℝ) ≤ (N : ℝ) := by
      have h1 : (Nat.ceil (max M₁ 2) : ℝ) ≤ (N : ℝ) := by
        have hx : (x₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have hceil : (Nat.ceil (max M₁ 2) : ℝ) ≤ (x₀ : ℝ) := by
          dsimp [x₀]
          exact_mod_cast (Nat.le_max_right _ _)
        linarith
      have h2 : (max M₁ 2 : ℝ) ≤ (Nat.ceil (max M₁ 2) : ℝ) := by
        exact_mod_cast (Nat.le_ceil _)
      linarith
    have hM1le : M₁ ≤ (N : ℝ) := (max_le_iff.mp hNge).1
    have hN2R : (2 : ℝ) ≤ (N : ℝ) := (max_le_iff.mp hNge).2
    have hN2 : 2 ≤ N := by exact_mod_cast hN2R
    have hlog2N : (2 : ℝ) ≤ Real.log (N : ℝ) := hM₁ (N : ℝ) hM1le
    have hlog1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by linarith
    have hlogpos : 0 < Real.log (N : ℝ) := by linarith
    have hFo := omega_forbidden_le N hN2
    have hNo := omega_le_log_two N hN2
    -- 1+ω(F) ≤ (1+1/log 2)·log N
    have h1wo : ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) ≤
        (1 + 1 / Real.log 2) * Real.log (N : ℝ) := by
      have hc2 : ((correctedChenForbiddenProduct N).primeFactors.card : ℝ) ≤ 1 + (N.primeFactors.card : ℝ) := by
        have hcast : ((correctedChenForbiddenProduct N).primeFactors.card : ℝ) ≤
            ((1 + N.primeFactors.card : ℕ) : ℝ) := by exact_mod_cast hFo
        norm_num at hcast ⊢
        linarith
      have hNo2 : (N.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := hNo
      have hleft : ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) ≤
          2 + Real.log (N : ℝ) / Real.log 2 := by
        calc
          (1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)
              ≤ 1 + (1 + (N.primeFactors.card : ℝ)) := by linarith
          _ = 2 + (N.primeFactors.card : ℝ) := by ring
          _ ≤ 2 + Real.log (N : ℝ) / Real.log 2 := by
                exact add_le_add_right hNo2 2
      have hright : 2 + Real.log (N : ℝ) / Real.log 2 ≤
          (1 + 1 / Real.log 2) * Real.log (N : ℝ) := by
        have hre : (1 + 1 / Real.log 2) * Real.log (N : ℝ) =
            Real.log (N : ℝ) + Real.log (N : ℝ) / Real.log 2 := by
          rw [add_mul, one_mul]
          field_simp
          ring
        rw [hre]
        nlinarith [hlog2N]
      exact le_trans hleft hright
    -- 核心: √N·log N·(log N)^A ≤ N
    have hsqrtN : (Real.log (N : ℝ)) ^ (A + 1) ≤ Real.sqrt (N : ℝ) := hsqrt₁ N hNx0₁
    have hlogpow : (Real.log (N : ℝ)) ^ A ≤ (Real.log (N : ℝ)) ^ (A + 1) := by
      have hAl : A ≤ A + 1 := by omega
      exact pow_le_pow_right₀ hlog1 hAl
    have hcore : Real.sqrt (N : ℝ) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A ≤ (N : ℝ) := by
      have hnn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      have hle1 : Real.sqrt (N : ℝ) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A ≤
          Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ (A + 1) := by
        -- √N·(log·log^A) = √N·log^(A+1) (pow_succ 结合)
        have hpow : Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A =
            (Real.log (N : ℝ)) ^ (A + 1) := by
          rw [mul_comm]
          rw [← pow_succ]
        have hre : Real.sqrt (N : ℝ) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A =
            Real.sqrt (N : ℝ) * (Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A) := by ring
        rw [hre, hpow]
      have hle2 : Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ (A + 1) ≤
          Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsqrtN hnn
      have hle3 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
        have hNnn : 0 ≤ (N : ℝ) := by positivity
        have hsq := Real.sq_sqrt hNnn
        rw [← sq]
        exact le_of_eq hsq
      exact le_trans (le_trans hle1 hle2) hle3
    -- 装配
    have hcN : (1 + 1 / Real.log 2) * Real.log (N : ℝ) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
      dsimp [C]
      have hnn : 0 ≤ (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) := by positivity
      have hdiv : Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
        have hlogApos : 0 < (Real.log (N : ℝ)) ^ A := pow_pos hlogpos A
        rw [le_div_iff₀ hlogApos]
        have hre : Real.sqrt (N : ℝ) * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ A ≤ (N : ℝ) := hcore
        simpa [mul_assoc, mul_comm, mul_left_comm] using hre
      have hmul : (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤
          (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
        have hcoef : 0 ≤ (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) := by positivity
        have hm := mul_le_mul_of_nonneg_left hdiv hcoef
        -- hm: ((1+1/log2)·16^8)·(√N·log N) ≤ ((1+1/log2)·16^8)·(N/log^A N)
        simpa [mul_assoc, mul_comm, mul_left_comm] using hm
      have hleft : ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) ≤
          (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
        have h16nn : 0 ≤ (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by positivity
        have hm1 := mul_le_mul_of_nonneg_right h1wo h16nn
        -- hm1: (1+ω(F))·(16^8·√N) ≤ (1+1/log2)·log N·(16^8·√N)
        -- 目标 RHS = (1+1/log2)·16^8·√N·log N = (1+1/log2)·log N·16^8·√N (交换)
        calc
          ((1 + (correctedChenForbiddenProduct N).primeFactors.card : ℝ)) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ)
              ≤ (1 + 1 / Real.log 2) * Real.log (N : ℝ) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) := by
                -- 由 hm1 (乘结合交换)
                simpa [mul_assoc, mul_comm, mul_left_comm] using hm1
          _ = (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by ring
      have hmul' : (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) * ((N : ℝ) / (Real.log (N : ℝ)) ^ A) ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
        have hcoef : (1 + 1 / Real.log 2) * (16 ^ 8 : ℝ) = C := by
          dsimp [C]
          ring
        rw [← hcoef]
        ring_nf
        rfl
      exact le_trans (le_trans hleft hmul) hmul'

/-- **`CorrectedChenPanTruncationInput` 的结构归约 (chen #8)**: 由两条解析台阶
(`ChenPanTruncationSieveBound` 分布误差部分, `ChenPanTruncationMainTermBound`
`li` 主项部分) 组装出截断输入: 对每个 `d | P(N)`,
`|rem d − Δ'(d)| ≤ |li(N−2)−li(N)|/φ(d) + Σ_{1≠e|F} |μ(e)|·(|Δ'(lcm(d,e))| + |li(N−2)|/φ(lcm(d,e)))`;
求和后分布误差部分由筛界控制、`li` 部分由主项界控制. 零 sorry, 全部结构步骤
(展开/三角不等式/求和) 均已证明; 常数取 `C = C₁ + C₂`, 起点取
`x₀ = max 4 x₀₁ x₀₂` (保证 `2 ≤ N` 使分布误差恒等式可用). -/
theorem CorrectedChenPanTruncationInput.of_sieveBound
    (hSieve : ChenPanTruncationSieveBound)
    (hMain : ChenPanTruncationMainTermBound) :
    CorrectedChenPanTruncationInput := by
  classical
  intro A hApos B
  rcases hSieve A hApos B with ⟨C1, hC1pos, x₀₁, hSieveN⟩
  rcases hMain A hApos B with ⟨C2, hC2pos, x₀₂, hMainN⟩
  refine ⟨C1 + C2, add_pos hC1pos hC2pos, max 4 (max x₀₁ x₀₂), ?_⟩
  intro N hN hEven
  have hN1 : x₀₁ ≤ N := by omega
  have hN2 : x₀₂ ≤ N := by omega
  have hN2' : 2 ≤ N := by omega
  have hS := hSieveN N hN1 hEven
  have hM := hMainN N hN2 hEven
  let P : ℕ := correctedChenSiftingProduct N
  let F : ℕ := correctedChenForbiddenProduct N
  let E : Finset ℕ := F.divisors.filter (fun e => e ≠ 1)
  let D : ℕ := Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) / (log (N : ℝ)) ^ B)
  let ω : ℕ → ℝ := fun d => (3 : ℝ) ^ d.primeFactors.card
  let Δ' : ℕ → ℝ := fun m => AnalyticNumberTheory.Sieve.panDistributionError (N - 2) 1 m (N % m)
  let L : ℕ → ℝ := fun d => |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ) -
      AnalyticNumberTheory.Sieve.logarithmicIntegral (N : ℝ)| / (Nat.totient d : ℝ)
  let S1 : ℕ → ℝ := fun d => ∑ e ∈ E, |(μ e : ℝ)| * |Δ' (Nat.lcm d e)|
  let S2 : ℕ → ℝ := fun d =>
      |∑ e ∈ E, (μ e : ℝ) * (((Finset.range N).filter (fun p =>
        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|
  let MainA : ℝ := ∑ d ∈ P.divisors, ω d * L d
  let Sieve1 : ℝ := ∑ d ∈ P.divisors, ω d * S1 d
  let MainB : ℝ := ∑ d ∈ P.divisors, ω d * S2 d
  let Sieve2 : ℝ := ∑ d ∈ P.divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)), ω d * |Δ' d|
  have hSieveSplit : Sieve1 + Sieve2 ≤ C1 * (N : ℝ) / (log (N : ℝ)) ^ A := by
    -- 目标 Sieve1 + Sieve2 与 hS 的 LHS 逐项定义相等 (let 展开后 = hS 的原始求和).
    -- 用 dsimp 展开 let, 然后 exact hS (hS 已是实例化的 ChenPanTruncationSieveBound).
    dsimp [Sieve1, Sieve2, S1, E, F, P, D, ω, Δ']
    -- 展开后目标 = (Σ_d ω·Σ_e|μ||Δ'(lcm)|) + (Σ_{d>D} ω|Δ'|) ≤ C1·N/log^A N = hS
    simpa [ChenPanTruncationSieveBound] using hS
  have hMainSplit : MainA + MainB ≤ C2 * (N : ℝ) / (log (N : ℝ)) ^ A := by
    dsimp [MainA, MainB, S2, E, F, P, L, ω]
    simpa [ChenPanTruncationMainTermBound] using hM
  have hterm : ∀ d ∈ P.divisors,
      ω d * |(correctedChenBoundingSieve N).rem d - Δ' d| ≤
        ω d * L d + ω d * S2 d := by
    intro d hdmem
    have hd : d ∣ correctedChenSiftingProduct N := (Nat.mem_divisors.mp hdmem).1
    have hPpos : 0 < P := Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hPpos
    have h3 : 0 ≤ ω d := by
      unfold ω
      positivity
    have hB := abs_correctedChenRem_sub_distributionError_le N d hd hN2'
    have hB' : |(correctedChenBoundingSieve N).rem d - Δ' d| ≤ L d + S2 d := by
      simpa [L, S2, E, F, Δ'] using hB
    calc
      ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|
          ≤ ω d * (L d + S2 d) := mul_le_mul_of_nonneg_left hB' h3
      _ = ω d * L d + ω d * S2 d := by ring
  have hsum1 : (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|) ≤
      MainA + MainB := by
    have hle := Finset.sum_le_sum hterm
    calc
      (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|)
          ≤ ∑ d ∈ P.divisors, (ω d * L d + ω d * S2 d) := hle
      _ = MainA + MainB := by
        rw [Finset.sum_add_distrib]
  calc
    (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|) +
        (∑ d ∈ P.divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)), ω d * |Δ' d|)
        ≤ (MainA + MainB) + Sieve2 := by
          -- hsum1: Σ ≤ MainA+MainB; 用 add_le_add 两边加 Sieve2
          exact add_le_add hsum1 (le_rfl : Sieve2 ≤ Sieve2)
    _ ≤ (MainA + MainB) + C1 * (N : ℝ) / (log (N : ℝ)) ^ A := by
        -- Sieve2 ≤ C1·N/log^A N (hSieveSplit 中 Sieve1 ≥ 0); 两边加 MainA+MainB
        have hS2le : Sieve2 ≤ C1 * (N : ℝ) / (log (N : ℝ)) ^ A := by
          have hS1nn : 0 ≤ Sieve1 := by
            dsimp [Sieve1]
            exact Finset.sum_nonneg (fun d hd => by
              apply mul_nonneg; positivity; positivity)
          nlinarith [hSieveSplit, hS1nn]
        nlinarith [hS2le]
    _ ≤ C2 * (N : ℝ) / (log (N : ℝ)) ^ A + C1 * (N : ℝ) / (log (N : ℝ)) ^ A :=
        add_le_add hMainSplit (le_rfl : C1 * (N : ℝ) / (log (N : ℝ)) ^ A ≤ C1 * (N : ℝ) / (log (N : ℝ)) ^ A)
    _ = (C1 + C2) * (N : ℝ) / (log (N : ℝ)) ^ A := by ring

