import MathlibNt.SieveTheory.SwitchingPrinciple

/-!
# Pan truncation input structural reduction

Structural reduction of CorrectedChenPanTruncationInput: rem Moebius decomposition,
triangle inequality, reduction to two analytic steps (ChenPanTruncationSieveBound,
ChenPanTruncationMainTermBound). Zero sorry; analytic steps are explicit Props.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset

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
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            |(μ e : ℝ)| * |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
              (Nat.totient (Nat.lcm d e) : ℝ))) ≤
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
        (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
          |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) := by
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
          (∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
            |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) := by
          have hSle : |∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
                (μ e : ℝ) * (((Finset.range N).filter (fun p =>
                  p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| ≤
              ∑ e ∈ (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1),
                |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
                  p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) := by
            let E : Finset ℕ := (correctedChenForbiddenProduct N).divisors.filter (fun e => e ≠ 1)
            calc
              |∑ e ∈ E, (μ e : ℝ) * (((Finset.range N).filter (fun p =>
                  p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)|
                  ≤ ∑ e ∈ E, |(μ e : ℝ) * (((Finset.range N).filter (fun p =>
                    p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)| :=
                    Finset.abs_sum_le_sum_abs (fun e => (μ e : ℝ) *
                      (((Finset.range N).filter (fun p =>
                        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) E
              _ = ∑ e ∈ E, |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
                    p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro e he
                    rw [abs_mul]
                    have hbase : 0 ≤ (((Finset.range N).filter (fun p =>
                        p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) := by positivity
                    rw [abs_of_nonneg hbase]
          exact add_le_add_right hSle _

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
                  by_cases hcop : ∀ r : ℕ, r.Prime → r ∣ F → ¬ r ∣ N - p
                  · simp [hcop, F]
                  · simp [hcop, F]
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
  let S2 : ℕ → ℝ := fun d => ∑ e ∈ E, |(μ e : ℝ)| * |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
      (Nat.totient (Nat.lcm d e) : ℝ)
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
        ω d * L d + ω d * S1 d + ω d * S2 d := by
    intro d hdmem
    have hd : d ∣ correctedChenSiftingProduct N := (Nat.mem_divisors.mp hdmem).1
    have hPpos : 0 < P := Nat.pos_of_ne_zero (correctedChenSiftingProduct_ne_zero N)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hPpos
    have h3 : 0 ≤ ω d := by
      unfold ω
      positivity
    have hB := abs_correctedChenRem_sub_distributionError_le N d hd hN2'
    have hS12 : (∑ e ∈ E, |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
          p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) ≤ S1 d + S2 d := by
      have hterm2 : ∀ e ∈ E,
          |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ) ≤
            |(μ e : ℝ)| * |Δ' (Nat.lcm d e)| +
              |(μ e : ℝ)| * |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
                (Nat.totient (Nat.lcm d e) : ℝ) := by
        intro e he
        have heF : e ∣ F := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
        have hFpos : 0 < F := Nat.pos_of_ne_zero (correctedChenForbiddenProduct_ne_zero N)
        have hepos : 0 < e := Nat.pos_of_dvd_of_pos heF hFpos
        have hlcmpos : 0 < Nat.lcm d e :=
          Nat.pos_of_ne_zero (Nat.lcm_ne_zero (ne_of_gt hdpos) (ne_of_gt hepos))
        have hC := baseCount_le_distributionError_add_li N (Nat.lcm d e) hN2' hlcmpos
        have hmu0 : 0 ≤ |(μ e : ℝ)| := abs_nonneg _
        calc
          |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
              p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)
              ≤ |(μ e : ℝ)| * (|Δ' (Nat.lcm d e)| +
                  |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
                    (Nat.totient (Nat.lcm d e) : ℝ)) :=
                mul_le_mul_of_nonneg_left hC hmu0
          _ = |(μ e : ℝ)| * |Δ' (Nat.lcm d e)| +
              |(μ e : ℝ)| * |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
                (Nat.totient (Nat.lcm d e) : ℝ) := by ring
      calc
        (∑ e ∈ E, |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
            p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ))
            ≤ ∑ e ∈ E, (|(μ e : ℝ)| * |Δ' (Nat.lcm d e)| +
                |(μ e : ℝ)| * |AnalyticNumberTheory.Sieve.logarithmicIntegral (N - 2 : ℝ)| /
                  (Nat.totient (Nat.lcm d e) : ℝ)) :=
              Finset.sum_le_sum hterm2
        _ = S1 d + S2 d := by
          rw [Finset.sum_add_distrib]
    have hB' : |(correctedChenBoundingSieve N).rem d - Δ' d| ≤ L d + S1 d + S2 d := by
      calc
        |(correctedChenBoundingSieve N).rem d - Δ' d|
            ≤ L d + (∑ e ∈ E, |(μ e : ℝ)| * (((Finset.range N).filter (fun p =>
                p.Prime ∧ 2 ≤ N - p ∧ p ≡ N [MOD Nat.lcm d e])).card : ℝ)) := by
              simpa [L, E, F, Δ'] using hB
        _ ≤ L d + (S1 d + S2 d) := add_le_add_right hS12 (L d)
        _ = L d + S1 d + S2 d := by ring
    calc
      ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|
          ≤ ω d * (L d + S1 d + S2 d) := mul_le_mul_of_nonneg_left hB' h3
      _ = ω d * L d + ω d * S1 d + ω d * S2 d := by ring
  have hsum1 : (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|) ≤
      MainA + Sieve1 + MainB := by
    have hle := Finset.sum_le_sum hterm
    calc
      (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|)
          ≤ ∑ d ∈ P.divisors, (ω d * L d + ω d * S1 d + ω d * S2 d) := hle
      _ = MainA + Sieve1 + MainB := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
  calc
    (∑ d ∈ P.divisors, ω d * |(correctedChenBoundingSieve N).rem d - Δ' d|) +
        (∑ d ∈ P.divisors.filter (fun d => ¬ (2 ≤ d ∧ d ≤ D)), ω d * |Δ' d|)
        ≤ (MainA + Sieve1 + MainB) + Sieve2 := by
          -- hsum1: Σ ≤ MainA+Sieve1+MainB; 用 add_le_add 两边加 Sieve2
          exact add_le_add hsum1 (le_rfl : Sieve2 ≤ Sieve2)
    _ = (MainA + MainB) + (Sieve1 + Sieve2) := by ring
    _ ≤ (MainA + MainB) + C1 * (N : ℝ) / (log (N : ℝ)) ^ A := by
        -- hSieveSplit: Sieve1+Sieve2 ≤ C1·N/log^A N; 两边加 MainA+MainB (线性重排)
        nlinarith [hSieveSplit]
    _ ≤ C2 * (N : ℝ) / (log (N : ℝ)) ^ A + C1 * (N : ℝ) / (log (N : ℝ)) ^ A :=
        add_le_add hMainSplit (le_rfl : C1 * (N : ℝ) / (log (N : ℝ)) ^ A ≤ C1 * (N : ℝ) / (log (N : ℝ)) ^ A)
    _ = (C1 + C2) * (N : ℝ) / (log (N : ℝ)) ^ A := by ring

