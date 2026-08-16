import MathlibNt.SieveTheory.PrimePair
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# 线性型素数对一致上界 (PrimePairLinearFormBound) 的推进与台阶分解

本文件研究 legacy `PrimePairLinearFormBound` (PrimePair.lean)。其裸
`a/φ(a)` 右端遗漏随 N 变化的 Goldbach 局部因子，因而其中的相关 Prop
与推导仅是条件性代数基础设施，不能被用作 corrected Chen 的解析供给：

    #{p₃ ≤ X : p₃ 素数, N − a·p₃ 素数} ≤ C·(a/φ(a))·X/(log X·log N),  X = N/a,

正确替代接口须携带 `primePairNu(N,a;ell)`、原始/固定因子分裂、实际 Chen
`a` 支撑与统一阈值，详见 `CHEN_VARIABLE_A_LOCAL_DENSITY_AUDIT.md`。
在该修复后，经典证明仍需要二线性型筛 (维度 2 的 Selberg/线性筛)
+ Bombieri--Vinogradov/Pan 级平均分布 + Mertens 主项; 当前 ant 材料不含
其中的平均 BV/Pan 定理 (ant 的 `bombieri_vinogradov` 只是逐参数平凡接口,
`PanMeanValueUniform` 是开放研究输入), 故本次无法完整证明该台阶。

本文件交付 (全部新定理零 sorry):

  1. **单 log 一致上界** (从 ant PNT `primeCounting_upper_bound` 真证明):
        count ≤ C₀·(N/a)/log(N/a)  与  count ≤ C₀·(N/φ(a))/log(N/a)。
     后者与目标形状一致但缺 `1/log N` 因子 (N−ap₃ 侧素性的第二个 log);
     `φ(a) ≤ a` 免费给出局部密度因子 `a/φ(a)` 的形状。
  2. **筛除包含步** (真证明):
        count ≤ #{n ≤ X : (n,P(z))=(N−an,P(z))=1} + 2·(z−1)。
  3. **代数收尾** (真证明):
        `PrimePairLinearFormLogSquareBound` (count ≤ C·(N/φ(a))/log²N)
        ⟹ `PrimePairLinearFormBound` (因 log(N/a) ≤ log N ⟹ log²N ≥ logN·log(N/a))。
  4. **解析核心的显式 Prop 子台阶** (精确陈述 + 数学路线, 与仓库纪律一致):
        `LinearFormPairDistributionCondition`   (BV/Pan 级二线性型平均分布)
        `LinearFormPairDimensionTwoSieveBound`  (维度 2 上界筛)
        `LinearFormPairLocalDensityBound`       (Mertens/奇异级数局部密度)
        `PrimePairLinearFormLogSquareBound`     (上述三者的组合输出)

剩余差距: 子台阶 4 的三个 Prop 需新建设备 (平均 BV/Pan + 维度 2 筛 +
局部密度主项), 见各 Prop 的路线注记与模块导言的"差距报告"。
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open scoped Classical

/-! ## 0. 分析不等式: x/log x 的换标 -/

/-- `2 ≤ x ≤ X` 时 `x/log x ≤ 2·(X/log X)`。

分三情形: `X ≤ e` (log X ≤ 1 直接吸收), `x ≤ e ≤ X` (常数吸收),
`e ≤ x ≤ X` (用 `log x/x` 在 `[e, ∞)` 上的反单调性
`Real.log_div_self_antitoneOn`)。 -/
private lemma div_log_le_mul_of_le {x X : ℝ} (hx2 : 2 ≤ x) (hxX : x ≤ X) :
    x / log x ≤ 2 * (X / log X) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hX1 : (1 : ℝ) < X := by
    have : (2 : ℝ) ≤ X := le_trans hx2 hxX
    linarith
  have hlogx : 0 < log x := Real.log_pos hx1
  have hlogX : 0 < log X := Real.log_pos hX1
  have hlogx12 : (1 / 2 : ℝ) ≤ log x := by
    have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by
      have : (1 / 2 : ℝ) < (0.6931471803 : ℝ) := by norm_num
      linarith [Real.log_two_gt_d9]
    have hlogle : log 2 ≤ log x := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx2
    linarith
  have hx_le_2x : x / log x ≤ 2 * x := by
    rw [div_le_iff₀ hlogx]
    nlinarith [hx1, hlogx12]
  by_cases hXe : X ≤ Real.exp 1
  · -- X ≤ e: log X ≤ 1, 直接吸收
    have hlogX1 : log X ≤ 1 := by
      have hle : log X ≤ log (Real.exp 1) := Real.log_le_log (by positivity : 0 < X) hXe
      simpa using hle
    have hX_le_Xdiv : X ≤ X / log X := by
      rw [le_div_iff₀ hlogX]
      have : X * log X ≤ X * 1 := mul_le_mul_of_nonneg_left hlogX1 (by positivity : 0 ≤ X)
      simpa using this
    calc
      x / log x ≤ 2 * x := hx_le_2x
      _ ≤ 2 * X := by
        exact mul_le_mul_of_nonneg_left hxX (by norm_num)
      _ ≤ 2 * (X / log X) := by
        exact mul_le_mul_of_nonneg_left hX_le_Xdiv (by norm_num)
  · -- e < X
    have heX : Real.exp 1 ≤ X := le_of_not_ge hXe
    have hanti := Real.log_div_self_antitoneOn
    have hmemE : Real.exp 1 ∈ Set.Ici (Real.exp 1) := by simp
    have hmemX : X ∈ Set.Ici (Real.exp 1) := by simpa using heX
    have hXge_e : Real.exp 1 ≤ X / log X := by
      have hle : log X / X ≤ log (Real.exp 1) / Real.exp 1 := hanti hmemE hmemX heX
      have hle' : log X / X ≤ (1 : ℝ) / Real.exp 1 := by simpa using hle
      rw [le_div_iff₀ hlogX]
      have hm := mul_le_mul_of_nonneg_right hle' (by positivity : 0 ≤ Real.exp 1 * X)
      field_simp [Real.exp_ne_zero (1 : ℝ), (ne_of_gt hX1)] at hm ⊢
      exact hm
    by_cases hxe : x ≤ Real.exp 1
    · -- x ≤ e ≤ X
      calc
        x / log x ≤ 2 * x := hx_le_2x
        _ ≤ 2 * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left hxe (by norm_num)
        _ ≤ 2 * (X / log X) := by
          exact mul_le_mul_of_nonneg_left hXge_e (by norm_num)
    · -- e ≤ x ≤ X: 反单调直接比较
      have hxge : Real.exp 1 ≤ x := le_of_not_ge hxe
      have hmemx : x ∈ Set.Ici (Real.exp 1) := by simpa using hxge
      have hle : log X / X ≤ log x / x := hanti hmemx hmemX hxX
      have hm := mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ x * X)
      have hm' : x * log X ≤ X * log x := by
        field_simp [ne_of_gt hX1, ne_of_gt hx1] at hm
        simpa [mul_comm] using hm
      have hxx : x / log x ≤ X / log X := by
        rw [div_le_div_iff₀ hlogx hlogX]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hm'
      exact le_trans hxx (by
        have hpos : 0 ≤ X / log X := by positivity
        nlinarith)

/-! ## 1. 素数对计数与素数计数的桥 -/

/-- 素数对计数不超过素数计数: `PrimePairLinearFormCount N a ≤ π(N/a)`。 -/
theorem primePairLinearFormCount_le_primeCounting (N a : ℕ) :
    PrimePairLinearFormCount N a ≤ Nat.primeCounting (N / a) := by
  unfold PrimePairLinearFormCount
  rw [show Nat.primeCounting (N / a) =
      ((Finset.range (N / a + 1)).filter Nat.Prime).card by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]]
  exact primePairLinearFormCount_le_pi N a

/-- `N/a < 2` 时线性型素数对计数为 0 (p₃ 候选至多为 1, 无素数)。 -/
theorem primePairLinearFormCount_eq_zero_of_two_mul_gt (N a : ℕ) (h : N < 2 * a) :
    PrimePairLinearFormCount N a = 0 := by
  unfold PrimePairLinearFormCount
  have hdiv : N / a < 2 := by
    by_contra hnot
    have hle2 : 2 ≤ N / a := by omega
    have hmul : 2 * a ≤ (N / a) * a := Nat.mul_le_mul_right a hle2
    have hleN : (N / a) * a ≤ N := by
      rw [mul_comm]
      exact Nat.mul_div_le N a
    omega
  have hsub : ((Finset.range (N / a + 1)).filter
      (fun p₃ => p₃.Prime ∧ (N - a * p₃).Prime)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p₃ hp₃ hp₃pp
    have hp3lt : p₃ < N / a + 1 := (Finset.mem_range.mp hp₃)
    have hp3le : p₃ ≤ 1 := by omega
    have h2 : 2 ≤ p₃ := hp₃pp.1.two_le
    omega
  rw [hsub]
  simp
/-! ## 2. 单 log 一致上界 (ant PNT 实例化) -/

/-- **线性型素数对的一致 π 上界** (零 sorry): 对 `1 ≤ a, 2a ≤ N`,

    #{p₃ ≤ N/a : p₃ 素数, N−a·p₃ 素数} ≤ C₀·(N/a)/log(N/a)。

这是 `PrimePairLinearFormBound` 目标形状的单 log 版本: 缺 `1/log N` 因子
(N−ap₃ 侧素性带来的第二个 log)。 -/
theorem primePairLinearFormCount_bound_by_piUpperBound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
      (PrimePairLinearFormCount N a : ℝ) ≤
        C₀ * (N : ℝ) / (a : ℝ) / log ((N : ℝ) / (a : ℝ)) := by
  rcases AnalyticNumberTheory.PrimeDistribution.primeCounting_upper_bound with ⟨C, hC, hcount⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro N a ha h2a
  have hx2n : 2 ≤ N / a := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
    exact h2a
  have hpi : (PrimePairLinearFormCount N a : ℝ) ≤ (Nat.primeCounting (N / a) : ℝ) := by
    exact_mod_cast primePairLinearFormCount_le_primeCounting N a
  have hcount' : (Nat.primeCounting (N / a) : ℝ) ≤
      C * ((N / a : ℕ) : ℝ) / log ((N / a : ℕ) : ℝ) :=
    hcount (N / a) hx2n
  let x : ℝ := ((N / a : ℕ) : ℝ)
  let X : ℝ := (N : ℝ) / (a : ℝ)
  have hx2 : (2 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hx2n
  have hxX : x ≤ X := by
    dsimp [x, X]
    have hmul : a * (N / a) ≤ N := Nat.mul_div_le N a
    rw [le_div_iff₀ (by exact_mod_cast (by omega : 0 < a))]
    exact_mod_cast (by simpa [mul_comm] using hmul)
  have hdl := div_log_le_mul_of_le (x := x) (X := X) hx2 hxX
  have hmain : C * x / log x ≤ (2 * C) * X / log X := by
    have hC0 : 0 ≤ C := le_of_lt hC
    calc
      C * x / log x = C * (x / log x) := by ring
      _ ≤ C * (2 * (X / log X)) := mul_le_mul_of_nonneg_left hdl hC0
      _ = (2 * C) * X / log X := by ring
  calc
    (PrimePairLinearFormCount N a : ℝ) ≤ (Nat.primeCounting (N / a) : ℝ) := hpi
    _ ≤ C * x / log x := by simpa [x] using hcount'
    _ ≤ (2 * C) * X / log X := hmain
    _ = (2 * C) * (N : ℝ) / (a : ℝ) / log ((N : ℝ) / (a : ℝ)) := by
          dsimp [X]
          ring

/-- **线性型素数对的一致 π 上界 (φ 形态)** (零 sorry): 对 `1 ≤ a, 2a ≤ N`,

    count ≤ C₀·(N/φ(a))/log(N/a)。

`φ(a) ≤ a` 免费给出局部密度因子 `a/φ(a)` 的形状; 与
`PrimePairLinearFormBound` 相比只缺 `1/log N` 因子。 -/
theorem primePairLinearFormCount_bound_by_piUpperBound_totient :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
      (PrimePairLinearFormCount N a : ℝ) ≤
        C₀ * (N : ℝ) / (Nat.totient a : ℝ) / log ((N : ℝ) / (a : ℝ)) := by
  rcases primePairLinearFormCount_bound_by_piUpperBound with ⟨C₀, hC₀, hb⟩
  refine ⟨C₀, hC₀, ?_⟩
  intro N a ha h2a
  have hφa : (Nat.totient a : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Nat.totient_le a)
  have hφpos : 0 < (Nat.totient a : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < a))
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hC0 : 0 ≤ C₀ := le_of_lt hC₀
  have hlogXpos : 0 < log ((N : ℝ) / (a : ℝ)) := by
    have hX2 : (2 : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
      rw [le_div_iff₀ hapos]
      exact_mod_cast h2a
    exact Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ) / (a : ℝ))
  have hle : C₀ * (N : ℝ) / (a : ℝ) ≤ C₀ * (N : ℝ) / (Nat.totient a : ℝ) := by
    rw [div_le_div_iff₀ hapos hφpos]
    exact mul_le_mul_of_nonneg_left hφa (mul_nonneg hC0 (le_of_lt hNpos))
  calc
    (PrimePairLinearFormCount N a : ℝ) ≤
        C₀ * (N : ℝ) / (a : ℝ) / log ((N : ℝ) / (a : ℝ)) := hb N a ha h2a
    _ ≤ C₀ * (N : ℝ) / (Nat.totient a : ℝ) / log ((N : ℝ) / (a : ℝ)) := by
          exact div_le_div_of_nonneg_right hle (le_of_lt hlogXpos)

/-! ## 3. 筛除包含步: count ≤ sifted + 2·(z−1) -/

/-- 线性型素数对的 z 筛除集: `#{n ≤ N/a : (n, P(z)) = (N−a·n, P(z)) = 1}`,
其中 `P(z) = ∏_{p < z, p 素数} p` 为小素数乘积 (筛水平 z)。 -/
noncomputable def PrimePairLinearFormSiftedCount (N a z : ℕ) : ℕ :=
  ((Finset.range (N / a + 1)).filter (fun n =>
    (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
    (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ (N - a * n)))).card

/-- **筛除包含步** (零 sorry): 素数对计数 ≤ z 筛除计数 + 2·(z−1)。

两个素性条件 (n 素数, N−an 素数) 蕴含 `(n, P(z)) = (N−an, P(z)) = 1`,
除了至多 `2·#{p < z 素数} ≤ 2(z−1)` 个退化情形 (n < z 或 N−an < z);
每个退化情形由对应的小素数唯一决定。 -/
theorem primePairLinearFormCount_le_siftedCount_add_two_z (N a z : ℕ) (ha : 1 ≤ a) :
    PrimePairLinearFormCount N a ≤ PrimePairLinearFormSiftedCount N a z + 2 * z := by
  unfold PrimePairLinearFormCount PrimePairLinearFormSiftedCount
  let S : Finset ℕ := (Finset.range (N / a + 1)).filter
    (fun n => n.Prime ∧ (N - a * n).Prime)
  let T : Finset ℕ := (Finset.range (N / a + 1)).filter
    (fun n => (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ n) ∧
      (∀ p : ℕ, p.Prime → p < z → ¬ p ∣ (N - a * n)))
  let U : Finset ℕ := S.filter (fun n => z ≤ n ∧ z ≤ N - a * n)
  let A : Finset ℕ := S.filter (fun n => n < z)
  let B : Finset ℕ := S.filter (fun n => z ≤ n ∧ N - a * n < z)
  have ha0 : a ≠ 0 := by omega
  have hsub : S ⊆ U ∪ A ∪ B := by
    intro n hn
    by_cases hnz : z ≤ n
    · by_cases hqz : z ≤ N - a * n
      · have hmem : n ∈ U := by
          rw [Finset.mem_filter]
          exact ⟨hn, hnz, hqz⟩
        simp [hmem]
      · have hmem : n ∈ B := by
          rw [Finset.mem_filter]
          exact ⟨hn, hnz, by omega⟩
        simp [hmem]
    · have hmem : n ∈ A := by
        rw [Finset.mem_filter]
        exact ⟨hn, by omega⟩
      simp [hmem]
  have hUT : U ⊆ T := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rcases hn with ⟨hnS, hnz, hqz⟩
    rw [Finset.mem_filter] at hnS
    rcases hnS with ⟨hnr, hnp⟩
    rw [Finset.mem_filter]
    constructor
    · exact hnr
    · constructor
      · intro p hp hplt hpd
        have hp_ne_one : p ≠ 1 := by exact (ne_of_gt hp.one_lt)
        have hn_eq : n = p := (hnp.1.dvd_iff_eq hp_ne_one).mp hpd
        have : z ≤ p := by rwa [← hn_eq]
        omega
      · intro p hp hplt hpd
        have hp_ne_one : p ≠ 1 := by exact (ne_of_gt hp.one_lt)
        have hq_eq : N - a * n = p := (hnp.2.dvd_iff_eq hp_ne_one).mp hpd
        have : z ≤ p := by rwa [← hq_eq]
        omega
  have hA : A.card ≤ z := by
    have hAsub : A ⊆ Finset.range z := by
      intro n hn
      rw [Finset.mem_filter] at hn
      exact Finset.mem_range.mpr (by omega)
    calc
      A.card ≤ (Finset.range z).card := Finset.card_le_card hAsub
      _ = z := by simp
  have hB : B.card ≤ z := by
    let f : ℕ → ℕ := fun n => N - a * n
    have hinj : Set.InjOn f (↑B : Set ℕ) := by
      intro n₁ hn₁ n₂ hn₂ hf
      have hn₁' : n₁ ∈ S ∧ z ≤ n₁ ∧ N - a * n₁ < z := by
        simpa [B] using hn₁
      have hn₂' : n₂ ∈ S ∧ z ≤ n₂ ∧ N - a * n₂ < z := by
        simpa [B] using hn₂
      have hn₁S : n₁ ∈ S := hn₁'.1
      have hn₂S : n₂ ∈ S := hn₂'.1
      have ha_n₁ : a * n₁ ≤ N := by
        rw [Finset.mem_filter] at hn₁S
        rcases hn₁S with ⟨hn₁r, hnp₁⟩
        have hn₁le : n₁ ≤ N / a := by
          rw [Finset.mem_range] at hn₁r
          omega
        calc
          a * n₁ ≤ a * (N / a) := Nat.mul_le_mul_left a hn₁le
          _ ≤ N := Nat.mul_div_le N a
      have ha_n₂ : a * n₂ ≤ N := by
        rw [Finset.mem_filter] at hn₂S
        rcases hn₂S with ⟨hn₂r, hnp₂⟩
        have hn₂le : n₂ ≤ N / a := by
          rw [Finset.mem_range] at hn₂r
          omega
        calc
          a * n₂ ≤ a * (N / a) := Nat.mul_le_mul_left a hn₂le
          _ ≤ N := Nat.mul_div_le N a
      change N - a * n₁ = N - a * n₂ at hf
      have heq : a * n₁ = a * n₂ := by omega
      have heq' : n₁ * a = n₂ * a := by simpa [mul_comm] using heq
      exact Nat.mul_right_cancel (by omega : 0 < a) heq'
    have himg : B.image f ⊆ (Finset.range z).filter (fun q => q.Prime) := by
      intro q hq
      rw [Finset.mem_image] at hq
      rcases hq with ⟨n, hn, rfl⟩
      have hn' : n ∈ S ∧ z ≤ n ∧ N - a * n < z := by
        simpa [B] using hn
      rcases hn' with ⟨hnS, hnz, hqlt⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · rw [Finset.mem_filter] at hnS
        exact hnS.2.2
    calc
      B.card = (B.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.range z).filter (fun q => q.Prime)).card := Finset.card_le_card himg
      _ ≤ z := by
        exact le_trans (Finset.card_le_card (by
          intro q hq
          exact (Finset.mem_filter.mp hq).1)) (by simp)
  have hU : U.card ≤ T.card := Finset.card_le_card hUT
  have hcard : S.card ≤ U.card + A.card + B.card := by
    have h1 : S.card ≤ (U ∪ A ∪ B).card := Finset.card_le_card hsub
    have hUA : (U ∪ A).card ≤ U.card + A.card := Finset.card_union_le _ _
    have hUAB : (U ∪ A ∪ B).card ≤ (U ∪ A).card + B.card := Finset.card_union_le _ _
    omega
  have hSleT : S.card ≤ T.card + 2 * z := by
    calc
      S.card ≤ U.card + A.card + B.card := hcard
      _ ≤ T.card + z + z := by omega
      _ = T.card + 2 * z := by omega
  simpa [S, T] using hSleT

/-- 筛除包含步的实数版本。 -/
theorem primePairLinearFormCount_le_siftedCount_add_two_z_real (N a z : ℕ) (ha : 1 ≤ a) :
    (PrimePairLinearFormCount N a : ℝ) ≤
      (PrimePairLinearFormSiftedCount N a z : ℝ) + 2 * (z : ℝ) := by
  exact_mod_cast primePairLinearFormCount_le_siftedCount_add_two_z N a z ha
/-! ## 4. 解析核心的显式 Prop 子台阶 -/

/-- 二线性型 `n·(N−a·n)` 的 `d` 倍数列计数: `#{n ≤ N/a : d | n(N−an)}`。 -/
def pairLinearFormMultiplesCount (N a d : ℕ) : ℕ :=
  ((Finset.range (N / a + 1)).filter (fun n => d ∣ n * (N - a * n))).card

/-- 二线性型的同余密度: `ρ(N,a;d) = #{n mod d : n(N−an) ≡ 0 (mod d)}`。 -/
def pairLinearFormDensity (N a d : ℕ) : ℕ :=
  ((Finset.range d).filter (fun n => d ∣ n * (N - a * n))).card

/-- **线性型素数对的 BV/Pan 级平均分布条件** (开放输入):

对模 `d ≤ N^{1/2}`, 二线性型 `n(N−an)` 的倍数列计数与密度主项之差
`|A_d − (ρ(d)/d)·X|` (X = N/a) 的 `2^{ω(d)}` 加权和 ≪ X/log^A N,
一致于 `N ≥ N₀, 1 ≤ a, 2a ≤ N` (对每个 `A > 0` 有常数 `C = C(A)`)。

经典来源: Bombieri–Vinogradov / Pan 均值定理对同余类
`{n ≤ X : d₁ | n, d₂ | N−an}` 的平均 (两个线性形式的分布水平 N^{1/2−ε}),
或等价地维度 2 筛余项 `Σ |R_d|` 的控制。ant 现有材料 (逐参数平凡接口
`bombieri_vinogradov`、开放 Prop `PanMeanValueUniform`/`WeightedPanCondition`)
不含此平均定理; 这是本台阶的关键缺失设备。 -/
def LinearFormPairDistributionCondition : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
    ∀ N a : ℕ, N₀ ≤ N → 1 ≤ a → 2 * a ≤ N →
      (∑ d ∈ Finset.range (Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ)) + 1),
         (2 : ℝ) ^ d.primeFactors.card *
           |(pairLinearFormMultiplesCount N a d : ℝ) -
             (pairLinearFormDensity N a d : ℝ) / (d : ℝ) * ((N : ℝ) / (a : ℝ))|) ≤
        C * (N : ℝ) / (a : ℝ) / (log (N : ℝ)) ^ A

/-- **线性型素数对的维度 2 上界筛** (开放输入):

给定分布条件, 对筛水平 `z = ⌊N^{1/4}⌋`, 筛除集
`#{n ≤ X : (n,P(z)) = (N−an,P(z)) = 1}` (X = N/a) 满足

    sifted ≤ C·(a/φ(a))·X/log²N,   (1 ≤ a, 2a ≤ N)

证明路线: Selberg 上界筛 (ant `selberg_upper_bound_moebius_pan` 于筛积
`P(z)`) 给出 `sifted ≤ X·∏_{p<z}(1−ρ(p)/p) + Σ_d 3^{ω(d)}·|R_d|`;
主项由局部密度台阶 (`LinearFormPairLocalDensityBound`) 界为
`≤ C·(a/φ(a))·X/log²z`, 误差由分布条件
(`LinearFormPairDistributionCondition`, 权重 `2^{ω(d)}`, 水平 `z² ≤ N^{1/2}`)
控制; 常数吸收 `log²z/log²N` 之比与筛除包含步
(`primePairLinearFormCount_le_siftedCount_add_two_z`) 的 `2z` 修正
(该修正 `≤ X/log²N` 由 `X = N/a ≥ N^{3/4}·poly` 保证, 即 `a ≤ N^{1/4}·poly` 区域;
大 `a` 区域需另作处理, 见模块导言)。 -/
def LinearFormPairDimensionTwoSieveBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
    (PrimePairLinearFormSiftedCount N a (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))) : ℝ) ≤
      C * (N : ℝ) / (Nat.totient a : ℝ) / (log (N : ℝ)) ^ 2

/-- **线性型素数对的局部密度界** (开放输入; 可由 ant Mertens 证明):

    ∏_{p < z, p 素数} (1 − ρ(N,a;p)/p) ≤ C·(a/φ(a))/log²z,   (z ≥ 3, a ≥ 1)

其中 ρ(N,a;p) = #{n mod p : n(N−an) ≡ 0} 是同余密度 (p ∤ a 时 = 2, p | a
时 = 1; p | N 情形使乘积变小, 可吸收)。

路线: `1−2/p = (1−1/p)²·(1+1/(p−1)²)` 与 ant 维度 1 Mertens
(`AnalyticNumberTheory.Mertens.primeProduct_mertens_nat`, 乘积
`∏_{p<z}(1−1/p) ≤ C₁/log z`) 给出 `∏_{p<z}(1−2/p) ≤ C₂/log²z`;
`∏_{p|a, p<z}(1−ρ/p)/(1−2/p) = ∏_{p|a}(p−1)/(p−2)` 逐项与
`∏_{p|a}(1+1/(p−1)) = a/φ(a)` 比较 (每项比 `(p−1)/(p−2) : p/(p−1) ≤
1 + 1/(p−2)²`), 收敛乘积 `∏_p(1+1/(p−2)²)` 吸收进常数。 -/
def LinearFormPairLocalDensityBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N a z : ℕ, 1 ≤ a → 3 ≤ z →
    (((Finset.range z).filter (fun p => p.Prime)).prod
      (fun p => (1 : ℝ) - (pairLinearFormDensity N a p : ℝ) / (p : ℝ))) ≤
      C * (a : ℝ) / (Nat.totient a : ℝ) / (log (z : ℝ)) ^ 2

/-- **线性型素数对的 log²N 上界** (解析核心的中间目标):

    count ≤ C·(N/φ(a))/log²N,   (1 ≤ a, 2a ≤ N)

作为 legacy 条件目标，它模拟维度 2 上界筛 + 平均分布 + 局部密度的尺度；
但遗漏 `N`-局部奇异因子，不能直接归因于 Chen 1966 / HR 1974。正确 API
必须先替换后才可启动此路线。
比 `PrimePairLinearFormBound` 更强: `log²N ≥ log N·log(N/a)` 故
`1/log²N ≤ 1/(logN·log(N/a))` (见 `PrimePairLinearFormBound.of_logSquareBound`)。 -/
def PrimePairLinearFormLogSquareBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
    (PrimePairLinearFormCount N a : ℝ) ≤
      C * (N : ℝ) / (Nat.totient a : ℝ) / (log (N : ℝ)) ^ 2

/-- **代数收尾** (零 sorry): log²N 形态的上界蕴含 `PrimePairLinearFormBound`。

`a ≥ 1 ⟹ log(N/a) ≤ log N`, 故 `log N·log(N/a) ≤ log²N`, 于是
`(N/φ(a))/log²N ≤ (N/φ(a))/(logN·log(N/a))` (全正因子)。 -/
theorem PrimePairLinearFormBound.of_logSquareBound (h : PrimePairLinearFormLogSquareBound) :
    PrimePairLinearFormBound := by
  rcases h with ⟨C, hC, hPP⟩
  refine ⟨C, hC, ?_⟩
  intro N a ha h2a
  have hle := hPP N a ha h2a
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hX2 : (2 : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ hapos]
    exact_mod_cast h2a
  have hlogX : 0 < log ((N : ℝ) / (a : ℝ)) := Real.log_pos (by linarith)
  have hlogXle : log ((N : ℝ) / (a : ℝ)) ≤ log (N : ℝ) := by
    apply Real.log_le_log (by positivity : 0 < (N : ℝ) / (a : ℝ))
    rw [div_le_iff₀ (by positivity : 0 < (a : ℝ))]
    nlinarith [show (1 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha]
  have hφpos : 0 < (Nat.totient a : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < a))
  have hC0 : 0 ≤ C := le_of_lt hC
  have hmain : C * (N : ℝ) / (Nat.totient a : ℝ) / (log (N : ℝ)) ^ 2 ≤
      C * (N : ℝ) / (Nat.totient a : ℝ) /
        (log (N : ℝ) * log ((N : ℝ) / (a : ℝ))) := by
    have hpos : 0 < C * (N : ℝ) / (Nat.totient a : ℝ) := by
      exact div_pos (mul_pos hC (by exact_mod_cast (by omega : 0 < N))) hφpos
    have h1 : log (N : ℝ) * log ((N : ℝ) / (a : ℝ)) ≤ (log (N : ℝ)) ^ 2 := by
      rw [pow_two]
      nlinarith [mul_le_mul_of_nonneg_left hlogXle (le_of_lt hlogN)]
    have hdiv : (C * (N : ℝ) / (Nat.totient a : ℝ)) *
          (log (N : ℝ) * log ((N : ℝ) / (a : ℝ))) ≤
        (C * (N : ℝ) / (Nat.totient a : ℝ)) * (log (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hpos)
    rw [div_le_div_iff₀ (sq_pos_of_pos hlogN) (mul_pos hlogN hlogX)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
  exact le_trans hle hmain

/-! ## 5. 组合路线注记 -/

/-- 路线注记 (非定理, 文档):

`LinearFormPairDistributionCondition` + `LinearFormPairDimensionTwoSieveBound`
+ `LinearFormPairLocalDensityBound` + `primePairLinearFormCount_le_siftedCount_add_two_z`
(+ 大 a 区域处理) ⟹ `PrimePairLinearFormLogSquareBound` ⟹
`PrimePairLinearFormBound`。前三个台阶的证明需新建设备 (平均 BV/Pan、维度 2
上界筛、Mertens 局部密度主项), 本次保留为显式 Prop。 -/
lemma linearFormBound_route_doc : True := by trivial

end MathlibNt.SieveTheory.SwitchingPrinciple
