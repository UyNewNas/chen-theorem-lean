import MathlibNt.SieveTheory.TripleMain

/-!
# 素数对线性型输入 (线 PP): ChenPrimePairInput 的解析核心

本文件落地 hTripleMain 的第二个解析输入 `ChenPrimePairInput`
(TripleMain.lean:50) 的完整归约链:

    switchingCount N a = #{p ∈ C(N) : ∃ p₃ 素数, a·p₃ = N−p}
        = #{p₃ ≤ N/a : p₃ 素数, p = N − a·p₃ ∈ C(N)}      (双射, 结构引理)
        ≤ #{p₃ ≤ N/a : p₃ 素数, N − a·p₃ 素数}           (小素因子筛除步骤)
        ≤ C · (N/φ(a)) · 1/(log N · log(N/a))            (解析台阶, Prop)

其中第一、二行 (结构部分) 全部零 sorry 证明: `p ↦ (N−p)/a` 是切换集合与
"线性型素数对" p₃ 集合之间的双射, 且 C(N) 的 < z 小素因子筛除条件在
上界方向上自动放宽为 N−ap₃ 素性。

第三行 `PrimePairLinearFormBound` 是**legacy provisional Prop**，不是当前可
直接归因于经典二线性型筛的接口：

    #{p₃ ≤ X : p₃ 素数, N − a·p₃ 素数} ≤ C · (a/φ(a)) · X/(log X · log N),  X = N/a,

该右端遗漏随 `N` 变化的 Goldbach 局部因子
`∏_{ell | N, ell>2}(ell-1)/(ell-2)`，故只能作为旧消费者的显式假设，
不得称为标准 Chen/Selberg 素数对供给。正确替代必须携带完整
`primePairNu(N,a,ell)` 局部密度、原始/固定因子分裂和实际 `a` 支撑；书面
规格见 `CHEN_VARIABLE_A_LOCAL_DENSITY_AUDIT.md`。本文件给出 legacy Prop
与目标之间的零 sorry 条件归约: `ChenPrimePairInput.of_linearFormBound`。
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset

open scoped Classical

/-- **线性型素数对计数**: #{p₃ ≤ N/a : p₃ 素数, N − a·p₃ 素数}.

Chen 方法的目标形态: 对 X = N/a, 统计 p₃ ≤ X 使 p₃ 与 N − a·p₃ 均为素数
(线性型素数对)。`switchingCount N a` 的 p₃ 侧重参数化就是它的子集
(见 `switchingCount_le_primePairLinearFormCount`)。 -/
def PrimePairLinearFormCount (N a : ℕ) : ℕ :=
  ((Finset.range (N / a + 1)).filter (fun p₃ => p₃.Prime ∧ (N - a * p₃).Prime)).card

/-- **switchingCount 的 p₃ 重参数化 (精确等式, 零 sorry)**:

`p ↦ (N−p)/a` 把切换集合 {p ∈ C(N) : a·p₃ = N−p, p₃ 素数} 双射到
{p₃ ≤ N/a : p₃ 素数, p = N − a·p₃ ∈ C(N)}。这是线 PP 的结构基础:
switchingCount 统计的正是"线性型素数对" (p₃ 素数, p = N−a·p₃ 为 C(N) 候选),
且映射在有效区域上无损 (p₃ ≤ N/a 即 a·p₃ ≤ N, 反向由 p 的 C(N) 成员性保证)。 -/
theorem switchingCount_eq_primePairCandidatesCount (N a : ℕ) (ha : 1 ≤ a) :
    switchingCount N a =
      ((Finset.range (N / a + 1)).filter
        (fun p₃ => p₃.Prime ∧ N - a * p₃ ∈ correctedChenCandidates N)).card := by
  unfold switchingCount
  let s : Finset ℕ := (correctedChenCandidates N).filter
    (fun p => ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p)
  let t : Finset ℕ := (Finset.range (N / a + 1)).filter
    (fun p₃ => p₃.Prime ∧ N - a * p₃ ∈ correctedChenCandidates N)
  let f : ℕ → ℕ := fun p => (N - p) / a
  have ha' : 0 < a := by omega
  have hinj : Set.InjOn f (↑s : Set ℕ) := by
    intro p hp q hq hpq
    have hpw : ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p := (Finset.mem_filter.mp hp).2
    have hqw : ∃ q₃ : ℕ, q₃.Prime ∧ a * q₃ = N - q := (Finset.mem_filter.mp hq).2
    rcases hpw with ⟨p₃, hp₃p, hp₃eq⟩
    rcases hqw with ⟨q₃, hq₃p, hq₃eq⟩
    have hfp : (N - p) / a = p₃ := by
      rw [← hp₃eq]
      exact Nat.mul_div_right p₃ ha'
    have hfq : (N - q) / a = q₃ := by
      rw [← hq₃eq]
      exact Nat.mul_div_right q₃ ha'
    change (N - p) / a = (N - q) / a at hpq
    have hp₃eqq₃ : p₃ = q₃ := by
      rw [hfp, hfq] at hpq
      exact hpq
    have hpN : p < N := by
      have hpC := (Finset.mem_filter.mp hp).1
      simpa using (Finset.mem_filter.mp hpC).1
    have hqN : q < N := by
      have hqC := (Finset.mem_filter.mp hq).1
      simpa using (Finset.mem_filter.mp hqC).1
    calc
      p = N - a * p₃ := by
            rw [hp₃eq]
            omega
      _ = N - a * q₃ := by rw [hp₃eqq₃]
      _ = q := by
            rw [hq₃eq]
            omega
  have himg : s.image f = t := by
    apply Finset.Subset.antisymm
    · intro q hq
      rw [Finset.mem_image] at hq
      rcases hq with ⟨p, hp, rfl⟩
      have hpw : ∃ p₃ : ℕ, p₃.Prime ∧ a * p₃ = N - p := (Finset.mem_filter.mp hp).2
      rcases hpw with ⟨p₃, hp₃p, hp₃eq⟩
      have hqeq : (N - p) / a = p₃ := by
        rw [← hp₃eq]
        exact Nat.mul_div_right p₃ ha'
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        change (N - p) / a < N / a + 1
        rw [hqeq]
        have hp3le : p₃ ≤ N / a := by
          calc
            p₃ = (N - p) / a := hqeq.symm
            _ ≤ N / a := Nat.div_le_div_right (Nat.sub_le N p)
        omega
      · constructor
        · change Nat.Prime ((N - p) / a)
          rwa [hqeq]
        · change N - a * ((N - p) / a) ∈ correctedChenCandidates N
          rw [hqeq]
          have hpN : p < N := by
            have hpC := (Finset.mem_filter.mp hp).1
            simpa using (Finset.mem_filter.mp hpC).1
          have hp3eq' : N - a * p₃ = p := by
            rw [hp₃eq, Nat.sub_sub_self (le_of_lt hpN)]
          rw [hp3eq']
          exact (Finset.mem_filter.mp hp).1
    · intro q hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hqr, hqw⟩
      rcases hqw with ⟨hqp, hqC⟩
      let p : ℕ := N - a * q
      have hqNdiv : q ≤ N / a := by
        rw [Finset.mem_range] at hqr
        omega
      have hqleN : a * q ≤ N := by
        calc
          a * q ≤ a * (N / a) := Nat.mul_le_mul_left a hqNdiv
          _ ≤ N := Nat.mul_div_le N a
      have hqeq' : N - p = a * q := by
        dsimp [p]
        rw [Nat.sub_sub_self hqleN]
      have hp_s : p ∈ s := by
        rw [Finset.mem_filter]
        constructor
        · exact hqC
        · refine ⟨q, hqp, ?_⟩
          exact hqeq'.symm
      have hfp : f p = q := by
        dsimp [f, p]
        rw [Nat.sub_sub_self hqleN]
        exact Nat.mul_div_right q ha'
      rw [Finset.mem_image]
      exact ⟨p, hp_s, hfp⟩
  have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn hinj
  have hcard2 : s.card = t.card := by
    calc
      s.card = (s.image f).card := by rw [hcard]
      _ = t.card := by rw [himg]
  simpa [s, t, f] using hcard2

/-- **小素因子筛除步骤 (零 sorry)**: `switchingCount N a ≤ #{p₃ ≤ N/a : p₃ 素数, N−ap₃ 素数}`.

C(N) 的定义筛掉了 N−p 的 < z 素因子; 对**上界**只需观察 p = N−ap₃ ∈ C(N)
蕴含 p 素数, 故切换计数 ⊆ 素数对计数 (去掉小素因子条件只会使计数变大)。
与 `switchingCount_le_pi` 不同, 此处保留 N−ap₃ 侧的素性, 正是
ChenPrimePairInput 的解析形态 (两个 1/log 因子)。 -/
theorem switchingCount_le_primePairLinearFormCount (N a : ℕ) (ha : 1 ≤ a) :
    switchingCount N a ≤ (PrimePairLinearFormCount N a : ℝ) := by
  have hEq := switchingCount_eq_primePairCandidatesCount N a ha
  have hsub : ((Finset.range (N / a + 1)).filter
      (fun p₃ => p₃.Prime ∧ N - a * p₃ ∈ correctedChenCandidates N)) ⊆
      ((Finset.range (N / a + 1)).filter
        (fun p₃ => p₃.Prime ∧ (N - a * p₃).Prime)) := by
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    rcases hq with ⟨hqr, hqp, hqC⟩
    refine ⟨hqr, hqp, ?_⟩
    exact (Finset.mem_filter.mp hqC).2.1
  have hcard : ((Finset.range (N / a + 1)).filter
      (fun p₃ => p₃.Prime ∧ N - a * p₃ ∈ correctedChenCandidates N)).card ≤
      PrimePairLinearFormCount N a := by
    unfold PrimePairLinearFormCount
    exact Finset.card_le_card hsub
  rw [hEq]
  exact_mod_cast hcard

/-- **素数对计数的 π 上界**: #{p₃ ≤ N/a : p₃ 素数, N−ap₃ 素数} ≤ #{p₃ ≤ N/a : p₃ 素数}.

`switchingCount_le_pi` 的 p₃ 侧对应; 单独只能给出 Θ(N/log N) 尺度
(缺 N−ap₃ 素性带来的 1/log N 因子), 无法达到 hTripleMain 的 N/log²N。 -/
theorem primePairLinearFormCount_le_pi (N a : ℕ) :
    PrimePairLinearFormCount N a ≤
      ((Finset.range (N / a + 1)).filter Nat.Prime).card := by
  unfold PrimePairLinearFormCount
  exact Finset.card_le_card (by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩)

/-- **legacy 线性型素数对上界（显式假设，非 source-valid Chen API）**:

这个裸 `a/φ(a)` 形态遗漏了 `N`-局部奇异因子；它只保留给已经引用它的
条件性归约，不宣称为经典估计：

    #{p₃ ≤ X : p₃ 素数, N − a·p₃ 素数} ≤ C · (a/φ(a)) · X / (log X · log N),  X = N/a,

即 `PrimePairLinearFormCount N a ≤ C·(N/φ(a))·1/(log N·log(N/a))` (1 ≤ a, 2a ≤ N)。
量词顺序仍是常数 C 先于 ∀ N a；任何把 C 放进 N 之后的版本不构成一致输入。
正确的支持型 API 见书面审计。 -/
def PrimePairLinearFormBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N a : ℕ, 1 ≤ a → 2 * a ≤ N →
    (PrimePairLinearFormCount N a : ℝ) ≤
      C * (N : ℝ) / (Nat.totient a : ℝ) /
        (log (N : ℝ) * log ((N : ℝ) / (a : ℝ)))

/-- **ChenPrimePairInput 由线性型素数对一致上界推出 (零 sorry)**:

    ChenPrimePairInput ⟸ PrimePairLinearFormBound + switchingCount_le_primePairLinearFormCount

即目标陈述正是"素数对一致上界在切换计数上的实例"; 小素因子筛除
(C(N) 条件) 已由结构归约吸收。 -/
theorem ChenPrimePairInput.of_linearFormBound (h : PrimePairLinearFormBound) :
    ChenPrimePairInput := by
  rcases h with ⟨C, hC, hPP⟩
  refine ⟨C, hC, ?_⟩
  intro N a ha h2a
  exact le_trans (switchingCount_le_primePairLinearFormCount N a ha) (hPP N a ha h2a)

end MathlibNt.SieveTheory.SwitchingPrinciple
