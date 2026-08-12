# 经典陈氏证明 ↔ 本项目接口 映射表

> 目的：让任何读者一眼看清本仓库（及 `analytic-number-theory-lean` 基础层）
> 的每个名字对应经典陈氏证明的哪一步。经典路线：Jurkat--Richert 下界 +
> Selberg 上界 + 切换原理（见 Nathanson GTM 164 Ch.10、Liu 2022、Chen 1973）。
> 状态列：已证 = 内核核验；条件 = 依赖显式命名假设；待证 = 研究级开放输入。

| 经典步骤 | 项目接口 | 位置 | 状态 |
| --- | --- | --- | --- |
| 陈氏定理陈述（充分大偶数 = 素数 + 至多二素因子数） | `chens_theorem` / `corrected_chens_theorem` | `MathlibNt.ChensTheorem` / `SwitchingPrinciple` | 条件（两个显式假设 / 一个正性义务） |
| 切换原理：好表示数 ≥ W − Ω/2 | `ChenCountingBridge`（历史，被有限检验证伪） | `SwitchingPrinciple` | 已证伪，见下 |
| 切换原理的修正版（显式罚函数纤维） | `corrected_counting_bridge_public_of_nine_le` | `SwitchingPrinciple` | 已证 |
| 坏候选罚 ≥ 2（`/2` 的精确依据） | `correctedChenBad_penalty_ge_two` | `SwitchingPrinciple` | 已证 |
| 权重函数 w(n) | `chenWeight` / `chenWeight_eq_one_sub_correctedChenPenalty` | `SwitchingPrinciple` | 已证 |
| W(N) 筛法计数 | `chenW` / `correctedChenCandidates` | `SwitchingPrinciple` | 已定义 |
| Ω(N) 切换和（三因子坏情形） | `chenOmega` / `correctedChenOmega`（显式罚函数） | `SwitchingPrinciple` | 已定义 |
| 筛函数 F(s)/f(s)（JR 定理的基础） | `AnalyticNumberTheory.Sieve` 的 LinearSieve 模块（`sieveFunctionF/f`） | ant `Sieve/LinearSieve.lean` | 接口层（一致版本待证） |
| JR 下界：W ≥ 2.6408·𝔖·N/log²N | 修正候选版：`correctedChenCandidates_card_ge_X_mul_sieveProduct_sub_errSum`（精确主项 `X·V(N)`）+ `correctedChenSieveProduct_eq_singularSeries_mul_primeProduct`（`V = 𝔖_trunc·primeProduct(z−1)`，奇异级数连接） | chen + ant | 组装完成；剩三个标准估计（𝔖 下界、Mertens 下界、log 参数） |
| Selberg 上界：Ω ≤ 3.9404·𝔖·N/log²N | `ChenAnalyticBounds`（一致版本） | chen | 待证（研究级，常数须重导出） |
| Selberg 主项分解：Σ_{d|P} g(d) = ∏(1−ν(p))⁻¹ | `AnalyticNumberTheory.Sieve.selbergSum_eq_prod_inv` | ant `Sieve/SelbergIdentities.lean` | 已证 |
| 素数处 Selberg 项 g(p) = ν(p)(1−ν(p))⁻¹ | `AnalyticNumberTheory.Sieve.selbergTerm_prime` | ant `Sieve/SelbergIdentities.lean` | 已证 |
| Goldbach 密度 ν(d) = ∏1/(p−1) | `AnalyticNumberTheory.Sieve.goldbachNu` | ant `Sieve/GoldbachDensity.lean` | 已证 |
| 密度主项 = li(x)/φ(d)（ν(d)=1/φ(d)） | `AnalyticNumberTheory.Sieve.goldbachNu_squarefree_eq_inv_totient` | ant `Sieve/GoldbachDensity.lean` | 已证 |
| 奇异级数 𝔖(N) 局部因子与截断 | `AnalyticNumberTheory.Sieve` 的 SingularSeries 模块 | ant `Sieve/SingularSeries.lean` | 已证 |
| 主项渐近：SelbergSum = Θ(log z/𝔖(N,z)) | `correctedChenSelbergSum_asymptotic_order` | chen `SwitchingPrinciple` | 已证 |
| 分布条件（Bombieri--Vinogradov / Pan） | `AnalyticNumberTheory.Sieve.WeightedPanCondition`（ant #7 输入）+ `CorrectedChenDistributionCondition` ↔ `ChenWeightedPanInput`（消费桥） | ant + chen | 输入已形式化并消费；定理证明待证（研究级） |
| errSum ≤ Σ 3^{ω(d)}·|Δ(d)|（加权重打包） | `correctedChenErrSum_le_panWeighted` | chen | 已证 |
| errSum = O(N/log^A N)（给定加权 Pan 输入） | `correctedChenErrSum_uniform_of_distribution` / `correctedChenErrSum_uniform_of_weightedPanInput`（直接消费 ant #7） | chen | 已证（条件） |
| 关键不等式 W − Ω/2 > 0 | `chen_key_inequality` / `CorrectedChenAnalyticPositivity` | chen | 条件 |
| 从正计数提取素数 + P₂ 表示 | `corrected_key_inequality_implies_chen_at` | chen | 已证 |
| PNT | `MertensTheorem.prime_number_theorem`（消费 ant） | chen | 已证 |
| Mertens 第二定理 | `MertensTheorem.mertens_second_theorem` | chen | 已证 |
| Mertens 乘积公式（精确 e^{−γ} 常数） | `MertensTheorem.mertens_product_formula` | chen | 已证 |

## 说明

- **切换原理的两种形态**：历史 `ChenCountingBridge` 对应朴素定义的对称性论证，
  有限检验证伪（N=1000 时 `chenW−Ω/2 = 144.5 > good.card = 122`）；修正版用显式
  罚函数（`correctedChenPenalty`）使 `/2` 成为精确纤维下界，并已内核核验。
- **通用层归属**：表中标记为 `ant` 的条目位于 `analytic-number-theory-lean` 的
  `AnalyticNumberTheory/Sieve/`（Goldbach 型筛法可复用）；chen 仓库只保留陈氏专属
  应用与消费接口。
- **研究级开放输入**（"待证"行）：一致 JR 下界、修正 Selberg 上界、加权 Pan/BV
  分布条件的**定理证明**（输入接口本身已由 ant #7 形式化并被 Chen 消费，见
  `correctedChenDistributionCondition_iff_chenWeightedPanInput`）。三者补上后
  `CorrectedChenAnalyticPositivity` 即可闭环。
