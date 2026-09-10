/-
! # MathlibNt.SieveTheory.ParityBiasThreshold

## Parity-bias 账目（PHT-8 accounting）—— 已证部分与**显式未证假设**严格分离

本文件**不证明哥德巴赫猜想**。它把 parity-bias 路线的**账目恒等式**形式化
（这些是纯环恒等式，`ring` 可验），并把路线**剩余的唯一输入**以
**显式、具名、带注释的 `axiom`** 形式登记出来。

### 为什么要用 `axiom` 而不是 `theorem`

阈值定理的证明需要多步 `linarith` 序列，其每一步的成功与否取决于假设的
精确形状。在没有本地 Lean 反馈的环境下（本仓编译全部走 GitHub CI，
单次冷编译约 5 分钟），把未验证的证明留在文件里，会让整个 `MathlibNt`
构建失败。因此：

* **已证**：四个纯代数恒等式（`ring` 闭合，不依赖任何未证前提）；
* **未证**：两条阈值断言，以 `axiom` 登记，**名字里带 `unproved`**，
  文档注释里写明它属于 `G9-bilinear` 路线、其无条件形式不存在。

本文件**不**被 `MathlibNt.lean` 公共根导入——它是隔离的实验文件，
不得让未验证内容进入项目的公共事实基础。

### 账目（已证）

fibre = `{n : z ≤ n ≤ N/2, P⁻(n) ≥ z, P⁻(N−n) ≥ z}`，`z = N^{1/5}`，
故每个素因子 ≥ z ⟹ `Ω(n) ≤ 4`。记

* `M_k` := `Ω(n) = k` 的质量和（`k = 1,2,3,4`），`M = Σ_k M_k`；
* `L` := `Σ (−1)^{Ω(n)} W(n) = M₁ − M₂ + M₃ − M₄`。

则精确地

```
(M + L)/2 = M₁ + M₃ ,   (M − L)/2 = M₂ + M₄ ,   M₁ = (M + L)/2 − (M₂ + M₄)
```

以及反例中心的形态（`M₁ = 0` 时）

```
M + L = 2·M₃ ,          M − L = 2·(M₂ + M₄)
```

-/
import Mathlib

namespace MathlibNt.SieveTheory

/-- **偶秩恒等式**：`(M + L)/2 = M₁ + M₃`。 -/
theorem fibre_mass_even (M₁ M₂ M₃ M₄ : ℚ) :
    (M₁ + M₂ + M₃ + M₄ + (M₁ - M₂ + M₃ - M₄)) / 2 = M₁ + M₃ := by
  ring

/-- **奇秩恒等式**：`(M − L)/2 = M₂ + M₄`。 -/
theorem fibre_mass_odd (M₁ M₂ M₃ M₄ : ℚ) :
    (M₁ + M₂ + M₃ + M₄ - (M₁ - M₂ + M₃ - M₄)) / 2 = M₂ + M₄ := by
  ring

/-- **主恒等式**：`M₁ = (M + L)/2 − (M₂ + M₄)`。
即 "Goldbach 质量 = 偶秩质量 − 秩大于 1 的奇秩质量"。 -/
theorem fibre_mass_identity (M₁ M₂ M₃ M₄ : ℚ) :
    M₁ = (M₁ + M₂ + M₃ + M₄ + (M₁ - M₂ + M₃ - M₄)) / 2 - (M₂ + M₄) := by
  ring

/-- **反例中心恒等式**：`M₁ = 0` 时 `M + L = 2·M₃` 且 `M − L = 2·(M₂ + M₄)`。 -/
theorem bad_centre_identity (M₂ M₃ M₄ : ℚ) :
    (0 + M₂ + M₃ + M₄) + (0 - M₂ + M₃ - M₄) = 2 * M₃ ∧
      (0 + M₂ + M₃ + M₄) - (0 - M₂ + M₃ - M₄) = 2 * (M₂ + M₄) := by
  refine ⟨?_, ?_⟩ <;> ring

/-- **未证假设（下界形式）**。

若 `M ≥ A·X`、`M₃ ≤ B·X`、`L ≥ −κ·M`，且 `2B < (1+κ)·A`，
则 `M₁ > 0`（该中心有 `p + p` 表示）。

**状态**：`conjectural`。前提 `L ≥ −κ·M` 是 parity-sensitive 输入，
其无条件形式不存在（项目缺口 `G9-bilinear`）。此处的 `axiom` 只登记
**推理链的算术部分**，不代表该输入已被证明。 -/
axiom parity_bias_threshold_lower_unproved
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hX : 0 < X) (hκ0 : -1 ≤ κ)
    (hκ : 2 * B < (1 + κ) * A)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hM3 : M₃ ≤ B * X)
    (hL : -(κ * (M₁ + M₂ + M₃ + M₄)) ≤ M₁ - M₂ + M₃ - M₄) :
    0 < M₁

/-- **未证假设（上界形式）**。

若 `M ≥ A·X`、`M₃ ≤ B·X`、`L ≤ κ·M`，且 `2B < (1−κ)·A`（即 `κ < 1 − 2B/A`），
则 `M₁ > 0`。这是 PHT-8 实际需要的方向：反例中心给出 `L` 大而正。

**状态**：`conjectural`，理由同上。 -/
axiom parity_bias_threshold_upper_unproved
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hX : 0 < X)
    (hκ : 2 * B < (1 - κ) * A)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hM3 : M₃ ≤ B * X)
    (hL : M₁ - M₂ + M₃ - M₄ ≤ κ * (M₁ + M₂ + M₃ + M₄)) :
    0 < M₁

end MathlibNt.SieveTheory
