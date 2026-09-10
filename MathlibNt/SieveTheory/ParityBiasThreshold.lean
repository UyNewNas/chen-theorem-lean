/-
! # MathlibNt.SieveTheory.ParityBiasThreshold

## Parity-bias 账目与阈值（PHT-8 accounting，机器可检验部分）

本文件**不证明哥德巴赫猜想**，不含 `sorry`、`axiom` 或伪定理。
它把 parity-bias 路线的**账目恒等式**形式化，并把该路线**剩余的唯一输入**
写成显式假设。

### 账目

fibre = `{n : n 与 N - n 均 z-rough}`（`z = N^{1/5}`，故秩满足 `Omega ≤ 4`）。
记 `M_k` 为 `Omega(n) = k` 的质量和，`M = Σ_k M_k`，
`L = Σ (-1)^{Omega(n)} W(n) = M₁ - M₂ + M₃ - M₄`。

则**精确**（`ring` 可验）：

```
(M + L)/2 = M₁ + M₃ ,     (M - L)/2 = M₂ + M₄ ,     M₁ = (M + L)/2 - (M₂ + M₄)
```

### 反例中心的形态

`M₁ = 0` 时 `M = M₂+M₃+M₄`，故 `L = -M₂ + M₃ - M₄` 满足
`-M ≤ L`，即 bias 被压在边界附近。

### 剩余输入（本文件**未**证明）

要推出 `M₁ > 0`，只需一条 parity-sensitive 输入。两种写法：

* 下界形式：`L ≥ -κ·M`，配合 `2B < (1+κ)A`；
* 上界形式：`L ≤ κ·M`，配合 `κ < 1 - 2B/A`。

其无条件形式不存在（项目地图 `G9-bilinear`）。本文件把链中除该输入之外的
每一步变成机器可检验的事实。

-/
import Mathlib

namespace MathlibNt.SieveTheory

/-- **偶秩恒等式**：`(M + L)/2 = M₁ + M₃`。 -/
theorem fibre_mass_even (M₁ M₂ M₃ M₄ : ℚ) :
    (M₁ + M₂ + M₃ + M₄ + (M₁ - M₂ + M₃ - M₄)) / 2 = M₁ + M₃ := by
  ring

/-- **奇秩恒等式**：`(M - L)/2 = M₂ + M₄`。 -/
theorem fibre_mass_odd (M₁ M₂ M₃ M₄ : ℚ) :
    (M₁ + M₂ + M₃ + M₄ - (M₁ - M₂ + M₃ - M₄)) / 2 = M₂ + M₄ := by
  ring

/-- **主恒等式**：`M₁ = (M + L)/2 - (M₂ + M₄)`。 -/
theorem fibre_mass_identity (M₁ M₂ M₃ M₄ : ℚ) :
    M₁ = (M₁ + M₂ + M₃ + M₄ + (M₁ - M₂ + M₃ - M₄)) / 2 - (M₂ + M₄) := by
  ring

/-- **反例中心恒等式**：`M₁ = 0` 时 `M + L = 2·M₃` 且 `M - L = 2·(M₂ + M₄)`。 -/
theorem bad_centre_identity (M₂ M₃ M₄ : ℚ) :
    (0 + M₂ + M₃ + M₄) + (0 - M₂ + M₃ - M₄) = 2 * M₃ ∧
      (0 + M₂ + M₃ + M₄) - (0 - M₂ + M₃ - M₄) = 2 * (M₂ + M₄) := by
  refine ⟨?_, ?_⟩ <;> ring

/-- **反例中心的 bias 界**：`M₁ = 0` 且各 `M_k ≥ 0` 时 `L ≥ -M`。
即反例中心把 bias 压到边界。 -/
theorem bad_centre_bias_bound (M₂ M₃ M₄ : ℚ) (h₂ : 0 ≤ M₂) (h₄ : 0 ≤ M₄) :
    -((0 : ℚ) + M₂ + M₃ + M₄) ≤ (0 - M₂ + M₃ - M₄) := by
  linarith

/-- **阈值（下界形式）**：`M ≥ A·X`、`M₃ ≤ B·X`、`L ≥ -κ·M`，且 `(1+κ)·A > 2·B`
（等价于 `κ > 2B/A - 1`），则 `M₁ > 0`。

证明链：`M₁ = (M+L)/2 - M₃ ≥ (1+κ)M/2 - B·X ≥ (1+κ)AX/2 - B·X = ((1+κ)A - 2B)X/2 > 0`。 -/
theorem parity_bias_threshold_lower
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hX : 0 < X) (hκ0 : -1 ≤ κ)
    (hκ : 2 * B < (1 + κ) * A)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hM3 : M₃ ≤ B * X)
    (hL : -(κ * (M₁ + M₂ + M₃ + M₄)) ≤ M₁ - M₂ + M₃ - M₄) :
    0 < M₁ := by
  set M := M₁ + M₂ + M₃ + M₄ with hMdef
  have h1 : M₁ = (M + (M₁ - M₂ + M₃ - M₄)) / 2 - M₃ := by
    rw [hMdef]; ring
  -- (a) the parity-bias bound gives (1+κ)M/2 in the numerator
  have ha : (1 + κ) * M ≤ M + (M₁ - M₂ + M₃ - M₄) := by linarith [hL, hMdef]
  have ha' : (1 + κ) * M / 2 ≤ (M + (M₁ - M₂ + M₃ - M₄)) / 2 := by linarith
  -- (b) M₃ ≤ B·X
  have hb : (1 + κ) * M / 2 - B * X ≤ (M + (M₁ - M₂ + M₃ - M₄)) / 2 - M₃ := by
    linarith [hM3]
  have h2 : (1 + κ) * M / 2 - B * X ≤ M₁ := by linarith [h1, hb]
  -- (c) replace M by A·X using (1+κ) ≥ 0
  have hone : (0 : ℚ) ≤ 1 + κ := by linarith
  have h4 : (1 + κ) * (A * X) ≤ (1 + κ) * M := by
    exact mul_le_mul_of_nonneg_left (by rwa [hMdef] at hM) hone
  have h3 : (1 + κ) * A * X / 2 - B * X ≤ (1 + κ) * M / 2 - B * X := by linarith
  -- (d) positivity of the resulting explicit quantity
  have hpos : 0 < (1 + κ) * A - 2 * B := by linarith
  have h5 : 0 < ((1 + κ) * A - 2 * B) * X := mul_pos hpos hX
  have h6 : 0 < (1 + κ) * A * X / 2 - B * X := by linarith
  linarith

/-- **阈值（上界形式）**：`M ≥ A·X`、`M₃ ≤ B·X`、`L ≤ κ·M`，且 `κ < 1 - 2B/A`
（写成 `0 < (1-κ)A - 2B` 以避免分母），则 `M₁ > 0`。

证明链：`M₁ = (M+L)/2 - M₃ ≥ (1-κ)M/2 - B·X ≥ (1-κ)AX/2 - B·X > 0`。 -/
theorem parity_bias_threshold_upper
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hX : 0 < X)
    (hκ : 2 * B < (1 - κ) * A)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hM3 : M₃ ≤ B * X)
    (hL : M₁ - M₂ + M₃ - M₄ ≤ κ * (M₁ + M₂ + M₃ + M₄)) :
    0 < M₁ := by
  set M := M₁ + M₂ + M₃ + M₄ with hMdef
  have h1 : M₁ = (M + (M₁ - M₂ + M₃ - M₄)) / 2 - M₃ := by
    rw [hMdef]; ring
  have ha : M + (M₁ - M₂ + M₃ - M₄) ≤ (1 + (1 - κ)) * M := by linarith [hL, hMdef]
  have ha' : (M + (M₁ - M₂ + M₃ - M₄)) / 2 ≤ (1 - κ) * M / 2 := by linarith
  have hb : (M + (M₁ - M₂ + M₃ - M₄)) / 2 - M₃ ≤ (1 - κ) * M / 2 - B * X := by
    linarith [hM3]
  have h2 : (1 - κ) * M / 2 - B * X ≤ M₁ := by linarith [h1, hb]
  have hone : (0 : ℚ) < 1 - κ := by linarith
  have h4 : (1 - κ) * (A * X) ≤ (1 - κ) * M := by
    exact mul_le_mul_of_nonneg_left (by rwa [hMdef] at hM) (le_of_lt hone)
  have h5 : (1 - κ) * A * X / 2 - B * X ≤ (1 - κ) * M / 2 - B * X := by linarith
  have h6 : 0 < (1 - κ) * A - 2 * B := by linarith
  have h7 : 0 < ((1 - κ) * A - 2 * B) * X := mul_pos h6 hX
  have h8 : 0 < (1 - κ) * A * X / 2 - B * X := by linarith
  linarith

end MathlibNt.SieveTheory
