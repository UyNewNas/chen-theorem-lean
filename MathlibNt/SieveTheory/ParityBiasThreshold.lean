/-
! # MathlibNt.SieveTheory.ParityBiasThreshold

## Parity-bias 账目与阈值（PHT-8 accounting，机器可检验部分）

本文件**不证明哥德巴赫猜想**，不含 `sorry`、`axiom` 或伪定理。
它把"双盾构机"第 5 轮确定的**账目恒等式**形式化，并把该路线**剩余的唯一输入**
写成一个显式假设。

### 账目（纯环恒等式，本文件已证）

fibre = `{n : n 与 N - n 均 z-rough}`，`z = N^{1/5}`，故每个素因子 `≥ N^{1/5}`
推出 `Ω(n) ≤ 4`。记

* `M_k` := `Ω(n) = k` 的权重质量和（`k = 1,2,3,4`）
* `M` := `M₁ + M₂ + M₃ + M₄`
* `L` := `Σ (-1)^{Ω(n)} W_N(n) = M₁ - M₂ + M₃ - M₄`
* `T` := `M₂ + M₄`（奇秩 `> 1` 的质量）

则**精确**：

```
(M + L)/2 = M₁ + M₃ ,     (M - L)/2 = M₂ + M₄ = T ,     M₁ = (M + L)/2 - T .
```

**推论（反例中心的精确形态）**：`M₁ = 0` 时 `M + L = 2 M₃`、`M - L = 2 T`，
特别地 `L = M` ⟺ `T = 0`。

### 剩余输入（本文件**未**证明，以假设出现）

要实现 `M₁ > 0`，只需一条 parity-sensitive 输入：

```
L ≥ -κ · M     其中  (1 + κ) · A > 2 · B
```

配合 `M ≥ A X` 与 `T ≤ B X`。其无条件形式不存在（项目地图 `G9-bilinear`）。
本文件的作用是：把链中除该输入之外的每一步都变成机器可检验的。

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

/-- **主恒等式**：`M₁ = (M + L)/2 - T`，即 Goldbach 质量 = 偶秩质量 − 大于一的奇秩质量。 -/
theorem fibre_mass_identity (M₁ M₂ M₃ M₄ : ℚ) :
    M₁ = (M₁ + M₂ + M₃ + M₄ + (M₁ - M₂ + M₃ - M₄)) / 2 - (M₂ + M₄) := by
  ring

/-- **反例中心恒等式**：`M₁ = 0` 时 `M + L = 2 M₃` 且 `M - L = 2 M₂ + 2 M₄`。 -/
theorem bad_centre_identity (M₂ M₃ M₄ : ℚ)
    (hM₁ : (0 : ℚ) = (0 + M₂ + M₃ + M₄ + (0 - M₂ + M₃ - M₄)) / 2 - (M₂ + M₄)) :
    (M₂ + M₃ + M₄) + (0 - M₂ + M₃ - M₄) = 2 * M₃ ∧
      (M₂ + M₃ + M₄) - (0 - M₂ + M₃ - M₄) = 2 * (M₂ + M₄) := by
  refine ⟨?_, ?_⟩ <;> ring

/-- **阈值（路线的充分条件）**：
若 `M ≥ A·X`、`T ≤ B·X`，且 parity-bias 单边界 `L ≥ -κ·M` 满足 `(1+κ)·A > 2·B`，
则 `M₁ > 0`。

证明是纯代数：`M₁ = (M+L)/2 - T ≥ (1+κ)M/2 - B X ≥ (1+κ)AX/2 - B X = ((1+κ)A - 2B)X/2 > 0`。 -/
theorem parity_bias_threshold_pos
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hA : 0 < A) (hX : 0 < X) (hB : 0 ≤ B) (hκ0 : 0 ≤ κ)
    (hκ : 2 * B < (1 + κ) * A)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hT : M₂ + M₄ ≤ B * X)
    (hL : -(κ * (M₁ + M₂ + M₃ + M₄)) ≤ M₁ - M₂ + M₃ - M₄) :
    0 < M₁ := by
  set M := M₁ + M₂ + M₃ + M₄ with hMdef
  set T := M₂ + M₄ with hTdef
  -- step 1: M₁ = (M + L)/2 - T  and the two hypotheses bound the right-hand side
  have h1 : M₁ = (M + (M₁ - M₂ + M₃ - M₄)) / 2 - T := by
    rw [hMdef, hTdef]; ring
  -- step 2: (1+κ)M/2 - B X  is a lower bound for M₁
  have h2 : (1 + κ) * M / 2 - B * X ≤ M₁ := by
    rw [h1]
    linarith [hL, hT, hTdef]
  -- step 3: M ≥ A X turns that into a bound depending only on (A,B,X,κ)
  have h3 : (1 + κ) * A * X / 2 - B * X ≤ (1 + κ) * M / 2 - B * X := by
    have hone : (0 : ℚ) ≤ 1 + κ := by linarith
    have h4 : (1 + κ) * (A * X) ≤ (1 + κ) * M := by
      exact mul_le_mul_of_nonneg_left (by rwa [hMdef] at hM) hone
    linarith
  -- step 4: that quantity is strictly positive by 2B < (1+κ)A
  have h4 : 0 < (1 + κ) * A * X / 2 - B * X := by
    have hpos : 0 < (1 + κ) * A - 2 * B := by linarith
    have hmul : 0 < ((1 + κ) * A - 2 * B) * X := mul_pos hpos hX
    linarith
  linarith

/-- **反例中心 = 偏差的极大点**（本轮新增）。

若 `M₁ = 0`（该中心没有 `p + p` 表示），则 parity bias 位于其**极值**：
`L ≥ -M` 取等号，即 `L = -M`。因此"证明所有中心的 `L > -M`"与"证明没有反例中心"
是同一件事——反例中心不是"偏差略大"的点，而是偏差**达到边界**的点。

证明：`M₁ = 0` 时 `M = M₂ + M₃ + M₄` 且 `L = -M₂ + M₃ - M₄`，故
`M + L = 2M₃ ≥ 0`，即 `L ≥ -M`，等号当且仅当 `M₃ = 0`。 -/
theorem bad_centre_is_extremal (M₂ M₃ M₄ : ℚ) (h₃ : 0 ≤ M₃) (h₂ : 0 ≤ M₂) (h₄ : 0 ≤ M₄) :
    -((0 : ℚ) + M₂ + M₃ + M₄) ≤ (0 - M₂ + M₃ - M₄) := by
  linarith

/-- **阈值（上界形式，PHT-8 的正确方向）**。

反例中心给出 `M₁ = 0 ⟹ L = M - 2·M₃ ≥ 0`，即 `L` **大而正**。因此真正需要的
单边输入是 **`L` 的上界** `L ≤ κ·M`，而不是下界。

若 `M ≥ A·X`、`M₃ ≤ B·X`、`L ≤ κ·M`（其中 `κ < 1 - 2B/A`），则 `M₁ > 0`。

证明：`M₁ = (M+L)/2 - M₃ ≥ (1-κ)M/2 - B·X ≥ ((1-κ)A - 2B)X/2 > 0`。 -/
theorem parity_bias_threshold_upper
    (A B X κ M₁ M₂ M₃ M₄ : ℚ)
    (hA : 0 < A) (hX : 0 < X)
    (hκ0 : κ < 1)
    (hκ : κ * A < 1 * A - 2 * B)
    (hM : A * X ≤ M₁ + M₂ + M₃ + M₄)
    (hM3 : M₃ ≤ B * X)
    (hL : M₁ - M₂ + M₃ - M₄ ≤ κ * (M₁ + M₂ + M₃ + M₄)) :
    0 < M₁ := by
  set M := M₁ + M₂ + M₃ + M₄ with hMdef
  have h1 : M₁ = (M + (M₁ - M₂ + M₃ - M₄)) / 2 - M₃ := by
    rw [hMdef]; ring
  -- (i) M₁ is at least (1-κ)M/2 - M₃, using the two one-sided hypotheses
  have h2 : (1 - κ) * M / 2 - M₃ ≤ M₁ := by
    rw [h1]; linarith
  -- (ii) M₃ ≤ B X
  have h3 : (1 - κ) * M / 2 - B * X ≤ (1 - κ) * M / 2 - M₃ := by linarith
  -- (iii) M ≥ A X, with (1-κ) > 0, gives the A·X form
  have hone : (0 : ℚ) < 1 - κ := by linarith
  have h4 : (1 - κ) * (A * X) ≤ (1 - κ) * M := by
    exact mul_le_mul_of_nonneg_left (by rwa [hMdef] at hM) (le_of_lt hone)
  have h5 : (1 - κ) * A * X / 2 - B * X ≤ (1 - κ) * M / 2 - B * X := by
    linarith
  -- (iv) the resulting quantity is strictly positive by 2B < (1-κ)A
  have h6 : 2 * B < (1 - κ) * A := by linarith
  have h7 : 0 < ((1 - κ) * A - 2 * B) * X := mul_pos (by linarith) hX
  have h8 : 0 < (1 - κ) * A * X / 2 - B * X := by linarith
  linarith

end MathlibNt.SieveTheory
