/-
D17 — 增长比 `growthRatio`
==========================

冻结接口（D18 直接消费）：

* `growthRatio A values = tracePeak values / matrixEntryMax A`（全定义，分母不做前提）
* `GrowthValues = {g | ∃ A values, A ≠ 0 ∧ LegalTrace A values ∧ g = growthRatio A values}`

本文件建立卡目标 2 与非零标量不变性（含负标量）：

* 合法非零矩阵的轨迹增长比 ≥ 1（`one_le_growthRatio`，用 D13 的
  `head_eq_matrixEntryMax`：头部就是原矩阵最大条目，而峰值 ≥ 头部）；
* 峰值上界 `tracePeak ≤ B` 时 `growthRatio ≤ B / matrixEntryMax A`
  （`growthRatio_le_of_tracePeak_le`，把 D18 的粗界/证书接口接到比值上）；
* 非零标量 `c` 下 `growthRatio (c • A) (values.map (fun v => |c| * v)) = growthRatio A values`
  （`growthRatio_smul`，含 `c < 0`；`c > 0` 的显式形式 `growthRatio_pos_smul`）。

总除法可定义，但每条数学陈述都保留 `A ≠ 0` 与 `LegalTrace A values`（必要时还有
`matrixEntryMax A ≠ 0`）作为显式前提；本文件不隐藏任何可除性假设。

复用（只读冻结输入）：`Rho5.matrixEntryMax`、D08 `MatrixNormalization`
（`matrixEntryMax_smul`、`matrixEntryMax_pos`、`matrixEntryMax_nonneg`）、
D13 `CompletePivotPath`（`LegalTrace`、`head_eq_matrixEntryMax`、`length_le_five`）。
本文件**不**定义 `Matrix5` 上的新范数、不重复路径存在性、不断言集合非空/有界。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.GrowthModel.TracePeak
import Rho5.Shared.CompletePivotPath
import Mathlib.Tactic.Linarith

namespace Rho5.GrowthModel

open Rho5

/-! ## 冻结定义 -/

/-- **冻结定义（D17 卡）**：轨迹 `values` 相对矩阵 `A` 的**增长比**，即全阶段峰值
除以矩阵元素最大范数。

分母用冻结的 `Rho5.matrixEntryMax`（25 个元素绝对值的最大者），不是算子范数；
除法是实数全除法，因此表达式对 `A = 0` 也有定义——所有数学使用都另带
`A ≠ 0`（以及 `LegalTrace A values`）作为显式前提，见 `one_le_growthRatio`、
`growthRatio_smul`、`growthValues_eq_normalized`。 -/
noncomputable def growthRatio (A : Matrix5) (values : List ℝ) : ℝ :=
  tracePeak values / matrixEntryMax A

/-- 展开式：增长比就是“峰值 / 元素最大范数”。 -/
theorem growthRatio_eq (A : Matrix5) (values : List ℝ) :
    growthRatio A values = tracePeak values / matrixEntryMax A := rfl

/-! ## 卡目标 2：合法非零矩阵的轨迹增长比 ≥ 1 -/

/-- **卡目标 2（增长比 ≥ 1）**：非零 `Matrix5` 的任意合法轨迹，其增长比 ≥ 1。

证明只用两件冻结事实：D13 说非零矩阵轨迹的头部恰好等于 `Rho5.matrixEntryMax A`
（`head_eq_matrixEntryMax`），而峰值 ≥ 头部（`le_tracePeak`）；分母为正
（`matrixEntryMax_pos`）。 -/
theorem one_le_growthRatio {A : Matrix5} (hA : A ≠ 0) {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) : 1 ≤ growthRatio A values := by
  have hne : values ≠ [] := Rho5.CompletePivotPath.ne_nil_of_pos h
  obtain ⟨v, vs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hhead : v = matrixEntryMax A := Rho5.CompletePivotPath.head_eq_matrixEntryMax hA h
  have hpos : 0 < matrixEntryMax A := Rho5.MatrixNormalization.matrixEntryMax_pos A hA
  have hpeak : matrixEntryMax A ≤ tracePeak (v :: vs) := by
    rw [hhead]
    exact le_tracePeak List.mem_cons_self
  rw [growthRatio_eq]
  have h1 : (1 : ℝ) ≤ tracePeak (v :: vs) / matrixEntryMax A := by
    rw [one_le_div hpos]
    exact hpeak
  linarith [h1]

/-! ## 峰值上界与比值上界（D18 证书接口） -/

/-- 合法轨迹的长度不超过矩阵阶数 `5`（D13 的 `length_le_five` 直接复用）。 -/
theorem length_le_five {A : Matrix5} {values : List ℝ}
    (h : Rho5.CompletePivotPath.LegalTrace A values) : values.length ≤ 5 :=
  Rho5.CompletePivotPath.length_le_five h

/-- **卡目标 2/4 的比值接口**：若某条合法轨迹的峰值 ≤ `B`，则该轨迹的增长比
≤ `B / matrixEntryMax A`。分母非负，且非零分母作为显式前提（通常由 `A ≠ 0` 派生），
不做隐式假设。 -/
theorem growthRatio_le_of_tracePeak_le {A : Matrix5} {values : List ℝ} {B : ℝ}
    (hm : matrixEntryMax A ≠ 0) (h : tracePeak values ≤ B) :
    growthRatio A values ≤ B / matrixEntryMax A :=
  div_le_div_of_nonneg_right h
    (le_of_lt (lt_of_le_of_ne (Rho5.MatrixNormalization.matrixEntryMax_nonneg A)
      (Ne.symm hm)))

/-! ## 非零标量不变性（含负标量） -/

/-- **卡目标 2（`|c|` 齐次性）**：非零标量 `c` 下，整条轨迹按 D13 的规矩缩放
（每项乘 `|c|`），峰值也乘以 `|c|`。这里 `|c| ≥ 0`，直接实例化
`tracePeak_map_mul`。 -/
theorem tracePeak_map_abs_mul (c : ℝ) (values : List ℝ) :
    tracePeak (values.map (fun v => |c| * v)) = |c| * tracePeak values :=
  tracePeak_map_mul (abs_nonneg c) values

/-- **卡目标 2（关键：非零标量不改变增长比，含负 `c`）**：把矩阵与**整条轨迹**
同时按 `c` 缩放，增长比不变。

两个因子都取绝对值：`tracePeak (map (· * |c|)) = |c| * tracePeak`、
`matrixEntryMax (c • A) = |c| * matrixEntryMax A`，`|c| ≠ 0` 时约去。`c < 0` 无需
单独处理，`c > 0` 的显式形式见 `growthRatio_pos_smul`。 -/
theorem growthRatio_smul (A : Matrix5) {c : ℝ} (hc : c ≠ 0) (values : List ℝ) :
    growthRatio (c • A) (values.map (fun v => |c| * v)) = growthRatio A values := by
  rw [growthRatio_eq, growthRatio_eq, tracePeak_map_abs_mul,
    Rho5.MatrixNormalization.matrixEntryMax_smul]
  exact mul_div_mul_left (tracePeak values) (matrixEntryMax A) (abs_ne_zero.mpr hc)

/-- **卡目标 2（正标量显式形式）**：`0 < c` 时缩放因子就是 `c` 本身。 -/
theorem growthRatio_pos_smul (A : Matrix5) {c : ℝ} (hc : 0 < c) (values : List ℝ) :
    growthRatio (c • A) (values.map (fun v => c * v)) = growthRatio A values := by
  have habs : |c| = c := abs_of_pos hc
  simpa only [habs] using growthRatio_smul A (ne_of_gt hc) values

/-- **卡目标 2（负标量显式形式）**：`c < 0` 时缩放因子是 `-c`。 -/
theorem growthRatio_neg_smul (A : Matrix5) {c : ℝ} (hc : c < 0) (values : List ℝ) :
    growthRatio (c • A) (values.map (fun v => -c * v)) = growthRatio A values := by
  have habs : |c| = -c := abs_of_neg hc
  simpa only [habs] using growthRatio_smul A (ne_of_lt hc) values

end Rho5.GrowthModel
