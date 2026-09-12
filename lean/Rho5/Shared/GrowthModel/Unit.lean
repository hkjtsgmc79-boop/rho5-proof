/-
D17 — D08 单位归一化后的增长比
==============================

**卡目标 2（归一化部分）** 与 **卡目标 3 的集合包含方向** 在此成型：对非零
`Matrix5`，D08 的单位归一化把峰值整体除以 `matrixEntryMax A`，于是

* `tracePeak_normalize`：
  `tracePeak (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) = tracePeak values / matrixEntryMax A`；
* `growthRatio_normalize_map`：归一化矩阵配**同一条缩放后的轨迹**时增长比不变
  ——这是 D13 `legalTrace_normalize_iff` 使用的轨迹写法，也就是后继 D18 直接消费的
  “归一化证书”形式；归一化后分母恰为 `1`（D08 `matrixEntryMax_normalize`），所以
  单位矩阵的增长比就等于该轨迹的峰值（`NormalizeSet` 的集合方向）。

D08 的归一化标量 `(matrixEntryMax A)⁻¹` 为正，因此 `|·|` 不出现符号分支；`A ≠ 0`
是让该标量可逆的唯一前提，全部显式保留。

复用（只读冻结输入）：D08 `MatrixNormalization`
（`normalize_eq_inv_smul`、`matrixEntryMax_normalize`、`matrixEntryMax_pos`）与
D13 `legalTrace_normalize_iff`。不重复实现归一化，不重复证明缩放等价。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.GrowthModel.Scalar
import Mathlib.Tactic.Ring

namespace Rho5.GrowthModel

open Rho5

/-- **卡目标 2（归一化后的峰值）**：非零矩阵的归一化轨迹峰值等于原轨迹峰值除以
原矩阵的元素最大范数。缩放因子 `(matrixEntryMax A)⁻¹` 为正，`|·|` 直接消去；
剩下的 `(matrixEntryMax A)⁻¹ * matrixEntryMax A` 由 `ring` 约去。 -/
theorem tracePeak_normalize {A : Matrix5} (hA : A ≠ 0) (values : List ℝ) :
    tracePeak (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) =
      tracePeak values / matrixEntryMax A := by
  have hpos : 0 < matrixEntryMax A := Rho5.MatrixNormalization.matrixEntryMax_pos A hA
  rw [tracePeak_map_mul (le_of_lt (inv_pos.mpr hpos)), div_eq_mul_inv]
  ring

/-- **卡目标 2/3（归一化 + 轨迹缩放）**：把矩阵换成 D08 的 `normalize A`、把轨迹换成
D13 归一化等价所用的 `values.map (fun v => (matrixEntryMax A)⁻¹ * v)`，增长比不变。
证明是定义展开 + 峰值归一化等式 + 分母 `= 1`，不引入第二种归一化或第二种轨迹约定。 -/
theorem growthRatio_normalize_map {A : Matrix5} (hA : A ≠ 0) (values : List ℝ) :
    growthRatio (Rho5.MatrixNormalization.normalize A)
        (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) = growthRatio A values := by
  rw [growthRatio_eq, growthRatio_eq, tracePeak_normalize hA,
    Rho5.MatrixNormalization.matrixEntryMax_normalize A hA, div_one]

end Rho5.GrowthModel
