/-
D23 — 首主元 `(0,0) = +1` 的增长值域
=====================================

**卡目标 1（冻结集合）.** `FirstPivotGrowthValues` 的元素由**实际** `Matrix5` 与**真实**
`Rho5.CompletePivotPath.LegalTrace` 给出，条件为

* `matrixEntryMax A = 1`（D08 冻结元素最大范数为单位），
* `A 0 0 = 1`（首主元恰为 `+1`），
* `Rho5.Pivot.IsCompletePivot A 0 0`（该位置真的是完整主元，ties 不受限），

元素值是 **D17 原来的** `Rho5.GrowthModel.growthRatio A values`——本文件**不**重新定义
增长比、不定义第二套范数或主元谓词。

本文件只放集合与“域 ⊆ 真实增长值”这一容易方向；“真实增长值 ⊆ 域”由 `Reduce` +
`SetEquality` 用已有完整主元存在、D10 `movePivot`、D20 置换等价与 D17 全路径缩放给出。

复用（只读冻结输入，哈希见 `INPUT_HASHES.json`）：D17 `GrowthModel`
（`GrowthValues`、`growthRatio`、`ne_zero_of_matrixEntryMax_eq_one`）、
pilot `Rho5.Matrix5`/`Rho5.matrixEntryMax`/`Rho5.Pivot.IsCompletePivot`、
D13 `CompletePivotPath.LegalTrace`。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.GrowthModel

namespace Rho5.FirstPivotDomain

open Rho5 Rho5.GrowthModel

/-- **冻结定义（D23 卡目标 1）**：首主元为 `+1`、元素最大范数为 `1` 的真实矩阵域的
增长值集合。成员条件全部是实际矩阵/实际合法轨迹上的条件，元素值是 D17 的
`growthRatio`（不重新定义）。 -/
def FirstPivotGrowthValues : Set ℝ :=
  {g | ∃ (A : Matrix5) (values : List ℝ),
    matrixEntryMax A = 1 ∧ A 0 0 = 1 ∧ Rho5.Pivot.IsCompletePivot A 0 0 ∧
      Rho5.CompletePivotPath.LegalTrace A values ∧ g = growthRatio A values}

/-- 成员展开式（后继组装与 D18 重写入口）。 -/
theorem mem_firstPivotGrowthValues_iff {g : ℝ} :
    g ∈ FirstPivotGrowthValues ↔ ∃ (A : Matrix5) (values : List ℝ),
      matrixEntryMax A = 1 ∧ A 0 0 = 1 ∧ Rho5.Pivot.IsCompletePivot A 0 0 ∧
        Rho5.CompletePivotPath.LegalTrace A values ∧ g = growthRatio A values :=
  Iff.rfl

/-- **域 ⊆ 真实增长值**：`matrixEntryMax A = 1` 本身蕴含 `A ≠ 0`（D17），所以首主元域的
每个成员都已经是 `GrowthValues` 的成员，不需要任何附加前提。 -/
theorem firstPivotGrowthValues_subset_growthValues :
    FirstPivotGrowthValues ⊆ GrowthValues := by
  rintro g ⟨A, values, hmax, -, -, htrace, rfl⟩
  exact ⟨A, values, ne_zero_of_matrixEntryMax_eq_one hmax, htrace, rfl⟩

end Rho5.FirstPivotDomain
