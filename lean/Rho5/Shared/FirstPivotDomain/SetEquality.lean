/-
D23 — 固定集合等式与全局界入口
===============================

**卡目标 3（固定名 `growthValues_eq_firstPivotGrowthValues`）.** D17 的真实增长值集合
`Rho5.GrowthModel.GrowthValues` 与首主元 `+1` 域 `FirstPivotGrowthValues` **相等**。

* `⊆`：任取真实 `A ≠ 0` 与其真实合法轨迹 `values`；`Reduce.exists_firstPivot_reduction`
  给出域中的 `B` 与整条缩放后的真实轨迹 `ws`，且 `growthRatio B ws = growthRatio A values`。
  该构造对每条已有轨迹都成立，**不要求**每条路径使用同一个 tie-break，也不假设路径存在性
  （轨迹是输入）；提前零终止的轨迹同样处理：`values` 原样被 D20 的置换等价运输，缩放由
  D13 的整条轨迹缩放完成，两者都不看 `values` 的形状。
* `⊇`：`matrixEntryMax A = 1` 蕴含 `A ≠ 0`（D17），故域成员本来就在 `GrowthValues` 里。

**卡目标 4（任意实 `B` 的界入口）.** 三个等价形式：

* `bound_growthValues_iff_bound_firstPivot`：集合形式（直接由集合等式）；
* `bound_iff_bound_firstPivot`：矩阵形式——“所有非零矩阵的所有真实轨迹增长比 ≤ `B`”
  ⟺ “所有满足 `matrixEntryMax = 1`、`A 0 0 = 1`、`IsCompletePivot A 0 0` 的矩阵的所有真实
  轨迹增长比 ≤ `B`”。反向用 `exists_firstPivot_reduction`，因此后继真实域证书只需在
  首主元域上出证书；
* `bound_firstPivot_values_iff_bound_set`：矩阵形式的 `∀` 与集合形式的 `∀` 的桥。

范围（冻结）：**不**定义 `sSup`，**不**声称集合非空或有界，**不**证明 alpha 最优或达到性，
**不**假设未知矩阵参数化。D18 的上确界/非空/有界工作不在此处。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotDomain.Reduce

namespace Rho5.FirstPivotDomain

open Rho5 Rho5.GrowthModel

/-- **卡目标 3（`⊆` 方向）**：真实增长值都在首主元域中（`Reduce` 的构造）。 -/
theorem growthValues_subset_firstPivotGrowthValues :
    GrowthValues ⊆ FirstPivotGrowthValues := by
  rintro g ⟨A, values, hA, htrace, rfl⟩
  exact growthValue_mem_firstPivotGrowthValues hA htrace

/-- **卡目标 3（固定名）**：`GrowthValues = FirstPivotGrowthValues`。

两向都真证明；`⊆` 用首主元约化（D10 搬主元 + D20 轨迹置换 + D13 整条轨迹缩放 +
D17 增长比不变），`⊇` 用 `matrixEntryMax = 1 ⇒ A ≠ 0`。 -/
theorem growthValues_eq_firstPivotGrowthValues : GrowthValues = FirstPivotGrowthValues :=
  Set.Subset.antisymm growthValues_subset_firstPivotGrowthValues
    firstPivotGrowthValues_subset_growthValues

/-- 集合等式的成员形式（后继组装按成员使用）。 -/
theorem mem_growthValues_iff_mem_firstPivot {g : ℝ} :
    g ∈ GrowthValues ↔ g ∈ FirstPivotGrowthValues := by
  rw [growthValues_eq_firstPivotGrowthValues]

/-- 反向集合等式（两个方向都单独可引用）。 -/
theorem firstPivotGrowthValues_eq_growthValues : FirstPivotGrowthValues = GrowthValues :=
  growthValues_eq_firstPivotGrowthValues.symm

/-- **卡目标 4（集合形式）**：`B` 控制全部真实增长值 ⟺ `B` 控制首主元域全部值。 -/
theorem bound_growthValues_iff_bound_firstPivot (B : ℝ) :
    (∀ g ∈ GrowthValues, g ≤ B) ↔ (∀ g ∈ FirstPivotGrowthValues, g ≤ B) := by
  rw [growthValues_eq_firstPivotGrowthValues]

/-- **卡目标 4（矩阵形式）**：“所有非零矩阵的所有真实合法轨迹增长比 ≤ `B`” ⟺
“所有 `matrixEntryMax = 1`、`A 0 0 = 1`、`(0, 0)` 为完整主元的矩阵的所有真实合法轨迹
增长比 ≤ `B`”。

`⇒` 只是丢掉条件（域成员非零由 D17 给出）；`⇐` 用 `exists_firstPivot_reduction` 把任意
非零矩阵的真实轨迹搬到域里，再对该轨迹用域上的界。 -/
theorem bound_iff_bound_firstPivot (B : ℝ) :
    (∀ (A : Matrix5) (values : List ℝ), A ≠ 0 →
        Rho5.CompletePivotPath.LegalTrace A values → growthRatio A values ≤ B) ↔
      (∀ (A : Matrix5) (values : List ℝ), matrixEntryMax A = 1 → A 0 0 = 1 →
        Rho5.Pivot.IsCompletePivot A 0 0 →
          Rho5.CompletePivotPath.LegalTrace A values → growthRatio A values ≤ B) := by
  constructor
  · intro h A values hmax _ _ htrace
    exact h A values (ne_zero_of_matrixEntryMax_eq_one hmax) htrace
  · intro h A values hA htrace
    obtain ⟨B', ws, hmaxB, h00B, hpivB, htraceB, hgr⟩ := exists_firstPivot_reduction hA htrace
    rw [← hgr]
    exact h B' ws hmaxB h00B hpivB htraceB

/-- **卡目标 4（桥）**：首主元域上的矩阵形式 `∀` 与集合形式 `∀` 等价
（成员条件与矩阵条件逐字对应）。 -/
theorem bound_firstPivot_values_iff_bound_set (B : ℝ) :
    (∀ (A : Matrix5) (values : List ℝ), matrixEntryMax A = 1 → A 0 0 = 1 →
        Rho5.Pivot.IsCompletePivot A 0 0 →
          Rho5.CompletePivotPath.LegalTrace A values → growthRatio A values ≤ B) ↔
      (∀ g ∈ FirstPivotGrowthValues, g ≤ B) := by
  constructor
  · intro h g hg
    obtain ⟨A, values, hmax, h00, hpiv, htrace, rfl⟩ := hg
    exact h A values hmax h00 hpiv htrace
  · intro h A values hmax h00 hpiv htrace
    exact h (growthRatio A values) ⟨A, values, hmax, h00, hpiv, htrace, rfl⟩

end Rho5.FirstPivotDomain
