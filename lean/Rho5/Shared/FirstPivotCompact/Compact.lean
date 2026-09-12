/-
D26 — `K` 的紧性
=================

**卡目标 2.** 在实际 `Matrix5` 的有限维乘积拓扑中：`K` 非空（`Domain`）且 `IsCompact K`。

证明路线（全部复用 mathlib，不自造拓扑框架）：

1. `K` 作为坐标空间中的集合恰是 **25 个坐标的闭区间盒子** `firstPivotBox` 与
   **一个坐标等式** `A 0 0 = 1` 的交（`firstPivotDomain_eq_box_inter`）；
2. 盒子紧：`isCompact_Icc`（`CompactIccSpace (Fin 5 → Fin 5 → ℝ)` 由 mathlib 的 Pi 实例给出）；
   盒子闭：`isClosed_Icc`（`OrderClosedTopology` 同理）；
3. 坐标等式集闭：`isClosed_eq` + 条目连续性 `continuous_entry`；
4. `K` 是紧集合的闭子集：`IsCompact.of_isClosed_subset`。

`IsCompact` 的陈述写在 `Matrix5` 上（桥实例给出乘积拓扑），坐标空间形式单独保留
（`_coe` 版本），两者定义相同。

**这不是全部达到性**：`K` 紧 + 第一步 `pivotSchur` 连续（见 `Schur.lean`）只是把
“连续泛函在 `K` 上取到最大值”这一条准备好；变长 `LegalTrace`、后续小主元/零终止与
峰值连续性都尚未支付（见 `Bridge.lean` 的未付接口清单）。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotCompact.Domain

namespace Rho5.FirstPivotCompact

open Rho5

/-- 25 个坐标的闭区间盒子是闭集（坐标空间的 `OrderClosedTopology` 由 mathlib 给出）。 -/
theorem isClosed_firstPivotBox : IsClosed firstPivotBox := by
  unfold firstPivotBox
  exact isClosed_Icc

/-- 25 个坐标的闭区间盒子是紧集（有限维乘积中的闭盒子）。 -/
theorem isCompact_firstPivotBox : IsCompact firstPivotBox := by
  unfold firstPivotBox
  exact isCompact_Icc

/-- 坐标等式 `A 0 0 = 1` 定义闭集。 -/
theorem isClosed_pivot_eq_one :
    IsClosed {A : Fin 5 → Fin 5 → ℝ | A 0 0 = 1} :=
  isClosed_eq (continuous_entry 0 0) continuous_const

/-- **卡目标 2（闭性，坐标空间形式）**：`K` 是紧盒子的闭子集。 -/
theorem isClosed_firstPivotDomain_coe :
    IsClosed (firstPivotDomain : Set (Fin 5 → Fin 5 → ℝ)) := by
  rw [firstPivotDomain_eq_box_inter]
  exact isClosed_firstPivotBox.inter isClosed_pivot_eq_one

/-- **卡目标 2（紧性，坐标空间形式）**：`K` 是闭盒子（紧）的闭子集，故紧。 -/
theorem isCompact_firstPivotDomain_coe :
    IsCompact (firstPivotDomain : Set (Fin 5 → Fin 5 → ℝ)) := by
  rw [firstPivotDomain_eq_box_inter]
  exact isCompact_firstPivotBox.of_isClosed_subset
    (isClosed_firstPivotBox.inter isClosed_pivot_eq_one)
    Set.inter_subset_left

/-- **卡目标 2（闭性，`Matrix5` 形式）**：同一个集合，写在带乘积拓扑的 `Matrix5` 上。 -/
theorem isClosed_firstPivotDomain : IsClosed (firstPivotDomain : Set Matrix5) :=
  isClosed_firstPivotDomain_coe

/-- **卡目标 2（紧性，`Matrix5` 形式）**：`K` 在 `Matrix5` 的乘积拓扑中紧。 -/
theorem isCompact_firstPivotDomain : IsCompact (firstPivotDomain : Set Matrix5) :=
  isCompact_firstPivotDomain_coe

end Rho5.FirstPivotCompact
