/-
D90 目标 C — 把 `T` 特化为实际 `alpha`（只消去已付义务）
========================================================

D09 已验收的独立 `AlphaRoot` 模块给出实际常数
`Rho5.Algebraic.AlphaRoot.alpha` 与 `alpha_gt_four : 4 < alpha`。把它代入目标 A/B 的
`T ≥ 4` 前提（`4 ≤ alpha` 由 `le_of_lt` 给出），即得**精确的**终点形式：

    `global_upper_alpha_iff_endpoint`         （`PolyCP` 全域版）
    `global_upper_alpha_iff_endpoint_sorted`  （排序四面边界版）

这只是**特化**，不是新的数学：两个方向都已经由 D69/D74（逆方向）与 D86 `r ≤ 4`
（第三条主元义务）付清。本文件**不**声称右端真的成立，**不**声称
`rho5Trace ≤ alpha`，**不**声称 `rho5Trace = alpha`，也**不**声称最大值可达。

关于 `alpha` 的来源：`Rho5.Algebraic.AlphaRoot` 是 D09 已验收的独立模块，其源码在
本 lane 的 X 构建树中按逐字节哈希核对后硬链接复用（不重编、不修改）；
`alpha` 由 D09 卡内的区间存在性定理定义，无 `RootSpec`、无外部根存在性参数。

无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Rho5.Shared.LastPivotUpperReduction.StageA
import Rho5.Shared.LastPivotUpperReduction.StageB
import Rho5.Algebraic.AlphaRoot.Root

namespace Rho5.LastPivotUpperReduction

open Rho5
open Rho5.MinorCPDomain (PolyCP)

/-- **D90 目标 C（全域版）**：`T := alpha` 处的精确终点等价式。 -/
theorem global_upper_alpha_iff_endpoint :
    Rho5.GrowthSupremum.rho5Trace ≤ Rho5.Algebraic.AlphaRoot.alpha ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M :=
  rho5Trace_le_iff_polyCP_det_bound (T := Rho5.Algebraic.AlphaRoot.alpha)
    (le_of_lt Rho5.Algebraic.AlphaRoot.alpha_gt_four)

/-- **D90 目标 C（排序四面边界版）**：同一特化在 D74 排序四面域上的形式，四个面全部
保留。 -/
theorem global_upper_alpha_iff_endpoint_sorted :
    Rho5.GrowthSupremum.rho5Trace ≤ Rho5.Algebraic.AlphaRoot.alpha ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
          Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
            Rho5.MinorBoundaryFaces.BoundaryFace M →
              |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M :=
  rho5Trace_le_iff_sorted_boundary_det_bound (T := Rho5.Algebraic.AlphaRoot.alpha)
    (le_of_lt Rho5.Algebraic.AlphaRoot.alpha_gt_four)

end Rho5.LastPivotUpperReduction
