/-
D96 目标 A — 最终等式的端点等价（复用 D82 下界 + D90 两条已编 alpha 端点等价）
================================================================================

对实际常数 `alpha`（D09 `Rho5.Algebraic.AlphaRoot.alpha`，D82 已验收其为实际达到值：

* `Rho5.ExternalAttainment.actualAlpha_attainment` — 实际矩阵、原 `LegalTrace`、增长比 = alpha；
* `Rho5.ExternalAttainment.actualAlpha_le_rho5Trace` — `alpha ≤ rho5Trace`）

本文件给出**最终等式**的精确端点接口：

    `rho5Trace = alpha  ↔  全域单一实际 det 端点界`
    `rho5Trace = alpha  ↔  排序四面域单一实际 det 端点界`

右端是**完全显式**的数学义务：原矩阵 `M : Matrix5`、`M 0 0 = 1`、实际多项式域 `PolyCP M`
（D62）、原行列式 `M.det`、D67 的实际四阶边框子式 `C M`。没有 `RootSpec`、没有抽象
未定义模型、没有增长的抽象上确界参数。

证明只用两个方向：

* `⟹`：`rho5Trace = alpha` 给出 `rho5Trace ≤ alpha`，代入 D90 已编的
  `global_upper_alpha_iff_endpoint{,_sorted}`；
* `⟸`：同一 D90 定理给出 `rho5Trace ≤ alpha`，而 D82 已付 `alpha ≤ rho5Trace`，
  反对称即得等式。

同时给出「更强的统一定理也足够」的组装引理，供外脑选择更省力的形态。
-/
import Rho5.Shared.FinalEndpointAssembly.Defs
import Rho5.Shared.LastPivotUpperReduction
import Rho5.ExternalAttainment.ActualAlpha

namespace Rho5.Shared.FinalEndpointAssembly

open Rho5
open Rho5.MinorCPDomain (PolyCP)

/-- `4 ≤ alpha`：由 D09 已验收的 `4 < alpha` 直接给出（D90 的 alpha 端点等价所需要的
`T ≥ 4` 前提）。 -/
theorem four_le_alpha : (4 : ℝ) ≤ Rho5.Algebraic.AlphaRoot.alpha :=
  le_of_lt Rho5.Algebraic.AlphaRoot.alpha_gt_four

/-- **D96 目标 A（全域版）**：最终等式等价于 `PolyCP` 全域上的单一实际 det 端点界。 -/
theorem rho5Trace_eq_alpha_iff_det_endpoint :
    Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M := by
  have hiff := Rho5.LastPivotUpperReduction.global_upper_alpha_iff_endpoint
  constructor
  · intro h
    exact hiff.mp (le_of_eq h)
  · intro h
    exact le_antisymm (hiff.mpr h) Rho5.ExternalAttainment.actualAlpha_le_rho5Trace

/-- **D96 目标 A（排序四面版）**：同一等式等价于 D74 排序四面边界域上的单一实际 det
端点界；四个面在语句里全部保留，未合并、未假设平衡。 -/
theorem rho5Trace_eq_alpha_iff_sorted_det_endpoint :
    Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
          Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
            Rho5.MinorBoundaryFaces.BoundaryFace M →
              |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M := by
  have hiff := Rho5.LastPivotUpperReduction.global_upper_alpha_iff_endpoint_sorted
  constructor
  · intro h
    exact hiff.mp (le_of_eq h)
  · intro h
    exact le_antisymm (hiff.mpr h) Rho5.ExternalAttainment.actualAlpha_le_rho5Trace

/-- **组装（更强的统一定理：全域单一 det 界 ⟹ 最终等式）**。外脑可以只交这一条更强的
定理，本卡的四条端点义务会自动全部满足。 -/
theorem rho5Trace_eq_alpha_of_det_endpoint
    (h : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
      |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M) :
    Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha :=
  rho5Trace_eq_alpha_iff_det_endpoint.mpr h

/-- **组装（更强的统一定理：排序四面域单一 det 界 ⟹ 最终等式）**。 -/
theorem rho5Trace_eq_alpha_of_sorted_det_endpoint
    (h : ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          Rho5.MinorBoundaryFaces.BoundaryFace M →
            |M.det| ≤ Rho5.Algebraic.AlphaRoot.alpha * Rho5.MinorGrowthThreshold.C M) :
    Rho5.GrowthSupremum.rho5Trace = Rho5.Algebraic.AlphaRoot.alpha :=
  rho5Trace_eq_alpha_iff_sorted_det_endpoint.mpr h

end Rho5.Shared.FinalEndpointAssembly
