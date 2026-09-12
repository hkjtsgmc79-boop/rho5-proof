/-
D96 目标 C — 消去极大见证的 `4 < rho5Trace` 前提
==================================================

D90 已验收的 `Rho5.LastPivotUpperReduction.exists_last_pivot_eq_rho` 以
`4 < rho5Trace` 为前提。本文件把该前提变成**定理**：

* D09 `alpha_gt_four : 4 < alpha`（实际常数的下界）；
* D82 `actualAlpha_le_rho5Trace : alpha ≤ rho5Trace`（实际达到性，已验收）；

两者合成 `4 < rho5Trace`（`four_lt_rho5Trace`），于是同一个 D68 排序四面实际最大者
**无任何额外前提**地满足 `|δ P| = rho5Trace`：

    `exists_last_pivot_eq_rho_unconditional`。

结论与原卡完全同形：同一个 `P`、同一张真实迹值表 `values`、同一条 `0 ≤ s P ≤ t P`、
同一个四选一饱和边界析取（四个面一个不少）、以及 `|δ P| = rho5Trace`。
**没有**换成第二个对象、**没有**假设平衡或最后主元主导、**没有**引入 V43 立方体成员假设。
D92 的全局区间/紧域非空结论在这里**不需要**：`4 < rho5Trace` 完全由 D09 + D82 支付。
-/
import Rho5.Shared.FinalEndpointAssembly.Defs
import Rho5.Shared.LastPivotUpperReduction
import Rho5.Shared.BoundaryMaximizer
import Rho5.Shared.CanonicalTail
import Rho5.ExternalAttainment.ActualAlpha

namespace Rho5.Shared.FinalEndpointAssembly

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.MinorCPDomain (PolyCP)

/-- **实际 `4 < rho5Trace`**：D09 的 `4 < alpha` 与 D82 的 `alpha ≤ rho5Trace` 合成。
这是本卡新增的、可独立消费的读数。 -/
theorem four_lt_rho5Trace : (4 : ℝ) < Rho5.GrowthSupremum.rho5Trace :=
  lt_of_lt_of_le Rho5.Algebraic.AlphaRoot.alpha_gt_four
    Rho5.ExternalAttainment.actualAlpha_le_rho5Trace

/-- **D96 目标 C**：同一个 D68 排序四面实际最大者，**无任何额外前提**地有
`|δ P| = rho5Trace`。 -/
theorem exists_last_pivot_eq_rho_unconditional :
    ∃ (P : Matrix5) (values : List ℝ),
      Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧ 0 ≤ s P ∧ s P ≤ t P ∧
        (P 4 4 = -1 ∨ S4 P 3 3 = -p P ∨ S3 P 2 2 = -k P ∨ T2 P 1 1 = -r P) ∧
          |Rho5.CanonicalTail.delta P| = Rho5.GrowthSupremum.rho5Trace :=
  Rho5.LastPivotUpperReduction.exists_last_pivot_eq_rho four_lt_rho5Trace

end Rho5.Shared.FinalEndpointAssembly
