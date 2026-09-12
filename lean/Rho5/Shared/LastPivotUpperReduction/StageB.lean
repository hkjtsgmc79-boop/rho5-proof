/-
D90 目标 B — 排序四面边界对象上的单一行列式形式
================================================

同样 `T ≥ 4`，把目标 A 的 `∀ M` 收缩到 D74 已验收的**排序四面边界域**（四个面一个不
少：`M 4 4 = -1`、`S4 M 3 3 = -p M`、`S3 M 2 2 = -k M`、`T2 M 1 1 = -r M` 的
D70 `BoundaryFace` 析取，加上排序 `0 ≤ m4 M 0 1 ≤ m4 M 1 0`）：

    `rho5Trace ≤ T  ↔  ∀ M, （M00 = 1 ∧ PolyCP M ∧ 排序 ∧ BoundaryFace M）
                              → |det M| ≤ T * C M`

* `⟹`：D74 已验收的 `inequalities_of_rho5Trace_le_sorted` 的第二分量。
* `⟸`：D74 的 `rho5Trace_le_iff_sorted_boundary` 需要两条不等式；第三条主元义务仍由
  本 lane 的 `C_le_T_mul_B`（D86 实际 `r M ≤ 4`）支付，第二条是假设 `h`。

四个面在语句里全部保留，没有被合并成平衡尾支路，也没有添加平衡假设。
无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Rho5.Shared.LastPivotUpperReduction.Common
import Rho5.Shared.BoundaryUpperReduction

namespace Rho5.LastPivotUpperReduction

open Rho5
open Rho5.MinorCPDomain (PolyCP)

/-- **D90 目标 B**：`T ≥ 4` 时，全局上界与排序四面边界域上的单一实际行列式界精确
等价（四个面全部保留）。 -/
theorem rho5Trace_le_iff_sorted_boundary_det_bound {T : ℝ} (hT : 4 ≤ T) :
    Rho5.GrowthSupremum.rho5Trace ≤ T ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
          Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
            Rho5.MinorBoundaryFaces.BoundaryFace M →
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M := by
  constructor
  · intro hrho M h00 hpoly hm1 hm2 hface
    exact (Rho5.BoundaryUpperReduction.inequalities_of_rho5Trace_le_sorted hT hrho
      M h00 hpoly hm1 hm2 hface).2
  · intro h
    refine (Rho5.BoundaryUpperReduction.rho5Trace_le_iff_sorted_boundary hT).mpr ?_
    intro M h00 hpoly hm1 hm2 hface
    exact ⟨C_le_T_mul_B M h00 hpoly hT, h M h00 hpoly hm1 hm2 hface⟩

end Rho5.LastPivotUpperReduction
