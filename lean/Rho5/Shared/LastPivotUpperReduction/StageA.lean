/-
D90 目标 A — 全局尖锐上界的单一行列式形式（`PolyCP` 全域）
==========================================================

对每个 `T ≥ 4`：

    `rho5Trace ≤ T  ↔  ∀ M : Matrix5, M 0 0 = 1 → PolyCP M → |det M| ≤ T * C M`

* `⟹`：D69 已验收的 `inequalities_of_rho5Trace_le` 的**第二分量**（旧定理直接给出，
  本 lane 只做投影）。
* `⟸`：D69 的 `rho5Trace_le_iff_polyCP_inequalities` 需要两条不等式；第三条主元义务
  `C M ≤ T * B M` 由本 lane 的 `C_le_T_mul_B`（消费 D86 实际 `r M ≤ 4`）**自动支付**，
  第二条正是假设 `h`。所以 `rho5Trace ≤ T` 仍由 D69 的逆方向（D48/D43 已付的实际
  规范见证）给出，没有新的极值框架。

最终语句不追加 `r` 界、不追加轨迹存在、不追加任何子块资格。
无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Rho5.Shared.LastPivotUpperReduction.Common
import Rho5.Shared.GlobalMinorReduction
import Rho5.Shared.GrowthFour

namespace Rho5.LastPivotUpperReduction

open Rho5
open Rho5.MinorCPDomain (PolyCP)

/-- **D90 目标 A**：`T ≥ 4` 时，全局上界与「全域单一实际行列式界」精确等价。 -/
theorem rho5Trace_le_iff_polyCP_det_bound {T : ℝ} (hT : 4 ≤ T) :
    Rho5.GrowthSupremum.rho5Trace ≤ T ↔
      ∀ M : Matrix5, M 0 0 = 1 → PolyCP M →
        |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M := by
  constructor
  · intro hrho M h00 hpoly
    exact (Rho5.GlobalMinorReduction.inequalities_of_rho5Trace_le hT hrho M h00 hpoly).2
  · intro h
    refine (Rho5.GlobalMinorReduction.rho5Trace_le_iff_polyCP_inequalities hT).mpr ?_
    intro M h00 hpoly
    exact ⟨C_le_T_mul_B M h00 hpoly hT, h M h00 hpoly⟩

/-- **推论（阈值取 `T := rho5Trace` 本身的无条件行列式界）**：D44 已验收的
`4 ≤ rho5Trace` 使目标 A 的 iff 可以在 `T := rho5Trace` 处实例化（前提 `4 ≤ T` 成立，
且 `rho5Trace ≤ rho5Trace` 是自反的）。于是得到对**每个**实际 `PolyCP` 矩阵都成立、
**不带任何 `T` 前提**的行列式界

    `|det M| ≤ rho5Trace * C M`。

注意方向：`T = 4` 处不能这样用——目标 A 给出的是 `rho5Trace ≤ 4 → …`，而 D44 给的是
`4 ≤ rho5Trace`，两者方向相反；真正可无条件实例化的是端点 `T = rho5Trace`。本推论也
不声称 `rho5Trace = alpha`、不声称右端在更小的 `T` 处成立。 -/
theorem det_bound_rho (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) :
    |M.det| ≤ Rho5.GrowthSupremum.rho5Trace * Rho5.MinorGrowthThreshold.C M :=
  (rho5Trace_le_iff_polyCP_det_bound (T := Rho5.GrowthSupremum.rho5Trace)
      Rho5.GrowthFour.four_le_rho5Trace).mp
    (le_refl Rho5.GrowthSupremum.rho5Trace) M h00 hP

end Rho5.LastPivotUpperReduction
