/-
D90 公共支付步 — `Rho5.Shared.LastPivotUpperReduction.Common`
==============================================================

本文件只做一件事：把 **D86 已验收的实际第四主元界** `r M ≤ 4`（前提仅
`M 0 0 = 1` 与 `PolyCP M`）与 **D67 已验收的读数** `C M = r M * B M`、`B M > 0`
组装成旧 D69 两条不等式中的**第三条主元义务**

    `C M ≤ T * B M`     （`T ≥ 4`）。

这是 D90 目标 A/B 共同的、唯一的新增数学内容：它不新建极值框架、不新建范数或范数
定义、不重编任何上游、也不引入新的主元读数。D86 `r ≤ 4` 的前提里没有 `r ≤ 4`
本身，也没有包络、子块资格或高支预算假设，因此这里是**真实支付**而不是循环。

无 `sorry`、无 `admit`、无 `native_decide`、无项目公理。
-/
import Rho5.Shared.NestedThreePivot.StageB
import Rho5.Shared.MinorGrowthThreshold.Defs
import Rho5.Shared.MinorCPDomain
import Mathlib.Tactic.Linarith

namespace Rho5.LastPivotUpperReduction

open Rho5
open Rho5.Certificate.B24Extraction (p k r)
open Rho5.MinorCPDomain (PolyCP)

/-- **实际正性读数**（复用 D62 已付引理 `p_pos_of_A`/`k_pos_of_B`）：`PolyCP M` 与
`M 0 0 = 1` 给出 `p M > 0` 与 `k M > 0`。 -/
theorem p_k_pos_of_polyCP (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) :
    0 < p M ∧ 0 < k M := by
  obtain ⟨hA, hB, -, -, -, -, -⟩ := hP
  have hp : 0 < p M := Rho5.MinorCPDomain.p_pos_of_A M h00 hA
  exact ⟨hp, Rho5.MinorCPDomain.k_pos_of_B M h00 hp hB⟩

/-- **D90 公共支付步**：`T ≥ 4` 时第三条主元义务 `C M ≤ T * B M` 成立。

由 D67 的 `C M = r M * B M` 与 `B M > 0`、以及 D86 的实际 `r M ≤ 4` 得到；
`T ≥ 4` 只用一次，并且是显式前提。语句里没有 `r` 界、没有轨迹存在、没有子块资格。 -/
theorem C_le_T_mul_B (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) {T : ℝ} (hT : 4 ≤ T) :
    Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M := by
  obtain ⟨hp, hk⟩ := p_k_pos_of_polyCP M h00 hP
  have hr : r M ≤ 4 := Rho5.NestedThreePivot.fourth_pivot_le_four M h00 hP
  have hB : 0 < Rho5.MinorGrowthThreshold.B M := Rho5.MinorGrowthThreshold.B_pos M h00 hp hk
  rw [Rho5.MinorGrowthThreshold.C_eq_r_mul_B M h00 hp hk]
  calc r M * Rho5.MinorGrowthThreshold.B M ≤ 4 * Rho5.MinorGrowthThreshold.B M :=
        mul_le_mul_of_nonneg_right hr (le_of_lt hB)
    _ ≤ T * Rho5.MinorGrowthThreshold.B M := mul_le_mul_of_nonneg_right hT (le_of_lt hB)

end Rho5.LastPivotUpperReduction
