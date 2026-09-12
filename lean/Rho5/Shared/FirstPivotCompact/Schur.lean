/-
D26 — 第一步 Schur 更新在 `K` 上的公式与连续性
===============================================

**卡目标 3.** 在 `K` 上（首主元 `A 0 0 = 1`）：

* 逐项公式：`pivotSchur A 0 0 i j = A (i+1) (j+1) - A (i+1) 0 * A 0 (j+1)`；
* `ContinuousOn (fun A => pivotSchur A 0 0) K`。

**不假设一般除法处处连续.** D10 的 `pivotSchur_apply` 带分母 `A p q`；在 `K` 上
`A 0 0 = 1`，于是除法项 `… / A 0 0` 恰为 `… / 1`，整条表达式退化为**多项式**坐标映射

  `A ↦ fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ`，

它的连续性只用到 Pi 投影（`continuous_entry`）与 `Continuous.sub`/`Continuous.mul`。
因此连续性来自“在 `K` 上等于一个处处连续的多项式映射”（`ContinuousOn.congr`），
而不是把 `A ↦ 1 / A 0 0` 当作处处连续。

无 `sorry`、无新公理、无 `native_decide`。
-/
import Rho5.Shared.FirstPivotCompact.Compact

namespace Rho5.FirstPivotCompact

open Rho5

/-- `remainingIndex 0 i = i.succ`：`(Equiv.swap 0 0) i.succ = i.succ`（D10 的定义 + `swap_self`）。 -/
theorem remainingIndex_zero (i : Fin 4) :
    Rho5.PivotReindex.remainingIndex (0 : Fin 5) i = i.succ := by
  simp only [Rho5.PivotReindex.remainingIndex_apply, Equiv.swap_self, Equiv.refl_apply]

/-- **卡目标 3（逐项公式）**：`K` 上第一步 Schur 更新没有除法——它是
`A (i+1) (j+1) - A (i+1) 0 * A 0 (j+1)`。 -/
theorem pivotSchur_zero_zero_apply_of_mem {A : Matrix5} (hA : A ∈ firstPivotDomain)
    (i j : Fin 4) :
    Rho5.PivotReindex.pivotSchur A 0 0 i j =
      A i.succ j.succ - A i.succ 0 * A 0 j.succ := by
  rw [Rho5.PivotReindex.pivotSchur_apply A 0 0 i j]
  simp only [remainingIndex_zero, (mem_firstPivotDomain_iff.mp hA).1, div_one]

/-- 上述多项式坐标映射（在**全空间**上连续）。 -/
theorem continuous_schurPoly : Continuous (fun A : Matrix5 => fun i j : Fin 4 =>
    A i.succ j.succ - A i.succ 0 * A 0 j.succ) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact (continuous_entry i.succ j.succ).sub
    ((continuous_entry i.succ 0).mul (continuous_entry 0 j.succ))

/-- **卡目标 3（连续性）**：`A ↦ pivotSchur A 0 0` 在 `K` 上连续。

证明：多项式映射处处连续（`continuous_schurPoly`），而在 `K` 上两者逐项相等
（`pivotSchur_zero_zero_apply_of_mem`），故由 `ContinuousOn.congr` 得到限制在 `K` 上的连续性。
注意这**只**说明第一步；后续步骤与变长轨迹的连续性未在此支付。 -/
theorem continuousOn_pivotSchur_zero_zero :
    ContinuousOn (fun A : Matrix5 => Rho5.PivotReindex.pivotSchur A 0 0) firstPivotDomain :=
  continuous_schurPoly.continuousOn.congr (fun A hA => by
    funext i j
    exact pivotSchur_zero_zero_apply_of_mem hA i j)

end Rho5.FirstPivotCompact
