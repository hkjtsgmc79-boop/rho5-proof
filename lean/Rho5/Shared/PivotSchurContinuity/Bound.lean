/-
D32 — 合法主元域上的 Schur 条目估计（含零主元）
=================================================

**卡目标 2.** 对任意 `n`、`p q : Fin (n+1)`，在 `CPDomain p q` 上**每一项**满足

  `|pivotSchur A p q i j| ≤ 2 * |A p q|`，

**包含零主元**（`A p q = 0`，此时由 D10 的
`eq_zero_of_isCompletePivot_of_pivot_eq_zero` 得 `A = 0`，两边都是 `0`）。

非零主元情形**优先搬运已有结果**而不是重证：D10 的
`pivotSchur A p q = fixedSchur (movePivot A p q)`（定义相同）把 D11 的
`fixedSchur_entry_abs_le_two_mul_pivot`
（`|fixedSchur A i j| ≤ 2 * |A 0 0|`，要求 `(0,0)` 是合法主元且非零）
经 D10 的实际重索引搬到任意 `(p, q)`：`movePivot` 把 `(p, q)` 放到 `(0, 0)`、
保持主元资格（`isCompletePivot_movePivot_iff`）并把该条目原样带过去
（`movePivot_zero_zero`）。

**不对不合法主元声称同样估计**：整条陈述以 `A ∈ CPDomain p q` 为前提；
离开这个域，结论一般不成立。
-/
import Rho5.Shared.PivotSchurContinuity.CPDomain
import Rho5.Shared.PivotGrowth

namespace Rho5.PivotSchurContinuity

open Rho5

/-- **卡目标 2（含零主元的条目估计）**：`A ∈ CPDomain p q` 时，Schur 更新的每一项满足
`|pivotSchur A p q i j| ≤ 2 * |A p q|`。

* `A p q = 0`：由 `eq_zero_of_mem_CPDomain_of_pivot_eq_zero` 得 `A = 0`，
  再用 `pivotSchur_zero`，两边都是 `0`；
* `A p q ≠ 0`：`pivotSchur A p q = fixedSchur (movePivot A p q)`（定义相同），
  `(0,0)` 是 `movePivot A p q` 的合法且非零主元，套 D11 的界，
  再用 `movePivot_zero_zero` 换回 `|A p q|`。 -/
theorem pivotSchur_entry_abs_le_two_mul_pivot {n : ℕ} {p q : Fin (n + 1)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A ∈ CPDomain p q) (i j : Fin n) :
    |Rho5.PivotReindex.pivotSchur A p q i j| ≤ 2 * |A p q| := by
  by_cases hpq : A p q = 0
  · have hzero : A = 0 := eq_zero_of_mem_CPDomain_of_pivot_eq_zero hA hpq
    subst hzero
    rw [pivotSchur_zero, hpq]
    simp
  · have hmax : Rho5.Pivot.IsCompletePivot (Rho5.PivotReindex.movePivot A p q) 0 0 :=
      (Rho5.PivotReindex.isCompletePivot_movePivot_iff A p q).mpr hA
    have hne : Rho5.PivotReindex.movePivot A p q 0 0 ≠ 0 := by
      rw [Rho5.PivotReindex.movePivot_zero_zero]
      exact hpq
    have hb := Rho5.PivotGrowth.fixedSchur_entry_abs_le_two_mul_pivot
      (Rho5.PivotReindex.movePivot A p q) hmax hne i j
    rw [Rho5.PivotReindex.pivotSchur_eq_fixedSchur]
    rwa [Rho5.PivotReindex.movePivot_zero_zero] at hb

end Rho5.PivotSchurContinuity
