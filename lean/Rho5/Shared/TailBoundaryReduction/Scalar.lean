/-
D57 阶段 A（1）— 尾部标量峰值：带符号归约与对 `d` 的单调性
=================================================================

固定 `r > 0`、`s, t ≥ 0`，尾部约束 `|d + h| ≤ r`（`h` 是 D55 将来的整矩阵位移参数）。
本模块只做两件**标量**事实：

* **A1（带符号归约）**：`max r |d + h - t*s/r| = max r (t*s/r - d - h)`。
  左边的带符号量在约束下确实 `≤ r`（`signed_tail_le_r`），而 `|·|` 的另一支
  `-(d + h - t*s/r)` 就是右边被 `max r` 提升前的量——两支都显式处理，不靠"第五值必为峰值"。
* **A2（对 `h` 单调不增）**：`h1 ≤ h2` 且各自满足尾约束时，`h1` 处的峰值 `≥` `h2` 处的峰值。

**不假设**尾块平衡、不假设 `d + h = -r`，也不假设 `t*s/r` 与 `d + h` 的符号关系。
-/
import Rho5.Shared.Conventions
import Mathlib.Tactic.Linarith

namespace Rho5.TailBoundaryReduction

open Rho5

/-- **A1 的辅助（带符号量 ≤ r）**：在 `|d+h| ≤ r` 与 `t*s/r ≥ 0` 下，
`d + h - t*s/r ≤ r`。这正是"左边带符号表达式不超过 `r`"的诚实陈述。 -/
theorem signed_tail_le_r {r s t d h : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d + h| ≤ r) : d + h - t * s / r ≤ r := by
  have hc : 0 ≤ t * s / r := div_nonneg (mul_nonneg ht hs) (le_of_lt hr)
  have hx : d + h ≤ r := (abs_le.mp hd).2
  linarith

/-- **A1（主）**：`max r |d + h - t*s/r| = max r (t*s/r - d - h)`。

证明只用两件事：带符号量 `y = d + h - t*s/r ≤ r`（`signed_tail_le_r`），
以及 `|y| ≤ max r (-y)` 与 `max r (-y) ≤ max r |y|`（`-y ≤ |y|`）两向夹逼；
`-(d + h - t*s/r)` 与 `t*s/r - d - h` 逐字相等（`ring`）。 -/
theorem max_abs_tail_eq_max_reduced {r s t d h : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hd : |d + h| ≤ r) :
    max r |d + h - t * s / r| = max r (t * s / r - d - h) := by
  have hy : d + h - t * s / r ≤ r := signed_tail_le_r hr hs ht hd
  have h1 : max r |d + h - t * s / r| = max r (-(d + h - t * s / r)) := by
    refine le_antisymm ?_ ?_
    · refine max_le (le_max_left _ _) ?_
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [le_max_right r (-(d + h - t * s / r))]
      · exact le_trans hy (le_max_left r (-(d + h - t * s / r)))
    · refine max_le (le_max_left _ _) ?_
      exact le_trans (neg_le_abs _) (le_max_right r |d + h - t * s / r|)
  rw [h1]
  congr 1
  ring

/-- **A2（归约形式的单调性）**：`max r (t*s/r - d - h)` 关于 `h` 单调不增
（这是纯格序事实，不需要任何约束）。 -/
theorem max_reduced_antitone {r s t d h1 h2 : ℝ} (h12 : h1 ≤ h2) :
    max r (t * s / r - d - h2) ≤ max r (t * s / r - d - h1) :=
  max_le_max le_rfl (by linarith)

/-- **A2（主）**：`h1 ≤ h2`、两者各自满足 `|d + h| ≤ r` 时，`h1` 处的尾部峰值不小于
`h2` 处的尾部峰值。 -/
theorem tailPeak_antitone {r s t d h1 h2 : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h1c : |d + h1| ≤ r) (h2c : |d + h2| ≤ r) (h12 : h1 ≤ h2) :
    max r |d + h2 - t * s / r| ≤ max r |d + h1 - t * s / r| := by
  rw [max_abs_tail_eq_max_reduced hr hs ht h1c, max_abs_tail_eq_max_reduced hr hs ht h2c]
  exact max_reduced_antitone h12

/-- **诚实的负向事实**：第五值 `|d + h - t*s/r|` **本身**并不关于 `h` 单调
（因此本卡不把"第五值单调"当作 A3 的跳板）：显式反例 `r = 2`、`s = t = 1`、`d = 0`、
`h1 = 2/5 ≤ h2 = 1`，两者都在尾约束内，而第五值反而变大。 -/
theorem fifth_value_not_antitone :
    ∃ (r s t d h1 h2 : ℝ), 0 < r ∧ 0 ≤ s ∧ 0 ≤ t ∧
      |d + h1| ≤ r ∧ |d + h2| ≤ r ∧ h1 ≤ h2 ∧
        |d + h1 - t * s / r| < |d + h2 - t * s / r| :=
  ⟨2, 1, 1, 0, 2 / 5, 1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end Rho5.TailBoundaryReduction
