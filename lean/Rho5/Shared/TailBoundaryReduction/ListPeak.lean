/-
D57 阶段 A（2）— 固定五值 `tracePeak` 的单调性（不经"第五值即峰值"）
=========================================================================

D48/D53 的真实迹在非负尾符号下恰是五项 `[1, p, k, r, |d + h - t*s/r|]`（`p, k` 与 `h` 无关）。
本模块证明：**整条列表的 `tracePeak`** 关于 `h` 单调不增——即使第五值本身并不单调
（见 `Scalar.fifth_value_not_antitone`），因为 `tracePeak` 是五项的最大值，
而"尾部峰值" `max r |d + h - t*s/r|` 是单调的，`max r (·)` 与第五值的组合恰好把
`max r e(h)` 单独拎出来，所以整表峰值随 `h` 增大而不增。

工具顺序：先给一般的"列表末项单调"引理（结构递归），再给固定五项形式，
最后给带真实尾数据（`r > 0`、`s, t ≥ 0`、各自尾约束）的 `h`-单调形式。
-/
import Rho5.Shared.TailBoundaryReduction.Scalar
import Rho5.Shared.GrowthModel

namespace Rho5.TailBoundaryReduction

open Rho5

/-- **工具（一般列表末项单调）**：把末项从 `e` 换成更大的 `e'`，`foldr max 0`（即 `tracePeak`）
不会变小。结构递归于前缀列表；这是唯一需要归纳的地方。 -/
theorem tracePeak_append_singleton_mono : ∀ (l : List ℝ) {e e' : ℝ}, e ≤ e' →
    Rho5.GrowthModel.tracePeak (l ++ [e]) ≤ Rho5.GrowthModel.tracePeak (l ++ [e'])
  | [], e, e', h => by simpa using max_le_max h le_rfl
  | a :: t, e, e', h => by
      simpa using max_le_max le_rfl (tracePeak_append_singleton_mono t h)

/-- **A3（第五值单调即整表单调）**：第五项变大时五项峰值不减。 -/
theorem tracePeak_five_mono {p k r e e' : ℝ} (h : e ≤ e') :
    Rho5.GrowthModel.tracePeak [1, p, k, r, e] ≤ Rho5.GrowthModel.tracePeak [1, p, k, r, e'] := by
  have := tracePeak_append_singleton_mono [1, p, k, r] h
  simpa using this

/-- **A3（主）**：`p, k` 固定，`r > 0`、`s, t ≥ 0`，`h1 ≤ h2` 且两者各自满足尾约束
`|d + h| ≤ r` 时，带真实尾值的五项峰值满足
`tracePeak [1,p,k,r,|d+h2-t*s/r|] ≤ tracePeak [1,p,k,r,|d+h1-t*s/r|]`。

证明不假设第五值是峰值：只用 A2 的 `max r |…h2| ≤ max r |…h1|`，
把它抬到 `max r (max e 0)` 层（`max_assoc` + `le_max_left`），再逐层 `max_le_max` 比较整表。 -/
theorem tracePeak_five_tail_antitone {r s t d p k h1 h2 : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (h1c : |d + h1| ≤ r) (h2c : |d + h2| ≤ r) (h12 : h1 ≤ h2) :
    Rho5.GrowthModel.tracePeak [1, p, k, r, |d + h2 - t * s / r|] ≤
      Rho5.GrowthModel.tracePeak [1, p, k, r, |d + h1 - t * s / r|] := by
  have key : max r |d + h2 - t * s / r| ≤ max r |d + h1 - t * s / r| :=
    tailPeak_antitone hr hs ht h1c h2c h12
  have hinner : max r (max |d + h2 - t * s / r| 0) ≤ max r (max |d + h1 - t * s / r| 0) := by
    refine max_le (le_max_left _ _) ?_
    have h0 : max |d + h2 - t * s / r| 0 ≤ max r |d + h2 - t * s / r| := by
      refine max_le (le_max_right _ _) ?_
      exact le_trans (le_of_lt hr) (le_max_left _ _)
    exact le_trans h0 (le_trans key (max_le_max le_rfl (le_max_left _ _)))
  simp only [Rho5.GrowthModel.tracePeak_cons, Rho5.GrowthModel.tracePeak_nil]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl hinner))

end Rho5.TailBoundaryReduction
