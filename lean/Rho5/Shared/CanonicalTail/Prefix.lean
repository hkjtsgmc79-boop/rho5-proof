/-
D48 — 目标 1：高增长规范矩阵的四步真实资格
=============================================

设真实 `M : Matrix5` 满足 `matrixEntryMax M = 1`、`M 0 0 = 1`、`LeadingTracePos M values`
且 `4 < growthRatio M values`。本模块**逐层解构真实关系**并推出：

* `IsCompletePivot M 0 0`、`IsCompletePivot (S4 M) 0 0`、`IsCompletePivot (S3 M) 0 0`、
  `IsCompletePivot (T2 M) 0 0`（D37 同名真实 Schur 定义）；
* `0 < M 0 0`、`0 < p M`、`0 < k M`、`0 < r M`；
* 顺带得到 `values.length = 5`（高增长下不存在早停）。

**没有**任何一条被写成前提：CP 与正性都由 `LeadingTracePos` 的真实构造子给出，
长度下界由 D45 已证的高增长分支接口给出（`4 ≤ values.length`），
长度上界由 D13 的 `length_le_five` 给出，`values.length = 4` 的早停分支
（`T2 M = 0` 的 `zeroStop`）由 D45 的 `getD 3/4` 峰值见证排除。
不重证 D15 的 `2^k` 归纳、不重证 D45 的分支定理、不假设满秩或尾块平衡。
-/
import Rho5.Shared.CanonicalTail.Defs

namespace Rho5.CanonicalTail

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r)

/-- **目标 1（四步资格）**：高增长（`4 < growthRatio`）的条目最大值 `1` 首主元正性前缀
矩阵在四层 `(0,0)` 上都有真实完整主元，且 `p`、`k`、`r` 严格为正；并且迹长恰为 `5`、
前四项恰是 `[M 0 0, p M, k M, r M]`。

`values.length = 4` 的早停分支（第三层 `T2 M = 0` 的 `zeroStop`）被 D45 的峰值见证排除：
该分支下 `values.getD 3 0 = 0`，与 `4 * matrixEntryMax M = 4 < values.getD 3 0` 矛盾；
索引 `4` 的分支则要求 `5 ≤ values.length`，与长度 `4` 矛盾。 -/
theorem prefix_structure {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.Pivot.IsCompletePivot M 0 0 ∧ Rho5.Pivot.IsCompletePivot (S4 M) 0 0 ∧
      Rho5.Pivot.IsCompletePivot (S3 M) 0 0 ∧ Rho5.Pivot.IsCompletePivot (T2 M) 0 0 ∧
        0 < M 0 0 ∧ 0 < p M ∧ 0 < k M ∧ 0 < r M ∧ values.length = 5 ∧
          ∃ t : List ℝ, values = M 0 0 :: p M :: k M :: r M :: t ∧
            Rho5.LeadingSigns.LeadingTracePos
              (Rho5.PivotReindex.pivotSchur (T2 M) 0 0) t := by
  have hMne : M ≠ 0 := by
    intro h0
    rw [h0] at h00
    exact one_ne_zero h00.symm
  have hl : Rho5.CompletePivotPath.LegalTrace M values :=
    Rho5.LeadingTrace.legalTrace_of_leading
      (Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos h)
  have hbr := Rho5.HighGrowthTail.peak_is_getD_three_or_four M hMne hl hgrowth
  have hlen4 : 4 ≤ values.length := by
    rcases hbr with ⟨h4, -, -⟩ | ⟨h5, -, -⟩
    · exact h4
    · exact le_trans (by norm_num) h5
  cases h with
  | zeroStop hzero => simp at hlen4
  | step hmax0 hne0 hpos0 htail1 =>
      cases htail1 with
      | zeroStop hzero => simp at hlen4
      | step hmax1 hne1 hpos1 htail2 =>
          cases htail2 with
          | zeroStop hzero => simp at hlen4
          | step hmax2 hne2 hpos2 htail3 =>
              cases htail3 with
              | zeroStop hzero =>
                  rcases hbr with ⟨-, -, hgt⟩ | ⟨h5, -, -⟩
                  · simp only [List.getD_cons_succ, List.getD_cons_zero] at hgt
                    have h4M : (4 : ℝ) * Rho5.HighGrowthTail.M M = 4 := by
                      rw [Rho5.HighGrowthTail.M, hM, mul_one]
                    rw [h4M] at hgt
                    exact absurd hgt (by norm_num)
                  · simp at h5
              | step hmax3 hne3 hpos3 htail4 =>
                  have htail4_one := leadingTracePos_fin_one htail4
                  refine ⟨hmax0, hmax1, hmax2, hmax3, hpos0, hpos1, hpos2, hpos3, ?_, ?_⟩
                  · rw [htail4_one]
                    simp
                  · exact ⟨_, rfl, htail4⟩

end Rho5.CanonicalTail
