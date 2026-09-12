/-
D48 — 目标 2：末两步的真实值列表与峰值分支
=============================================

在目标 1 的四步资格之上，把真实正性前缀迹的**最后一项**读出来：末位 `1 × 1` 块的主元是
`δ = d - t * s / r`（`d = T2 M 1 1`），于是

`values = [1, p M, k M, r M, |δ|]`，`values.length = 5`。

因为 `matrixEntryMax M = 1`，增长比就是峰值；D45 的 `getD 3/4` 峰值见证把它落到第四个或
第五个值上，于是 `growthRatio M values = r M`（此时 `4 < r M`）或 `= |δ|`
（此时 `4 < |δ|`）。

**长度 5 不蕴含满秩**：末值允许为 `0`（末位 `zeroStop` 分支，见
`CanonicalTail.leadingTracePos_fin_one_zeroStop`），本模块不声称末主元非零。
-/
import Rho5.Shared.CanonicalTail.Prefix

namespace Rho5.CanonicalTail

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **目标 2（值列表与峰值分支）**：高增长规范矩阵的真实迹恰有五项
`[1, p M, k M, r M, |δ M|]`；增长比等于峰值，且峰值落在第四项（`= r M`）或第五项
（`= |δ M|`）上，对应分支分别有 `4 < r M` 或 `4 < |δ M|`。 -/
theorem values_eq_five {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    values = [1, p M, k M, r M, |delta M|] ∧ values.length = 5 ∧
      Rho5.GrowthModel.growthRatio M values = Rho5.GrowthModel.tracePeak values ∧
        (Rho5.GrowthModel.growthRatio M values = r M ∨
          Rho5.GrowthModel.growthRatio M values = |delta M|) ∧
          (4 < r M ∨ 4 < |delta M|) := by
  obtain ⟨-, -, -, -, -, -, -, -, hlen5, t, hshape, htail⟩ := prefix_structure hM h00 h hgrowth
  have ht : t = [|delta M|] := by
    have h1 := leadingTracePos_fin_one htail
    rwa [← delta_eq_pivotSchur M] at h1
  have hvalues : values = [1, p M, k M, r M, |delta M|] := by
    rw [hshape, ht, h00]
  have hratio : Rho5.GrowthModel.growthRatio M values = Rho5.GrowthModel.tracePeak values :=
    Rho5.GrowthModel.growthRatio_eq_tracePeak_of_matrixEntryMax_eq_one hM
  have hMne : M ≠ 0 := by
    intro h0
    rw [h0] at h00
    exact one_ne_zero h00.symm
  have hl : Rho5.CompletePivotPath.LegalTrace M values :=
    Rho5.LeadingTrace.legalTrace_of_leading
      (Rho5.LeadingSigns.leadingLegalTrace_of_leadingTracePos h)
  have h4M : (4 : ℝ) * Rho5.HighGrowthTail.M M = 4 := by
    rw [Rho5.HighGrowthTail.M, hM, mul_one]
  have hd3 : values.getD 3 0 = r M := by rw [hvalues]; simp
  have hd4 : values.getD 4 0 = |delta M| := by rw [hvalues]; simp
  rcases Rho5.HighGrowthTail.peak_is_getD_three_or_four M hMne hl hgrowth with
    ⟨-, hget3, hgt3⟩ | ⟨-, hget4, hgt4⟩
  · refine ⟨hvalues, hlen5, hratio, Or.inl ?_, Or.inl ?_⟩
    · rw [hratio, ← hget3, hd3]
    · rw [hd3] at hgt3
      rwa [h4M] at hgt3
  · refine ⟨hvalues, hlen5, hratio, Or.inr ?_, Or.inr ?_⟩
    · rw [hratio, ← hget4, hd4]
    · rw [hd4] at hgt4
      rwa [h4M] at hgt4

/-- **目标 2（末值就是 `|δ|`，允许为 0）**：第五项恰是 `|δ M|`；本卡不声称它非零，
`values.length = 5` 只说明路径走满五步，不说明满秩。 -/
theorem last_value_eq_abs_delta {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    values.getD 4 0 = |delta M| := by
  obtain ⟨hvalues, -, -, -, -⟩ := values_eq_five hM h00 h hgrowth
  rw [hvalues]
  simp

end Rho5.CanonicalTail
