/-
D48 — 目标 3：同一实际尾块的 D46 包络
========================================

把 D46 已证的**精确二阶尾块包络**接到真实高增长矩阵的峰值上：

`growthRatio M values ≤ r M + |s M * t M| / r M`。

前提全部来自目标 1/2 的结论：`r M > 0`（四步资格）、`|T2 M 1 1| ≤ r M`（`T2 M` 在 `(0,0)`
的完整主元），以及峰值落在 `r M` 或 `|δ M|` 上。**不**假设 `T2 M 1 1 = -r M`、**不**假设
`s M ≥ 0`、`t M ≥ 0`，也不声称把尾块平衡后仍全局可行（那是 B24 覆盖方的责任）。
-/
import Rho5.Shared.CanonicalTail.TailValues

namespace Rho5.CanonicalTail

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **目标 3（尾部包络）**：真实高增长规范矩阵的增长比不超过 D46 的二阶尾块精确包络
`r M + |s M * t M| / r M`。 -/
theorem growthRatio_le_tailEnvelope {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    Rho5.GrowthModel.growthRatio M values ≤ r M + |s M * t M| / r M := by
  obtain ⟨-, -, -, hcpT2, -, -, -, hrpos, -, -, -⟩ := prefix_structure hM h00 h hgrowth
  obtain ⟨-, -, hratio, hpeak, -⟩ := values_eq_five hM h00 h hgrowth
  have hd : |T2 M 1 1| ≤ r M := by
    have hle : |T2 M 1 1| ≤ |T2 M 0 0| := hcpT2 1 1
    exact hle.trans (le_of_eq (abs_of_pos hrpos))
  have hdelta : |delta M| ≤ r M + |s M * t M| / r M := by
    have h := Rho5.TailEnvelope.abs_delta_le_envelope (r := r M) (s := s M) (t := t M)
      (d := T2 M 1 1) hrpos hd
    simpa [delta] using h
  have hrle : r M ≤ r M + |s M * t M| / r M := by
    have hnn : 0 ≤ |s M * t M| / r M := div_nonneg (abs_nonneg _) (le_of_lt hrpos)
    linarith
  rcases hpeak with hp | hp
  · rw [hp]; exact hrle
  · rw [hp]; exact hdelta

/-- **目标 3（包络的另一半，`max` 形式）**：峰值即 `max (r M) |δ M|` 且不超过包络。 -/
theorem peak_le_tailEnvelope {M : Matrix5} {values : List ℝ}
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M values)
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M values) :
    max (r M) |delta M| ≤ r M + |s M * t M| / r M := by
  obtain ⟨-, -, -, hcpT2, -, -, -, hrpos, -, -, -⟩ := prefix_structure hM h00 h hgrowth
  obtain ⟨-, -, hratio, hpeak, -⟩ := values_eq_five hM h00 h hgrowth
  have hd : |T2 M 1 1| ≤ r M := by
    have hle : |T2 M 1 1| ≤ |T2 M 0 0| := hcpT2 1 1
    exact hle.trans (le_of_eq (abs_of_pos hrpos))
  have hdelta : |delta M| ≤ r M + |s M * t M| / r M := by
    have h := Rho5.TailEnvelope.abs_delta_le_envelope (r := r M) (s := s M) (t := t M)
      (d := T2 M 1 1) hrpos hd
    simpa [delta] using h
  have hrle : r M ≤ r M + |s M * t M| / r M := by
    have hnn : 0 ≤ |s M * t M| / r M := div_nonneg (abs_nonneg _) (le_of_lt hrpos)
    linarith
  exact max_le hrle hdelta

end Rho5.CanonicalTail
