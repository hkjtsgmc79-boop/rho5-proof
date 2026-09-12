/-
D48 — 目标 4：条件式真实见证（`4 < rho5Trace` 为前提）
=========================================================

用 D43 已验收的**无前提存在定理** `exists_canonical_maximizer` 取真实规范最大矩阵，
把目标 1–3 的资格与尾部公式全部附上，并保留原全局比较。

**条件明确保留**：`4 < Rho5.GrowthSupremum.rho5Trace` 是本定理的**假设**，本卡不证明它；
不平衡尾块（`T2 M 1 1 = -r M`）、`s M ≥ 0`、`t M ≥ 0`、满秩、B24 全域覆盖、`rho5Trace = alpha`
都不在本卡的结论里。末值 `|δ M|` 允许为 `0`（末位 `zeroStop` 分支已覆盖）。
-/
import Rho5.Shared.CanonicalTail.Envelope
import Rho5.Shared.CanonicalMaximizer

namespace Rho5.CanonicalTail

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **目标 4（条件式规范尾部见证）**：若 `4 < rho5Trace`，则存在真实 `M : Matrix5` 与真实
值列表 `values`，使得

* `matrixEntryMax M = 1`、`M ≠ 0`、`M 0 0 = 1`、`LeadingTracePos M values`；
* 四层 `(0,0)` 都是真实完整主元：`M`、`S4 M`、`S3 M`、`T2 M`；
* `0 < p M`、`0 < k M`、`0 < r M`；
* `values = [1, p M, k M, r M, |δ M|]` 且 `values.length = 5`；
* `growthRatio M values = rho5Trace = tracePeak values`；
* 峰值在第四项（`= r M`，此时 `4 < r M`）或第五项（`= |δ M|`，此时 `4 < |δ M|`）；
* D46 尾部包络 `growthRatio M values ≤ r M + |s M * t M| / r M`；
* **原全局比较**：每个真实非零矩阵的每条原 `LegalTrace` 增长比都不超过该见证。 -/
theorem exists_canonical_tail_witness (h4 : 4 < Rho5.GrowthSupremum.rho5Trace) :
    ∃ (M : Matrix5) (values : List ℝ),
      matrixEntryMax M = 1 ∧ M ≠ 0 ∧ M 0 0 = 1 ∧
        Rho5.LeadingSigns.LeadingTracePos M values ∧
          Rho5.Pivot.IsCompletePivot M 0 0 ∧ Rho5.Pivot.IsCompletePivot (S4 M) 0 0 ∧
            Rho5.Pivot.IsCompletePivot (S3 M) 0 0 ∧ Rho5.Pivot.IsCompletePivot (T2 M) 0 0 ∧
              0 < p M ∧ 0 < k M ∧ 0 < r M ∧
                values = [1, p M, k M, r M, |delta M|] ∧ values.length = 5 ∧
                  Rho5.GrowthModel.growthRatio M values = Rho5.GrowthSupremum.rho5Trace ∧
                    Rho5.GrowthModel.growthRatio M values = Rho5.GrowthModel.tracePeak values ∧
                      (Rho5.GrowthModel.growthRatio M values = r M ∨
                        Rho5.GrowthModel.growthRatio M values = |delta M|) ∧
                        (4 < r M ∨ 4 < |delta M|) ∧
                          Rho5.GrowthModel.growthRatio M values ≤ r M + |s M * t M| / r M ∧
                            ∀ (N : Matrix5), N ≠ 0 → ∀ ws : List ℝ,
                              Rho5.CompletePivotPath.LegalTrace N ws →
                                Rho5.GrowthModel.growthRatio N ws ≤
                                  Rho5.GrowthModel.growthRatio M values := by
  obtain ⟨M, hM, hMne, h00, values, hpos, -, -, hratio, hcmp⟩ :=
    Rho5.CanonicalMaximizer.exists_canonical_maximizer
  have hgrowth : 4 < Rho5.GrowthModel.growthRatio M values := by
    rw [hratio]; exact h4
  obtain ⟨hcp0, hcp4, hcp3, hcp2, hpos0, hposp, hposk, hposr, hlen5, -, -, -⟩ :=
    prefix_structure hM h00 hpos hgrowth
  obtain ⟨hvalues, hlen5', hratioPeak, hpeakBranch, hbranch4⟩ :=
    values_eq_five hM h00 hpos hgrowth
  have henv := growthRatio_le_tailEnvelope hM h00 hpos hgrowth
  exact ⟨M, values, hM, hMne, h00, hpos, hcp0, hcp4, hcp3, hcp2, hposp, hposk, hposr,
    hvalues, hlen5', hratio, hratioPeak, hpeakBranch, hbranch4, henv, hcmp⟩

end Rho5.CanonicalTail
