/-
D131 阶段 B — 全局最大者的实际 X / ProperB 二分
================================================================================

输入：阶段 A 的**同一个**实际全局最大者 `P`（`LeadingInput P`、`4 < height P`），
经 D126 已发布的 `high_input_physical_X_or_properB` 送到实际高值 X/B 代表 `N`。

本文件**只做组装与转发**：payload 完全按 D126 已发布类型，含义不更换；
`|r P| ≤ 4` 在 D126 内部由 D125 `input_early_bounds` 支付，本卡不重新证明。

不声称：所有最大者落在 V43 cube（无 cube 前提）、`ProperB` 升级为 `NormalizedB`、
X 盒覆盖、B 前缀归一化、`rho5Trace = alpha`。
-/
import Rho5.Shared.GlobalXBMaximizer.Basic
import Rho5.Shared.ActualXBReduction

noncomputable section
namespace Rho5.Shared.GlobalXBMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **D131 阶段 B 主定理**：无条件存在的实际全局最大者 `P`（`height P = rho5Trace`、
`4 < height P`）经 D126 的实际高值 X/B 二分给出实际代表 `N`：`TailReduction P N`、
`p/k` 相等、`r N > 0` 且 `r N ≤ |r P|`、真实 `LegalTrace`、初始 `matrixEntryMax = 1`、
D125 的高值增长读数，并且 `N` 或由实际 X22 `Physical` 点重构（同高度），或是 `ProperB N`。 -/
theorem exists_global_max_X_or_properB :
    ∃ (P : Matrix5) (values : List ℝ) (N : Matrix5),
      Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧
        Rho5.ExternalTailSaturation.LeadingInput P ∧
          Rho5.ExternalTailSaturation.height P = Rho5.GrowthSupremum.rho5Trace ∧
            (4 : ℝ) < Rho5.ExternalTailSaturation.height P ∧
              Rho5.ExternalTailSaturation.TailReduction P N ∧
                p N = p P ∧ k N = k P ∧ 0 < r N ∧ r N ≤ |r P| ∧
                  Rho5.CompletePivotPath.LegalTrace N
                    [1, p P, k P, r N, Rho5.ExternalTailSaturation.height P] ∧
                    matrixEntryMax N = 1 ∧
                      Rho5.GrowthModel.growthRatio P
                        [1, p P, k P, |r P|, Rho5.ExternalTailSaturation.height P] =
                          Rho5.ExternalTailSaturation.height P ∧
                        ((∃ x : Rho5.LocalAnalysis.X,
                            Rho5.LocalAnalysis.V43.Physical x ∧
                              Rho5.Shared.ActualXBReduction.reconstruct x = N ∧
                                Rho5.LocalAnalysis.height x =
                                  Rho5.ExternalTailSaturation.height P) ∨
                          Rho5.ExternalTailSaturation.ProperB N) := by
  obtain ⟨P, values, hf, hlin, hgt, h4, _hrho, _hs, _hst, _hem, _hlg, _hgr, _hb, _hgm⟩ :=
    exists_global_ts_maximizer
  obtain ⟨N, hred, hp, hk, hrpos, hrle, hleg, hen, hgro, hbr⟩ :=
    Rho5.Shared.ActualXBReduction.high_input_physical_X_or_properB P hlin h4
  exact ⟨P, values, N, hf, hlin, hgt, h4, hred, hp, hk, hrpos, hrle, hleg, hen, hgro, hbr⟩

end Rho5.Shared.GlobalXBMaximizer
