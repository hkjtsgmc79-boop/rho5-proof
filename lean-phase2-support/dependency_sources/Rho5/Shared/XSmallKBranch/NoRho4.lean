import Rho5.Shared.XSmallKBranch.PhysicalBridge
import Rho5.Shared.SchurFourPivotBound

/-
D136 续（第三叶）— D138 薄适配：去掉 `Rho4Input` 前提
=========================================================

`Rho4Input (chartState M)`（即 `F ≤ 4p`，原文 §1.1 的唯一外部低阶输入 ρ₄=4）
现由 **D138 已冻结**的 `Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p` 支付：

* `SatFrame M` + 高值分支 ⇒ 实际的 TS `LeadingInput M`（`delta_ne` 由高值给出）；
* 该定理给 `TS.height M ≤ 4 p M`，而 `r M - w` 是 `TS.height M = |w - r|` 的一侧，故 `F ≤ 4p`。

不重编/不重审任何上游与冻结模块；`NormalizedSigns`/`HighValue`/`SmallThirdPivot` 仍显式保留。
-/
noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-- 高值分支下实际矩阵满足 TS `LeadingInput`（八字段：`delta_ne` 来自 `F > 0`）。 -/
theorem leadingInput_of_satFrame_high (M : Matrix5) (h : SatFrame M)
    (hF : HighValue (chartState M)) : Rho5.ExternalTailSaturation.LeadingInput M where
  head := h.h00
  cp0 := h.cp1
  cp1 := h.cp2
  cp2 := h.cp3
  cp3 := h.cp4
  p_pos := h.hp
  k_pos := h.hk
  delta_ne := by
    have hF' : (1653 / 400 : ℝ) ≤ r M - T2 M 1 1 := by
      simpa only [rr_chartState, ww_chartState, wX, rX] using hF
    rw [ts_delta_eq_wX_sub_rX h]
    intro hz
    linarith

/-- **D138 薄适配**：`SatFrame M` + 高值 ⇒ `Rho4Input (chartState M)`（`F ≤ 4p`）。 -/
theorem rho4Input_chartState (M : Matrix5) (h : SatFrame M)
    (hF : HighValue (chartState M)) : Rho4Input (chartState M) := by
  have hlin : Rho5.ExternalTailSaturation.LeadingInput M := leadingInput_of_satFrame_high M h hF
  have h4 : Rho5.ExternalTailSaturation.height M ≤ 4 * p M :=
    Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p M hlin
  have hheight : Rho5.ExternalTailSaturation.height M = |T2 M 1 1 - r M| := by
    rw [Rho5.ExternalTailSaturation.height, ts_delta_eq_wX_sub_rX h]
  have hle : r M - T2 M 1 1 ≤ Rho5.ExternalTailSaturation.height M := by
    rw [hheight]
    simpa using neg_le_abs (T2 M 1 1 - r M)
  have hp : pp (chartState M) = p M := by rw [pp_chartState, pX_eq_p]
  have h1 : rr (chartState M) = r M := rr_chartState M
  have h2 : ww (chartState M) = T2 M 1 1 := by rw [ww_chartState, wX]
  show rr (chartState M) - ww (chartState M) ≤ 4 * pp (chartState M)
  rw [h1, h2, hp]
  linarith

/-- **实际矩阵 106 行入口（无 `PhysicalBounds`、无 `Rho4Input`）**：
`SatFrame` + 符号规范 + 高值 + `k ≤ 2` 即可。 -/
theorem all_rows_sound_of_satFrame_noRho4 (M : Matrix5) (h : SatFrame M)
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) :
    ∀ i, i ∈ paidIdx ∨ i = 96 ∨ i = 98 → RowProp i (chartState M) :=
  all_rows_sound_of_satFrame_noPhys M h hs hF (rho4Input_chartState M h hF) hk2

end Rho5.Shared.XSmallKBranch
