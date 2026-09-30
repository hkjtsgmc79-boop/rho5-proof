import Rho5.Shared.XSmallKBranch.Sound
import Rho5.ExternalTailSaturation.Basic
import Rho5.Shared.V43MatrixRoundTrip
import Rho5.Shared.LastThreePivotEnvelope
import Rho5.Shared.MinorThreeBound

/-
D136 续（叶模块）— 实际矩阵 ↔ 模型 chart 状态的精确桥，以及两条矩阵行的接入
=================================================================================

* `chartState M` 的前 22 个坐标**就是** D119 `Rho5.Shared.V43MatrixRoundTrip.extractX`
  的 22 个反向读数（顺序与 `Model.varNames` 完全一致），后 35 个坐标是真实共享乘积；
  因此该桥是**定义级**的（`rfl`），不是假设。
* 同一 height 读数：`TS.delta M = wX M - rX M`（`SatFrame` 的 `s = t = r`），
  于是 `TS.height M = rr z - ww z`（在 `w ≤ r` 时），与模型行 `F = r - w` 一致。
* 两条此前未付的行由**已编译上游定理**支付，不重做数学：
  - `Fcore`（`F ≤ 9k/4`）← D87 `Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k`；
  - `det3`（`p·k ≤ 4`）← D54 `Rho5.MinorThreeBound.p_mul_k_le_four`。
* 不修改冻结的 `Model`/`Sound`；不触碰 D135 与任何上游。
-/

noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-- 实际矩阵的 chart 状态：22 个 D119 反向读数 + 35 个真实共享乘积。 -/
def chartState (M : Matrix5) : Z := fun i =>
  match i.1 with
  | 0 => extractX M 0
  | 1 => extractX M 1
  | 2 => extractX M 2
  | 3 => extractX M 3
  | 4 => extractX M 4
  | 5 => extractX M 5
  | 6 => extractX M 6
  | 7 => extractX M 7
  | 8 => extractX M 8
  | 9 => extractX M 9
  | 10 => extractX M 10
  | 11 => extractX M 11
  | 12 => extractX M 12
  | 13 => extractX M 13
  | 14 => extractX M 14
  | 15 => extractX M 15
  | 16 => extractX M 16
  | 17 => extractX M 17
  | 18 => extractX M 18
  | 19 => extractX M 19
  | 20 => extractX M 20
  | 21 => extractX M 21
  | 22 => extractX M 15 * extractX M 21
  | 23 => extractX M 15 * extractX M 20
  | 24 => extractX M 15 * extractX M 19
  | 25 => extractX M 14 * extractX M 21
  | 26 => extractX M 14 * extractX M 20
  | 27 => extractX M 14 * extractX M 19
  | 28 => extractX M 13 * extractX M 21
  | 29 => extractX M 13 * extractX M 20
  | 30 => extractX M 13 * extractX M 19
  | 31 => extractX M 12 * extractX M 18
  | 32 => extractX M 12 * extractX M 17
  | 33 => extractX M 12 * extractX M 16
  | 34 => extractX M 11 * extractX M 18
  | 35 => extractX M 11 * extractX M 17
  | 36 => extractX M 11 * extractX M 16
  | 37 => extractX M 10 * extractX M 18
  | 38 => extractX M 10 * extractX M 17
  | 39 => extractX M 10 * extractX M 16
  | 40 => extractX M 9 * extractX M 18
  | 41 => extractX M 9 * extractX M 17
  | 42 => extractX M 9 * extractX M 16
  | 43 => extractX M 8 * extractX M 12
  | 44 => extractX M 8 * extractX M 11
  | 45 => extractX M 8 * extractX M 10
  | 46 => extractX M 8 * extractX M 9
  | 47 => extractX M 7 * extractX M 15
  | 48 => extractX M 7 * extractX M 14
  | 49 => extractX M 7 * extractX M 13
  | 50 => extractX M 4 * extractX M 6
  | 51 => extractX M 4 * extractX M 5
  | 52 => extractX M 3 * extractX M 6
  | 53 => extractX M 3 * extractX M 5
  | 54 => extractX M 0 * extractX M 7
  | 55 => extractX M 0 * extractX M 6
  | 56 => extractX M 0 * extractX M 5
  | _ => 0

/-- 逐坐标读数（`rfl`）。 -/
@[simp] theorem chartState_0 (M : Matrix5) : chartState M 0 = extractX M 0 := rfl
@[simp] theorem chartState_1 (M : Matrix5) : chartState M 1 = extractX M 1 := rfl
@[simp] theorem chartState_2 (M : Matrix5) : chartState M 2 = extractX M 2 := rfl
@[simp] theorem chartState_3 (M : Matrix5) : chartState M 3 = extractX M 3 := rfl
@[simp] theorem chartState_4 (M : Matrix5) : chartState M 4 = extractX M 4 := rfl
@[simp] theorem chartState_5 (M : Matrix5) : chartState M 5 = extractX M 5 := rfl
@[simp] theorem chartState_6 (M : Matrix5) : chartState M 6 = extractX M 6 := rfl
@[simp] theorem chartState_7 (M : Matrix5) : chartState M 7 = extractX M 7 := rfl
@[simp] theorem chartState_8 (M : Matrix5) : chartState M 8 = extractX M 8 := rfl
@[simp] theorem chartState_9 (M : Matrix5) : chartState M 9 = extractX M 9 := rfl
@[simp] theorem chartState_10 (M : Matrix5) : chartState M 10 = extractX M 10 := rfl
@[simp] theorem chartState_11 (M : Matrix5) : chartState M 11 = extractX M 11 := rfl
@[simp] theorem chartState_12 (M : Matrix5) : chartState M 12 = extractX M 12 := rfl
@[simp] theorem chartState_13 (M : Matrix5) : chartState M 13 = extractX M 13 := rfl
@[simp] theorem chartState_14 (M : Matrix5) : chartState M 14 = extractX M 14 := rfl
@[simp] theorem chartState_15 (M : Matrix5) : chartState M 15 = extractX M 15 := rfl
@[simp] theorem chartState_16 (M : Matrix5) : chartState M 16 = extractX M 16 := rfl
@[simp] theorem chartState_17 (M : Matrix5) : chartState M 17 = extractX M 17 := rfl
@[simp] theorem chartState_18 (M : Matrix5) : chartState M 18 = extractX M 18 := rfl
@[simp] theorem chartState_19 (M : Matrix5) : chartState M 19 = extractX M 19 := rfl
@[simp] theorem chartState_20 (M : Matrix5) : chartState M 20 = extractX M 20 := rfl
@[simp] theorem chartState_21 (M : Matrix5) : chartState M 21 = extractX M 21 := rfl

/-- **提升事实**：后 35 个坐标确实是前 22 个的真实乘积（35 个 `rfl`）。 -/
theorem chartState_isLift (M : Matrix5) : IsLift (chartState M) where
  lift_x2_q2 := rfl
  lift_x2_q1 := rfl
  lift_x2_q0 := rfl
  lift_x1_q2 := rfl
  lift_x1_q1 := rfl
  lift_x1_q0 := rfl
  lift_x0_q2 := rfl
  lift_x0_q1 := rfl
  lift_x0_q0 := rfl
  lift_u2_v2 := rfl
  lift_u2_v1 := rfl
  lift_u2_v0 := rfl
  lift_u1_v2 := rfl
  lift_u1_v1 := rfl
  lift_u1_v0 := rfl
  lift_u0_v2 := rfl
  lift_u0_v1 := rfl
  lift_u0_v0 := rfl
  lift_be_v2 := rfl
  lift_be_v1 := rfl
  lift_be_v0 := rfl
  lift_e_u2 := rfl
  lift_e_u1 := rfl
  lift_e_u0 := rfl
  lift_e_be := rfl
  lift_p_x2 := rfl
  lift_p_x1 := rfl
  lift_p_x0 := rfl
  lift_B_d := rfl
  lift_B_c := rfl
  lift_A_d := rfl
  lift_A_c := rfl
  lift_k_p := rfl
  lift_k_d := rfl
  lift_k_c := rfl

/-- 冻结读数的定义级对应。 -/
theorem chartState_kk (M : Matrix5) : kk (chartState M) = k M := rfl
theorem chartState_rr (M : Matrix5) : rr (chartState M) = r M := rfl
theorem chartState_ww (M : Matrix5) : ww (chartState M) = T2 M 1 1 := rfl
theorem chartState_pp (M : Matrix5) : pp (chartState M) = p M := rfl
theorem chartState_AA (M : Matrix5) : AA (chartState M) = S3 M 0 1 := rfl
theorem chartState_BB (M : Matrix5) : BB (chartState M) = S3 M 0 2 := rfl
theorem chartState_cc (M : Matrix5) : cc (chartState M) = S3 M 1 0 / S3 M 0 0 := rfl
theorem chartState_dd (M : Matrix5) : dd (chartState M) = S3 M 2 0 / S3 M 0 0 := rfl
theorem chartState_ee (M : Matrix5) : ee (chartState M) = -(M 0 1) := rfl
theorem chartState_be (M : Matrix5) : be (chartState M) = M 1 0 := rfl
theorem chartState_uu0 (M : Matrix5) : uu (chartState M) 0 = M 2 0 := rfl
theorem chartState_xx0 (M : Matrix5) : xx (chartState M) 0 = (M 2 1 + ee (chartState M) * uu (chartState M) 0) / pp (chartState M) := rfl
theorem chartState_vv0 (M : Matrix5) : vv (chartState M) 0 = M 0 2 := rfl
theorem chartState_qq0 (M : Matrix5) : qq (chartState M) 0 = M 1 2 - be (chartState M) * vv (chartState M) 0 := rfl
theorem chartState_uu1 (M : Matrix5) : uu (chartState M) 1 = M 3 0 := rfl
theorem chartState_xx1 (M : Matrix5) : xx (chartState M) 1 = (M 3 1 + ee (chartState M) * uu (chartState M) 1) / pp (chartState M) := rfl
theorem chartState_vv1 (M : Matrix5) : vv (chartState M) 1 = M 0 3 := rfl
theorem chartState_qq1 (M : Matrix5) : qq (chartState M) 1 = M 1 3 - be (chartState M) * vv (chartState M) 1 := rfl
theorem chartState_uu2 (M : Matrix5) : uu (chartState M) 2 = M 4 0 := rfl
theorem chartState_xx2 (M : Matrix5) : xx (chartState M) 2 = (M 4 1 + ee (chartState M) * uu (chartState M) 2) / pp (chartState M) := rfl
theorem chartState_vv2 (M : Matrix5) : vv (chartState M) 2 = M 0 4 := rfl
theorem chartState_qq2 (M : Matrix5) : qq (chartState M) 2 = M 1 4 - be (chartState M) * vv (chartState M) 2 := rfl

/-! ## 同一 height 读数 -/

/-- `SatFrame` 下 `CanonicalTail.delta` 就是 chart 的 `w - r`。 -/
theorem delta_eq_wX_sub_rX {M : Matrix5} (h : SatFrame M) :
    Rho5.CanonicalTail.delta M = T2 M 1 1 - r M := by
  have hr : r M ≠ 0 := ne_of_gt h.hr
  rw [Rho5.CanonicalTail.delta, h.hs, h.ht]
  field_simp

/-- `TS.delta` 与 chart 的 `w - r` 相同（`TS.w M = T2 M 1 1`）。 -/
theorem ts_delta_eq_wX_sub_rX {M : Matrix5} (h : SatFrame M) :
    Rho5.ExternalTailSaturation.delta M = T2 M 1 1 - r M := by
  have hr : r M ≠ 0 := ne_of_gt h.hr
  rw [Rho5.ExternalTailSaturation.delta, Rho5.ExternalTailSaturation.w, h.hs, h.ht]
  field_simp

/-- **同一 height 读数**：chart 状态上的 `F = r - w` 就是 `TS.height M`（在 `w ≤ r` 时）。 -/
theorem height_reading {M : Matrix5} (h : SatFrame M) (hwr : T2 M 1 1 ≤ r M) :
    Rho5.ExternalTailSaturation.height M = rr (chartState M) - ww (chartState M) := by
  rw [Rho5.ExternalTailSaturation.height, ts_delta_eq_wX_sub_rX h, chartState_rr, chartState_ww,
    abs_of_nonpos (by linarith : T2 M 1 1 - r M ≤ 0)]
  ring

/-- 高值分支下 `F > 0`，故 `|δ| = F`。 -/
theorem abs_delta_eq_F {M : Matrix5} (h : SatFrame M) (hwr : T2 M 1 1 ≤ r M) :
    |Rho5.CanonicalTail.delta M| = rr (chartState M) - ww (chartState M) := by
  rw [delta_eq_wX_sub_rX h, chartState_rr, chartState_ww,
    abs_of_nonpos (by linarith : T2 M 1 1 - r M ≤ 0)]
  ring

/-! ## 两条矩阵行：接入 D54 / D87（不重做行列式或 (3.4) 数学） -/

/-- **`det3`（`p·k ≤ 4`）** ← D54 `Rho5.MinorThreeBound.p_mul_k_le_four`。 -/
theorem det3_of_satFrame {M : Matrix5} (h : SatFrame M) :
    (0 : ℝ) ≤ 4 - kk (chartState M) * pp (chartState M) := by
  have hle : p M * k M ≤ 4 := Rho5.MinorThreeBound.p_mul_k_le_four M h.hmax h.h00 h.hp h.hk
  have hcomm : kk (chartState M) * pp (chartState M) = p M * k M := by
    rw [chartState_kk, chartState_pp, mul_comm]
  rw [hcomm]
  linarith

/-- **`Fcore`（`F ≤ 9k/4`）** ← D87 `delta_abs_le_nine_quarters_mul_k`（配合 `le_abs_self`）。 -/
theorem Fcore_of_satFrame {M : Matrix5} (h : SatFrame M) :
    (0 : ℝ) ≤ (9 / 4 : ℝ) * kk (chartState M) - rr (chartState M) + ww (chartState M) := by
  have hCP : Rho5.MinorCPDomain.PolyCP M :=
    (Rho5.MinorCPDomain.polyCP_iff_frame M h.h00).mpr
      ⟨h.hmax, h.cp1, h.cp2, h.cp3, h.cp4, h.hp, h.hk, h.hr⟩
  have hd := Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k M h.h00 hCP
  have hdel : Rho5.CanonicalTail.delta M = T2 M 1 1 - r M := delta_eq_wX_sub_rX h
  have hle : r M - T2 M 1 1 ≤ |Rho5.CanonicalTail.delta M| := by
    rw [hdel]; simpa using neg_le_abs (T2 M 1 1 - r M)
  have hmain : rr (chartState M) - ww (chartState M) ≤ (9 / 4 : ℝ) * kk (chartState M) := by
    rw [chartState_rr, chartState_ww, chartState_kk]
    linarith
  linarith [hmain]

/-- 冻结行 `RowProp 98`（`det3` 的 LP 形式）对实际 `SatFrame` 矩阵成立。 -/
theorem rowProp98_of_satFrame {M : Matrix5} (h : SatFrame M) :
    RowProp 98 (chartState M) := by
  have hd := det3_of_satFrame h
  simp only [chartState, kk, pp] at hd
  norm_num at hd
  simp only [RowProp, chartState, kk, pp]
  norm_num
  linarith [hd]

/-- 冻结行 `RowProp 96`（`Fcore` 的 LP 形式）对实际 `SatFrame` 矩阵成立。 -/
theorem rowProp96_of_satFrame {M : Matrix5} (h : SatFrame M) :
    RowProp 96 (chartState M) := by
  have hd := Fcore_of_satFrame h
  simp only [chartState, kk, rr, ww] at hd
  norm_num at hd
  simp only [RowProp, chartState, kk, rr, ww]
  norm_num
  linarith [hd]

/-! ## 封口：冻结 104 行 + 两条矩阵行 = 106 行 -/

/-- **106 行齐备（在显式输入与 `SatFrame` 之下）**：`paidIdx` 的 104 行由冻结的
`paid_rows_sound` 支付，索引 `96`（`Fcore`）与 `98`（`det3`）由 D87/D54 支付。
`PhysicalBounds`/`NormalizedSigns`/`HighValue`/`Rho4Input`/`SmallThirdPivot` 仍是显式输入。 -/
theorem all_rows_sound_of_satFrame (M : Matrix5) (h : SatFrame M)
    (hb : PhysicalBounds (chartState M)) (hs : NormalizedSigns (chartState M))
    (hF : HighValue (chartState M)) (hrho : Rho4Input (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) :
    ∀ i, i ∈ paidIdx ∨ i = 96 ∨ i = 98 → RowProp i (chartState M) := by
  intro i hi
  rcases hi with hi | rfl | rfl
  · exact paid_rows_sound (chartState M) (chartState_isLift M) hb hs hF hrho hk2 i hi
  · exact rowProp96_of_satFrame h
  · exact rowProp98_of_satFrame h

end Rho5.Shared.XSmallKBranch
