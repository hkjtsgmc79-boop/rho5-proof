import Rho5.Shared.XSmallKBranch.MatrixBridge
import Mathlib.Tactic.FinCases

/-
D136 续（第二叶）— `SatFrame M → PhysicalBounds (chartState M)` 的 15 个字段
================================================================================

全部**直接复用 D119 `Rho5.Shared.V43MatrixRoundTrip` 已编译读数**（`Physical.lean` 的两侧带），
不重做 Schur/主元数学，也不动冻结的 `Model`/`Sound` 与 104 行来源层：

* `e/β/head/u/x/v` 与 `L/P/q/D/S/O` 的带 ← D119 的同名读数定理；
* `k > 0`、`r > 0` ← `SatFrame` 的 `hk`/`hr`；
* `|w| ≤ r` ← `SatFrame.cp4 1 1`（尾块完整主元）。

并给出**去掉 `PhysicalBounds` 前提**的实际矩阵 106 行入口 `all_rows_sound_of_satFrame_noPhys`。
`NormalizedSigns`/`HighValue`/`SmallThirdPivot` 仍显式保留；`F ≤ 4p`（ρ₄=4）由 D138 独占，本卡不重复证明。
-/
noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-! ## 1. chart 读数与 D119 反向读数的逐坐标对应 -/

theorem kk_chartState (M : Matrix5) : kk (chartState M) = kX M := by
  simp only [kk, chartState_0, extractX_0]
theorem rr_chartState (M : Matrix5) : rr (chartState M) = rX M := by
  simp only [rr, chartState_1, extractX_1]
theorem ww_chartState (M : Matrix5) : ww (chartState M) = wX M := by
  simp only [ww, chartState_2, extractX_2]
theorem AA_chartState (M : Matrix5) : AA (chartState M) = aX M := by
  simp only [AA, chartState_3, extractX_3]
theorem BB_chartState (M : Matrix5) : BB (chartState M) = bX M := by
  simp only [BB, chartState_4, extractX_4]
theorem cc_chartState (M : Matrix5) : cc (chartState M) = cX M := by
  simp only [cc, chartState_5, extractX_5]
theorem dd_chartState (M : Matrix5) : dd (chartState M) = dX M := by
  simp only [dd, chartState_6, extractX_6]
theorem pp_chartState (M : Matrix5) : pp (chartState M) = pX M := by
  simp only [pp, chartState_7, extractX_7]
theorem ee_chartState (M : Matrix5) : ee (chartState M) = eX M := by
  simp only [ee, chartState_8, extractX_8]
theorem be_chartState (M : Matrix5) : be (chartState M) = betaX M := by
  simp only [be, chartState_9, extractX_9]

theorem uu_chartState (M : Matrix5) (i : Fin 3) : uu (chartState M) i = uX M i := by
  fin_cases i <;>
    simp only [uu, chartState_10, chartState_11, chartState_12, extractX_10, extractX_11, extractX_12] <;>
    rfl
theorem xx_chartState (M : Matrix5) (i : Fin 3) : xx (chartState M) i = xX M i := by
  fin_cases i <;>
    simp only [xx, chartState_13, chartState_14, chartState_15, extractX_13, extractX_14, extractX_15] <;>
    rfl
theorem vv_chartState (M : Matrix5) (i : Fin 3) : vv (chartState M) i = vX M i := by
  fin_cases i <;>
    simp only [vv, chartState_16, chartState_17, chartState_18, extractX_16, extractX_17, extractX_18] <;>
    rfl
theorem qq_chartState (M : Matrix5) (i : Fin 3) : qq (chartState M) i = qX M i := by
  fin_cases i <;>
    simp only [qq, chartState_19, chartState_20, chartState_21, extractX_19, extractX_20, extractX_21] <;>
    rfl

/-- `chartState` 下的 `Dc` 就是 D119 的 `DX`。 -/
theorem Dc_chartState_eq_DX (M : Matrix5) (i j : Fin 3) :
    Dc (chartState M) i j = DX M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Dc, DX, chartState] <;> ring

/-- `chartState` 下的 `Sc` 就是 D119 的 `SX`。 -/
theorem Sc_chartState_eq_SX (M : Matrix5) (i j : Fin 3) :
    Sc (chartState M) i j = SX M i j := by
  simp only [Sc, SX, Dc_chartState_eq_DX, xx_chartState, qq_chartState]

/-- `chartState` 下的 `Oc` 就是 D119 的 `OX`（和式次序不同，`ring` 归一）。 -/
theorem Oc_chartState_eq_OX (M : Matrix5) (i j : Fin 3) :
    Oc (chartState M) i j = OX M i j := by
  simp only [Oc, Sc, OX, SX, Dc_chartState_eq_DX, xx_chartState, qq_chartState,
    uu_chartState, vv_chartState]
  ring

/-! ## 2. 15 个字段（全部由 D119 读数支付） -/

/-- **`SatFrame M → PhysicalBounds (chartState M)`**（15 个字段一次付清）。 -/
theorem physicalBounds_chartState (M : Matrix5) (h : SatFrame M) :
    PhysicalBounds (chartState M) where
  e_abs := by simpa only [ee, chartState_8, extractX_8] using eX_abs_le_one M h
  be_abs := by simpa only [be, chartState_9, extractX_9] using betaX_abs_le_one M h
  head_abs := by
    simpa only [pp, ee, be, chartState_7, chartState_8, chartState_9,
      extractX_7, extractX_8, extractX_9] using head_abs_le_one M h
  u_abs := by
    intro i; fin_cases i <;>
      simp only [uu, chartState_10, chartState_11, chartState_12,
        extractX_10, extractX_11, extractX_12] <;>
      first | exact uX_abs_le_one M h 0 | exact uX_abs_le_one M h 1 | exact uX_abs_le_one M h 2
  x_abs := by
    intro i; fin_cases i <;>
      simp only [xx, chartState_13, chartState_14, chartState_15,
        extractX_13, extractX_14, extractX_15] <;>
      first | exact xX_abs_le_one M h 0 | exact xX_abs_le_one M h 1 | exact xX_abs_le_one M h 2
  v_abs := by
    intro i; fin_cases i <;>
      simp only [vv, chartState_16, chartState_17, chartState_18,
        extractX_16, extractX_17, extractX_18] <;>
      first | exact vX_abs_le_one M h 0 | exact vX_abs_le_one M h 1 | exact vX_abs_le_one M h 2
  q_abs := by
    intro i; fin_cases i <;>
      simp only [qq, pp, chartState_7, chartState_19, chartState_20, chartState_21,
        extractX_7, extractX_19, extractX_20, extractX_21] <;>
      first | exact qX_abs_le_p M h 0 | exact qX_abs_le_p M h 1 | exact qX_abs_le_p M h 2
  L_abs := by
    intro i; fin_cases i <;>
      simp only [Lc, pp, xx, ee, uu, chartState_7, chartState_8, chartState_10, chartState_11,
        chartState_12, chartState_13, chartState_14, chartState_15, extractX_7, extractX_8,
        extractX_10, extractX_11, extractX_12, extractX_13, extractX_14, extractX_15] <;>
      first | exact LX_abs_le_one M h 0 | exact LX_abs_le_one M h 1 | exact LX_abs_le_one M h 2
  P_abs := by
    intro i; fin_cases i <;>
      simp only [Pc, qq, be, vv, chartState_9, chartState_16, chartState_17, chartState_18,
        chartState_19, chartState_20, chartState_21, extractX_9, extractX_16, extractX_17,
        extractX_18, extractX_19, extractX_20, extractX_21] <;>
      first | exact PX_abs_le_one M h 0 | exact PX_abs_le_one M h 1 | exact PX_abs_le_one M h 2
  D_abs := by
    intro i j
    have h1 : DX M i j ≤ kX M := DX_le_kX M h i j
    have h2 : -kX M ≤ DX M i j := neg_kX_le_DX M h i j
    have h3 : kk (chartState M) = kX M := kk_chartState M
    rw [Dc_chartState_eq_DX M i j, h3]
    exact abs_le.mpr ⟨h2, h1⟩
  S_abs := by
    intro i j
    have h1 : SX M i j ≤ pX M := SX_le_pX M h i j
    have h2 : -pX M ≤ SX M i j := neg_pX_le_SX M h i j
    have h3 : pp (chartState M) = pX M := pp_chartState M
    rw [Sc_chartState_eq_SX M i j, h3]
    exact abs_le.mpr ⟨h2, h1⟩
  O_abs := by
    intro i j
    have h1 : OX M i j ≤ 1 := OX_le_one M h i j
    have h2 : -1 ≤ OX M i j := neg_one_le_OX M h i j
    rw [Oc_chartState_eq_OX M i j]
    exact abs_le.mpr ⟨h2, h1⟩
  k_pos := by rw [kk_chartState, kX_eq_k]; exact h.hk
  r_pos := by rw [rr_chartState, rX_eq_r]; exact h.hr
  w_abs := by
    have hw : |T2 M 1 1| ≤ |T2 M 0 0| := h.cp4 1 1
    have hpos : (0 : ℝ) < T2 M 0 0 := h.hr
    rw [abs_of_pos hpos] at hw
    simpa only [ww_chartState, rr_chartState, wX, rX] using hw

/-! ## 3. 去掉 `PhysicalBounds` 前提的实际矩阵 106 行入口 -/

/-- **实际矩阵（`SatFrame`）的 106 行入口**：`PhysicalBounds` 已由上一条定理支付，
不再作为前提；`NormalizedSigns`/`HighValue`/`Rho4Input`/`SmallThirdPivot` 仍显式保留。 -/
theorem all_rows_sound_of_satFrame_noPhys (M : Matrix5) (h : SatFrame M)
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hrho : Rho4Input (chartState M)) (hk2 : SmallThirdPivot (chartState M)) :
    ∀ i, i ∈ paidIdx ∨ i = 96 ∨ i = 98 → RowProp i (chartState M) :=
  all_rows_sound_of_satFrame M h (physicalBounds_chartState M h) hs hF hrho hk2

end Rho5.Shared.XSmallKBranch
