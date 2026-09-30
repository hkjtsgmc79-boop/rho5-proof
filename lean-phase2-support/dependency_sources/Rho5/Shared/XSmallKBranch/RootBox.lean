import Rho5.Shared.XSmallKBranch.NoRho4

/-
D136 续（第四叶）— 原论文 §3.4 的精确 22 维根盒
====================================================

在**显式前提** `NormalizedSigns`、`0 < e`、`0 < β`、`0 ≤ u₀`、`F ≥ q_*`、`k ≤ 2`
（以及已付的 `PhysicalBounds` 与 D138 的 `F ≤ 4p`）下，**导出**模型根盒的 22 个坐标界；
本文件**不把根盒当假设**（`BoxIn` 是结论）。

推导来源（原文 §3.3–§3.4 + 冻结的 §3 结构性行）：
* `k ≥ 551/300` ← `Fcore`（`F ≤ 9k/4`）与 `F ≥ q_*`；
* `r ∈ [1653/800, 3147/800]` ← `|w| ≤ r`、`rAd`（`r ≤ k(1+d)`）、`d ≤ 1 − η`；
* `w ∈ [−2, −53/800]` ← `D₂₂` 带（`w + dB ≥ −k`）与 `w = r − F`；
* `A, B ≤ −53/400` ← §3.3 的 `B ≤ 2k − F`、`A − B ≤ 2k − F`；
* `c ≥ 53/400`、`d ∈ [53/800, 747/800]` ← (3.3) 的 `c − d ≥ η` 与 `d ≥ η`（由 (3.1)/(3.2) 与 `B−A ≤ k`、`−B ≤ k`）；
* `p ∈ [1653/1600, 2]` ← `F ≤ 4p`、`|p − eβ| ≤ 1` 与 `|e|,|β| ≤ 1`；
* `e, β ≥ 53/1600` ← `p − eβ ≤ 1`、`p ≥ q_*/4`、`β ≤ 1`（及对称）；
* `u₀ ∈ [0,1]`、`u₁,u₂,x,v ∈ [−1,1]`、`q ∈ [−2,2]` ← 物理带 + `p ≤ 2`。
-/
noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-- 原文 §2 的符号规范之外，本阶段显式保留的正性输入（`e > 0`、`β > 0`）。 -/
structure PosSigns (z : Z) : Prop where
  e_pos : 0 < ee z
  be_pos : 0 < be z

variable {M : Matrix5}

/-- 关键常数恒等式：`q_* = 4 + 2η`（`η = 53/800`）。 -/
theorem qstar_eq : (1653 / 400 : ℝ) = 4 + 2 * (53 / 800) := by norm_num

/-! ## 各坐标界 -/

theorem k_lower (h : SatFrame M) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : (551 / 300 : ℝ) ≤ kk (chartState M) := by
  have hc := Fcore_of_satFrame h
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

theorem r_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hF : HighValue (chartState M)) : (1653 / 800 : ℝ) ≤ rr (chartState M) := by
  have hw := (abs_le.mp hb.w_abs).1
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  linarith

theorem d_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : dd (chartState M) ≤ 747 / 800 := by
  have hcd := row_cd (chartState M) hb hs hF hk2
  have hc := c_le_one (chartState M) hb
  linarith

theorem r_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : rr (chartState M) ≤ 3147 / 800 := by
  have hrd := row_rAd (chartState M) hb hs
  have hdu := d_upper h hb hs hF hk2
  have h1 : rr (chartState M) ≤ kk (chartState M) * (1 + dd (chartState M)) := by linarith
  have h2 : (0 : ℝ) ≤ 1 + dd (chartState M) := by linarith [hs.d_nonneg]
  have h3 : kk (chartState M) * (1 + dd (chartState M)) ≤ 2 * (1 + dd (chartState M)) :=
    mul_le_mul_of_nonneg_right hk2 h2
  linarith

theorem w_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hk2 : SmallThirdPivot (chartState M)) :
    (-2 : ℝ) ≤ ww (chartState M) := by
  have h22 : -(kk (chartState M)) ≤ Dc (chartState M) 2 2 := (abs_le.mp (hb.D_abs 2 2)).1
  have hdB : dd (chartState M) * BB (chartState M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs.d_nonneg hs.B_nonpos
  rw [Dc_2_2] at h22
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

theorem w_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : ww (chartState M) ≤ -(53 / 800) := by
  have hru := r_upper h hb hs hF hk2
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  linarith

theorem d_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : (53 / 800 : ℝ) ≤ dd (chartState M) := by
  have hcb := core_bound_2 (chartState M) hb
  have hA : -(kk (chartState M)) ≤ AA (chartState M) := (abs_le.mp (hb.D_abs 0 1)).1
  have hBA : BB (chartState M) - AA (chartState M) ≤ kk (chartState M) := by
    linarith [hs.B_nonpos]
  have hdk : rr (chartState M) - ww (chartState M) - 2 * kk (chartState M)
      ≤ dd (chartState M) * kk (chartState M) := by
    have h1 : dd (chartState M) * (BB (chartState M) - AA (chartState M))
        ≤ dd (chartState M) * kk (chartState M) :=
      mul_le_mul_of_nonneg_left hBA hs.d_nonneg
    linarith
  have h2 : (53 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) - 2 * kk (chartState M) := by
    have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
    have hk' : kk (chartState M) ≤ 2 := hk2
    linarith
  have h3 : (53 / 400 : ℝ) ≤ dd (chartState M) * kk (chartState M) := le_trans h2 hdk
  have h4 : dd (chartState M) * kk (chartState M) ≤ dd (chartState M) * 2 :=
    mul_le_mul_of_nonneg_left hk2 hs.d_nonneg
  linarith

theorem c_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : (53 / 400 : ℝ) ≤ cc (chartState M) := by
  have hcd := row_cd (chartState M) hb hs hF hk2
  have hdl := d_lower h hb hs hF hk2
  linarith

theorem B_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : BB (chartState M) ≤ -(53 / 400) := by
  have hB := row_B (chartState M) hb hs hF hk2
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

theorem A_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : AA (chartState M) ≤ -(53 / 400) := by
  have hBA := row_BA (chartState M) hb hs hF hk2
  have hBu := B_upper h hb hs hF hk2
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

theorem p_lower (h : SatFrame M) (hF : HighValue (chartState M))
    (hrho : Rho4Input (chartState M)) : (1653 / 1600 : ℝ) ≤ pp (chartState M) := by
  have hF' : (1653 / 400 : ℝ) ≤ rr (chartState M) - ww (chartState M) := hF
  have hr : rr (chartState M) - ww (chartState M) ≤ 4 * pp (chartState M) := hrho
  linarith

theorem p_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hpos : PosSigns (chartState M)) : pp (chartState M) ≤ 2 := by
  have hhead : pp (chartState M) - ee (chartState M) * be (chartState M) ≤ 1 :=
    (abs_le.mp hb.head_abs).2
  have he1 : ee (chartState M) ≤ 1 := (abs_le.mp hb.e_abs).2
  have hb1 : be (chartState M) ≤ 1 := (abs_le.mp hb.be_abs).2
  have he0 : (0 : ℝ) ≤ ee (chartState M) := le_of_lt hpos.e_pos
  have hbe0 : (0 : ℝ) ≤ be (chartState M) := le_of_lt hpos.be_pos
  have h1 : ee (chartState M) * be (chartState M) ≤ 1 * be (chartState M) :=
    mul_le_mul_of_nonneg_right he1 hbe0
  have h2 : (1 : ℝ) * be (chartState M) ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb1 zero_le_one
  linarith

theorem e_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hpos : PosSigns (chartState M)) (hF : HighValue (chartState M))
    (hrho : Rho4Input (chartState M)) : (53 / 1600 : ℝ) ≤ ee (chartState M) := by
  have hhead : pp (chartState M) - ee (chartState M) * be (chartState M) ≤ 1 :=
    (abs_le.mp hb.head_abs).2
  have hpl := p_lower h hF hrho
  have hb1 : be (chartState M) ≤ 1 := (abs_le.mp hb.be_abs).2
  have hebe : ee (chartState M) * be (chartState M) ≤ ee (chartState M) * 1 :=
    mul_le_mul_of_nonneg_left hb1 (le_of_lt hpos.e_pos)
  linarith

theorem be_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hpos : PosSigns (chartState M)) (hF : HighValue (chartState M))
    (hrho : Rho4Input (chartState M)) : (53 / 1600 : ℝ) ≤ be (chartState M) := by
  have hhead : pp (chartState M) - ee (chartState M) * be (chartState M) ≤ 1 :=
    (abs_le.mp hb.head_abs).2
  have hpl := p_lower h hF hrho
  have he1 : ee (chartState M) ≤ 1 := (abs_le.mp hb.e_abs).2
  have hebe : ee (chartState M) * be (chartState M) ≤ 1 * be (chartState M) :=
    mul_le_mul_of_nonneg_right he1 (le_of_lt hpos.be_pos)
  linarith

/-- `q_i ≥ −2`（由 `|q_i| ≤ p ≤ 2`）。 -/
theorem q_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hpos : PosSigns (chartState M)) (i : Fin 3) : (-2 : ℝ) ≤ qq (chartState M) i := by
  have h1 : -pp (chartState M) ≤ qq (chartState M) i := (abs_le.mp (hb.q_abs i)).1
  have hp2 : pp (chartState M) ≤ 2 := p_upper h hb hpos
  linarith

/-- `q_i ≤ 2`（由 `|q_i| ≤ p ≤ 2`）。 -/
theorem q_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hpos : PosSigns (chartState M)) (i : Fin 3) : qq (chartState M) i ≤ 2 := by
  have h2 : qq (chartState M) i ≤ pp (chartState M) := (abs_le.mp (hb.q_abs i)).2
  have hp2 : pp (chartState M) ≤ 2 := p_upper h hb hpos
  linarith

/-! ## 22 维根盒 -/

theorem k_upper (hk2 : SmallThirdPivot (chartState M)) : kk (chartState M) ≤ 2 := hk2

theorem c_upper (h : SatFrame M) (hb : PhysicalBounds (chartState M)) :
    cc (chartState M) ≤ 1 := c_le_one (chartState M) hb

theorem A_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : (-2 : ℝ) ≤ AA (chartState M) := by
  have hA := (abs_le.mp (hb.D_abs 0 1)).1
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

theorem B_lower (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : (-2 : ℝ) ≤ BB (chartState M) := by
  have hB := (abs_le.mp (hb.D_abs 0 2)).1
  have hk' : kk (chartState M) ≤ 2 := hk2
  linarith

/-- **§3.4 根盒**：在显式前提（符号规范、`e,β > 0`、`u₀ ≥ 0`、高值、`k ≤ 2`、`F ≤ 4p`）
下，实际矩阵的 chart 状态落在模型根盒内。**本定理不假设根盒**。 -/
theorem rootBox_chartState (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hpos : PosSigns (chartState M))
    (hu0 : 0 ≤ uu (chartState M) 0) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) (hrho : Rho4Input (chartState M)) :
    BoxIn (chartState M) := by
  intro j
  fin_cases j
  · norm_num [boxLo, boxHi]
    exact ⟨k_lower h hF hk2, hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨r_lower h hb hF, r_upper h hb hs hF hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨w_lower h hb hs hk2, w_upper h hb hs hF hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨A_lower h hb hk2, A_upper h hb hs hF hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨B_lower h hb hk2, B_upper h hb hs hF hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨c_lower h hb hs hF hk2, c_upper h hb⟩
  · norm_num [boxLo, boxHi]
    exact ⟨d_lower h hb hs hF hk2, d_upper h hb hs hF hk2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨p_lower h hF hrho, p_upper h hb hpos⟩
  · norm_num [boxLo, boxHi]
    exact ⟨e_lower h hb hpos hF hrho, (abs_le.mp hb.e_abs).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨be_lower h hb hpos hF hrho, (abs_le.mp hb.be_abs).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨hu0, (abs_le.mp (hb.u_abs 0)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.u_abs 1)).1, (abs_le.mp (hb.u_abs 1)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.u_abs 2)).1, (abs_le.mp (hb.u_abs 2)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.x_abs 0)).1, (abs_le.mp (hb.x_abs 0)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.x_abs 1)).1, (abs_le.mp (hb.x_abs 1)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.x_abs 2)).1, (abs_le.mp (hb.x_abs 2)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.v_abs 0)).1, (abs_le.mp (hb.v_abs 0)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.v_abs 1)).1, (abs_le.mp (hb.v_abs 1)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨(abs_le.mp (hb.v_abs 2)).1, (abs_le.mp (hb.v_abs 2)).2⟩
  · norm_num [boxLo, boxHi]
    exact ⟨q_lower h hb hpos 0, q_upper h hb hpos 0⟩
  · norm_num [boxLo, boxHi]
    exact ⟨q_lower h hb hpos 1, q_upper h hb hpos 1⟩
  · norm_num [boxLo, boxHi]
    exact ⟨q_lower h hb hpos 2, q_upper h hb hpos 2⟩

/-- **不依赖 D138 的 106 行入口 + 根盒**（`Rho4Input` 由 D138 薄适配内部支付）。 -/
theorem rootBox_chartState_noRho4 (h : SatFrame M) (hb : PhysicalBounds (chartState M))
    (hs : NormalizedSigns (chartState M)) (hpos : PosSigns (chartState M))
    (hu0 : 0 ≤ uu (chartState M) 0) (hF : HighValue (chartState M))
    (hk2 : SmallThirdPivot (chartState M)) : BoxIn (chartState M) :=
  rootBox_chartState h hb hs hpos hu0 hF hk2 (rho4Input_chartState M h hF)

end Rho5.Shared.XSmallKBranch
