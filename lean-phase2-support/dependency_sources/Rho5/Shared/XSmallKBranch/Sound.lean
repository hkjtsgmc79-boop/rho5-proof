import Rho5.Shared.XSmallKBranch.Model
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-
D136 — V31 源行 soundness（实际 X chart ⇒ 精确模型行）
=====================================================

* 状态 `z : Fin 57 → ℝ`：前 22 个分量是原模型变量（顺序与 `Model.varNames` 一致），
  后 35 个是**共享乘积变量**（`22 + i` 对应 `productPairs[i]`）。
  这是 D135 侧通用格式所需的提升形态；`IsLift` 说明乘积变量确实取真实乘积。
* `PhysicalBounds`：原论文 §1 式 (1.2)–(1.3) 的物理带（chart 表达式上），
  逐元素写在**实际状态**上，不是行的复述。
* `RowProp i`：第 `i` 条源行的 LP 语义（`rows` 的左右端，精确有理数）。
* `paid_rows_sound`：**104/106** 行由 `PhysicalBounds`（及显式声明的分支输入）推出；
  未付两行 `Fcore`/`det3` 见 `unpaidIdx`，其所需证明（§3.1 恒等式、§3.2 行列式界）尚未形式化。
* 显式声明的输入（不隐藏）：`HighValue`（原文 `F ≥ q_*`）、`Rho4Input`（原文 §1.1 的 `F ≤ 4p`，
  唯一外部低阶输入 ρ₄=4）、`NormalizedSigns`（原文 §2 的合法符号规范输出：`A,B ≤ 0 ≤ c,d`）、
  `SmallThirdPivot`（原文 §6 第 1 块假设 `0 < k ≤ 2`）。
-/

noncomputable section
namespace Rho5.Shared.XSmallKBranch

open Rho5

/-- 提升状态：22 个模型变量 + 35 个共享乘积变量。 -/
abbrev Z := Fin 57 → ℝ

abbrev kk (z : Z) : ℝ := z 0
abbrev rr (z : Z) : ℝ := z 1
abbrev ww (z : Z) : ℝ := z 2
abbrev AA (z : Z) : ℝ := z 3
abbrev BB (z : Z) : ℝ := z 4
abbrev cc (z : Z) : ℝ := z 5
abbrev dd (z : Z) : ℝ := z 6
abbrev pp (z : Z) : ℝ := z 7
abbrev ee (z : Z) : ℝ := z 8
abbrev be (z : Z) : ℝ := z 9
/-- 四组三维坐标：按**字面量**模式匹配定义，使 `uu z 0` 与模型行的 `z 10` 归约到同一形式。 -/
abbrev uu (z : Z) : Fin 3 → ℝ
  | 0 => z 10
  | 1 => z 11
  | 2 => z 12

abbrev xx (z : Z) : Fin 3 → ℝ
  | 0 => z 13
  | 1 => z 14
  | 2 => z 15

abbrev vv (z : Z) : Fin 3 → ℝ
  | 0 => z 16
  | 1 => z 17
  | 2 => z 18

abbrev qq (z : Z) : Fin 3 → ℝ
  | 0 => z 19
  | 1 => z 20
  | 2 => z 21

/-- 原论文式 (1.2) 的三个 chart 组合：`L = p x - e u`、`P = q + β v`、`S = D + x qᵀ`、`O = S + u vᵀ`。 -/
abbrev Lc (z : Z) (i : Fin 3) : ℝ := pp z * xx z i - ee z * uu z i
abbrev Pc (z : Z) (i : Fin 3) : ℝ := qq z i + be z * vv z i

/-- 原论文式 (1.3) 的核心 3×3 块 `D`（未缩放 `A,B` 形式，故行至多二次）。 -/
abbrev Dc (z : Z) : Fin 3 → Fin 3 → ℝ
  | 0, 0 => kk z
  | 0, 1 => AA z
  | 0, 2 => BB z
  | 1, 0 => cc z * kk z
  | 1, 1 => rr z + cc z * AA z
  | 1, 2 => rr z + cc z * BB z
  | 2, 0 => dd z * kk z
  | 2, 1 => rr z + dd z * AA z
  | 2, 2 => ww z + dd z * BB z

abbrev Sc (z : Z) (i j : Fin 3) : ℝ := Dc z i j + xx z i * qq z j
abbrev Oc (z : Z) (i j : Fin 3) : ℝ := Sc z i j + uu z i * vv z j

/-- **共享乘积提升**：第 `22+i` 个分量确实是 `productPairs[i]` 的真实乘积。 -/
structure IsLift (z : Z) : Prop where
  lift_x2_q2 : z 22 = xx z 2 * qq z 2
  lift_x2_q1 : z 23 = xx z 2 * qq z 1
  lift_x2_q0 : z 24 = xx z 2 * qq z 0
  lift_x1_q2 : z 25 = xx z 1 * qq z 2
  lift_x1_q1 : z 26 = xx z 1 * qq z 1
  lift_x1_q0 : z 27 = xx z 1 * qq z 0
  lift_x0_q2 : z 28 = xx z 0 * qq z 2
  lift_x0_q1 : z 29 = xx z 0 * qq z 1
  lift_x0_q0 : z 30 = xx z 0 * qq z 0
  lift_u2_v2 : z 31 = uu z 2 * vv z 2
  lift_u2_v1 : z 32 = uu z 2 * vv z 1
  lift_u2_v0 : z 33 = uu z 2 * vv z 0
  lift_u1_v2 : z 34 = uu z 1 * vv z 2
  lift_u1_v1 : z 35 = uu z 1 * vv z 1
  lift_u1_v0 : z 36 = uu z 1 * vv z 0
  lift_u0_v2 : z 37 = uu z 0 * vv z 2
  lift_u0_v1 : z 38 = uu z 0 * vv z 1
  lift_u0_v0 : z 39 = uu z 0 * vv z 0
  lift_be_v2 : z 40 = be z * vv z 2
  lift_be_v1 : z 41 = be z * vv z 1
  lift_be_v0 : z 42 = be z * vv z 0
  lift_e_u2 : z 43 = ee z * uu z 2
  lift_e_u1 : z 44 = ee z * uu z 1
  lift_e_u0 : z 45 = ee z * uu z 0
  lift_e_be : z 46 = ee z * be z
  lift_p_x2 : z 47 = pp z * xx z 2
  lift_p_x1 : z 48 = pp z * xx z 1
  lift_p_x0 : z 49 = pp z * xx z 0
  lift_B_d : z 50 = BB z * dd z
  lift_B_c : z 51 = BB z * cc z
  lift_A_d : z 52 = AA z * dd z
  lift_A_c : z 53 = AA z * cc z
  lift_k_p : z 54 = kk z * pp z
  lift_k_d : z 55 = kk z * dd z
  lift_k_c : z 56 = kk z * cc z

/-- **物理带（原论文 §1 式 (1.2)–(1.3)）**，写在 chart 表达式上。 -/
structure PhysicalBounds (z : Z) : Prop where
  e_abs : |ee z| ≤ 1
  be_abs : |be z| ≤ 1
  head_abs : |pp z - ee z * be z| ≤ 1
  u_abs : ∀ i, |uu z i| ≤ 1
  x_abs : ∀ i, |xx z i| ≤ 1
  v_abs : ∀ i, |vv z i| ≤ 1
  q_abs : ∀ i, |qq z i| ≤ pp z
  L_abs : ∀ i, |Lc z i| ≤ 1
  P_abs : ∀ i, |Pc z i| ≤ 1
  D_abs : ∀ i j, |Dc z i j| ≤ kk z
  S_abs : ∀ i j, |Sc z i j| ≤ pp z
  O_abs : ∀ i j, |Oc z i j| ≤ 1
  k_pos : 0 < kk z
  r_pos : 0 < rr z
  w_abs : |ww z| ≤ rr z

/-- 原文 §2 的合法符号规范输出（本模块**显式声明为输入**，其 §2 论证尚未形式化）。 -/
structure NormalizedSigns (z : Z) : Prop where
  A_nonpos : AA z ≤ 0
  B_nonpos : BB z ≤ 0
  c_nonneg : 0 ≤ cc z
  d_nonneg : 0 ≤ dd z

/-- 原文 §6 第 1 块的高值分支假设 `F ≥ q_* = 1653/400`。 -/
abbrev HighValue (z : Z) : Prop := (1653 / 400 : ℝ) ≤ rr z - ww z

/-- 原文 §1.1 的**唯一外部低阶输入** ρ₄=4 的实例形态 `F ≤ 4p`。 -/
abbrev Rho4Input (z : Z) : Prop := rr z - ww z ≤ 4 * pp z

/-- 原文 §6 第 1 块的第三主元范围 `0 < k ≤ 2`（`0 < k` 亦在 `PhysicalBounds` 中）。 -/
abbrev SmallThirdPivot (z : Z) : Prop := kk z ≤ 2

/-! ## `Dc` 的九条定义方程（`rfl`）与结构性行引理（原文 §3） -/

theorem Dc_0_0 (z : Z) : Dc z 0 0 = kk z := rfl
theorem Dc_0_1 (z : Z) : Dc z 0 1 = AA z := rfl
theorem Dc_0_2 (z : Z) : Dc z 0 2 = BB z := rfl
theorem Dc_1_0 (z : Z) : Dc z 1 0 = cc z * kk z := rfl
theorem Dc_1_1 (z : Z) : Dc z 1 1 = rr z + cc z * AA z := rfl
theorem Dc_1_2 (z : Z) : Dc z 1 2 = rr z + cc z * BB z := rfl
theorem Dc_2_0 (z : Z) : Dc z 2 0 = dd z * kk z := rfl
theorem Dc_2_1 (z : Z) : Dc z 2 1 = rr z + dd z * AA z := rfl
theorem Dc_2_2 (z : Z) : Dc z 2 2 = ww z + dd z * BB z := rfl

/-- 原文 (3.1)：`(c-d)(-B) - (F-2k) = (k - D₁₂) + (k + D₂₂)`（恒等式）。 -/
theorem core_identity_1 (z : Z) :
    (cc z - dd z) * (-BB z) - (rr z - ww z - 2 * kk z)
      = (kk z - Dc z 1 2) + (kk z + Dc z 2 2) := by
  rw [Dc_1_2, Dc_2_2]; ring

/-- 原文 (3.2)：`d(B-A) - (F-2k) = (k - D₂₁) + (k + D₂₂)`（恒等式）。 -/
theorem core_identity_2 (z : Z) :
    dd z * (BB z - AA z) - (rr z - ww z - 2 * kk z)
      = (kk z - Dc z 2 1) + (kk z + Dc z 2 2) := by
  rw [Dc_2_1, Dc_2_2]; ring

/-- 由 (3.1) 与 `|D₁₂|,|D₂₂| ≤ k` 得 `F - 2k ≤ (c-d)(-B)`。 -/
theorem core_bound_1 (z : Z) (hb : PhysicalBounds z) :
    rr z - ww z - 2 * kk z ≤ (cc z - dd z) * (-BB z) := by
  have h1 : 0 ≤ kk z - Dc z 1 2 := by linarith [(abs_le.mp (hb.D_abs 1 2)).2]
  have h2 : 0 ≤ kk z + Dc z 2 2 := by linarith [(abs_le.mp (hb.D_abs 2 2)).1]
  linarith [core_identity_1 z]

/-- 由 (3.2) 与 `|D₂₁|,|D₂₂| ≤ k` 得 `F - 2k ≤ d(B-A)`。 -/
theorem core_bound_2 (z : Z) (hb : PhysicalBounds z) :
    rr z - ww z - 2 * kk z ≤ dd z * (BB z - AA z) := by
  have h1 : 0 ≤ kk z - Dc z 2 1 := by linarith [(abs_le.mp (hb.D_abs 2 1)).2]
  have h2 : 0 ≤ kk z + Dc z 2 2 := by linarith [(abs_le.mp (hb.D_abs 2 2)).1]
  linarith [core_identity_2 z]

/-- 高值分支 + `k ≤ 2` ⇒ `F - 2k > 0`（`q_* = 1653/400 > 4 ≥ 2k`）。 -/
theorem F_sub_two_k_pos (z : Z) (hF : HighValue z) (hk2 : SmallThirdPivot z) :
    0 < rr z - ww z - 2 * kk z := by
  have h1 : (1653 / 400 : ℝ) ≤ rr z - ww z := hF
  have h2 : kk z ≤ 2 := hk2
  linarith

/-- `c ≤ 1`（由 `|D₁₀| = |c·k| ≤ k` 与 `k > 0`）。 -/
theorem c_le_one (z : Z) (hb : PhysicalBounds z) : cc z ≤ 1 := by
  have h : cc z * kk z ≤ (1 : ℝ) * kk z := by
    simpa using (abs_le.mp (hb.D_abs 1 0)).2
  exact le_of_mul_le_mul_right h hb.k_pos

/-- `d ≤ 1`（由 `|D₂₀| = |d·k| ≤ k` 与 `k > 0`）。 -/
theorem d_le_one (z : Z) (hb : PhysicalBounds z) : dd z ≤ 1 := by
  have h : dd z * kk z ≤ (1 : ℝ) * kk z := by
    simpa using (abs_le.mp (hb.D_abs 2 0)).2
  exact le_of_mul_le_mul_right h hb.k_pos

/-- 行 `r+w`：`r + w ≥ 0`（来自 `|w| ≤ r`）。 -/
theorem row_r_add_w (z : Z) (hb : PhysicalBounds z) : 0 ≤ rr z + ww z := by
  have h := (abs_le.mp hb.w_abs).1
  linarith

/-- 行 `rAd`：`r ≤ k(1+d)`（原文 (3.6)：`k(1+d) - r = (k - D₂₁) + d(k + A)`）。 -/
theorem row_rAd (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z) :
    0 ≤ dd z * kk z + kk z - rr z := by
  have hD : Dc z 2 1 ≤ kk z := (abs_le.mp (hb.D_abs 2 1)).2
  have hA : -kk z ≤ AA z := (abs_le.mp (hb.D_abs 0 1)).1
  have h1 : 0 ≤ kk z - Dc z 2 1 := by linarith
  have h2 : 0 ≤ kk z + AA z := by linarith
  have hid : dd z * kk z + kk z - rr z = (kk z - Dc z 2 1) + dd z * (kk z + AA z) := by
    rw [Dc_2_1]; ring
  rw [hid]; exact add_nonneg h1 (mul_nonneg hs.d_nonneg h2)

/-- 行 `rBc`：`B ≤ k - r`（原文 (3.6)：`k - B - r = (k - D₁₂) + (1-c)(-B)`）。 -/
theorem row_rBc (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z) :
    0 ≤ -BB z + kk z - rr z := by
  have hD : Dc z 1 2 ≤ kk z := (abs_le.mp (hb.D_abs 1 2)).2
  have hc : cc z ≤ 1 := c_le_one z hb
  have h1 : 0 ≤ kk z - Dc z 1 2 := by linarith
  have h2 : 0 ≤ (1 - cc z) * (-BB z) := mul_nonneg (by linarith) (by linarith [hs.B_nonpos])
  have hid : -BB z + kk z - rr z = (kk z - Dc z 1 2) + (1 - cc z) * (-BB z) := by
    rw [Dc_1_2]; ring
  rw [hid]; exact add_nonneg h1 h2

/-- 行 `rAc`：`A ≤ k - r`（原文 (3.6)：`k - A - r = (k - D₁₁) + (1-c)(-A)`）。 -/
theorem row_rAc (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z) :
    0 ≤ -AA z + kk z - rr z := by
  have hD : Dc z 1 1 ≤ kk z := (abs_le.mp (hb.D_abs 1 1)).2
  have hc : cc z ≤ 1 := c_le_one z hb
  have h1 : 0 ≤ kk z - Dc z 1 1 := by linarith
  have h2 : 0 ≤ (1 - cc z) * (-AA z) := mul_nonneg (by linarith) (by linarith [hs.A_nonpos])
  have hid : -AA z + kk z - rr z = (kk z - Dc z 1 1) + (1 - cc z) * (-AA z) := by
    rw [Dc_1_1]; ring
  rw [hid]; exact add_nonneg h1 h2

/-- 行 `B`：`B ≤ 2k - F`（(3.1) + `0 ≤ c-d ≤ 1` 与 `B ≤ 0`）。 -/
theorem row_B (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z)
    (hF : HighValue z) (hk2 : SmallThirdPivot z) :
    0 ≤ -BB z + 2 * kk z - rr z + ww z := by
  have hpos : 0 < rr z - ww z - 2 * kk z := F_sub_two_k_pos z hF hk2
  have hkey := core_bound_1 z hb
  have hB0 : 0 ≤ -BB z := by linarith [hs.B_nonpos]
  have hprod : 0 < (cc z - dd z) * (-BB z) := lt_of_lt_of_le hpos hkey
  have hcd : 0 < cc z - dd z := by
    by_contra h
    push_neg at h
    have : (cc z - dd z) * (-BB z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hB0
    linarith
  have hcd1 : cc z - dd z ≤ 1 := by have h := c_le_one z hb; linarith [hs.d_nonneg]
  have hle : (cc z - dd z) * (-BB z) ≤ -BB z := by
    have := mul_le_mul_of_nonneg_right hcd1 hB0
    simpa using this
  linarith

/-- 行 `B-A`：`B - A ≥ F - 2k`（(3.2) + `0 < d ≤ 1`）。 -/
theorem row_BA (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z)
    (hF : HighValue z) (hk2 : SmallThirdPivot z) :
    0 ≤ -AA z + BB z + 2 * kk z - rr z + ww z := by
  have hpos : 0 < rr z - ww z - 2 * kk z := F_sub_two_k_pos z hF hk2
  have hkey := core_bound_2 z hb
  have hd0 : 0 ≤ dd z := hs.d_nonneg
  have hprod : 0 < dd z * (BB z - AA z) := lt_of_lt_of_le hpos hkey
  have hBA : 0 < BB z - AA z := by
    by_contra h
    push_neg at h
    have : dd z * (BB z - AA z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd0 h
    linarith
  have hd1 : dd z ≤ 1 := d_le_one z hb
  have hle : dd z * (BB z - AA z) ≤ BB z - AA z := by
    have := mul_le_mul_of_nonneg_right hd1 (le_of_lt hBA)
    simpa using this
  linarith

/-- 行 `cd`：`c - d ≥ η = 53/800`（原文 (3.3)：`b(c-d) ≥ F/k - 2 ≥ η`）。 -/
theorem row_cd (z : Z) (hb : PhysicalBounds z) (hs : NormalizedSigns z)
    (hF : HighValue z) (hk2 : SmallThirdPivot z) :
    0 ≤ cc z - dd z - (53 / 800 : ℝ) := by
  have hpos : 0 < rr z - ww z - 2 * kk z := F_sub_two_k_pos z hF hk2
  have hkey := core_bound_1 z hb
  have hB0 : 0 ≤ -BB z := by linarith [hs.B_nonpos]
  have hprod : 0 < (cc z - dd z) * (-BB z) := lt_of_lt_of_le hpos hkey
  have hcd : 0 < cc z - dd z := by
    by_contra h
    push_neg at h
    have : (cc z - dd z) * (-BB z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hB0
    linarith
  have hnegB : 0 < -BB z := by
    by_contra h
    push_neg at h
    have : (cc z - dd z) * (-BB z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hcd) h
    linarith
  have hBle : -BB z ≤ kk z := by
    have h := (abs_le.mp (hb.D_abs 0 2)).1
    rw [Dc_0_2] at h
    linarith
  by_contra h
  push_neg at h
  have hcdlt : cc z - dd z < (53 / 800 : ℝ) := by linarith
  have h1 : (cc z - dd z) * (-BB z) < (53 / 800 : ℝ) * (-BB z) :=
    mul_lt_mul_of_pos_right hcdlt hnegB
  have h2 : (53 / 800 : ℝ) * (-BB z) ≤ (53 / 800 : ℝ) * kk z :=
    mul_le_mul_of_nonneg_left hBle (by norm_num)
  have h3 : (53 / 800 : ℝ) * kk z ≤ (53 / 800 : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hk2 (by norm_num)
  have h4 : (53 / 800 : ℝ) * 2 < rr z - ww z - 2 * kk z := by
    have h5 : (1653 / 400 : ℝ) ≤ rr z - ww z := hF
    have h6 : kk z ≤ 2 := hk2
    linarith
  linarith

/-! ## 四条 McCormick 外包（原文 (5.1)）的 soundness -/

/-- 四条外包：对区间内的两个真实数与真实乘积同时成立。 -/
structure McCormick (x y lx ux ly uy : ℝ) : Prop where
  ll : ly * x + lx * y - x * y ≤ lx * ly
  uu : uy * x + ux * y - x * y ≤ ux * uy
  ul : -uy * x - lx * y + x * y ≤ -lx * uy
  lu : -ly * x - ux * y + x * y ≤ -ux * ly

/-- **McCormick soundness**：`x ∈ [lx,ux]`、`y ∈ [ly,uy]`、`z = x*y` ⇒ 四条外包全成立。
每条都是两个非负因子之积（原文 §5 的说明）。 -/
theorem mccormick_of_bounds {x y lx ux ly uy : ℝ}
    (hx : lx ≤ x) (hx' : x ≤ ux) (hy : ly ≤ y) (hy' : y ≤ uy) :
    McCormick x y lx ux ly uy where
  ll := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  uu := by nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy')]
  ul := by nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr hy)]
  lu := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy')]


open Rho5.Shared.XSmallKBranch in

/-! ## 根盒与共享乘积的 McCormick 实例 -/

/-- 根盒下端点（22 个坐标，精确有理数，来自 `Model.rootLo`）。 -/
def boxLo : Fin 22 → ℚ
  | 0 => (551 / 300 : ℚ)
  | 1 => (1653 / 800 : ℚ)
  | 2 => (-2 / 1 : ℚ)
  | 3 => (-2 / 1 : ℚ)
  | 4 => (-2 / 1 : ℚ)
  | 5 => (53 / 400 : ℚ)
  | 6 => (53 / 800 : ℚ)
  | 7 => (1653 / 1600 : ℚ)
  | 8 => (53 / 1600 : ℚ)
  | 9 => (53 / 1600 : ℚ)
  | 10 => (0 / 1 : ℚ)
  | 11 => (-1 / 1 : ℚ)
  | 12 => (-1 / 1 : ℚ)
  | 13 => (-1 / 1 : ℚ)
  | 14 => (-1 / 1 : ℚ)
  | 15 => (-1 / 1 : ℚ)
  | 16 => (-1 / 1 : ℚ)
  | 17 => (-1 / 1 : ℚ)
  | 18 => (-1 / 1 : ℚ)
  | 19 => (-2 / 1 : ℚ)
  | 20 => (-2 / 1 : ℚ)
  | 21 => (-2 / 1 : ℚ)
  | _ => 0

/-- 根盒上端点。 -/
def boxHi : Fin 22 → ℚ
  | 0 => (2 / 1 : ℚ)
  | 1 => (3147 / 800 : ℚ)
  | 2 => (-53 / 800 : ℚ)
  | 3 => (-53 / 400 : ℚ)
  | 4 => (-53 / 400 : ℚ)
  | 5 => (1 / 1 : ℚ)
  | 6 => (747 / 800 : ℚ)
  | 7 => (2 / 1 : ℚ)
  | 8 => (1 / 1 : ℚ)
  | 9 => (1 / 1 : ℚ)
  | 10 => (1 / 1 : ℚ)
  | 11 => (1 / 1 : ℚ)
  | 12 => (1 / 1 : ℚ)
  | 13 => (1 / 1 : ℚ)
  | 14 => (1 / 1 : ℚ)
  | 15 => (1 / 1 : ℚ)
  | 16 => (1 / 1 : ℚ)
  | 17 => (1 / 1 : ℚ)
  | 18 => (1 / 1 : ℚ)
  | 19 => (2 / 1 : ℚ)
  | 20 => (2 / 1 : ℚ)
  | 21 => (2 / 1 : ℚ)
  | _ => 0

/-- 状态落在根盒内（对 22 个变量）。 -/
def BoxIn (z : Z) : Prop := ∀ j : Fin 22, (boxLo j : ℝ) ≤ z ⟨j.1, by omega⟩ ∧ z ⟨j.1, by omega⟩ ≤ (boxHi j : ℝ)

/-- **35 个共享乘积的四条外包实例**：盒内 + 真实乘积 ⇒ 每个 `y_ij` 满足 (5.1)。 -/
theorem envelope_0 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 15) (z 21) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ)
      ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) := by
  have ha := hbox ⟨15, by omega⟩
  have hb' := hbox ⟨21, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_1 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 15) (z 20) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ)
      ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) := by
  have ha := hbox ⟨15, by omega⟩
  have hb' := hbox ⟨20, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_2 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 15) (z 19) ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ)
      ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) := by
  have ha := hbox ⟨15, by omega⟩
  have hb' := hbox ⟨19, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_3 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 14) (z 21) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ)
      ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) := by
  have ha := hbox ⟨14, by omega⟩
  have hb' := hbox ⟨21, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_4 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 14) (z 20) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ)
      ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) := by
  have ha := hbox ⟨14, by omega⟩
  have hb' := hbox ⟨20, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_5 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 14) (z 19) ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ)
      ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) := by
  have ha := hbox ⟨14, by omega⟩
  have hb' := hbox ⟨19, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_6 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 13) (z 21) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ)
      ((boxLo 21 : ℚ) : ℝ) ((boxHi 21 : ℚ) : ℝ) := by
  have ha := hbox ⟨13, by omega⟩
  have hb' := hbox ⟨21, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_7 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 13) (z 20) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ)
      ((boxLo 20 : ℚ) : ℝ) ((boxHi 20 : ℚ) : ℝ) := by
  have ha := hbox ⟨13, by omega⟩
  have hb' := hbox ⟨20, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_8 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 13) (z 19) ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ)
      ((boxLo 19 : ℚ) : ℝ) ((boxHi 19 : ℚ) : ℝ) := by
  have ha := hbox ⟨13, by omega⟩
  have hb' := hbox ⟨19, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_9 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 12) (z 18) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ)
      ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) := by
  have ha := hbox ⟨12, by omega⟩
  have hb' := hbox ⟨18, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_10 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 12) (z 17) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ)
      ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) := by
  have ha := hbox ⟨12, by omega⟩
  have hb' := hbox ⟨17, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_11 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 12) (z 16) ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ)
      ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) := by
  have ha := hbox ⟨12, by omega⟩
  have hb' := hbox ⟨16, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_12 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 11) (z 18) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ)
      ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) := by
  have ha := hbox ⟨11, by omega⟩
  have hb' := hbox ⟨18, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_13 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 11) (z 17) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ)
      ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) := by
  have ha := hbox ⟨11, by omega⟩
  have hb' := hbox ⟨17, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_14 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 11) (z 16) ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ)
      ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) := by
  have ha := hbox ⟨11, by omega⟩
  have hb' := hbox ⟨16, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_15 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 10) (z 18) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ)
      ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) := by
  have ha := hbox ⟨10, by omega⟩
  have hb' := hbox ⟨18, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_16 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 10) (z 17) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ)
      ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) := by
  have ha := hbox ⟨10, by omega⟩
  have hb' := hbox ⟨17, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_17 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 10) (z 16) ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ)
      ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) := by
  have ha := hbox ⟨10, by omega⟩
  have hb' := hbox ⟨16, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_18 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 9) (z 18) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ)
      ((boxLo 18 : ℚ) : ℝ) ((boxHi 18 : ℚ) : ℝ) := by
  have ha := hbox ⟨9, by omega⟩
  have hb' := hbox ⟨18, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_19 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 9) (z 17) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ)
      ((boxLo 17 : ℚ) : ℝ) ((boxHi 17 : ℚ) : ℝ) := by
  have ha := hbox ⟨9, by omega⟩
  have hb' := hbox ⟨17, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_20 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 9) (z 16) ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ)
      ((boxLo 16 : ℚ) : ℝ) ((boxHi 16 : ℚ) : ℝ) := by
  have ha := hbox ⟨9, by omega⟩
  have hb' := hbox ⟨16, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_21 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 8) (z 12) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ)
      ((boxLo 12 : ℚ) : ℝ) ((boxHi 12 : ℚ) : ℝ) := by
  have ha := hbox ⟨8, by omega⟩
  have hb' := hbox ⟨12, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_22 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 8) (z 11) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ)
      ((boxLo 11 : ℚ) : ℝ) ((boxHi 11 : ℚ) : ℝ) := by
  have ha := hbox ⟨8, by omega⟩
  have hb' := hbox ⟨11, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_23 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 8) (z 10) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ)
      ((boxLo 10 : ℚ) : ℝ) ((boxHi 10 : ℚ) : ℝ) := by
  have ha := hbox ⟨8, by omega⟩
  have hb' := hbox ⟨10, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_24 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 8) (z 9) ((boxLo 8 : ℚ) : ℝ) ((boxHi 8 : ℚ) : ℝ)
      ((boxLo 9 : ℚ) : ℝ) ((boxHi 9 : ℚ) : ℝ) := by
  have ha := hbox ⟨8, by omega⟩
  have hb' := hbox ⟨9, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_25 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 7) (z 15) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ)
      ((boxLo 15 : ℚ) : ℝ) ((boxHi 15 : ℚ) : ℝ) := by
  have ha := hbox ⟨7, by omega⟩
  have hb' := hbox ⟨15, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_26 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 7) (z 14) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ)
      ((boxLo 14 : ℚ) : ℝ) ((boxHi 14 : ℚ) : ℝ) := by
  have ha := hbox ⟨7, by omega⟩
  have hb' := hbox ⟨14, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_27 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 7) (z 13) ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ)
      ((boxLo 13 : ℚ) : ℝ) ((boxHi 13 : ℚ) : ℝ) := by
  have ha := hbox ⟨7, by omega⟩
  have hb' := hbox ⟨13, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_28 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 4) (z 6) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ)
      ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) := by
  have ha := hbox ⟨4, by omega⟩
  have hb' := hbox ⟨6, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_29 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 4) (z 5) ((boxLo 4 : ℚ) : ℝ) ((boxHi 4 : ℚ) : ℝ)
      ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) := by
  have ha := hbox ⟨4, by omega⟩
  have hb' := hbox ⟨5, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_30 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 3) (z 6) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ)
      ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) := by
  have ha := hbox ⟨3, by omega⟩
  have hb' := hbox ⟨6, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_31 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 3) (z 5) ((boxLo 3 : ℚ) : ℝ) ((boxHi 3 : ℚ) : ℝ)
      ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) := by
  have ha := hbox ⟨3, by omega⟩
  have hb' := hbox ⟨5, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_32 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 0) (z 7) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ)
      ((boxLo 7 : ℚ) : ℝ) ((boxHi 7 : ℚ) : ℝ) := by
  have ha := hbox ⟨0, by omega⟩
  have hb' := hbox ⟨7, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_33 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 0) (z 6) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ)
      ((boxLo 6 : ℚ) : ℝ) ((boxHi 6 : ℚ) : ℝ) := by
  have ha := hbox ⟨0, by omega⟩
  have hb' := hbox ⟨6, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

theorem envelope_34 (z : Z) (hl : IsLift z) (hbox : BoxIn z) :
    McCormick (z 0) (z 5) ((boxLo 0 : ℚ) : ℝ) ((boxHi 0 : ℚ) : ℝ)
      ((boxLo 5 : ℚ) : ℝ) ((boxHi 5 : ℚ) : ℝ) := by
  have ha := hbox ⟨0, by omega⟩
  have hb' := hbox ⟨5, by omega⟩
  exact mccormick_of_bounds ha.1 ha.2 hb'.1 hb'.2

/-! ## 106 条源行的 LP 语义与逐行 soundness -/

/-- `RowProp i z`：第 `i` 条源行（`Model.rows`，与原 JSON 逐项一致）的 LP 语义。 -/
def RowProp : Nat → Z → Prop
  | 0, z => (1 / 1 : ℝ) * z 8 ≤ (1 / 1 : ℝ)
  | 1, z => (-1 / 1 : ℝ) * z 8 ≤ (1 / 1 : ℝ)
  | 2, z => (1 / 1 : ℝ) * z 9 ≤ (1 / 1 : ℝ)
  | 3, z => (-1 / 1 : ℝ) * z 9 ≤ (1 / 1 : ℝ)
  | 4, z => (1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 46 ≤ (1 / 1 : ℝ)
  | 5, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 46 ≤ (1 / 1 : ℝ)
  | 6, z => (1 / 1 : ℝ) * z 10 ≤ (1 / 1 : ℝ)
  | 7, z => (-1 / 1 : ℝ) * z 10 ≤ (1 / 1 : ℝ)
  | 8, z => (1 / 1 : ℝ) * z 13 ≤ (1 / 1 : ℝ)
  | 9, z => (-1 / 1 : ℝ) * z 13 ≤ (1 / 1 : ℝ)
  | 10, z => (1 / 1 : ℝ) * z 16 ≤ (1 / 1 : ℝ)
  | 11, z => (-1 / 1 : ℝ) * z 16 ≤ (1 / 1 : ℝ)
  | 12, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 19 ≤ (0 / 1 : ℝ)
  | 13, z => (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 19 ≤ (0 / 1 : ℝ)
  | 14, z => (-1 / 1 : ℝ) * z 45 + (1 / 1 : ℝ) * z 49 ≤ (1 / 1 : ℝ)
  | 15, z => (1 / 1 : ℝ) * z 45 + (-1 / 1 : ℝ) * z 49 ≤ (1 / 1 : ℝ)
  | 16, z => (1 / 1 : ℝ) * z 19 + (1 / 1 : ℝ) * z 42 ≤ (1 / 1 : ℝ)
  | 17, z => (-1 / 1 : ℝ) * z 19 + (-1 / 1 : ℝ) * z 42 ≤ (1 / 1 : ℝ)
  | 18, z => (-2 / 1 : ℝ) * z 0 ≤ (0 / 1 : ℝ)
  | 19, z => (1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 30 ≤ (0 / 1 : ℝ)
  | 20, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 30 ≤ (0 / 1 : ℝ)
  | 21, z => (1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 30 + (1 / 1 : ℝ) * z 39 ≤ (1 / 1 : ℝ)
  | 22, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 30 + (-1 / 1 : ℝ) * z 39 ≤ (1 / 1 : ℝ)
  | 23, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 3 ≤ (0 / 1 : ℝ)
  | 24, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 3 ≤ (0 / 1 : ℝ)
  | 25, z => (1 / 1 : ℝ) * z 3 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 29 ≤ (0 / 1 : ℝ)
  | 26, z => (-1 / 1 : ℝ) * z 3 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 29 ≤ (0 / 1 : ℝ)
  | 27, z => (1 / 1 : ℝ) * z 3 + (1 / 1 : ℝ) * z 29 + (1 / 1 : ℝ) * z 38 ≤ (1 / 1 : ℝ)
  | 28, z => (-1 / 1 : ℝ) * z 3 + (-1 / 1 : ℝ) * z 29 + (-1 / 1 : ℝ) * z 38 ≤ (1 / 1 : ℝ)
  | 29, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 4 ≤ (0 / 1 : ℝ)
  | 30, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 4 ≤ (0 / 1 : ℝ)
  | 31, z => (1 / 1 : ℝ) * z 4 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 28 ≤ (0 / 1 : ℝ)
  | 32, z => (-1 / 1 : ℝ) * z 4 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 28 ≤ (0 / 1 : ℝ)
  | 33, z => (1 / 1 : ℝ) * z 4 + (1 / 1 : ℝ) * z 28 + (1 / 1 : ℝ) * z 37 ≤ (1 / 1 : ℝ)
  | 34, z => (-1 / 1 : ℝ) * z 4 + (-1 / 1 : ℝ) * z 28 + (-1 / 1 : ℝ) * z 37 ≤ (1 / 1 : ℝ)
  | 35, z => (1 / 1 : ℝ) * z 11 ≤ (1 / 1 : ℝ)
  | 36, z => (-1 / 1 : ℝ) * z 11 ≤ (1 / 1 : ℝ)
  | 37, z => (1 / 1 : ℝ) * z 14 ≤ (1 / 1 : ℝ)
  | 38, z => (-1 / 1 : ℝ) * z 14 ≤ (1 / 1 : ℝ)
  | 39, z => (1 / 1 : ℝ) * z 17 ≤ (1 / 1 : ℝ)
  | 40, z => (-1 / 1 : ℝ) * z 17 ≤ (1 / 1 : ℝ)
  | 41, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 20 ≤ (0 / 1 : ℝ)
  | 42, z => (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 20 ≤ (0 / 1 : ℝ)
  | 43, z => (-1 / 1 : ℝ) * z 44 + (1 / 1 : ℝ) * z 48 ≤ (1 / 1 : ℝ)
  | 44, z => (1 / 1 : ℝ) * z 44 + (-1 / 1 : ℝ) * z 48 ≤ (1 / 1 : ℝ)
  | 45, z => (1 / 1 : ℝ) * z 20 + (1 / 1 : ℝ) * z 41 ≤ (1 / 1 : ℝ)
  | 46, z => (-1 / 1 : ℝ) * z 20 + (-1 / 1 : ℝ) * z 41 ≤ (1 / 1 : ℝ)
  | 47, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 56 ≤ (0 / 1 : ℝ)
  | 48, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 56 ≤ (0 / 1 : ℝ)
  | 49, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 27 + (1 / 1 : ℝ) * z 56 ≤ (0 / 1 : ℝ)
  | 50, z => (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 27 + (-1 / 1 : ℝ) * z 56 ≤ (0 / 1 : ℝ)
  | 51, z => (1 / 1 : ℝ) * z 27 + (1 / 1 : ℝ) * z 36 + (1 / 1 : ℝ) * z 56 ≤ (1 / 1 : ℝ)
  | 52, z => (-1 / 1 : ℝ) * z 27 + (-1 / 1 : ℝ) * z 36 + (-1 / 1 : ℝ) * z 56 ≤ (1 / 1 : ℝ)
  | 53, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 53 ≤ (0 / 1 : ℝ)
  | 54, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 53 ≤ (0 / 1 : ℝ)
  | 55, z => (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 26 + (1 / 1 : ℝ) * z 53 ≤ (0 / 1 : ℝ)
  | 56, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 26 + (-1 / 1 : ℝ) * z 53 ≤ (0 / 1 : ℝ)
  | 57, z => (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 26 + (1 / 1 : ℝ) * z 35 + (1 / 1 : ℝ) * z 53 ≤ (1 / 1 : ℝ)
  | 58, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 26 + (-1 / 1 : ℝ) * z 35 + (-1 / 1 : ℝ) * z 53 ≤ (1 / 1 : ℝ)
  | 59, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 51 ≤ (0 / 1 : ℝ)
  | 60, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 51 ≤ (0 / 1 : ℝ)
  | 61, z => (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 25 + (1 / 1 : ℝ) * z 51 ≤ (0 / 1 : ℝ)
  | 62, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 25 + (-1 / 1 : ℝ) * z 51 ≤ (0 / 1 : ℝ)
  | 63, z => (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 25 + (1 / 1 : ℝ) * z 34 + (1 / 1 : ℝ) * z 51 ≤ (1 / 1 : ℝ)
  | 64, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 25 + (-1 / 1 : ℝ) * z 34 + (-1 / 1 : ℝ) * z 51 ≤ (1 / 1 : ℝ)
  | 65, z => (1 / 1 : ℝ) * z 12 ≤ (1 / 1 : ℝ)
  | 66, z => (-1 / 1 : ℝ) * z 12 ≤ (1 / 1 : ℝ)
  | 67, z => (1 / 1 : ℝ) * z 15 ≤ (1 / 1 : ℝ)
  | 68, z => (-1 / 1 : ℝ) * z 15 ≤ (1 / 1 : ℝ)
  | 69, z => (1 / 1 : ℝ) * z 18 ≤ (1 / 1 : ℝ)
  | 70, z => (-1 / 1 : ℝ) * z 18 ≤ (1 / 1 : ℝ)
  | 71, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 21 ≤ (0 / 1 : ℝ)
  | 72, z => (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 21 ≤ (0 / 1 : ℝ)
  | 73, z => (-1 / 1 : ℝ) * z 43 + (1 / 1 : ℝ) * z 47 ≤ (1 / 1 : ℝ)
  | 74, z => (1 / 1 : ℝ) * z 43 + (-1 / 1 : ℝ) * z 47 ≤ (1 / 1 : ℝ)
  | 75, z => (1 / 1 : ℝ) * z 21 + (1 / 1 : ℝ) * z 40 ≤ (1 / 1 : ℝ)
  | 76, z => (-1 / 1 : ℝ) * z 21 + (-1 / 1 : ℝ) * z 40 ≤ (1 / 1 : ℝ)
  | 77, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 55 ≤ (0 / 1 : ℝ)
  | 78, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 55 ≤ (0 / 1 : ℝ)
  | 79, z => (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 24 + (1 / 1 : ℝ) * z 55 ≤ (0 / 1 : ℝ)
  | 80, z => (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 24 + (-1 / 1 : ℝ) * z 55 ≤ (0 / 1 : ℝ)
  | 81, z => (1 / 1 : ℝ) * z 24 + (1 / 1 : ℝ) * z 33 + (1 / 1 : ℝ) * z 55 ≤ (1 / 1 : ℝ)
  | 82, z => (-1 / 1 : ℝ) * z 24 + (-1 / 1 : ℝ) * z 33 + (-1 / 1 : ℝ) * z 55 ≤ (1 / 1 : ℝ)
  | 83, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 52 ≤ (0 / 1 : ℝ)
  | 84, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 52 ≤ (0 / 1 : ℝ)
  | 85, z => (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 23 + (1 / 1 : ℝ) * z 52 ≤ (0 / 1 : ℝ)
  | 86, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 23 + (-1 / 1 : ℝ) * z 52 ≤ (0 / 1 : ℝ)
  | 87, z => (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 23 + (1 / 1 : ℝ) * z 32 + (1 / 1 : ℝ) * z 52 ≤ (1 / 1 : ℝ)
  | 88, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 23 + (-1 / 1 : ℝ) * z 32 + (-1 / 1 : ℝ) * z 52 ≤ (1 / 1 : ℝ)
  | 89, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 2 + (1 / 1 : ℝ) * z 50 ≤ (0 / 1 : ℝ)
  | 90, z => (-1 / 1 : ℝ) * z 0 + (-1 / 1 : ℝ) * z 2 + (-1 / 1 : ℝ) * z 50 ≤ (0 / 1 : ℝ)
  | 91, z => (1 / 1 : ℝ) * z 2 + (-1 / 1 : ℝ) * z 7 + (1 / 1 : ℝ) * z 22 + (1 / 1 : ℝ) * z 50 ≤ (0 / 1 : ℝ)
  | 92, z => (-1 / 1 : ℝ) * z 2 + (-1 / 1 : ℝ) * z 7 + (-1 / 1 : ℝ) * z 22 + (-1 / 1 : ℝ) * z 50 ≤ (0 / 1 : ℝ)
  | 93, z => (1 / 1 : ℝ) * z 2 + (1 / 1 : ℝ) * z 22 + (1 / 1 : ℝ) * z 31 + (1 / 1 : ℝ) * z 50 ≤ (1 / 1 : ℝ)
  | 94, z => (-1 / 1 : ℝ) * z 2 + (-1 / 1 : ℝ) * z 22 + (-1 / 1 : ℝ) * z 31 + (-1 / 1 : ℝ) * z 50 ≤ (1 / 1 : ℝ)
  | 95, z => (-1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 2 ≤ (-1653 / 400 : ℝ)
  | 96, z => (-9 / 4 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 2 ≤ (0 / 1 : ℝ)
  | 97, z => (-1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 2 ≤ (0 / 1 : ℝ)
  | 98, z => (1 / 1 : ℝ) * z 54 ≤ (4 / 1 : ℝ)
  | 99, z => (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 2 + (-4 / 1 : ℝ) * z 7 ≤ (0 / 1 : ℝ)
  | 100, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 55 ≤ (0 / 1 : ℝ)
  | 101, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 4 ≤ (0 / 1 : ℝ)
  | 102, z => (-1 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (1 / 1 : ℝ) * z 3 ≤ (0 / 1 : ℝ)
  | 103, z => (-2 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 2 + (1 / 1 : ℝ) * z 3 + (-1 / 1 : ℝ) * z 4 ≤ (0 / 1 : ℝ)
  | 104, z => (-2 / 1 : ℝ) * z 0 + (1 / 1 : ℝ) * z 1 + (-1 / 1 : ℝ) * z 2 + (1 / 1 : ℝ) * z 4 ≤ (0 / 1 : ℝ)
  | 105, z => (-1 / 1 : ℝ) * z 5 + (1 / 1 : ℝ) * z 6 ≤ (-53 / 800 : ℝ)
  | _, _ => True

/-- 本阶段**已支付**的行索引（104 条）。 -/
def paidIdx : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 97, 99, 100, 101, 102, 103, 104, 105]

/-- 本阶段**未支付**的行索引（2 条：`Fcore` 需 §3.1 恒等式、`det3` 需 §3.2 行列式界）。 -/
def unpaidIdx : List Nat := [96, 98]

/-- 覆盖核对（内核可复查，`decide`）：并集恰好 106 条、互不重叠、索引都在 0..105。 -/
theorem coverage_complete :
    (paidIdx ++ unpaidIdx).length = 106 ∧
      (paidIdx ++ unpaidIdx).eraseDups.length = 106 ∧
        (paidIdx ++ unpaidIdx).all (fun i => i < 106) = true ∧
          (paidIdx.all (fun i => unpaidIdx.contains i)) = false := by decide

theorem coverage_lengths : paidIdx.length = 104 ∧ unpaidIdx.length = 2 := by decide

/-- **源行 soundness（本阶段范围）**：实际状态满足物理带、符号规范、
高值分支假设、ρ₄ 输入与 `k ≤ 2` 时，`paidIdx` 中的每一行 LP 语义成立。 -/
theorem paid_rows_sound (z : Z) (hl : IsLift z) (hb : PhysicalBounds z)
    (hs : NormalizedSigns z) (hF : HighValue z) (hrho : Rho4Input z)
    (hk2 : SmallThirdPivot z) :
    ∀ i, i ∈ paidIdx → RowProp i z := by
  intro i hi
  simp only [paidIdx, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [RowProp]
    have h := (abs_le.mp (hb.e_abs)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.e_abs)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.be_abs)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.be_abs)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_be]
    have h := (abs_le.mp (hb.head_abs)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_be]
    have h := (abs_le.mp (hb.head_abs)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u0, hl.lift_p_x0]
    have h := (abs_le.mp (hb.L_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u0, hl.lift_p_x0]
    have h := (abs_le.mp (hb.L_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v0]
    have h := (abs_le.mp (hb.P_abs 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v0]
    have h := (abs_le.mp (hb.P_abs 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    linarith [hb.k_pos]
  · simp only [RowProp, hl.lift_x0_q0]
    have h := (abs_le.mp (hb.S_abs 0 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q0]
    have h := (abs_le.mp (hb.S_abs 0 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q0, hl.lift_u0_v0]
    have h := (abs_le.mp (hb.O_abs 0 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q0, hl.lift_u0_v0]
    have h := (abs_le.mp (hb.O_abs 0 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.D_abs 0 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.D_abs 0 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q1]
    have h := (abs_le.mp (hb.S_abs 0 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q1]
    have h := (abs_le.mp (hb.S_abs 0 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q1, hl.lift_u0_v1]
    have h := (abs_le.mp (hb.O_abs 0 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q1, hl.lift_u0_v1]
    have h := (abs_le.mp (hb.O_abs 0 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.D_abs 0 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.D_abs 0 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q2]
    have h := (abs_le.mp (hb.S_abs 0 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q2]
    have h := (abs_le.mp (hb.S_abs 0 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q2, hl.lift_u0_v2]
    have h := (abs_le.mp (hb.O_abs 0 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x0_q2, hl.lift_u0_v2]
    have h := (abs_le.mp (hb.O_abs 0 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u1, hl.lift_p_x1]
    have h := (abs_le.mp (hb.L_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u1, hl.lift_p_x1]
    have h := (abs_le.mp (hb.L_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v1]
    have h := (abs_le.mp (hb.P_abs 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v1]
    have h := (abs_le.mp (hb.P_abs 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_k_c]
    have h := (abs_le.mp (hb.D_abs 1 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_k_c]
    have h := (abs_le.mp (hb.D_abs 1 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q0, hl.lift_k_c]
    have h := (abs_le.mp (hb.S_abs 1 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q0, hl.lift_k_c]
    have h := (abs_le.mp (hb.S_abs 1 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q0, hl.lift_u1_v0, hl.lift_k_c]
    have h := (abs_le.mp (hb.O_abs 1 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q0, hl.lift_u1_v0, hl.lift_k_c]
    have h := (abs_le.mp (hb.O_abs 1 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_A_c]
    have h := (abs_le.mp (hb.D_abs 1 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_A_c]
    have h := (abs_le.mp (hb.D_abs 1 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q1, hl.lift_A_c]
    have h := (abs_le.mp (hb.S_abs 1 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q1, hl.lift_A_c]
    have h := (abs_le.mp (hb.S_abs 1 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q1, hl.lift_u1_v1, hl.lift_A_c]
    have h := (abs_le.mp (hb.O_abs 1 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q1, hl.lift_u1_v1, hl.lift_A_c]
    have h := (abs_le.mp (hb.O_abs 1 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_B_c]
    have h := (abs_le.mp (hb.D_abs 1 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_B_c]
    have h := (abs_le.mp (hb.D_abs 1 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q2, hl.lift_B_c]
    have h := (abs_le.mp (hb.S_abs 1 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q2, hl.lift_B_c]
    have h := (abs_le.mp (hb.S_abs 1 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q2, hl.lift_u1_v2, hl.lift_B_c]
    have h := (abs_le.mp (hb.O_abs 1 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x1_q2, hl.lift_u1_v2, hl.lift_B_c]
    have h := (abs_le.mp (hb.O_abs 1 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.u_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.x_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.v_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    have h := (abs_le.mp (hb.q_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u2, hl.lift_p_x2]
    have h := (abs_le.mp (hb.L_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_e_u2, hl.lift_p_x2]
    have h := (abs_le.mp (hb.L_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v2]
    have h := (abs_le.mp (hb.P_abs 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_be_v2]
    have h := (abs_le.mp (hb.P_abs 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_k_d]
    have h := (abs_le.mp (hb.D_abs 2 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_k_d]
    have h := (abs_le.mp (hb.D_abs 2 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q0, hl.lift_k_d]
    have h := (abs_le.mp (hb.S_abs 2 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q0, hl.lift_k_d]
    have h := (abs_le.mp (hb.S_abs 2 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q0, hl.lift_u2_v0, hl.lift_k_d]
    have h := (abs_le.mp (hb.O_abs 2 0)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q0, hl.lift_u2_v0, hl.lift_k_d]
    have h := (abs_le.mp (hb.O_abs 2 0)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_A_d]
    have h := (abs_le.mp (hb.D_abs 2 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_A_d]
    have h := (abs_le.mp (hb.D_abs 2 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q1, hl.lift_A_d]
    have h := (abs_le.mp (hb.S_abs 2 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q1, hl.lift_A_d]
    have h := (abs_le.mp (hb.S_abs 2 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q1, hl.lift_u2_v1, hl.lift_A_d]
    have h := (abs_le.mp (hb.O_abs 2 1)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q1, hl.lift_u2_v1, hl.lift_A_d]
    have h := (abs_le.mp (hb.O_abs 2 1)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_B_d]
    have h := (abs_le.mp (hb.D_abs 2 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_B_d]
    have h := (abs_le.mp (hb.D_abs 2 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q2, hl.lift_B_d]
    have h := (abs_le.mp (hb.S_abs 2 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q2, hl.lift_B_d]
    have h := (abs_le.mp (hb.S_abs 2 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q2, hl.lift_u2_v2, hl.lift_B_d]
    have h := (abs_le.mp (hb.O_abs 2 2)).2
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp, hl.lift_x2_q2, hl.lift_u2_v2, hl.lift_B_d]
    have h := (abs_le.mp (hb.O_abs 2 2)).1
    simp only [uu, xx, vv, qq, Lc, Pc, Sc, Oc, Dc_0_0, Dc_0_1, Dc_0_2, Dc_1_0, Dc_1_1, Dc_1_2, Dc_2_0, Dc_2_1, Dc_2_2] at h
    norm_num at h ⊢
    linarith
  · simp only [RowProp]
    norm_num
    linarith [hF]
  · simp only [RowProp]
    norm_num
    linarith [(abs_le.mp hb.w_abs).1]
  · simp only [RowProp]
    norm_num
    linarith [hrho]
  · simp only [RowProp, hl.lift_k_d]
    norm_num
    linarith [row_rAd z hb hs]
  · simp only [RowProp]
    norm_num
    linarith [row_rBc z hb hs]
  · simp only [RowProp]
    norm_num
    linarith [row_rAc z hb hs]
  · simp only [RowProp]
    norm_num
    linarith [row_BA z hb hs hF hk2]
  · simp only [RowProp]
    norm_num
    linarith [row_B z hb hs hF hk2]
  · simp only [RowProp]
    norm_num
    linarith [row_cd z hb hs hF hk2]

end Rho5.Shared.XSmallKBranch
