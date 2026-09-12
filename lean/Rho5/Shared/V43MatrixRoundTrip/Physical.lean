/-
D119 — stage B: the 100 `V43.Physical` conditions of the extracted point
=======================================================================

`Physical (extractX M)` is paid **entirely from the four complete pivots and the normalization** of
`M` — no `V43.Physical` input, no `HeadBand`, no `B24.Physical`, no 5 × 5 determinant expansion:

* `e`, `β`, `u_i`, `v_j` and the composite readings `head = p - eβ`, `L_i = p x_i - e u_i`,
  `P_j = q_j + β v_j`, `O_ij` are bounded by `1` because they are *literally* the corresponding
  entries of `M` (`head_eq`, `L_eq`, the definition of `q`, `OX_eq_entry`) and every entry of a
  `matrixEntryMax = 1` matrix is in `[-1,1]`;
* `x_i` and `q_j` are bounded by `1` and `p` because they are the normalized first-layer readings
  `S4 M i⁺ 0 / p` and `S4 M 0 j⁺`, and `IsCompletePivot (S4 M) 0 0` bounds every entry of `S4 M`
  by `S4 M 0 0 = p`;
* the `S_ij` pair is exactly `S4 M i⁺ j⁺` (`SX_eq_S4`) and the `D_ij` pair is exactly `S3 M i j`,
  so the same complete pivots give `|S_ij| ≤ p` and `|D_ij| ≤ k`;
* `r ± w` is `IsCompletePivot (T2 M) 0 0` read on the tail `[[r, r], [r, w]]`;
* the three strict pivots supply `positive_p/k/r` and the `D00` condition `0 ≤ 2k`.

The three families `DX`/`SX`/`OX` below are the reconstruction's core block, its `S` block and its
`O` block, written in the reverse coordinates; each is proved equal to the corresponding actual
Schur layer, which is what makes the correspondence explicit rather than assumed.
-/
import Rho5.Shared.V43MatrixRoundTrip.Readings

namespace Rho5.Shared.V43MatrixRoundTrip

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The three blocks in reverse coordinates -/

/-- The core `D` block (the second Schur layer) in closed reverse coordinates. -/
def DX (M : Matrix5) : Fin 3 → Fin 3 → ℝ :=
  ![![kX M, aX M, bX M],
    ![kX M * cX M, rX M + aX M * cX M, rX M + bX M * cX M],
    ![kX M * dX M, rX M + aX M * dX M, wX M + bX M * dX M]]

/-- The `S = D + x qᵀ` block, i.e. the first Schur layer. -/
def SX (M : Matrix5) (i j : Fin 3) : ℝ := DX M i j + xX M i * qX M j

/-- The `O = D + u vᵀ + x qᵀ` block, i.e. the original bottom-right entries. -/
def OX (M : Matrix5) (i j : Fin 3) : ℝ := DX M i j + uX M i * vX M j + xX M i * qX M j

/-- `DX` is the reconstruction's own `Dcore` at the extracted point (definitional). -/
theorem DX_eq_Dcore (M : Matrix5) :
    DX M = Rho5.Shared.V43ActualMatrix.Dcore (extractX M) := rfl

/-- **`SX` is the actual first Schur layer.**  `SX M i j = S4 M i⁺ j⁺`. -/
theorem SX_eq_S4 (M : Matrix5) (h : SatFrame M) (i j : Fin 3) :
    SX M i j = S4 M i.succ j.succ := by
  have hp : pX M ≠ 0 := pX_ne_zero M h
  rw [SX, DX_eq_Dcore, Dcore_extractX M h, S3_block M h.h00 hp i j, S4_block M h.h00 i j]
  ring

/-- **`OX` is the actual bottom-right entry.**  `OX M i j = M i⁺⁺ j⁺⁺`. -/
theorem OX_eq_entry (M : Matrix5) (h : SatFrame M) (i j : Fin 3) :
    OX M i j = M i.succ.succ j.succ.succ := by
  have hp : pX M ≠ 0 := pX_ne_zero M h
  rw [OX, DX_eq_Dcore, Dcore_extractX M h, S3_block M h.h00 hp i j]
  ring

/-! ## 2. The grouped bounds -/

/-- `|e| ≤ 1`: `e` is minus an entry of `M`. -/
theorem eX_abs_le_one (M : Matrix5) (h : SatFrame M) : |eX M| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h 0 1
  rwa [eX, abs_neg]

/-- `|β| ≤ 1`. -/
theorem betaX_abs_le_one (M : Matrix5) (h : SatFrame M) : |betaX M| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h 1 0
  rwa [betaX]

/-- `|p - eβ| ≤ 1`: it is the `(1,1)` entry of `M`. -/
theorem head_abs_le_one (M : Matrix5) (h : SatFrame M) : |pX M - eX M * betaX M| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h 1 1
  rwa [head_eq M h.h00]

/-- `|u_i| ≤ 1`. -/
theorem uX_abs_le_one (M : Matrix5) (h : SatFrame M) (i : Fin 3) : |uX M i| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h i.succ.succ 0
  rwa [uX]

/-- `|v_j| ≤ 1`. -/
theorem vX_abs_le_one (M : Matrix5) (h : SatFrame M) (j : Fin 3) : |vX M j| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h 0 j.succ.succ
  rwa [vX]

/-- `|x_i| ≤ 1`: `x_i` is the normalized first-layer reading `S4 M i⁺ 0 / p`. -/
theorem xX_abs_le_one (M : Matrix5) (h : SatFrame M) (i : Fin 3) : |xX M i| ≤ 1 := by
  have hp : 0 < pX M := pX_pos M h
  have hbase : |S4 M 0 0| = pX M := abs_of_pos hp
  have hcol := S4_col0 M h.h00 (ne_of_gt hp) i
  have hle := h.cp2 i.succ 0
  rw [hbase] at hle
  rw [hcol, abs_mul, abs_of_pos hp] at hle
  have h2 : pX M * |xX M i| ≤ pX M * 1 := by rwa [mul_one]
  exact le_of_mul_le_mul_left h2 hp

/-- `|q_j| ≤ p`: `q_j` is the first-layer reading `S4 M 0 j⁺`. -/
theorem qX_abs_le_p (M : Matrix5) (h : SatFrame M) (j : Fin 3) : |qX M j| ≤ pX M := by
  have hp : 0 < pX M := pX_pos M h
  have hbase : |S4 M 0 0| = pX M := abs_of_pos hp
  have hrow := S4_row0 M h.h00 j
  have hle := h.cp2 0 j.succ
  rw [hbase] at hle
  rwa [hrow] at hle

/-- `|L_i| ≤ 1`: `L_i = p x_i - e u_i` is the `(i⁺⁺, 1)` entry of `M`. -/
theorem LX_abs_le_one (M : Matrix5) (h : SatFrame M) (i : Fin 3) :
    |pX M * xX M i - eX M * uX M i| ≤ 1 := by
  have hp : pX M ≠ 0 := pX_ne_zero M h
  have hle := SatFrame.entry_le_one M h i.succ.succ 1
  rwa [L_eq M hp i]

/-- `|P_j| ≤ 1`: `P_j = q_j + β v_j` is the `(1, j⁺⁺)` entry of `M`. -/
theorem PX_abs_le_one (M : Matrix5) (h : SatFrame M) (j : Fin 3) :
    |qX M j + betaX M * vX M j| ≤ 1 := by
  have hle := SatFrame.entry_le_one M h 1 j.succ.succ
  have h : qX M j + betaX M * vX M j = M 1 j.succ.succ := by
    rw [qX]; ring
  rwa [h]

/-- `|D_ij| ≤ k`: every entry of the actual `S3 M`. -/
theorem DX_le_kX (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : DX M i j ≤ kX M := by
  have hbase : |S3 M 0 0| = kX M := abs_of_pos (kX_pos M h)
  have hle := h.cp3 i j
  rw [hbase] at hle
  have h' := (abs_le.mp hle).2
  rwa [DX_eq_Dcore, Dcore_extractX M h]

/-- `-k ≤ D_ij`. -/
theorem neg_kX_le_DX (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : -kX M ≤ DX M i j := by
  have hbase : |S3 M 0 0| = kX M := abs_of_pos (kX_pos M h)
  have hle := h.cp3 i j
  rw [hbase] at hle
  have h' := (abs_le.mp hle).1
  rwa [DX_eq_Dcore, Dcore_extractX M h]

/-- `|S_ij| ≤ p`: every entry of the actual `S4 M`. -/
theorem SX_le_pX (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : SX M i j ≤ pX M := by
  have hbase : |S4 M 0 0| = pX M := abs_of_pos (pX_pos M h)
  have hle := h.cp2 i.succ j.succ
  rw [hbase] at hle
  have h' := (abs_le.mp hle).2
  rwa [SX_eq_S4 M h]

/-- `-p ≤ S_ij`. -/
theorem neg_pX_le_SX (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : -pX M ≤ SX M i j := by
  have hbase : |S4 M 0 0| = pX M := abs_of_pos (pX_pos M h)
  have hle := h.cp2 i.succ j.succ
  rw [hbase] at hle
  have h' := (abs_le.mp hle).1
  rwa [SX_eq_S4 M h]

/-- `|O_ij| ≤ 1`: `O_ij` is the `(i⁺⁺, j⁺⁺)` entry of `M`. -/
theorem OX_le_one (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : OX M i j ≤ 1 := by
  have hle := SatFrame.entry_le_one M h i.succ.succ j.succ.succ
  have h' := (abs_le.mp hle).2
  rwa [← OX_eq_entry M h] at h'

/-- `-1 ≤ O_ij`. -/
theorem neg_one_le_OX (M : Matrix5) (h : SatFrame M) (i j : Fin 3) : -1 ≤ OX M i j := by
  have hle := SatFrame.entry_le_one M h i.succ.succ j.succ.succ
  have h' := (abs_le.mp hle).1
  rwa [← OX_eq_entry M h] at h'

/-! ## 3. The 100 conditions -/

/-- **`V43.Physical (extractX M)`.**  Every one of the 100 polynomial conditions is discharged from
the raw two-sided readings collected above, i.e. from the four complete pivots, the normalization
and the three strict pivots — nothing else. -/
theorem physical_extractX (M : Matrix5) (h : SatFrame M) :
    Rho5.LocalAnalysis.V43.Physical (extractX M) := by
  -- every raw reading used below, in the exact shape the 100 conditions have
  have he_lo : -1 ≤ eX M := (abs_le.mp (eX_abs_le_one M h)).1
  have he_hi : eX M ≤ 1 := (abs_le.mp (eX_abs_le_one M h)).2
  have hb_lo : -1 ≤ betaX M := (abs_le.mp (betaX_abs_le_one M h)).1
  have hb_hi : betaX M ≤ 1 := (abs_le.mp (betaX_abs_le_one M h)).2
  have hh_lo : -1 ≤ pX M - eX M * betaX M := (abs_le.mp (head_abs_le_one M h)).1
  have hh_hi : pX M - eX M * betaX M ≤ 1 := (abs_le.mp (head_abs_le_one M h)).2
  have hu0_lo : -1 ≤ uX M 0 := (abs_le.mp (uX_abs_le_one M h 0)).1
  have hu0_hi : uX M 0 ≤ 1 := (abs_le.mp (uX_abs_le_one M h 0)).2
  have hu1_lo : -1 ≤ uX M 1 := (abs_le.mp (uX_abs_le_one M h 1)).1
  have hu1_hi : uX M 1 ≤ 1 := (abs_le.mp (uX_abs_le_one M h 1)).2
  have hu2_lo : -1 ≤ uX M 2 := (abs_le.mp (uX_abs_le_one M h 2)).1
  have hu2_hi : uX M 2 ≤ 1 := (abs_le.mp (uX_abs_le_one M h 2)).2
  have hv0_lo : -1 ≤ vX M 0 := (abs_le.mp (vX_abs_le_one M h 0)).1
  have hv0_hi : vX M 0 ≤ 1 := (abs_le.mp (vX_abs_le_one M h 0)).2
  have hv1_lo : -1 ≤ vX M 1 := (abs_le.mp (vX_abs_le_one M h 1)).1
  have hv1_hi : vX M 1 ≤ 1 := (abs_le.mp (vX_abs_le_one M h 1)).2
  have hv2_lo : -1 ≤ vX M 2 := (abs_le.mp (vX_abs_le_one M h 2)).1
  have hv2_hi : vX M 2 ≤ 1 := (abs_le.mp (vX_abs_le_one M h 2)).2
  have hx0_lo : -1 ≤ xX M 0 := (abs_le.mp (xX_abs_le_one M h 0)).1
  have hx0_hi : xX M 0 ≤ 1 := (abs_le.mp (xX_abs_le_one M h 0)).2
  have hx1_lo : -1 ≤ xX M 1 := (abs_le.mp (xX_abs_le_one M h 1)).1
  have hx1_hi : xX M 1 ≤ 1 := (abs_le.mp (xX_abs_le_one M h 1)).2
  have hx2_lo : -1 ≤ xX M 2 := (abs_le.mp (xX_abs_le_one M h 2)).1
  have hx2_hi : xX M 2 ≤ 1 := (abs_le.mp (xX_abs_le_one M h 2)).2
  have hq0_lo : -pX M ≤ qX M 0 := (abs_le.mp (qX_abs_le_p M h 0)).1
  have hq0_hi : qX M 0 ≤ pX M := (abs_le.mp (qX_abs_le_p M h 0)).2
  have hq1_lo : -pX M ≤ qX M 1 := (abs_le.mp (qX_abs_le_p M h 1)).1
  have hq1_hi : qX M 1 ≤ pX M := (abs_le.mp (qX_abs_le_p M h 1)).2
  have hq2_lo : -pX M ≤ qX M 2 := (abs_le.mp (qX_abs_le_p M h 2)).1
  have hq2_hi : qX M 2 ≤ pX M := (abs_le.mp (qX_abs_le_p M h 2)).2
  have hL0_lo : -1 ≤ pX M * xX M 0 - eX M * uX M 0 := (abs_le.mp (LX_abs_le_one M h 0)).1
  have hL0_hi : pX M * xX M 0 - eX M * uX M 0 ≤ 1 := (abs_le.mp (LX_abs_le_one M h 0)).2
  have hL1_lo : -1 ≤ pX M * xX M 1 - eX M * uX M 1 := (abs_le.mp (LX_abs_le_one M h 1)).1
  have hL1_hi : pX M * xX M 1 - eX M * uX M 1 ≤ 1 := (abs_le.mp (LX_abs_le_one M h 1)).2
  have hL2_lo : -1 ≤ pX M * xX M 2 - eX M * uX M 2 := (abs_le.mp (LX_abs_le_one M h 2)).1
  have hL2_hi : pX M * xX M 2 - eX M * uX M 2 ≤ 1 := (abs_le.mp (LX_abs_le_one M h 2)).2
  have hP0_lo : -1 ≤ qX M 0 + betaX M * vX M 0 := (abs_le.mp (PX_abs_le_one M h 0)).1
  have hP0_hi : qX M 0 + betaX M * vX M 0 ≤ 1 := (abs_le.mp (PX_abs_le_one M h 0)).2
  have hP1_lo : -1 ≤ qX M 1 + betaX M * vX M 1 := (abs_le.mp (PX_abs_le_one M h 1)).1
  have hP1_hi : qX M 1 + betaX M * vX M 1 ≤ 1 := (abs_le.mp (PX_abs_le_one M h 1)).2
  have hP2_lo : -1 ≤ qX M 2 + betaX M * vX M 2 := (abs_le.mp (PX_abs_le_one M h 2)).1
  have hP2_hi : qX M 2 + betaX M * vX M 2 ≤ 1 := (abs_le.mp (PX_abs_le_one M h 2)).2
  have hw_lo : -rX M ≤ wX M := (abs_le.mp (abs_wX_le_rX M h)).1
  have hw_hi : wX M ≤ rX M := (abs_le.mp (abs_wX_le_rX M h)).2
  have hD00_lo : kX M ≤ kX M := DX_le_kX M h 0 0
  have hD00_hi : -kX M ≤ kX M := neg_kX_le_DX M h 0 0
  have hD01_lo : aX M ≤ kX M := DX_le_kX M h 0 1
  have hD01_hi : -kX M ≤ aX M := neg_kX_le_DX M h 0 1
  have hD02_lo : bX M ≤ kX M := DX_le_kX M h 0 2
  have hD02_hi : -kX M ≤ bX M := neg_kX_le_DX M h 0 2
  have hD10_lo : kX M * cX M ≤ kX M := DX_le_kX M h 1 0
  have hD10_hi : -kX M ≤ kX M * cX M := neg_kX_le_DX M h 1 0
  have hD11_lo : rX M + aX M * cX M ≤ kX M := DX_le_kX M h 1 1
  have hD11_hi : -kX M ≤ rX M + aX M * cX M := neg_kX_le_DX M h 1 1
  have hD12_lo : rX M + bX M * cX M ≤ kX M := DX_le_kX M h 1 2
  have hD12_hi : -kX M ≤ rX M + bX M * cX M := neg_kX_le_DX M h 1 2
  have hD20_lo : kX M * dX M ≤ kX M := DX_le_kX M h 2 0
  have hD20_hi : -kX M ≤ kX M * dX M := neg_kX_le_DX M h 2 0
  have hD21_lo : rX M + aX M * dX M ≤ kX M := DX_le_kX M h 2 1
  have hD21_hi : -kX M ≤ rX M + aX M * dX M := neg_kX_le_DX M h 2 1
  have hD22_lo : wX M + bX M * dX M ≤ kX M := DX_le_kX M h 2 2
  have hD22_hi : -kX M ≤ wX M + bX M * dX M := neg_kX_le_DX M h 2 2
  have hS00_lo : kX M + xX M 0 * qX M 0 ≤ pX M := SX_le_pX M h 0 0
  have hS00_hi : -pX M ≤ kX M + xX M 0 * qX M 0 := neg_pX_le_SX M h 0 0
  have hS01_lo : aX M + xX M 0 * qX M 1 ≤ pX M := SX_le_pX M h 0 1
  have hS01_hi : -pX M ≤ aX M + xX M 0 * qX M 1 := neg_pX_le_SX M h 0 1
  have hS02_lo : bX M + xX M 0 * qX M 2 ≤ pX M := SX_le_pX M h 0 2
  have hS02_hi : -pX M ≤ bX M + xX M 0 * qX M 2 := neg_pX_le_SX M h 0 2
  have hS10_lo : kX M * cX M + xX M 1 * qX M 0 ≤ pX M := SX_le_pX M h 1 0
  have hS10_hi : -pX M ≤ kX M * cX M + xX M 1 * qX M 0 := neg_pX_le_SX M h 1 0
  have hS11_lo : rX M + aX M * cX M + xX M 1 * qX M 1 ≤ pX M := SX_le_pX M h 1 1
  have hS11_hi : -pX M ≤ rX M + aX M * cX M + xX M 1 * qX M 1 := neg_pX_le_SX M h 1 1
  have hS12_lo : rX M + bX M * cX M + xX M 1 * qX M 2 ≤ pX M := SX_le_pX M h 1 2
  have hS12_hi : -pX M ≤ rX M + bX M * cX M + xX M 1 * qX M 2 := neg_pX_le_SX M h 1 2
  have hS20_lo : kX M * dX M + xX M 2 * qX M 0 ≤ pX M := SX_le_pX M h 2 0
  have hS20_hi : -pX M ≤ kX M * dX M + xX M 2 * qX M 0 := neg_pX_le_SX M h 2 0
  have hS21_lo : rX M + aX M * dX M + xX M 2 * qX M 1 ≤ pX M := SX_le_pX M h 2 1
  have hS21_hi : -pX M ≤ rX M + aX M * dX M + xX M 2 * qX M 1 := neg_pX_le_SX M h 2 1
  have hS22_lo : wX M + bX M * dX M + xX M 2 * qX M 2 ≤ pX M := SX_le_pX M h 2 2
  have hS22_hi : -pX M ≤ wX M + bX M * dX M + xX M 2 * qX M 2 := neg_pX_le_SX M h 2 2
  have hO00_lo : kX M + uX M 0 * vX M 0 + xX M 0 * qX M 0 ≤ 1 := OX_le_one M h 0 0
  have hO00_hi : -1 ≤ kX M + uX M 0 * vX M 0 + xX M 0 * qX M 0 := neg_one_le_OX M h 0 0
  have hO01_lo : aX M + uX M 0 * vX M 1 + xX M 0 * qX M 1 ≤ 1 := OX_le_one M h 0 1
  have hO01_hi : -1 ≤ aX M + uX M 0 * vX M 1 + xX M 0 * qX M 1 := neg_one_le_OX M h 0 1
  have hO02_lo : bX M + uX M 0 * vX M 2 + xX M 0 * qX M 2 ≤ 1 := OX_le_one M h 0 2
  have hO02_hi : -1 ≤ bX M + uX M 0 * vX M 2 + xX M 0 * qX M 2 := neg_one_le_OX M h 0 2
  have hO10_lo : kX M * cX M + uX M 1 * vX M 0 + xX M 1 * qX M 0 ≤ 1 := OX_le_one M h 1 0
  have hO10_hi : -1 ≤ kX M * cX M + uX M 1 * vX M 0 + xX M 1 * qX M 0 := neg_one_le_OX M h 1 0
  have hO11_lo : rX M + aX M * cX M + uX M 1 * vX M 1 + xX M 1 * qX M 1 ≤ 1 := OX_le_one M h 1 1
  have hO11_hi : -1 ≤ rX M + aX M * cX M + uX M 1 * vX M 1 + xX M 1 * qX M 1 := neg_one_le_OX M h 1 1
  have hO12_lo : rX M + bX M * cX M + uX M 1 * vX M 2 + xX M 1 * qX M 2 ≤ 1 := OX_le_one M h 1 2
  have hO12_hi : -1 ≤ rX M + bX M * cX M + uX M 1 * vX M 2 + xX M 1 * qX M 2 := neg_one_le_OX M h 1 2
  have hO20_lo : kX M * dX M + uX M 2 * vX M 0 + xX M 2 * qX M 0 ≤ 1 := OX_le_one M h 2 0
  have hO20_hi : -1 ≤ kX M * dX M + uX M 2 * vX M 0 + xX M 2 * qX M 0 := neg_one_le_OX M h 2 0
  have hO21_lo : rX M + aX M * dX M + uX M 2 * vX M 1 + xX M 2 * qX M 1 ≤ 1 := OX_le_one M h 2 1
  have hO21_hi : -1 ≤ rX M + aX M * dX M + uX M 2 * vX M 1 + xX M 2 * qX M 1 := neg_one_le_OX M h 2 1
  have hO22_lo : wX M + bX M * dX M + uX M 2 * vX M 2 + xX M 2 * qX M 2 ≤ 1 := OX_le_one M h 2 2
  have hO22_hi : -1 ≤ wX M + bX M * dX M + uX M 2 * vX M 2 + xX M 2 * qX M 2 := neg_one_le_OX M h 2 2
  have hk0 : 0 ≤ kX M := (kX_pos M h).le
  have hp0 : 0 ≤ pX M := (pX_pos M h).le
  have hr0 : 0 ≤ rX M := (rX_pos M h).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      (simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, extractX]
       try linarith)
  · exact kX_pos M h
  · exact rX_pos M h
  · exact pX_pos M h

end

end Rho5.Shared.V43MatrixRoundTrip
