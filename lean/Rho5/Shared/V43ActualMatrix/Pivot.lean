/-
D103 — stage B (1/3): the four actual complete-pivot readings of the reconstruction `M x`
=========================================================================================

Stage A produced the actual matrix `M x` (general tail `[[r, r], [r, w]]`) together with its
real Schur layer readings `S4 (M x) = S4template x`, `S3 (M x) = Dcore x`,
`T2 (M x) = !![r, r; r, w]`.  This file pays the first stage-B obligation: **the four leading
complete pivots**

* `IsCompletePivot (M x) 0 0`      (`M 0 0 = 1` and `matrixEntryMax (M x) = 1`),
* `IsCompletePivot (S4 (M x)) 0 0` (`S4 (M x) 0 0 = p = x 7`),
* `IsCompletePivot (S3 (M x)) 0 0` (`S3 (M x) 0 0 = k = x 0`),
* `IsCompletePivot (T2 (M x)) 0 0` (`T2 (M x) 0 0 = r = x 1`),

together with the three readings `p (M x) = x 7`, `k (M x) = x 0`, `r (M x) = x 1` of the
*frozen* D37 accessors and their strict positivity from `V43.Physical`.

Every entry bound below is one of the original 100 `V43.physicalExpr` conditions, in the same
correspondence stage A used: `q_j ±` (12/13, 41/42, 71/72), `x_i ±` (8/9, 37/38, 67/68), the
`S_ij ±` family (19/20 … 91/92) for the first Schur layer `S = D + x qᵀ`, the `D_ij ±` family
(18, 23/24, 29/30, 47/48, 53/54, 59/60, 77/78, 83/84, 89/90) for the second layer, and `r ∓ w`
(95/96) for the tail.  Nothing is assumed: no `w = -r`, no `B24.Physical`, no cube membership,
no correspondence between the 100 condition classes and the four complete pivots (each bound is
discharged from its two named conditions).
-/
import Rho5.Shared.V43ActualMatrix.Schur

namespace Rho5.Shared.V43ActualMatrix

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2)

/-! ## 1. The first Schur layer: every entry of `S4template x` is bounded by `p = x 7`

`S4template x` is `[[p, qᵀ], [p x, S]]` with `S = D + x qᵀ`, so the readings are the three
`q_j` conditions, the three `x_i` conditions (through `|p x_i| = p |x_i| ≤ p`) and the nine
`S_ij` conditions. -/

/-- `|S4template x 0 0| ≤ p` is the pivot itself. -/
theorem S4_00 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 0 0| ≤ pOf x := by
  have hp : 0 < x 7 := hx.2.2.2
  simp [S4template, pOf, abs_of_pos hp]

/-- `S4template x 0 1 = q 0`, bounded by `p` through conditions 12/13. -/
theorem S4_01 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 0 1| ≤ pOf x := by
  have h12 := hx.1 12
  have h13 := hx.1 13
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf] at h12 h13 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 0 2 = q 1`, bounded by `p` through conditions 41/42. -/
theorem S4_02 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 0 2| ≤ pOf x := by
  have h41 := hx.1 41
  have h42 := hx.1 42
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf] at h41 h42 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 0 3 = q 2`, bounded by `p` through conditions 71/72. -/
theorem S4_03 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 0 3| ≤ pOf x := by
  have h71 := hx.1 71
  have h72 := hx.1 72
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf] at h71 h72 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 1 0 = p x 0`: the `x 0` box condition (8/9) times the positive pivot. -/
theorem S4_10 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 1 0| ≤ pOf x := by
  have hp : 0 < x 7 := hx.2.2.2
  have h8 := hx.1 8
  have h9 := hx.1 9
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval] at h8 h9
  have hx0 : |x 13| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp [S4template, pOf, xvOf, abs_of_pos hp]
  exact mul_le_of_le_one_right (le_of_lt hp) hx0

/-- `S4template x 2 0 = p x 1` via conditions 37/38. -/
theorem S4_20 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 2 0| ≤ pOf x := by
  have hp : 0 < x 7 := hx.2.2.2
  have h37 := hx.1 37
  have h38 := hx.1 38
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval] at h37 h38
  have hx1 : |x 14| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp [S4template, pOf, xvOf, abs_of_pos hp]
  exact mul_le_of_le_one_right (le_of_lt hp) hx1

/-- `S4template x 3 0 = p x 2` via conditions 67/68. -/
theorem S4_30 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 3 0| ≤ pOf x := by
  have hp : 0 < x 7 := hx.2.2.2
  have h67 := hx.1 67
  have h68 := hx.1 68
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval] at h67 h68
  have hx2 : |x 15| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp [S4template, pOf, xvOf, abs_of_pos hp]
  exact mul_le_of_le_one_right (le_of_lt hp) hx2

/-- `S4template x 1 1 = k + x 0 q 0` (the `S 00` condition pair 19/20). -/
theorem S4_11 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 1 1| ≤ pOf x := by
  have h19 := hx.1 19
  have h20 := hx.1 20
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, kOf, xvOf] at h19 h20 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 1 2 = A + x 0 q 1` (conditions 25/26). -/
theorem S4_12 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 1 2| ≤ pOf x := by
  have h25 := hx.1 25
  have h26 := hx.1 26
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, aOf, xvOf] at h25 h26 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 1 3 = B + x 0 q 2` (conditions 31/32). -/
theorem S4_13 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 1 3| ≤ pOf x := by
  have h31 := hx.1 31
  have h32 := hx.1 32
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, bOf, xvOf] at h31 h32 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 2 1 = k c + x 1 q 0` (conditions 49/50). -/
theorem S4_21 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 2 1| ≤ pOf x := by
  have h49 := hx.1 49
  have h50 := hx.1 50
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, kOf, cOf, xvOf] at h49 h50 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 2 2 = r + A c + x 1 q 1` (conditions 55/56). -/
theorem S4_22 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 2 2| ≤ pOf x := by
  have h55 := hx.1 55
  have h56 := hx.1 56
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, rOf, aOf, cOf, xvOf] at h55 h56 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 2 3 = r + B c + x 1 q 2` (conditions 61/62). -/
theorem S4_23 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 2 3| ≤ pOf x := by
  have h61 := hx.1 61
  have h62 := hx.1 62
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, rOf, bOf, cOf, xvOf] at h61 h62 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 3 1 = k d + x 2 q 0` (conditions 79/80). -/
theorem S4_31 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 3 1| ≤ pOf x := by
  have h79 := hx.1 79
  have h80 := hx.1 80
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, kOf, dOf, xvOf] at h79 h80 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 3 2 = r + A d + x 2 q 1` (conditions 85/86). -/
theorem S4_32 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 3 2| ≤ pOf x := by
  have h85 := hx.1 85
  have h86 := hx.1 86
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, rOf, aOf, dOf, xvOf] at h85 h86 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `S4template x 3 3 = w + B d + x 2 q 2` (conditions 91/92) — the general `w` entry. -/
theorem S4_33 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |S4template x 3 3| ≤ pOf x := by
  have h91 := hx.1 91
  have h92 := hx.1 92
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, S4template, pOf,
    qOf, wOf, bOf, dOf, xvOf] at h91 h92 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **First-layer entry bound**: every entry of `S4template x` is bounded by the first pivot
`p = x 7`.  The nine `S_ij` conditions are exactly the `S4` complete-pivot readings. -/
theorem S4template_entries_le_p (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    ∀ i j : Fin 4, |S4template x i j| ≤ pOf x := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact S4_00 x hx
  · exact S4_01 x hx
  · exact S4_02 x hx
  · exact S4_03 x hx
  · exact S4_10 x hx
  · exact S4_11 x hx
  · exact S4_12 x hx
  · exact S4_13 x hx
  · exact S4_20 x hx
  · exact S4_21 x hx
  · exact S4_22 x hx
  · exact S4_23 x hx
  · exact S4_30 x hx
  · exact S4_31 x hx
  · exact S4_32 x hx
  · exact S4_33 x hx

/-! ## 2. The second Schur layer: every entry of `Dcore x` is bounded by `k = x 0`

`Dcore x = [[k, A, B], [k c, r + A c, r + B c], [k d, r + A d, w + B d]]`, and the `D_ij ±`
conditions are *exactly* the two-sided bounds `k ∓ (D_ij) ≥ 0`.  The uniform `abs_le` close below
also covers the pivot entry itself, through `D 00 = k` and condition 18 (`0 ≤ 2k`). -/

/-- **Second-layer entry bound**: every entry of the core `D` block is bounded by `k = x 0`. -/
theorem Dcore_entries_le_k (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    ∀ i j : Fin 3, |Dcore x i j| ≤ kOf x := by
  have h18 := hx.1 18
  have h23 := hx.1 23
  have h24 := hx.1 24
  have h29 := hx.1 29
  have h30 := hx.1 30
  have h47 := hx.1 47
  have h48 := hx.1 48
  have h53 := hx.1 53
  have h54 := hx.1 54
  have h59 := hx.1 59
  have h60 := hx.1 60
  have h77 := hx.1 77
  have h78 := hx.1 78
  have h83 := hx.1 83
  have h84 := hx.1 84
  have h89 := hx.1 89
  have h90 := hx.1 90
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval] at h18 h23 h24 h29 h30 h47 h48 h53 h54 h59 h60 h77 h78 h83 h84 h89 h90
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp [Dcore, kOf, rOf, wOf, aOf, bOf, cOf, dOf]
     -- `simp` splits `|k * c|` into `|k| * |c|`; the two entries carrying a product inside the
     -- absolute value are put back so that the two-sided `k ∓ entry ≥ 0` conditions apply directly.
     try rw [← abs_mul]
     refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith)

/-! ## 3. The four complete pivots -/

/-- **First complete pivot.**  `M x 0 0 = 1` and every entry is in `[-1, 1]` (stage A). -/
theorem isCompletePivot_M (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Pivot.IsCompletePivot (M x) 0 0 := by
  intro i j
  rw [M_zero_zero x, abs_one]
  exact entries_le_one x hx i j

/-- **Second complete pivot.**  After the first step (`S4_eq_template`) the pivot is `p = x 7`
and every entry of the template is bounded by it. -/
theorem isCompletePivot_S4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Pivot.IsCompletePivot (S4 (M x)) 0 0 := by
  have hp : 0 < x 7 := hx.2.2.2
  have hbase : |S4 (M x) 0 0| = pOf x := by
    rw [S4_eq_template x]
    simp [S4template, pOf, abs_of_pos hp]
  intro i j
  rw [hbase, S4_eq_template x]
  exact S4template_entries_le_p x hx i j

/-- **Third complete pivot.**  After the second step (`S3_eq_Dcore`) the pivot is `k = x 0`
and every entry of the core `D` block is bounded by it. -/
theorem isCompletePivot_S3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Pivot.IsCompletePivot (S3 (M x)) 0 0 := by
  have hk : 0 < x 0 := hx.2.1
  have hbase : |S3 (M x) 0 0| = kOf x := by
    rw [S3_eq_Dcore x hx]
    simp [Dcore, kOf, abs_of_pos hk]
  intro i j
  rw [hbase, S3_eq_Dcore x hx]
  exact Dcore_entries_le_k x hx i j

/-- **Tail complete pivot.**  After the third step (`T2_eq_tail`) the tail is
`[[r, r], [r, w]]`, so the pivot is `r = x 1` and the only other value is `|w| ≤ r`
(conditions 95/96). -/
theorem isCompletePivot_T2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Pivot.IsCompletePivot (T2 (M x)) 0 0 := by
  have hr : 0 < rOf x := hx.2.2.1
  have hwr : |wOf x| ≤ rOf x := abs_w_le_r x hx
  have hbase : |T2 (M x) 0 0| = rOf x := by
    rw [T2_eq_tail x hx]
    simp [abs_of_pos hr]
  -- the four entries of the tail, with the pivot `r > 0` already substituted
  have e00 : |(!![rOf x, rOf x; rOf x, wOf x] : Matrix (Fin 2) (Fin 2) ℝ) 0 0| ≤ rOf x := by
    simp [abs_of_pos hr]
  have e01 : |(!![rOf x, rOf x; rOf x, wOf x] : Matrix (Fin 2) (Fin 2) ℝ) 0 1| ≤ rOf x := by
    simp [abs_of_pos hr]
  have e10 : |(!![rOf x, rOf x; rOf x, wOf x] : Matrix (Fin 2) (Fin 2) ℝ) 1 0| ≤ rOf x := by
    simp [abs_of_pos hr]
  have e11 : |(!![rOf x, rOf x; rOf x, wOf x] : Matrix (Fin 2) (Fin 2) ℝ) 1 1| ≤ rOf x := by
    simpa using hwr
  intro i j
  rw [hbase, T2_eq_tail x hx]
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e10
  · exact e11

/-! ## 4. The frozen pivot readings `p`, `k`, `r` and their strict positivity -/

/-- The frozen D37 reading `p (M x)` is the reconstruction's first Schur pivot `x 7`. -/
theorem p_M_eq (x : X) : Rho5.Certificate.B24Extraction.p (M x) = pOf x := by
  rw [Rho5.Certificate.B24Extraction.p, S4_eq_template x]
  simp [S4template]

/-- The frozen D37 reading `k (M x)` is the reconstruction's second Schur pivot `x 0`. -/
theorem k_M_eq (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Certificate.B24Extraction.k (M x) = kOf x := by
  rw [Rho5.Certificate.B24Extraction.k, S3_eq_Dcore x hx]
  simp [Dcore]

/-- The frozen D37 reading `r (M x)` is the reconstruction's tail pivot `x 1`. -/
theorem r_M_eq (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.Certificate.B24Extraction.r (M x) = rOf x := by
  rw [Rho5.Certificate.B24Extraction.r, T2_eq_tail x hx]
  simp

/-- **Positive prefix**: `p (M x) > 0`. -/
theorem p_M_pos (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    0 < Rho5.Certificate.B24Extraction.p (M x) := by
  rw [p_M_eq x]; exact hx.2.2.2

/-- **Positive prefix**: `k (M x) > 0`. -/
theorem k_M_pos (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    0 < Rho5.Certificate.B24Extraction.k (M x) := by
  rw [k_M_eq x hx]; exact hx.2.1

/-- **Positive prefix**: `r (M x) > 0`. -/
theorem r_M_pos (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    0 < Rho5.Certificate.B24Extraction.r (M x) := by
  rw [r_M_eq x hx]; exact hx.2.2.1

end

end Rho5.Shared.V43ActualMatrix
