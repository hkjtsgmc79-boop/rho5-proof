/-
D103 — stage A: the *actual* `5 × 5` matrix reconstructed from a V43 `X22` point with the general
tail `[[r, r], [r, w]]` (no `w = -r`, no `B24.Physical` input).

Why this is the right inverse-Schur object.  The accepted D91/D95 chain showed that the X22
constraint list is written for the saturated tail `s = t = r` with a *free* `w`: its `D`-block
halves are `k - (r + B*c)`, `k - (r + A*d)`, `k - (w + B*d)`, i.e. exactly the reconstruction entries
`S3 1 2 = s + c*B`, `S3 2 1 = t + d*A`, `S3 2 2 = -r + d*B` **after** substituting `s = t = r` and
replacing the hard-coded `-r` of the frozen B24 template by `w`.  So this file writes the template
with that one change isolated in `Dcore x 2 2 = w + B*d` and proves the entry readings directly from
the original 100 constraints of `Rho5.LocalAnalysis.V43.Physical`.

Frozen inputs (read-only): pilot `Rho5.LocalAnalysis` (`X`, `height`, `V43.physicalExpr`,
`V43.Physical`), plus the cited (not imported here) D28/D65/D69/D75 matrix-reconstruction and
GrowthValues interfaces for the Schur-layer stage recorded in `STAGE_B_REMAINING.md`.

Scope: this file proves `M x 0 0 = 1`, `|M x i j| ≤ 1` for all 25 entries (entry-max reading), the
`|w| ≤ r` head-band reading, and `delta = w - r`, `|delta| = height x`.  It does **not** assert the
four complete pivots, a `LegalTrace`, `growthRatio`/`rho5Trace`, or that an arbitrary global matrix
lies in a cube; those stay explicit obligations.
-/
import Rho5.LocalAnalysis.Model
import Rho5.Shared.Conventions
import Rho5.LocalAnalysis.SampleData
import Rho5.LocalAnalysis.PhysicalCover
import Mathlib.Tactic.FinCases

namespace Rho5.Shared.V43ActualMatrix

noncomputable section
set_option maxHeartbeats 800000

abbrev X := Rho5.LocalAnalysis.X

/-- `k`, the first Schur pivot of the reconstruction. -/
def kOf (x : X) : ℝ := x 0
/-- `r`, the tail pivot. -/
def rOf (x : X) : ℝ := x 1
/-- `w`, the free tail entry (the coordinate the frozen B24 template replaces by `-r`). -/
def wOf (x : X) : ℝ := x 2
def aOf (x : X) : ℝ := x 3
def bOf (x : X) : ℝ := x 4
def cOf (x : X) : ℝ := x 5
def dOf (x : X) : ℝ := x 6
/-- `p`, the third pivot. -/
def pOf (x : X) : ℝ := x 7
def eOf (x : X) : ℝ := x 8
def betaOf (x : X) : ℝ := x 9
def uOf (x : X) : Fin 3 → ℝ := ![(x 10), (x 11), (x 12)]
def xvOf (x : X) : Fin 3 → ℝ := ![(x 13), (x 14), (x 15)]
def vOf (x : X) : Fin 3 → ℝ := ![(x 16), (x 17), (x 18)]
def qOf (x : X) : Fin 3 → ℝ := ![(x 19), (x 20), (x 21)]

/-- The reconstructed `3 × 3` core BEFORE the `u vᵀ + x qᵀ` update: the frozen B24 template with
`s = t = r` and the single isolated change `D 2 2 = w + B*d` (the template hard-codes `-r`). -/
def Dcore (x : X) : Fin 3 → Fin 3 → ℝ :=
  ![![kOf x, aOf x, bOf x],
    ![kOf x * cOf x, rOf x + aOf x * cOf x, rOf x + bOf x * cOf x],
    ![kOf x * dOf x, rOf x + aOf x * dOf x, wOf x + bOf x * dOf x]]

/-- The actual `O` block: `D + u vᵀ + x qᵀ` (the frozen `O_doc` reading). -/
def Ocore (x : X) : Fin 3 → Fin 3 → ℝ := fun i j =>
  Dcore x i j + uOf x i * vOf x j + xvOf x i * qOf x j

/-- The actual `P` row: `β v + q` (the frozen `P_doc` reading). -/
def Pvec (x : X) (j : Fin 3) : ℝ := betaOf x * vOf x j + qOf x j

/-- The actual `L` column: `p x - e u`. -/
def Lvec (x : X) (j : Fin 3) : ℝ := pOf x * xvOf x j - eOf x * uOf x j

/-- **The actual matrix.**  Inverse-Schur reconstruction with `M 0 0 = 1`, first Schur pivot `p`,
second `k`, tail `[[r, r], [r, w]]`; the general `w` sits in `Ocore x 2 2 = w + B*d`. -/
def M (x : X) : Rho5.Matrix5 :=
  ![![1, -eOf x, vOf x 0, vOf x 1, vOf x 2],
    ![betaOf x, pOf x - eOf x * betaOf x, Pvec x 0, Pvec x 1, Pvec x 2],
    ![uOf x 0, Lvec x 0, Ocore x 0 0, Ocore x 0 1, Ocore x 0 2],
    ![uOf x 1, Lvec x 1, Ocore x 1 0, Ocore x 1 1, Ocore x 1 2],
    ![uOf x 2, Lvec x 2, Ocore x 2 0, Ocore x 2 1, Ocore x 2 2]]

/-! ## Stage A readings -/

/-- `M 0 0 = 1` (the normalization of the reconstruction). -/
theorem M_zero_zero (x : X) : M x 0 0 = 1 := by
  simp [M]

/-- Isolation of the frozen template's hard-coded `-r`: the template's `D 2 2` is `M`'s at
`x 2 = -x 1`. -/
theorem Dcore_two_two_saturated (x : X) : Dcore (Function.update x 2 (-(x 1))) 2 2 = -(x 1) + bOf x * dOf x := by
  simp [Dcore, wOf, bOf, dOf]

/-- The free tail entry dominates `r` in absolute value: `|w| ≤ r` (`physicalExpr 95/96`). -/
theorem abs_w_le_r (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) : |wOf x| ≤ rOf x := by
  have hp := hx.1 95
  have hn := hx.1 96
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, wOf, rOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- The tail's Schur reading: with the tail `[[r, r], [r, w]]` the frozen
`CanonicalTail.delta = T2 1 1 - T2 0 1 * T2 1 0 / T2 0 0` is `w - r`. -/
def delta (x : X) : ℝ := wOf x - rOf x

theorem delta_eq (x : X) : delta x = x 2 - x 1 := rfl

/-- `height x = r - w ≥ 0` (`physicalExpr 96`). -/
theorem height_nonneg (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    0 ≤ Rho5.LocalAnalysis.height x := by
  have hn := hx.1 96
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval,
    Rho5.LocalAnalysis.height] at hn ⊢
  linarith

/-- **The \(\delta\)/height identity.**  `|delta| = r - w = V43.height x`. -/
theorem abs_delta_eq_height (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |delta x| = Rho5.LocalAnalysis.height x := by
  have h := height_nonneg x hx
  simp only [Rho5.LocalAnalysis.height] at h
  rw [delta, wOf, rOf, Rho5.LocalAnalysis.height]
  rw [abs_of_nonpos (by linarith)]
  ring

theorem entry_0_0 (x : X) (_hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 0 0| ≤ 1 := by
  simp [M]
/-- `M x 0 1` is in `[-1,1]` through `physicalExpr 0` / `physicalExpr 1`. -/
theorem entry_0_1 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 0 1| ≤ 1 := by
  have hp := hx.1 0
  have hn := hx.1 1
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 0 2` is in `[-1,1]` through `physicalExpr 10` / `physicalExpr 11`. -/
theorem entry_0_2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 0 2| ≤ 1 := by
  have hp := hx.1 10
  have hn := hx.1 11
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 0 3` is in `[-1,1]` through `physicalExpr 39` / `physicalExpr 40`. -/
theorem entry_0_3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 0 3| ≤ 1 := by
  have hp := hx.1 39
  have hn := hx.1 40
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 0 4` is in `[-1,1]` through `physicalExpr 69` / `physicalExpr 70`. -/
theorem entry_0_4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 0 4| ≤ 1 := by
  have hp := hx.1 69
  have hn := hx.1 70
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 1 0` is in `[-1,1]` through `physicalExpr 2` / `physicalExpr 3`. -/
theorem entry_1_0 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 1 0| ≤ 1 := by
  have hp := hx.1 2
  have hn := hx.1 3
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 1 1` is in `[-1,1]` through `physicalExpr 4` / `physicalExpr 5`. -/
theorem entry_1_1 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 1 1| ≤ 1 := by
  have hp := hx.1 4
  have hn := hx.1 5
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 1 2` is in `[-1,1]` through `physicalExpr 16` / `physicalExpr 17`. -/
theorem entry_1_2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 1 2| ≤ 1 := by
  have hp := hx.1 16
  have hn := hx.1 17
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 1 3` is in `[-1,1]` through `physicalExpr 45` / `physicalExpr 46`. -/
theorem entry_1_3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 1 3| ≤ 1 := by
  have hp := hx.1 45
  have hn := hx.1 46
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 1 4` is in `[-1,1]` through `physicalExpr 75` / `physicalExpr 76`. -/
theorem entry_1_4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 1 4| ≤ 1 := by
  have hp := hx.1 75
  have hn := hx.1 76
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 2 0` is in `[-1,1]` through `physicalExpr 6` / `physicalExpr 7`. -/
theorem entry_2_0 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 2 0| ≤ 1 := by
  have hp := hx.1 6
  have hn := hx.1 7
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 2 1` is in `[-1,1]` through `physicalExpr 14` / `physicalExpr 15`. -/
theorem entry_2_1 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 2 1| ≤ 1 := by
  have hp := hx.1 14
  have hn := hx.1 15
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 2 2` is in `[-1,1]` through `physicalExpr 21` / `physicalExpr 22`. -/
theorem entry_2_2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 2 2| ≤ 1 := by
  have hp := hx.1 21
  have hn := hx.1 22
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 2 3` is in `[-1,1]` through `physicalExpr 27` / `physicalExpr 28`. -/
theorem entry_2_3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 2 3| ≤ 1 := by
  have hp := hx.1 27
  have hn := hx.1 28
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 2 4` is in `[-1,1]` through `physicalExpr 33` / `physicalExpr 34`. -/
theorem entry_2_4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 2 4| ≤ 1 := by
  have hp := hx.1 33
  have hn := hx.1 34
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 3 0` is in `[-1,1]` through `physicalExpr 35` / `physicalExpr 36`. -/
theorem entry_3_0 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 3 0| ≤ 1 := by
  have hp := hx.1 35
  have hn := hx.1 36
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 3 1` is in `[-1,1]` through `physicalExpr 43` / `physicalExpr 44`. -/
theorem entry_3_1 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 3 1| ≤ 1 := by
  have hp := hx.1 43
  have hn := hx.1 44
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 3 2` is in `[-1,1]` through `physicalExpr 51` / `physicalExpr 52`. -/
theorem entry_3_2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 3 2| ≤ 1 := by
  have hp := hx.1 51
  have hn := hx.1 52
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 3 3` is in `[-1,1]` through `physicalExpr 57` / `physicalExpr 58`. -/
theorem entry_3_3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 3 3| ≤ 1 := by
  have hp := hx.1 57
  have hn := hx.1 58
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 3 4` is in `[-1,1]` through `physicalExpr 63` / `physicalExpr 64`. -/
theorem entry_3_4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 3 4| ≤ 1 := by
  have hp := hx.1 63
  have hn := hx.1 64
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 4 0` is in `[-1,1]` through `physicalExpr 65` / `physicalExpr 66`. -/
theorem entry_4_0 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 4 0| ≤ 1 := by
  have hp := hx.1 65
  have hn := hx.1 66
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 4 1` is in `[-1,1]` through `physicalExpr 73` / `physicalExpr 74`. -/
theorem entry_4_1 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 4 1| ≤ 1 := by
  have hp := hx.1 73
  have hn := hx.1 74
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 4 2` is in `[-1,1]` through `physicalExpr 81` / `physicalExpr 82`. -/
theorem entry_4_2 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 4 2| ≤ 1 := by
  have hp := hx.1 81
  have hn := hx.1 82
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 4 3` is in `[-1,1]` through `physicalExpr 87` / `physicalExpr 88`. -/
theorem entry_4_3 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 4 3| ≤ 1 := by
  have hp := hx.1 87
  have hn := hx.1 88
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
/-- `M x 4 4` is in `[-1,1]` through `physicalExpr 93` / `physicalExpr 94`. -/
theorem entry_4_4 (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    |M x 4 4| ≤ 1 := by
  have hp := hx.1 93
  have hn := hx.1 94
  simp [Rho5.LocalAnalysis.V43.physicalExpr, Rho5.LocalAnalysis.Expr.eval, M, Dcore, Ocore, Pvec, Lvec,
    kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, eOf, betaOf, uOf, xvOf, vOf, qOf] at hp hn ⊢
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- **Entry-max reading**: every entry of the actual reconstruction is in `[-1, 1]`. -/
theorem entries_le_one (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    ∀ (i j : Fin 5), |M x i j| ≤ 1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0 x hx
  · exact entry_0_1 x hx
  · exact entry_0_2 x hx
  · exact entry_0_3 x hx
  · exact entry_0_4 x hx
  · exact entry_1_0 x hx
  · exact entry_1_1 x hx
  · exact entry_1_2 x hx
  · exact entry_1_3 x hx
  · exact entry_1_4 x hx
  · exact entry_2_0 x hx
  · exact entry_2_1 x hx
  · exact entry_2_2 x hx
  · exact entry_2_3 x hx
  · exact entry_2_4 x hx
  · exact entry_3_0 x hx
  · exact entry_3_1 x hx
  · exact entry_3_2 x hx
  · exact entry_3_3 x hx
  · exact entry_3_4 x hx
  · exact entry_4_0 x hx
  · exact entry_4_1 x hx
  · exact entry_4_2 x hx
  · exact entry_4_3 x hx
  · exact entry_4_4 x hx

/-- **`matrixEntryMax` reading**: with the frozen `Rho5.matrixEntryMax`
(`Finset.univ.sup'` of the absolute entries) the actual reconstruction has entry-max `1`. -/
theorem matrixEntryMax_eq_one (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.matrixEntryMax (M x) = 1 := by
  have hle : Rho5.matrixEntryMax (M x) ≤ 1 := by
    rw [Rho5.matrixEntryMax, Finset.sup'_le_iff]
    intro ij _
    exact entries_le_one x hx ij.1 ij.2
  have hge : 1 ≤ Rho5.matrixEntryMax (M x) := by
    rw [Rho5.matrixEntryMax]
    have h := Finset.le_sup' (s := (Finset.univ : Finset (Fin 5 × Fin 5)))
      (f := fun ij : Fin 5 × Fin 5 => |M x ij.1 ij.2|) (Finset.mem_univ ((0, 0) : Fin 5 × Fin 5))
    simpa [M_zero_zero x] using h
  linarith

end

end Rho5.Shared.V43ActualMatrix
