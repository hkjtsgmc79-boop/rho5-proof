/-
D103 — stage A (continued): the **actual Schur layer readings** of the reconstruction `M x`.

The frozen D37 accessors are `S4 A = pivotSchur A 0 0`, `S3 A = pivotSchur (S4 A) 0 0`,
`T2 A = pivotSchur (S3 A) 0 0` with entrywise formulas `S4_apply`/`S3_apply`/`T2_apply`.  This file
computes them for the general-`w` reconstruction of `Matrix.lean`:

* `S4 (M x) = S4template x` — the first Schur layer is the frozen `S` block together with the `q`
  row and the `p x` column;
* `S3 (M x) = Dcore x` — the second layer is exactly the core `D` block (with the general `w`);
* `T2 (M x) = !![r, r; r, w]` — the tail is `[[r, r], [r, w]]`, i.e. `s = t = r` with free `w`;
* hence the frozen `Rho5.CanonicalTail.delta` (`= T2 1 1 - t * s / r`) reads `w - r`
  (`canonicalTail_delta_eq`) — this is the theorem the accepted `delta x := w - r` coordinate
  identity was missing.

Only the two real pivots of the construction are used as non-zero denominators (`p = x 7` and
`k = x 0`), both from `V43.Physical`'s strict positivity.  No `w = -r` and no `B24.Physical` input.
-/
import Rho5.Shared.CanonicalTail.Defs
import Rho5.Shared.V43ActualMatrix.Matrix

namespace Rho5.Shared.V43ActualMatrix

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2)

/-- The first Schur layer of the reconstruction: frozen `S` block, `q` row, `p x` column. -/
def S4template (x : X) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![pOf x, qOf x 0, qOf x 1, qOf x 2],
    ![pOf x * xvOf x 0, kOf x + xvOf x 0 * qOf x 0, aOf x + xvOf x 0 * qOf x 1,
      bOf x + xvOf x 0 * qOf x 2],
    ![pOf x * xvOf x 1, kOf x * cOf x + xvOf x 1 * qOf x 0,
      rOf x + aOf x * cOf x + xvOf x 1 * qOf x 1, rOf x + bOf x * cOf x + xvOf x 1 * qOf x 2],
    ![pOf x * xvOf x 2, kOf x * dOf x + xvOf x 2 * qOf x 0,
      rOf x + aOf x * dOf x + xvOf x 2 * qOf x 1, wOf x + bOf x * dOf x + xvOf x 2 * qOf x 2]]

/-- **First layer reading.** -/
theorem S4_eq_template (x : X) : S4 (M x) = S4template x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Rho5.Certificate.B24Extraction.S4_apply]
     simp [S4template, M, Dcore, Ocore, Pvec, Lvec, kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf,
       eOf, betaOf, uOf, xvOf, vOf, qOf]
     try field_simp
     try ring)

/-- **Second layer reading**: the core `D` block, with the general `w`. -/
theorem S3_eq_Dcore (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    S3 (M x) = Dcore x := by
  have hp : x 7 ≠ 0 := ne_of_gt hx.2.2.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Rho5.Certificate.B24Extraction.S3_apply, S4_eq_template]
     simp [S4template, Dcore, kOf, rOf, wOf, aOf, bOf, cOf, dOf, pOf, xvOf, qOf]
     field_simp
     try field_simp
     try ring)

/-- **Tail reading**: `T2 (M x) = [[r, r], [r, w]]` (`s = t = r`, free `w`). -/
theorem T2_eq_tail (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    T2 (M x) = !![rOf x, rOf x; rOf x, wOf x] := by
  have hk : x 0 ≠ 0 := ne_of_gt hx.2.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    (rw [Rho5.Certificate.B24Extraction.T2_apply, S3_eq_Dcore x hx]
     simp [Dcore, kOf, rOf, wOf, aOf, bOf, cOf, dOf]
     field_simp
     try field_simp
     try ring)

/-- **`CanonicalTail.delta` reading**: the frozen `δ = T2 1 1 - t * s / r` of the actual
reconstruction is `w - r`, with `s = t = r` and `r ≠ 0` supplied by `V43.Physical`. -/
theorem canonicalTail_delta_eq (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    Rho5.CanonicalTail.delta (M x) = wOf x - rOf x := by
  have hr : x 1 ≠ 0 := ne_of_gt hx.2.2.1
  rw [Rho5.CanonicalTail.delta]
  simp only [Rho5.Certificate.B24Extraction.s, Rho5.Certificate.B24Extraction.t,
    Rho5.Certificate.B24Extraction.r]
  rw [T2_eq_tail x hx]
  simp [rOf, wOf]
  try field_simp
  try ring

end

end Rho5.Shared.V43ActualMatrix
