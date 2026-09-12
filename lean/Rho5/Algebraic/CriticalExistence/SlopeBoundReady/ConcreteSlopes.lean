/-
# D50 phase B — `concrete_slopes` from the delivered Newton-row jets

This module proves the card's original contraction-slope statement

`|(newtonExpr i).secant j v w| * radius j ≤ radius i / 16`

for every `i j : Fin 4` and every pair `v w` of the centered box
`CenteredBox midpoint radius`, using exactly two already-verified inputs:

* the **delivered jets** `jet12256`, `jet12270`, `jet12284`, `jet12298` — the
  `JetSound coarseBox eNNNNN ivNNNNN dvNNNNN` theorems of D39's `JetBounds` layer
  (frozen delivery `JET_READY`), which enclose the four Newton rows' secants, and
* the **phase-A arithmetic** `slope_arith` / `slope_arith_magnitude` of
  `Rho5.Algebraic.CriticalExistence.SlopeBoundReady`.

Nothing is recomputed and no constant is changed.  The only remaining obligation is
the *connection* between the jets' derivative enclosures `dvNNNNN` and the frozen
`errorIntervals` rows that phase A bounds.  That connection is not assumed from the
printed literals: it is **proved here**, per row, as a definitional equality of the
two interval vectors (`dv12256_eq_errorIntervals` and its three siblings), and then
transported to the magnitude form (`magnitude_dv12256`, ...) that phase A names.

`dvRow` bundles the four jet rows in `newtonExpr` order and carries the same bridge in
one statement (`dvRow_eq_errorIntervals`, `magnitude_dvRow`).

Scope: phase B only.  No jet is rebuilt, no constant, interval, expression or
definition is modified, and no certificate or existence statement is asserted here.
-/
import Rho5.Algebraic.CriticalExistence.Circuit
import Rho5.Algebraic.CriticalExistence.JetBounds
import Rho5.Algebraic.CriticalExistence.SlopeBoundReady

namespace Rho5.Algebraic.CriticalExistence.SlopeBoundReady

open Rho5.Algebraic.CriticalExistence

/-- The four derivative enclosures of the delivered Newton-row jets, in exactly the
order in which `newtonExpr` lists the rows. -/
def dvRow : Fin 4 → Fin 4 → QI := ![dv12256, dv12270, dv12284, dv12298]

/-! ## The real relation between the jet rows and the frozen `errorIntervals` -/

/-- Row 0 of the delivered jets **is** the frozen `errorIntervals` row 0: proved by
unfolding both definitions componentwise (the two interval vectors are definitionally
equal), not inferred from their printed literals. -/
theorem dv12256_eq_errorIntervals : dv12256 = errorIntervals 0 := by
  funext j
  fin_cases j <;> rfl

/-- Row 1 of the delivered jets is the frozen `errorIntervals` row 1. -/
theorem dv12270_eq_errorIntervals : dv12270 = errorIntervals 1 := by
  funext j
  fin_cases j <;> rfl

/-- Row 2 of the delivered jets is the frozen `errorIntervals` row 2. -/
theorem dv12284_eq_errorIntervals : dv12284 = errorIntervals 2 := by
  funext j
  fin_cases j <;> rfl

/-- Row 3 of the delivered jets is the frozen `errorIntervals` row 3. -/
theorem dv12298_eq_errorIntervals : dv12298 = errorIntervals 3 := by
  funext j
  fin_cases j <;> rfl

/-- The bundled form: for every row index, the delivered jets' enclosure vector equals
the frozen `errorIntervals` row of the same index. -/
theorem dvRow_eq_errorIntervals (i : Fin 4) : dvRow i = errorIntervals i := by
  fin_cases i
  · exact dv12256_eq_errorIntervals
  · exact dv12270_eq_errorIntervals
  · exact dv12284_eq_errorIntervals
  · exact dv12298_eq_errorIntervals

/-- Row 0 in the magnitude form phase A uses. -/
theorem magnitude_dv12256 (j : Fin 4) :
    (max |(dv12256 j).lo| |(dv12256 j).hi| : ℚ) = magnitude 0 j := by
  rw [dv12256_eq_errorIntervals]
  rfl

/-- Row 1 in the magnitude form phase A uses. -/
theorem magnitude_dv12270 (j : Fin 4) :
    (max |(dv12270 j).lo| |(dv12270 j).hi| : ℚ) = magnitude 1 j := by
  rw [dv12270_eq_errorIntervals]
  rfl

/-- Row 2 in the magnitude form phase A uses. -/
theorem magnitude_dv12284 (j : Fin 4) :
    (max |(dv12284 j).lo| |(dv12284 j).hi| : ℚ) = magnitude 2 j := by
  rw [dv12284_eq_errorIntervals]
  rfl

/-- Row 3 in the magnitude form phase A uses. -/
theorem magnitude_dv12298 (j : Fin 4) :
    (max |(dv12298 j).lo| |(dv12298 j).hi| : ℚ) = magnitude 3 j := by
  rw [dv12298_eq_errorIntervals]
  rfl

/-- The bundled magnitude bridge: the magnitude of the delivered jets' row `i` is
phase A's `magnitude i` in every coordinate. -/
theorem magnitude_dvRow (i j : Fin 4) :
    (max |(dvRow i j).lo| |(dvRow i j).hi| : ℚ) = magnitude i j := by
  rw [dvRow_eq_errorIntervals i]
  rfl

/-! ## The card's statement -/

/-- **Phase B (the card's `concrete_slopes`).**  On the centered box of `Data`, every
Newton-row secant is bounded by the phase-A weighted magnitude, hence by `radius i / 16`.

The proof consumes one delivered jet per row: the jet's `slope` field encloses the
secant in `dvRow i j`, `QI.abs_le_of_mem` turns that enclosure into the magnitude bound
`max |lo| |hi|`, and the bridge lemma above identifies that magnitude with phase A's
`magnitude i j`, which `slope_arith_magnitude` bounds by `radius i / 16`. -/
theorem concrete_slopes (i j : Fin 4) (v w : Vec)
    (hv : CenteredBox midpoint radius v) (hw : CenteredBox midpoint radius w) :
    |(newtonExpr i).secant j v w| * radius j ≤ radius i / 16 := by
  have hv' : MemBox coarseBox v := in_coarse ((inBox_iff_centered v).mpr hv)
  have hw' : MemBox coarseBox w := in_coarse ((inBox_iff_centered w).mpr hw)
  have bound : ∀ (i : Fin 4) (e : Expr) (I : QI) (dv : Fin 4 → QI),
      JetSound coarseBox e I dv →
      (max |(dv j).lo| |(dv j).hi| : ℚ) = magnitude i j →
      |e.secant j v w| * radius j ≤ radius i / 16 := by
    intro i e I dv hjet hmag
    have hb := QI.abs_le_of_mem (hjet.slope j v w hv' hw')
    have hn := mul_le_mul_of_nonneg_right hb (radius_pos j).le
    calc |e.secant j v w| * radius j
        ≤ ((max |(dv j).lo| |(dv j).hi| : ℚ) : ℝ) * radius j := hn
      _ = (magnitude i j : ℝ) * radius j := by rw [hmag]
      _ ≤ radius i / 16 := slope_arith_magnitude i j
  fin_cases i
  · show |e12256.secant j v w| * radius j ≤ radius 0 / 16
    exact bound 0 e12256 iv12256 dv12256 jet12256 (magnitude_dv12256 j)
  · show |e12270.secant j v w| * radius j ≤ radius 1 / 16
    exact bound 1 e12270 iv12270 dv12270 jet12270 (magnitude_dv12270 j)
  · show |e12284.secant j v w| * radius j ≤ radius 2 / 16
    exact bound 2 e12284 iv12284 dv12284 jet12284 (magnitude_dv12284 j)
  · show |e12298.secant j v w| * radius j ≤ radius 3 / 16
    exact bound 3 e12298 iv12298 dv12298 jet12298 (magnitude_dv12298 j)

/-- The same statement with the quantifiers in the order D30's interface uses. -/
theorem concrete_slopes_all :
    ∀ (i j : Fin 4) (v w : Vec),
      CenteredBox midpoint radius v → CenteredBox midpoint radius w →
        |(newtonExpr i).secant j v w| * radius j ≤ radius i / 16 :=
  fun i j v w hv hw => concrete_slopes i j v w hv hw

end Rho5.Algebraic.CriticalExistence.SlopeBoundReady
