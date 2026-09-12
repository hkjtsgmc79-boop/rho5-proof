import Rho5.Shared.SchurFourPivotBound.Embed

/-!
# D138 / `Rho5.Shared.SchurFourPivotBound.Bound` — the first-Schur fourth-pivot bound `F ≤ 4p`

`S4 M`, `S3 M`, `T2 M` and the final `1 x 1` block are literally a chain of pivot-`(0,0)` Schur
steps (`S3 M = pivotSchur (S4 M) 0 0`, `T2 M = pivotSchur (S3 M) 0 0`, both by definition), so an
`LeadingInput M` supplies a real `ZeroTrace (S4 M) [|p|, |k|, |r|, |delta|]` whose fourth readout is
`|delta M| = height M`.  Padding the `4 x 4` block with a zero row and column turns it into a
`Matrix5`, whose frozen `LegalTrace` gets the fourth readout bounded by D124's already-proved

`Rho5.ExternalFourthPivot.early_pivot_bounds_including_zero :
   values.getD 3 0 ≤ 4 * matrixEntryMax A`,

and `matrixEntryMax (padLast (S4 M)) = |S4 M 0 0| = p M` because `(0,0)` is a complete pivot.
Hence `height M ≤ 4 * p M` with no extra hypothesis beyond `LeadingInput`.
-/

noncomputable section

namespace Rho5.Shared.SchurFourPivotBound

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.FirstPivotDomain (matrixEntryMax_eq_abs_of_isCompletePivot)
open Rho5.Pivot (IsCompletePivot)
open Rho5.PivotReindex (pivotSchur)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.ExternalTailSaturation (LeadingInput height delta w)
open Rho5.CompletePivotPath (LegalTrace)

/-- The first Schur complement padded to a `5 x 5` matrix by a zero last row and column. -/
def padS4 (M : Matrix5) : Matrix5 := padLast (S4 M)

/-- The fifth pivot of `M` read on the padded first Schur complement. -/
theorem pivotSchur_T2_zero_zero (M : Matrix5) :
    pivotSchur (T2 M) 0 0 0 0 = delta M := by
  rw [pivotSchur_zero_zero]
  simp only [Rho5.Pivot.fixedSchur]
  simp [delta, w, t, s, r]

/-- The complete pivot of the `4 x 4` block survives the padding. -/
theorem isCompletePivot_padS4 {M : Matrix5} (h : IsCompletePivot (S4 M) 0 0) :
    IsCompletePivot (padS4 M) 0 0 :=
  (isCompletePivot_padLast_iff (S4 M)).mpr h

/-- **The real path.**  A `LeadingInput M` gives an all-`(0,0)` complete-pivot path of the actual
`4 x 4` first Schur complement, with the successive readouts `|p|`, `|k|`, `|r|`, `|delta|`. -/
theorem zeroTrace_S4 (M : Matrix5) (h : LeadingInput M) :
    ZeroTrace 4 (S4 M)
      [|S4 M 0 0|, |S3 M 0 0|, |T2 M 0 0|, |pivotSchur (T2 M) 0 0 0 0|] := by
  have h4 : IsCompletePivot (pivotSchur (T2 M) 0 0) 0 0 := by
    intro i j
    fin_cases i
    fin_cases j
    simp
  have hd0 : pivotSchur (T2 M) 0 0 0 0 ≠ 0 := by
    rw [pivotSchur_T2_zero_zero]
    exact h.delta_ne
  have t1 : ZeroTrace 1 (pivotSchur (T2 M) 0 0) [|pivotSchur (T2 M) 0 0 0 0|] := by
    have hnil : ZeroTrace 0 (pivotSchur (pivotSchur (T2 M) 0 0) 0 0) [] := by
      have hzero : pivotSchur (pivotSchur (T2 M) 0 0) 0 0 = (0 : Matrix (Fin 0) (Fin 0) ℝ) :=
        Subsingleton.elim _ _
      rw [hzero]
      exact ZeroTrace.nil
    exact ZeroTrace.step h4 hd0 hnil
  have t2 : ZeroTrace 2 (T2 M) [|T2 M 0 0|, |pivotSchur (T2 M) 0 0 0 0|] :=
    ZeroTrace.step h.cp3 (Rho5.ExternalTailSaturation.r_ne_zero h) t1
  have t3 : ZeroTrace 3 (S3 M) [|S3 M 0 0|, |T2 M 0 0|, |pivotSchur (T2 M) 0 0 0 0|] :=
    ZeroTrace.step h.cp2 (ne_of_gt h.k_pos) t2
  exact ZeroTrace.step h.cp1 (ne_of_gt h.p_pos) t3

/-- **The card's main theorem.**  `TS.height M ≤ 4 * B24Extraction.p M` for the actual matrix,
from `LeadingInput M` alone. -/
theorem height_le_four_mul_p (M : Matrix5) (h : LeadingInput M) :
    height M ≤ 4 * p M := by
  have hz : LegalTrace (padLast (S4 M))
      ([|S4 M 0 0|, |S3 M 0 0|, |T2 M 0 0|, |pivotSchur (T2 M) 0 0 0 0|] ++ [0]) :=
    (zeroTrace_S4 M h).toLegalTrace_padLast
  have hbound := Rho5.ExternalFourthPivot.fourth_pivot_le_four_mul_entryMax_including_zero
    (padLast (S4 M)) _ hz
  have hget : (([|S4 M 0 0|, |S3 M 0 0|, |T2 M 0 0|, |pivotSchur (T2 M) 0 0 0 0|] : List ℝ) ++ [0]).getD 3 0
      = |delta M| := by
    simp [pivotSchur_T2_zero_zero]
  have hmax : matrixEntryMax (padLast (S4 M)) = p M := by
    rw [matrixEntryMax_eq_abs_of_isCompletePivot (A := padLast (S4 M)) (p := 0) (q := 0)
      (isCompletePivot_padS4 h.cp1)]
    rw [padLast_zero_zero, show S4 M 0 0 = p M from rfl, abs_of_pos h.p_pos]
  rw [hget, hmax] at hbound
  rwa [height]

end Rho5.Shared.SchurFourPivotBound
