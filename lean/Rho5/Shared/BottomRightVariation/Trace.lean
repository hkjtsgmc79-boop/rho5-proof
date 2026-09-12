import Rho5.Shared.BottomRightVariation.Feasible

/-!
# D55 — the actual legal trace and growth ratio of a feasible corner shift

The card's last item: for a feasible shift of the actual matrix, the varied matrix
carries a real D13 `LegalTrace` whose values are the actual successive pivot absolute
values `[1, p M, k M, r M, |delta M + h|]`.

The first four entries are produced by the four *actual* first steps (`LegalTrace.step`
at `(0,0)` on `shift M h`, on `S4`, on `S3`, on `T2`), each justified by the
complete-pivot qualification proved in `Feasible.lean`.  The last `2 × 2` block is
handled by D46's arbitrary-tail trace, which already covers the vanishing-final-`1 × 1`
case through `zeroStop`; the tail entry is rewritten with D48's actual
`delta_eq_pivotSchur`.  Nothing here requires full rank, a balanced tail, or an isolated
tail hypothesis.

`growthRatio` is then the `tracePeak` of that same list, because the varied matrix is
normalized (`matrixEntryMax (shift M h) = 1`).
-/

namespace Rho5.BottomRightVariation

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.Pivot (IsCompletePivot)

/-- **The trace values of a feasible shift**: the four unchanged leading pivot readings
and the moved tail reading. -/
noncomputable def traceValues (M : Matrix5) (h : ℝ) : List ℝ :=
  [1, p M, k M, r M, |Rho5.CanonicalTail.delta M + h|]

theorem traceValues_eq (M : Matrix5) (h : ℝ) :
    traceValues M h = [1, p M, k M, r M, |Rho5.CanonicalTail.delta M + h|] := rfl

/-- **Item 4 (normalization of the varied matrix).** -/
theorem matrixEntryMax_shift (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hfeas : Feasible M h) :
    matrixEntryMax (shift M h) = 1 :=
  ((shift_qualifications_iff M h hmax h00 hcp hS4 hS3 hT2 hp hk hr).mpr hfeas).1

/-- **Item 4 (the actual legal trace).**  A feasible corner shift of the actual matrix
carries the real D13 `LegalTrace` with the values `[1, p M, k M, r M, |delta M + h|]`. -/
theorem legalTrace_shift (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hfeas : Feasible M h) :
    Rho5.CompletePivotPath.LegalTrace (shift M h) (traceValues M h) := by
  obtain ⟨_hnorm, hcp', hS4', hS3', hT2'⟩ :=
    (shift_qualifications_iff M h hmax h00 hcp hS4 hS3 hT2 hp hk hr).mpr hfeas
  -- the actual `2 × 2` tail, by D46's arbitrary-tail trace (zero final `1 × 1` included)
  have htail : Rho5.CompletePivotPath.LegalTrace (T2 (shift M h))
      [r M, |Rho5.CanonicalTail.delta M + h|] := by
    have h := Rho5.TailEnvelope.legalTrace_two_of_pivot_pos (T := T2 (shift M h)) hT2'
      (by rw [T2_shift_00]; exact hr)
    rwa [T2_shift_00, ← Rho5.CanonicalTail.delta_eq_pivotSchur, delta_shift] at h
  -- third actual step
  have step3 : Rho5.CompletePivotPath.LegalTrace (S3 (shift M h))
      [k M, r M, |Rho5.CanonicalTail.delta M + h|] := by
    have hne : S3 (shift M h) 0 0 ≠ 0 := by rw [S3_shift_00]; exact ne_of_gt hk
    have hv : |S3 (shift M h) 0 0| = k M := by rw [S3_shift_00]; exact abs_of_pos hk
    have h := Rho5.CompletePivotPath.LegalTrace.step (A := S3 (shift M h)) 0 0 hS3' hne htail
    simpa [hv] using h
  -- second actual step
  have step2 : Rho5.CompletePivotPath.LegalTrace (S4 (shift M h))
      [p M, k M, r M, |Rho5.CanonicalTail.delta M + h|] := by
    have hne : S4 (shift M h) 0 0 ≠ 0 := by rw [S4_shift_00]; exact ne_of_gt hp
    have hv : |S4 (shift M h) 0 0| = p M := by rw [S4_shift_00]; exact abs_of_pos hp
    have h := Rho5.CompletePivotPath.LegalTrace.step (A := S4 (shift M h)) 0 0 hS4' hne step3
    simpa [hv] using h
  -- first actual step
  have hne1 : shift M h 0 0 ≠ 0 := by
    rw [shift_of_ne_left M h (by decide : (0 : Fin 5) ≠ 4), h00]
    norm_num
  have h := Rho5.CompletePivotPath.LegalTrace.step (A := shift M h) 0 0 hcp' hne1 step2
  simpa [traceValues, h00] using h

/-- **Item 4 (growth ratio = peak of the trace list).**  With the varied matrix
normalized, its D17 growth ratio along that trace is exactly the `tracePeak` of the
card's five values. -/
theorem growthRatio_shift (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hfeas : Feasible M h) :
    Rho5.GrowthModel.growthRatio (shift M h) (traceValues M h) =
      Rho5.GrowthModel.tracePeak (traceValues M h) := by
  have hnorm := matrixEntryMax_shift M h hmax h00 hcp hS4 hS3 hT2 hp hk hr hfeas
  rw [Rho5.GrowthModel.growthRatio_eq, hnorm, div_one]

/-- The same growth ratio written with the literal five values. -/
theorem growthRatio_shift_eq (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) (hfeas : Feasible M h) :
    Rho5.GrowthModel.growthRatio (shift M h)
        [1, p M, k M, r M, |Rho5.CanonicalTail.delta M + h|] =
      Rho5.GrowthModel.tracePeak [1, p M, k M, r M, |Rho5.CanonicalTail.delta M + h|] :=
  growthRatio_shift M h hmax h00 hcp hS4 hS3 hT2 hp hk hr hfeas

end Rho5.BottomRightVariation
