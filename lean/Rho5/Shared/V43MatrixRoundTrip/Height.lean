/-
D119 — the height reading of the extracted point
================================================

Two readings that tie the reverse coordinates to the frozen δ notation:

* `delta_eq_wX_sub_rX : CanonicalTail.delta M = w - r` — the reverse counterpart of D103's
  `canonicalTail_delta_eq`.  With the saturated tail `s = t = r`, the frozen
  `δ = T2 1 1 - t s / r` collapses to `T2 1 1 - r`, i.e. to the free coordinate `w` minus the tail
  pivot; `D 2 2 = w + B d` is what carries `w`, so no `w = -r` substitution appears anywhere.
* `height_extractX : height (extractX M) = |delta M|` — the extracted point's height is exactly the
  absolute value of the frozen δ.  The orientation uses `IsCompletePivot (T2 M) 0 0`, which gives
  `|w| ≤ r` and hence `w ≤ r`, so `r - w = |w - r|`.
-/
import Rho5.Shared.V43MatrixRoundTrip.Physical

namespace Rho5.Shared.V43MatrixRoundTrip

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **`δ M = w - r`** for a saturated-frame matrix.  This is the reverse of D103's forward reading:
the frozen `δ = T2 1 1 - t · s / r` with `s = t = r` is `T2 1 1 - r`, and `T2 1 1` is the free
coordinate `w`. -/
theorem delta_eq_wX_sub_rX (M : Matrix5) (h : SatFrame M) :
    Rho5.CanonicalTail.delta M = wX M - rX M := by
  have hs : T2 M 0 1 = T2 M 0 0 := h.hs
  have ht : T2 M 1 0 = T2 M 0 0 := h.ht
  have hr : T2 M 0 0 ≠ 0 := rX_ne_zero M h
  rw [Rho5.CanonicalTail.delta]
  simp only [Rho5.Certificate.B24Extraction.s, Rho5.Certificate.B24Extraction.t,
    Rho5.Certificate.B24Extraction.r, hs, ht, wX, rX]
  try field_simp
  try ring

/-- **The height of the extracted point is `|δ M|`.** -/
theorem height_extractX (M : Matrix5) (h : SatFrame M) :
    Rho5.LocalAnalysis.height (extractX M) = |Rho5.CanonicalTail.delta M| := by
  have hd : Rho5.CanonicalTail.delta M = wX M - rX M := delta_eq_wX_sub_rX M h
  have hwr : wX M ≤ rX M := wX_le_rX M h
  rw [Rho5.LocalAnalysis.height, extractX_1, extractX_2, hd,
    abs_of_nonpos (by linarith : wX M - rX M ≤ 0)]
  ring

end

end Rho5.Shared.V43MatrixRoundTrip
