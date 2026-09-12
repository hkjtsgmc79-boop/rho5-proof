import Rho5.Certificate.B24Trace.Trace
import Rho5.Shared.GrowthModel

/-!
# D33 / B24Trace — the growth ratio of the reconstructed trace

**Item 4 of the card.**  With D28's `matrixEntryMax (reconstruct z) = 1` and D17's
frozen definitions `tracePeak values = values.foldr max 0` and
`growthRatio A values = tracePeak values / matrixEntryMax A`:

* the actual growth ratio of the reconstructed matrix along the five-step trace is
  exactly the trace peak of `[1, p z, z 0, z 1, z 23]`
  (`growthRatio_reconstruct`);
* consequently the height coordinate is bounded by it, `z 23 ≤ growthRatio`
  (`le_growthRatio_z23`);
* the peak is *equal* to `z 23` only under the additional explicit bounds
  `1 ≤ z 23`, `p z ≤ z 23`, `z 0 ≤ z 23`, `z 1 ≤ z 23` (`growthRatio_eq_z23`).

The last statement is the conditional entry point for a future *sourced* attainment
witness: it does **not** assert that any point satisfying all the conditions exists,
does not assert that the height coordinate is attained by the model, and makes no
claim about `alpha`, about arbitrary matrices, or about the G04 critical-existence
path.
-/

namespace Rho5.Certificate.B24Trace

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage p HeadBand)

/-- **Item 4 (growth ratio = trace peak).**  The reconstructed matrix has entry
maximum `1` (D28), so its actual growth ratio along the five-step trace is the trace
peak itself. -/
theorem growthRatio_reconstruct (z : Point) (hz : Physical z) (hband : HeadBand z) :
    Rho5.GrowthModel.growthRatio (reconstruct z) [1, p z, z 0, z 1, z 23]
      = Rho5.GrowthModel.tracePeak [1, p z, z 0, z 1, z 23] := by
  rw [Rho5.GrowthModel.growthRatio_eq,
    Rho5.Certificate.B24Reconstruction.matrixEntryMax_reconstruct z hz hband, div_one]

/-- **Item 4 (`z 23 ≤ growthRatio`).**  The height coordinate is one of the recorded
stage values, hence bounded by the trace peak, hence by the growth ratio. -/
theorem le_growthRatio_z23 (z : Point) (hz : Physical z) (hband : HeadBand z) :
    z 23 ≤ Rho5.GrowthModel.growthRatio (reconstruct z) [1, p z, z 0, z 1, z 23] := by
  rw [growthRatio_reconstruct z hz hband]
  exact Rho5.GrowthModel.le_tracePeak (by simp)

/-- **Item 4 (conditional equality).**  If in addition the other four stage values
are bounded by `z 23`, then the trace peak — and therefore the growth ratio — is
exactly `z 23`.  This is the *conditional* form: the four bounds are explicit
hypotheses, not consequences of `Physical` or `HeadBand`. -/
theorem growthRatio_eq_z23 (z : Point) (hz : Physical z) (hband : HeadBand z)
    (h1 : 1 ≤ z 23) (h2 : p z ≤ z 23) (h3 : z 0 ≤ z 23) (h4 : z 1 ≤ z 23) :
    Rho5.GrowthModel.growthRatio (reconstruct z) [1, p z, z 0, z 1, z 23] = z 23 := by
  rw [growthRatio_reconstruct z hz hband]
  refine le_antisymm ?_ (Rho5.GrowthModel.le_tracePeak (by simp))
  refine Rho5.GrowthModel.tracePeak_le (le_trans zero_le_one h1) ?_
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact le_rfl

end Rho5.Certificate.B24Trace
