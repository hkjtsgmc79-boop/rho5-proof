import Rho5.ExternalTailSaturation.Growth
import Rho5.ExternalFourthPivot.SharpEarly

/-!
# D125 — the real early bounds of a tail-saturation input

For the real TS input `Rho5.ExternalTailSaturation.LeadingInput M` (D122's eight fields: head
`M 0 0 = 1`, the four leading complete pivots, `0 < p M`, `0 < k M`, `delta M ≠ 0`) this module
pays, with no extra hypothesis,

* `p M ≤ 2`, `k M ≤ 9/4`, `|r M| ≤ 4`.

Route: D122's real five-step trace `LegalTrace M [1, p M, k M, |r M|, height M]` and
`matrixEntryMax M = 1`, fed into **D124's arbitrary-original-path packet**
(`normalized_early_pivots`).  The fourth pivot **may be negative**: this does not go through the
positive-`r` D86 route, so no unpaid positive-pivot shortcut is used.
-/

noncomputable section
namespace Rho5.Shared.TailSaturationBounds

open Rho5
open Rho5.Certificate.B24Extraction (p k r)
open Rho5.ExternalTailSaturation (LeadingInput height leading_legalTrace entryMax_eq_one)

/-- **The real early bounds of the TS input**: `p M ≤ 2 ∧ k M ≤ 9/4 ∧ |r M| ≤ 4`, for an
arbitrary `LeadingInput M` — in particular with a negative fourth pivot. -/
theorem input_early_bounds {M : Matrix5} (h : LeadingInput M) :
    p M ≤ 2 ∧ k M ≤ (9 : ℝ) / 4 ∧ |r M| ≤ 4 := by
  have htrace : Rho5.CompletePivotPath.LegalTrace M [1, p M, k M, |r M|, height M] :=
    leading_legalTrace h
  have hmax : matrixEntryMax M = 1 := entryMax_eq_one M h.head h.cp0
  obtain ⟨-, h1, h2, h3⟩ :=
    Rho5.ExternalFourthPivot.normalized_early_pivots M _ hmax htrace
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

end Rho5.Shared.TailSaturationBounds
