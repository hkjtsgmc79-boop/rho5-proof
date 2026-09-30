import Rho5.Shared.XSmallKSigns.Tail

/-!
# D143 stage B (adapter) — `1 < p` from the high-value branch and D138's `F ≤ 4p`

The card's stage B needs `p > 1`.  It comes from two already-proved inputs:

* the high-value branch `q_* = 1653/400 ≤ height M` (which is exactly the V31 reading
  `F = r - w`, **not** the balanced–negative-D `F = 2r`), and
* D138's `height M ≤ 4 * p M`, applied through the `SatFrame → LeadingInput` adapter.

`4 < q_* ≤ height M ≤ 4p` gives `1 < p M`; D119's head band then gives `e β > 0`.
-/

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.ExternalTailSaturation (w delta height)
open Rho5.Shared.V43MatrixRoundTrip

/-- `q_* ≤ height M` makes the fifth pivot non-zero, so D138's `LeadingInput` applies. -/
theorem delta_ne_of_height {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) :
    delta M ≠ 0 := by
  intro h0
  have hz : height M = 0 := by unfold height; rw [h0, abs_zero]
  linarith [qstar_gt_four]

/-- D138's `F ≤ 4p` read on the actual X frame (no extra hypothesis beyond the card's). -/
theorem height_le_four_mul_p_of_satFrame {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) :
    height M ≤ 4 * p M :=
  Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p M
    (leadingInput_of_satFrame h (delta_ne_of_height h hq))

/-- **The `1 < p` adapter**: `4 < q_* ≤ height M ≤ 4p`. -/
theorem one_lt_p_of_height {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) :
    1 < p M := by
  have h4 := height_le_four_mul_p_of_satFrame h hq
  linarith [qstar_gt_four]

/-- The head band `p - 1 ≤ e β` then forces `e β > 0` — the input of the head flip. -/
theorem eX_mul_betaX_pos {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) :
    0 < eX M * betaX M := by
  have hge := eX_mul_betaX_ge h
  have hp : pX M = p M := rfl
  have h1 := one_lt_p_of_height h hq
  rw [hp] at hge
  linarith

end Rho5.Shared.XSmallKSigns
