import Rho5.Shared.XSmallKSigns.Defs
import Rho5.Shared.SchurFourPivotBound.Bound
import Mathlib.Tactic.Linarith

/-!
# D143 stage A — the tied-tail arithmetic and the `LeadingInput` adapter

For the X case (`SatFrame M` gives `s M = t M = r M`):

* `F M = 2 * r M`, `delta M = w M - r M`, `height M = |w M - r M|`;
* `SatFrame M` plus `delta M ≠ 0` is exactly `LeadingInput M` (so D138's `F ≤ 4 p` applies);
* `|w M| ≤ r M` with `q_* ≤ height M` forces `r M > 2`, hence `k M < r M` from `k M ≤ 2`.

These are the numeric inputs the sign normalization consumes; no sign conclusion is assumed.
-/

noncomputable section

namespace Rho5.Shared.XSmallKSigns

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.ExternalTailSaturation (LeadingInput delta w height)
open Rho5.Shared.V43MatrixRoundTrip (SatFrame rX wX)

/-- In the tied X case the height `F` is exactly twice the tail pivot. -/
theorem F_eq_two_mul_r {M : Matrix5} (h : SatFrame M) : F M = 2 * r M := by
  have hr : r M ≠ 0 := ne_of_gt h.hr
  unfold F
  rw [h.hs, h.ht, mul_div_cancel_right₀ _ hr]
  ring

/-- The fifth pivot read through the tied tail. -/
theorem delta_eq {M : Matrix5} (h : SatFrame M) : delta M = w M - r M := by
  unfold delta
  rw [h.hs, h.ht, mul_div_cancel_right₀ _ (ne_of_gt h.hr)]

theorem height_eq {M : Matrix5} (h : SatFrame M) : height M = |w M - r M| := by
  unfold height
  rw [delta_eq h]

/-- `SatFrame` plus a non-zero fifth pivot is exactly D138's `LeadingInput`, so the already-proved
`height_le_four_mul_p` applies to the actual X frame without any new hypothesis. -/
theorem leadingInput_of_satFrame {M : Matrix5} (h : SatFrame M) (hdelta : delta M ≠ 0) :
    LeadingInput M where
  head := h.h00
  cp0 := h.cp1
  cp1 := h.cp2
  cp2 := h.cp3
  cp3 := h.cp4
  p_pos := h.hp
  k_pos := h.hk
  delta_ne := hdelta

/-- The paper's `r ≥ F/2 > 2 ≥ k` chain, from `|w| ≤ r`, `q_* ≤ height M` and `k M ≤ 2`. -/
theorem two_lt_r {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) : 2 < r M := by
  have hw := Rho5.Shared.V43MatrixRoundTrip.abs_wX_le_rX M h
  have hle : w M ≤ r M := Rho5.Shared.V43MatrixRoundTrip.wX_le_rX M h
  have hwle : -r M ≤ w M := neg_le_of_abs_le hw
  have hheight : height M = r M - w M := by
    rw [height_eq h, abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  have h2 : qstar ≤ 2 * r M := by linarith
  have := two_lt_qstar_half
  linarith

/-- The third pivot stays strictly below the tail pivot on this branch. -/
theorem k_lt_r {M : Matrix5} (h : SatFrame M) (hq : qstar ≤ height M) (hk2 : k M ≤ 2) :
    k M < r M :=
  lt_of_le_of_lt hk2 (two_lt_r h hq)

end Rho5.Shared.XSmallKSigns
