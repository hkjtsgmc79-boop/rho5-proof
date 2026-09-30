import Rho5.Shared.XSmallKSigns.Representative
import Rho5.Shared.XSmallKBranch.PhysicalBridge
import Rho5.Shared.XSmallKBranch.RootBox

/-!
# D143 final gate — the D136 `chartState` interface of the real representative

This module closes the card by instantiating the **already-compiled** D136 interface
(`parallel/D136`, reused read-only through its olean root — no D136 source is re-elaborated):

* `NormalizedSigns (chartState N)` from the stage-A signs `A, B < 0 < c, d` (strict implies the
  non-strict fields D136 declares as its input);
* `PosSigns (chartState N)` from `e, β > 0`;
* `0 ≤ uu (chartState N) 0` from `0 ≤ uX N 0`;
* `HighValue`/`SmallThirdPivot` transported along the *proved* invariance `height N = height M`,
  `k N = k M` (so the representative really is on the same high-value small-`k` branch);
* `PhysicalBounds (chartState N)` re-derived from `SatFrame N` by D136's own theorem, and
  `Rho4Input (chartState N)` re-derived from D138's `F ≤ 4p` on `N`.

Nothing is assumed about the target: every field is a theorem about the actual matrix `N`.
-/

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.ExternalTailSaturation (w delta height)
open Rho5.Shared.V43MatrixRoundTrip
open Rho5.Shared.XSmallKBranch

/-- On the tied X frame the card's `F` is read as `r - w` (V31), so the model's
`rr - ww` is exactly `height`. -/
theorem height_eq_rr_sub_ww {M : Matrix5} (h : SatFrame M) :
    height M = rr (chartState M) - ww (chartState M) := by
  have hle : w M ≤ r M := Rho5.Shared.V43MatrixRoundTrip.wX_le_rX M h
  rw [height_eq h, abs_of_nonpos (sub_nonpos.mpr hle), rr_chartState, ww_chartState]
  simp only [rX, wX, r, w]
  ring

/-- **The D136 interface of a frame carrying the D143 sign pattern.** -/
theorem chartState_interface {N : Matrix5} (hN : SatFrame N) (hq : qstar ≤ height N)
    (hk2 : k N ≤ 2)
    (hA : aX N < 0) (hB : bX N < 0) (hC : 0 < cX N) (hD : 0 < dX N)
    (he : 0 < eX N) (hb : 0 < betaX N) (hu : 0 ≤ uX N 0) :
    PhysicalBounds (chartState N) ∧ NormalizedSigns (chartState N) ∧ PosSigns (chartState N) ∧
      HighValue (chartState N) ∧ SmallThirdPivot (chartState N) ∧ Rho4Input (chartState N) ∧
        0 ≤ uu (chartState N) 0 := by
  refine ⟨physicalBounds_chartState N hN, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [AA_chartState]; linarith, by rw [BB_chartState]; linarith,
      by rw [cc_chartState]; linarith, by rw [dd_chartState]; linarith⟩
  · exact ⟨by rw [ee_chartState]; exact he, by rw [be_chartState]; exact hb⟩
  · show qstar ≤ rr (chartState N) - ww (chartState N)
    rw [← height_eq_rr_sub_ww hN]; exact hq
  · show kk (chartState N) ≤ 2
    rw [kk_chartState]; exact hk2
  · show rr (chartState N) - ww (chartState N) ≤ 4 * pp (chartState N)
    rw [← height_eq_rr_sub_ww hN, pp_chartState]
    exact height_le_four_mul_p_of_satFrame hN hq
  · rw [uu_chartState]; exact hu

/-- **D143 final theorem.**  From the actual `SatFrame M` with `q_* ≤ height M` and `k M ≤ 2`
there is a real same-height representative `N` (an explicit three-fold sign flip of `M`) whose
chart state satisfies, *as theorems*, the exact interface D136 consumes: `SatFrame N`,
`PhysicalBounds`, `NormalizedSigns`, `PosSigns`, `HighValue`, `SmallThirdPivot`, `Rho4Input` and
`0 ≤ u₀`. -/
theorem sign_representative_chartState {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ height M) (hk2 : k M ≤ 2) :
    ∃ (σ₁ σ₂ σ₃ : ℝ) (N : Matrix5),
      (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧ (σ₃ = 1 ∨ σ₃ = -1) ∧
        N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M)) ∧
          SatFrame N ∧ PhysicalBounds (chartState N) ∧ NormalizedSigns (chartState N) ∧
            PosSigns (chartState N) ∧ HighValue (chartState N) ∧ SmallThirdPivot (chartState N) ∧
              Rho4Input (chartState N) ∧ 0 ≤ uu (chartState N) 0 ∧
                height N = height M ∧ k N = k M := by
  obtain ⟨σ₁, σ₂, σ₃, hσ₁, hσ₂, hσ₃, hS, hH, _hP, hK, _hR, _hW, hA, hB, hC, hD, he, hb, hu⟩ :=
    sign_representative_exists h hq hk2
  have hqN : qstar ≤ height (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) := by rw [hH]; exact hq
  have hk2N : k (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ≤ 2 := by rw [hK]; exact hk2
  obtain ⟨hPhys, hNS, hPS, hHV, hSTP, hR4, hu0⟩ := chartState_interface hS hqN hk2N hA hB hC hD he hb hu
  exact ⟨σ₁, σ₂, σ₃, _, hσ₁, hσ₂, hσ₃, rfl, hS, hPhys, hNS, hPS, hHV, hSTP, hR4, hu0, hH, hK⟩

end Rho5.Shared.XSmallKSigns
