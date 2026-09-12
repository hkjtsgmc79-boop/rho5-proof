import Rho5.ExternalBFibreCapacity
import Rho5.Certificate.B24MinorBridge.Schur
import Rho5.Shared.LastThreePivotEnvelope.GlobalBound
import Rho5.Shared.GlobalAttainedWitness.Range
import Rho5.Shared.GrowthSupremum

/-!
# D139 — the real B-fibre capacity endpoint

Assembly only: this module consumes the accepted D121 capacity layer
(`Rho5.ExternalBFibreCapacity`), D87's compiled pivot bounds
(`Rho5.LastThreePivotEnvelope`), D92's global range fact (`4 < rho5Trace`) and the frozen
`GrowthValues`/`rho5Trace` interface.  Nothing is re-proved and no numerical search or global
`alpha` statement is made.

For an arbitrary `NormalizedB z` the *actual* reconstruction
`reconstruct (canonicalPoint (frameOf z))` with the *actual* pivot list
`canonicalPivots (frameOf z)` is used throughout; no matrix or trace is replaced by an abstract
sequence.

## 1. High-value premise

* `four_lt_capF` — `4 < z 23` implies `4 < capF (frameOf z)` through D121's `height_le_capF`;
* `prefixP_le_two` — D120's `prefix_maximum` at the decoded source;
* `k_le_nine_quarters` — D87's second-pivot bound at the real reconstruction, read back with
  `k_reconstruct : k (reconstruct z) = z 0`;
* hence the three explicit dominance premises of D121's `actual_growth_eq_capacity` are paid and
  `growth_eq_capF_of_four_lt` gives the *actual* `growthRatio = capF`.

## 2. `capF` below the global trace supremum

`capF_le_rho5Trace` — the capacity height is realised by the real reconstruction with its real
legal trace, so it is a member of `Rho5.GrowthModel.GrowthValues` and hence below
`Rho5.GrowthSupremum.rho5Trace` (this is the actual global growth upper bound, not an abstract
sequence bound).
-/

namespace Rho5.Shared.BFibreGlobalEndpoint

noncomputable section

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct reconstruct_zero_zero)
open Rho5.Certificate.B24MinorBridge (Qualified polyCP_reconstruct k_reconstruct)
open Rho5.ExternalBFibreCapacity

/-! ## 1. The high-value premise and the frame bounds it needs -/

/-- The high-value premise lifts to the canonical capacity height. -/
theorem four_lt_capF (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    (4 : ℝ) < capF (frameOf z) :=
  lt_of_lt_of_le hz (height_le_capF z h)

/-- The first dominance premise of `actual_growth_eq_capacity`. -/
theorem one_le_capF (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    (1 : ℝ) ≤ capF (frameOf z) :=
  le_trans (by norm_num) (le_of_lt (four_lt_capF z h hz))

/-- The frame prefix is at most `2` (D120's `prefix_maximum` at the decoded source). -/
theorem prefixP_le_two (z : Point) (h : NormalizedB z) : prefixP (frameOf z) ≤ (2 : ℝ) :=
  (prefix_maximum (admissible_decode z h)).2.2.2.1

/-- The second dominance premise: `p ≤ 2 < 4 < capF`. -/
theorem prefixP_lt_capF (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    prefixP (frameOf z) < capF (frameOf z) :=
  lt_of_le_of_lt (prefixP_le_two z h) (lt_trans (by norm_num) (four_lt_capF z h hz))

/-- The frame coordinate `k` is at most `9/4`: D87's second-pivot bound at the real
reconstruction, read back with `k_reconstruct`. -/
theorem k_le_nine_quarters (z : Point) (h : NormalizedB z) : (frameOf z).k ≤ (9 : ℝ) / 4 := by
  have hk := Rho5.LastThreePivotEnvelope.k_le_nine_quarters (reconstruct z)
    (reconstruct_zero_zero z) (polyCP_reconstruct z h.1)
  rwa [k_reconstruct z (ne_of_gt h.1.p_pos)] at hk

/-- The third dominance premise: `k ≤ 9/4 < 4 < capF`. -/
theorem k_lt_capF (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    (frameOf z).k < capF (frameOf z) :=
  lt_of_le_of_lt (k_le_nine_quarters z h) (lt_trans (by norm_num) (four_lt_capF z h hz))

/-! ## 2. The actual canonical endpoint -/

theorem canonical_endpoint_normalized (z : Point) (h : NormalizedB z) :
    NormalizedB (canonicalPoint (frameOf z)) :=
  (complete_fibre_argmax z h).1

theorem canonical_endpoint_frame (z : Point) (h : NormalizedB z) :
    frameOf (canonicalPoint (frameOf z)) = frameOf z :=
  (complete_fibre_argmax z h).2.1

theorem canonical_endpoint_height (z : Point) (h : NormalizedB z) :
    canonicalPoint (frameOf z) 23 = capF (frameOf z) :=
  (complete_fibre_argmax z h).2.2.1

theorem canonical_endpoint_dominates (z : Point) (h : NormalizedB z) :
    ∀ w : Point, NormalizedB w → frameOf w = frameOf z →
      w 23 ≤ canonicalPoint (frameOf z) 23 :=
  (complete_fibre_argmax z h).2.2.2

/-- The real-matrix facts at the canonical endpoint (entry max `1`, legal trace, `PolyCP`, and the
capacity below the actual growth), re-exposed from D121's `actual_matrix_attainment`. -/
theorem canonical_endpoint_matrix (z : Point) (h : NormalizedB z) :
    Rho5.matrixEntryMax (reconstruct (canonicalPoint (frameOf z))) = 1 ∧
    Rho5.CompletePivotPath.LegalTrace (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) ∧
    Rho5.MinorCPDomain.PolyCP (reconstruct (canonicalPoint (frameOf z))) ∧
    capF (frameOf z) ≤ Rho5.GrowthModel.growthRatio
      (reconstruct (canonicalPoint (frameOf z))) (canonicalPivots (frameOf z)) :=
  actual_matrix_attainment z h

/-! ## 3. `capF` below the global trace supremum -/

/-- **`capF (frameOf z) ≤ rho5Trace`** for every `NormalizedB z`.  The capacity height is
realised by the actual reconstruction with its actual legal trace, hence its growth ratio is a
member of `Rho5.GrowthModel.GrowthValues`, hence below the supremum. -/
theorem capF_le_rho5Trace (z : Point) (h : NormalizedB z) :
    capF (frameOf z) ≤ Rho5.GrowthSupremum.rho5Trace := by
  obtain ⟨hmax, hlegal, -, hle⟩ := actual_matrix_attainment z h
  refine le_trans hle (Rho5.GrowthSupremum.le_rho5Trace ?_)
  exact ⟨reconstruct (canonicalPoint (frameOf z)), canonicalPivots (frameOf z),
    Rho5.GrowthModel.ne_zero_of_matrixEntryMax_eq_one hmax, hlegal, rfl⟩

/-! ## 4. The high-value endpoint: the real growth is exactly `capF` -/

/-- **The actual growth of the canonical endpoint equals its capacity**, with all three explicit
dominance premises paid from `4 < z 23` (`p ≤ 2`, `k ≤ 9/4`); `r`'s dominance is D121's
`canonical_r_le_height`, used inside `actual_growth_eq_capacity`. -/
theorem growth_eq_capF_of_four_lt (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    Rho5.GrowthModel.growthRatio (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) = capF (frameOf z) :=
  actual_growth_eq_capacity z h
    (one_le_capF z h hz) (le_of_lt (prefixP_lt_capF z h hz)) (le_of_lt (k_lt_capF z h hz))

/-- **High-value capacity endpoint bundle**: the canonical endpoint is a normalized source with
the original frame, height `capF`, `4 < capF`, `capF ≤ rho5Trace`, actual `growth = capF`, a real
legal trace and `PolyCP`. -/
theorem high_value_capacity_endpoint (z : Point) (h : NormalizedB z) (hz : (4 : ℝ) < z 23) :
    NormalizedB (canonicalPoint (frameOf z)) ∧
    frameOf (canonicalPoint (frameOf z)) = frameOf z ∧
    canonicalPoint (frameOf z) 23 = capF (frameOf z) ∧
    (4 : ℝ) < capF (frameOf z) ∧
    capF (frameOf z) ≤ Rho5.GrowthSupremum.rho5Trace ∧
    Rho5.GrowthModel.growthRatio (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) = capF (frameOf z) ∧
    Rho5.CompletePivotPath.LegalTrace (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) ∧
    Rho5.MinorCPDomain.PolyCP (reconstruct (canonicalPoint (frameOf z))) :=
  ⟨canonical_endpoint_normalized z h, canonical_endpoint_frame z h, canonical_endpoint_height z h,
    four_lt_capF z h hz, capF_le_rho5Trace z h, growth_eq_capF_of_four_lt z h hz,
    (canonical_endpoint_matrix z h).2.1, (canonical_endpoint_matrix z h).2.2.1⟩

end

end Rho5.Shared.BFibreGlobalEndpoint
