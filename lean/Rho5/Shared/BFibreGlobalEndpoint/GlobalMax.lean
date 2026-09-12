import Rho5.Shared.BFibreGlobalEndpoint.Basic

/-!
# D139 — the global maximizer endpoint at `z 23 = rho5Trace`

From `NormalizedB z` together with `z 23 = Rho5.GrowthSupremum.rho5Trace` (so `4 < rho5Trace` is
reused, not assumed), the fixed-frame fibre has a canonical endpoint that attains exactly the
global supremum: `capF (frameOf z) = rho5Trace`, the canonical point keeps the original frame, its
height is `rho5Trace`, and it dominates every `NormalizedB` source of that frame.  The real
reconstruction at that endpoint has a legal trace, `PolyCP`, and actual growth ratio `rho5Trace`.

The main interface is `normalizedB_global_max_has_canonical_fibre_endpoint`; it keeps the
`NormalizedB` source premise and does **not** assume that an original `ProperB` source has already
been converted into this domain.
-/

namespace Rho5.Shared.BFibreGlobalEndpoint

noncomputable section

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.ExternalBFibreCapacity

/-- `z 23 = rho5Trace` forces the capacity height to be exactly `rho5Trace`
(the upper bound is `capF_le_rho5Trace`, the lower bound is D121's `height_le_capF`). -/
theorem capF_eq_rho5Trace (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace) :
    capF (frameOf z) = Rho5.GrowthSupremum.rho5Trace :=
  le_antisymm (capF_le_rho5Trace z h) (hz ▸ height_le_capF z h)

/-- The high-value premise is automatic at `z 23 = rho5Trace` (D92's `four_lt_rho5Trace`). -/
theorem four_lt_of_eq_rho5Trace (z : Point) (hz : z 23 = Rho5.GrowthSupremum.rho5Trace) :
    (4 : ℝ) < z 23 := by
  rw [hz]
  exact Rho5.Shared.GlobalAttainedWitness.four_lt_rho5Trace

/-- At `z 23 = rho5Trace` the actual growth of the canonical endpoint is the global supremum. -/
theorem global_max_growth_eq_rho5Trace (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace) :
    Rho5.GrowthModel.growthRatio (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) = Rho5.GrowthSupremum.rho5Trace := by
  rw [growth_eq_capF_of_four_lt z h (four_lt_of_eq_rho5Trace z hz), capF_eq_rho5Trace z h hz]

/-- **Main interface (D139)**: a `NormalizedB` source whose height is the global supremum has a
canonical fibre endpoint attaining exactly that supremum, with the original frame preserved, real
legal trace / `PolyCP`, and domination of every `NormalizedB` source of the same frame. -/
theorem normalizedB_global_max_has_canonical_fibre_endpoint (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace) :
    capF (frameOf z) = Rho5.GrowthSupremum.rho5Trace ∧
    frameOf (canonicalPoint (frameOf z)) = frameOf z ∧
    canonicalPoint (frameOf z) 23 = Rho5.GrowthSupremum.rho5Trace ∧
    NormalizedB (canonicalPoint (frameOf z)) ∧
    (∀ w : Point, NormalizedB w → frameOf w = frameOf z →
      w 23 ≤ canonicalPoint (frameOf z) 23) ∧
    (∀ w : Point, NormalizedB w → frameOf w = frameOf z →
      w 23 ≤ Rho5.GrowthSupremum.rho5Trace) ∧
    Rho5.CompletePivotPath.LegalTrace (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) ∧
    Rho5.MinorCPDomain.PolyCP (reconstruct (canonicalPoint (frameOf z))) ∧
    Rho5.GrowthModel.growthRatio (reconstruct (canonicalPoint (frameOf z)))
      (canonicalPivots (frameOf z)) = Rho5.GrowthSupremum.rho5Trace := by
  have hcap := capF_eq_rho5Trace z h hz
  obtain ⟨hnorm, hframe, hheight, hdom⟩ := complete_fibre_argmax z h
  obtain ⟨-, hlegal, hpoly, -⟩ := canonical_endpoint_matrix z h
  refine ⟨hcap, hframe, ?_, hnorm, hdom, ?_, hlegal, hpoly,
    global_max_growth_eq_rho5Trace z h hz⟩
  · rw [hheight, hcap]
  · intro w hw hf
    have hwv := height_le_capF w hw
    rw [hf, hcap] at hwv
    exact hwv

/-- Existence form of the main interface: the canonical fibre endpoint itself is the witness. -/
theorem exists_global_max_canonical_fibre_endpoint (z : Point) (h : NormalizedB z)
    (hz : z 23 = Rho5.GrowthSupremum.rho5Trace) :
    ∃ zStar : Point,
      NormalizedB zStar ∧ frameOf zStar = frameOf z ∧
      zStar 23 = Rho5.GrowthSupremum.rho5Trace ∧
      Rho5.matrixEntryMax (reconstruct zStar) = 1 ∧
      Rho5.CompletePivotPath.LegalTrace (reconstruct zStar)
        [1, Rho5.Certificate.B24Reconstruction.p zStar, zStar 0, zStar 1, zStar 23] ∧
      (∀ w : Point, NormalizedB w → frameOf w = frameOf z → w 23 ≤ zStar 23) := by
  refine ⟨canonicalPoint (frameOf z), canonical_endpoint_normalized z h,
    canonical_endpoint_frame z h, ?_, (canonical_endpoint_matrix z h).1,
    (canonical_endpoint_matrix z h).2.1, canonical_endpoint_dominates z h⟩
  rw [canonical_endpoint_height z h, capF_eq_rho5Trace z h hz]

end

end Rho5.Shared.BFibreGlobalEndpoint
