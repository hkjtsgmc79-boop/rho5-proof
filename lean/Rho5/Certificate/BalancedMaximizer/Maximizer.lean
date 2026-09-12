/-
D65 — item 4: the conditional interface for a global maximizer on the balanced branch
=====================================================================================

If an actual qualified matrix `M` is a global maximizer in the sense that its own growth ratio
equals `rho5Trace`, then — **conditionally on its balanced branch** — there is an explicit
physical B24 point at height `rho5Trace` reconstructing `M`, together with the original global
comparison that `rho5Trace` bounds every growth value.

This is the interface D57's fourth saturation case (`T2_11 = -r`) will consume.  The other three
shifted-endpoint branches (`M44 = -1`, `S4_33 = -p`, `S3_22 = -k`) are **not** covered here, and
nothing in this file claims they can be reduced to this one.
-/
import Rho5.Certificate.BalancedMaximizer.Physical
import Rho5.Shared.GrowthSupremum

namespace Rho5.Certificate.BalancedMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.Certificate.B16 (Physical)
open Rho5.Certificate.B24Reconstruction (HeadBand)

/-- **Item 4.**  Conditional packaging of the balanced global maximizer: a physical point at
height `rho5Trace` plus the original global comparison. -/
theorem exists_physical_point_at_rho (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (hrho : Rho5.GrowthModel.growthRatio M (balancedValues M)
      = Rho5.GrowthSupremum.rho5Trace)
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    (∃ z : Rho5.Certificate.B16.Point,
        Physical z ∧ HeadBand z ∧ z 23 = Rho5.GrowthSupremum.rho5Trace ∧
          Rho5.Certificate.B24Reconstruction.reconstruct z = M) ∧
      (∀ g ∈ Rho5.GrowthModel.GrowthValues, g ≤ Rho5.GrowthSupremum.rho5Trace) := by
  obtain ⟨hphys, hband, hrec, h23, -⟩ :=
    physical_point_at_height M hM h00 h hgrowth htail hs ht
  refine ⟨⟨Rho5.Certificate.B24Extraction.extract M, hphys, hband, ?_, hrec⟩, ?_⟩
  · rw [h23, hrho]
  · intro g hg
    exact Rho5.GrowthSupremum.le_rho5Trace hg

/-- The same witness read as a lower bound for the supremum: on the balanced branch the global
maximizer's own growth value is one of the growth values. -/
theorem balanced_mem_growthValues (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Rho5.GrowthModel.growthRatio M (balancedValues M)
      ∈ Rho5.GrowthModel.GrowthValues := by
  obtain ⟨-, -, -, -, htrace⟩ :=
    physical_point_at_height M hM h00 h hgrowth htail hs ht
  -- `prefix_structure`: four pivot conjuncts, then `0 < M 0 0`, `0 < p`, `0 < k`, `0 < r`.
  obtain ⟨-, -, -, -, -, -, -, hrpos, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth

  have hFabs : |Rho5.CanonicalTail.delta M| = F M := abs_delta_eq_F M htail hrpos hs ht
  have hvals : balancedValues M = [1, p M, k M, r M, F M] := by
    simp only [balancedValues, hFabs]
  refine ⟨M, [1, p M, k M, r M, F M], ?_, htrace, ?_⟩
  · intro hzero
    have h01 : (0 : ℝ) = 1 := by
      have h' := h00
      rw [hzero] at h'
      simpa only [Matrix.zero_apply] using h'
    exact zero_ne_one h01
  · rw [← hvals]

end Rho5.Certificate.BalancedMaximizer
