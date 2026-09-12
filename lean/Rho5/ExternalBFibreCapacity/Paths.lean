import Rho5.ExternalBFibreCapacity.Maximum
import Rho5.ExternalBFibreCapacity.PrefixPaths

namespace Rho5.ExternalBFibreCapacity
noncomputable section
open Rho5.Certificate.B16 (Point)

/-- F is recomputed from r,s,t by encode. This is NOT a convex combination of
all 24 coordinates. -/
def tailPath (z : Point) (lam : ℝ) : Point :=
  encode (frameOf z) (betaBar (frameOf z)) (prefixP (frameOf z)) (prefixE (frameOf z))
    (tailMix (tailOf z) (canonicalTail (frameOf z)) lam)

theorem tailPath_spec (z : Point) (h : NormalizedB z) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    NormalizedB (tailPath z lam) ∧ frameOf (tailPath z lam) = frameOf z ∧
      tailPath z lam 23 = tailPath z lam 1 + tailPath z lam 2*tailPath z lam 3/tailPath z lam 1 := by
  exact ⟨(admissible_iff_normalized _ _ _ _ _).mp
    (tail_segment_admissible (admissible_decode z h) h0 h1), frameOf_encode _ _ _ _ _, rfl⟩

theorem tailPath_height_monotone (z : Point) (h : NormalizedB z)
    {lam μ : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hlamμ : lam ≤ μ) : tailPath z lam 23 ≤ tailPath z μ 23 :=
  tail_segment_height_mono (admissible_decode z h) hlam0 hlam1 hμ0 hμ1 hlamμ

theorem three_path_endpoints (z : Point) (h : NormalizedB z) :
    betaPath z 0 = z ∧ betaPath z 1 = pePath z 0 ∧
    pePath z 1 = tailPath z 0 ∧ tailPath z 1 = canonicalPoint (frameOf z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [betaPath] using encode_decode z h.1.physical
  · simp [betaPath, pePath]
  · simp [pePath, tailPath]
  · simp [tailPath, canonicalPoint]

/-- Physical matrices on every path, not merely formal coordinate curves. -/
theorem actual_path_legal_traces (z : Point) (h : NormalizedB z)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (∀ w ∈ [betaPath z lam, pePath z lam, tailPath z lam],
      Rho5.CompletePivotPath.LegalTrace (Rho5.Certificate.B24Reconstruction.reconstruct w)
        [1, Rho5.Certificate.B24Reconstruction.p w, w 0, w 1, w 23]) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Rho5.Certificate.B24MinorBridge.legalTrace_reconstruct _ (betaPath_spec z h h0 h1).1.1
  · exact Rho5.Certificate.B24MinorBridge.legalTrace_reconstruct _ (pePath_spec z h h0 h1).1.1
  · exact Rho5.Certificate.B24MinorBridge.legalTrace_reconstruct _ (tailPath_spec z h h0 h1).1.1

end
end Rho5.ExternalBFibreCapacity
