import Rho5.ExternalBFibreCapacity.Prefix
import Rho5.ExternalBFibreCapacity.CapacityCount

namespace Rho5.ExternalBFibreCapacity
noncomputable section
open Rho5.Certificate.B16 (Point)

/-- Only beta changes in the first actual B24 path. -/
def betaPath (z : Point) (lam : ℝ) : Point :=
  encode (frameOf z) (mix (z 10) (betaBar (frameOf z)) lam) (z 8) (z 9) (tailOf z)

/-- Both p and e change in the second actual path; D,S,O and height do not. -/
def pePath (z : Point) (lam : ℝ) : Point :=
  encode (frameOf z) (betaBar (frameOf z))
    (mix (z 8) (prefixP (frameOf z)) lam)
    (mix (z 9) (prefixE (frameOf z)) lam) (tailOf z)

theorem betaPath_spec (z : Point) (h : NormalizedB z) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    NormalizedB (betaPath z lam) ∧ frameOf (betaPath z lam) = frameOf z ∧
      betaPath z lam 23 = z 23 := by
  refine ⟨(admissible_iff_normalized _ _ _ _ _).mp
    (beta_segment_admissible (admissible_decode z h) h0 h1), frameOf_encode _ _ _ _ _, ?_⟩
  exact h.1.physical.height.symm

theorem pePath_spec (z : Point) (h : NormalizedB z) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    NormalizedB (pePath z lam) ∧ frameOf (pePath z lam) = frameOf z ∧
      pePath z lam 23 = z 23 ∧ z 8 ≤ pePath z lam 8 := by
  have hp := prefix_maximum (admissible_decode z h)
  exact ⟨(admissible_iff_normalized _ _ _ _ _).mp
    (pe_segment_admissible (admissible_decode z h) h0 h1), frameOf_encode _ _ _ _ _,
    h.1.physical.height.symm, (mix_between hp.2.1 h0 h1).1⟩


/-- Independently buildable A-layer endpoint; the original tail is unchanged. -/
def prefixPoint (z : Point) : Point :=
  encode (frameOf z) (betaBar (frameOf z)) (prefixP (frameOf z))
    (prefixE (frameOf z)) (tailOf z)

theorem prefixPoint_spec (z : Point) (h : NormalizedB z) :
    NormalizedB (prefixPoint z) ∧ frameOf (prefixPoint z) = frameOf z ∧
    prefixPoint z 23 = z 23 ∧ z 8 ≤ prefixPoint z 8 ∧
    1 ≤ prefixPoint z 8 ∧ prefixPoint z 8 ≤ 2 := by
  have hm := prefix_maximum (admissible_decode z h)
  exact ⟨(admissible_iff_normalized _ _ _ _ _).mp hm.1,
    frameOf_encode _ _ _ _ _, h.1.physical.height.symm,
    hm.2.1, hm.2.2.1, hm.2.2.2.1⟩

theorem prefix_path_endpoints (z : Point) (h : NormalizedB z) :
    betaPath z 0 = z ∧ betaPath z 1 = pePath z 0 ∧ pePath z 1 = prefixPoint z := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [betaPath] using encode_decode z h.1.physical
  · simp [betaPath, pePath]
  · simp [pePath, prefixPoint]

end
end Rho5.ExternalBFibreCapacity
