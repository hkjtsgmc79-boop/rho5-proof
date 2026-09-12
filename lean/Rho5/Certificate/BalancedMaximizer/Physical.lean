/-
D65 — item 3: the explicit physical point at the growth height
==============================================================

For an actual `Matrix5 M` that satisfies the card's hypotheses on the balanced branch, the
extracted point `z = extract M : Rho5.Certificate.B16.Point` is physical, has a head band,
reconstructs `M`, sits at the height `z 23 = growthRatio M (balancedValues M)`, and carries an
actual legal trace `[1, p M, k M, r M, F M]`.

Every membership fact is **reused** from D37 (`physical_extract`, `headBand_extract`,
`reconstruct_extract`, `legalTrace_extract`); the physical inequality list is not expanded
again here.
-/
import Rho5.Certificate.BalancedMaximizer.GrowthValue

namespace Rho5.Certificate.BalancedMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.Certificate.B16 (Physical)
open Rho5.Certificate.B24Reconstruction (HeadBand)

/-- **Item 3.**  The extracted point of a balanced qualified matrix is a physical B24 point
whose height coordinate is the matrix's growth ratio. -/
theorem physical_point_at_height (M : Matrix5)
    (hM : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (h : Rho5.LeadingSigns.LeadingTracePos M (balancedValues M))
    (hgrowth : 4 < Rho5.GrowthModel.growthRatio M (balancedValues M))
    (htail : T2 M 1 1 = -r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    Physical (Rho5.Certificate.B24Extraction.extract M) ∧
      HeadBand (Rho5.Certificate.B24Extraction.extract M) ∧
        Rho5.Certificate.B24Reconstruction.reconstruct (Rho5.Certificate.B24Extraction.extract M) = M ∧
          (Rho5.Certificate.B24Extraction.extract M) 23
              = Rho5.GrowthModel.growthRatio M (balancedValues M) ∧
            Rho5.CompletePivotPath.LegalTrace M [1, p M, k M, r M, F M] := by
  obtain ⟨hcp0, hS4, hS3, hT2, -, hppos, hkpos, hrpos, -, -⟩ :=
    Rho5.CanonicalTail.prefix_structure hM h00 h hgrowth
  have hpne : p M ≠ 0 := ne_of_gt hppos
  have hkne : k M ≠ 0 := ne_of_gt hkpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Rho5.Certificate.B24Extraction.physical_extract M h00 hpne hkne htail
      hcp0 hS4 hS3 hT2 hppos hkpos hrpos
  · exact Rho5.Certificate.B24Extraction.headBand_extract M h00 hcp0 hS4 hppos
  · exact Rho5.Certificate.B24Extraction.reconstruct_extract M h00 hpne hkne htail
  · rw [Rho5.Certificate.B24Extraction.extract_twentythree,
      growthRatio_eq_F M hM h00 h hgrowth htail hs ht]
  · exact Rho5.Certificate.B24Extraction.legalTrace_extract M h00 hpne hkne htail
      hcp0 hS4 hS3 hT2 hppos hkpos hrpos hs ht

/-- The width form of item 3, convenient for consumers: the extracted point's height
coordinate is the matrix's tail height `F M` (a re-export of D37's `extract_twentythree`). -/
theorem extract_height_eq_F (M : Matrix5) :
    (Rho5.Certificate.B24Extraction.extract M) 23 = F M :=
  Rho5.Certificate.B24Extraction.extract_twentythree M

end Rho5.Certificate.BalancedMaximizer
