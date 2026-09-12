import Rho5.Certificate.B24Trace.Legality
import Rho5.Shared.CompletePivotPath

/-!
# D33 / B24Trace — the real five-step legal trace of the reconstruction

**Item 3 of the card.**  Under the fully listed conditions

`Physical z`, `HeadBand z`, `0 < p z`, `0 < z 0`, `0 ≤ z 2`, `z 2 ≤ z 1`, `0 ≤ z 3`

the reconstructed matrix `reconstruct z` carries the honest D13 legal trace

`LegalTrace (reconstruct z) [1, p z, z 0, z 1, z 23]`.

Every entry is paid for by a real `LegalTrace.step` with the frozen complete-pivot
predicate and a non-zero pivot entry; the successive matrices are the *actual*
`pivotSchur` updates (`firstStage z`, `D z`, `[[r, s], [t, -r]]`, the `1 × 1` tail,
and finally the `0 × 0` matrix).  The terminal `0 × 0` stage contributes the empty
trace `LegalTrace.empty` — no extra `0` is appended.

The three recorded values are literal absolute values of the pivot entries and are
simplified by the `abs_*` lemmas of `Steps`:
`|M 0 0| = 1`, `|firstStage 0 0| = p z`, `|D 0 0| = z 0`, `|r| = z 1`,
`|-(r + st/r)| = z 23` (the last one through the frozen `Physical.height`).
-/

namespace Rho5.Certificate.B24Trace

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage p HeadBand)
open Rho5.CompletePivotPath (LegalTrace)

/-- **Item 3 (the five-step legal trace).**  The reconstructed matrix has the legal
complete-pivot trace `[1, p z, z 0, z 1, z 23]` under exactly the card's conditions.
No condition is hidden and no step is skipped. -/
theorem legalTrace_reconstruct (z : Point) (hz : Physical z) (hband : HeadBand z)
    (hp : 0 < p z) (hk : 0 < z 0) (hs : 0 ≤ z 2) (hsr : z 2 ≤ z 1) (ht : 0 ≤ z 3) :
    LegalTrace (reconstruct z) [1, p z, z 0, z 1, z 23] := by
  have hF : 0 < z 23 := F_pos z hz hs ht
  have hx : ∀ i, |Rho5.Certificate.B24Reconstruction.x z i| ≤ 1 := hband.abs_x
  have hq : ∀ j, |q z j| ≤ p z := fun j => hz.q_bound j
  have hS : ∀ i j, |S z i j| ≤ p z := fun i j => hz.s_bound i j
  -- the same trace with the recorded values kept in absolute-value form
  have h : LegalTrace (reconstruct z)
      [|reconstruct z 0 0|, |firstStage z 0 0|, |D z 0 0|, |tail2 z 0 0|, |tail1 z 0 0|] := by
    refine LegalTrace.step (0 : Fin 5) 0 ?_ ?_ ?_
    · exact Rho5.Certificate.B24Reconstruction.isCompletePivot_reconstruct_zero_zero z hz hband
    · rw [Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero]
      norm_num
    · rw [Rho5.Certificate.B24Reconstruction.pivotSchur_reconstruct_zero_zero z]
      refine LegalTrace.step (0 : Fin 4) 0 ?_ ?_ ?_
      · exact Rho5.Certificate.B24Reconstruction.isCompletePivot_firstStage_zero_zero z hp hx hq hS
      · rw [Rho5.Certificate.B24Reconstruction.firstStage_zero_zero]
        exact ne_of_gt hp
      · rw [Rho5.Certificate.B24Reconstruction.pivotSchur_firstStage_zero_zero z (ne_of_gt hp)]
        refine LegalTrace.step (0 : Fin 3) 0 ?_ ?_ ?_
        · exact isCompletePivot_D_zero_zero z hz hk
        · rw [D_zero_zero]
          exact ne_of_gt hk
        · rw [pivotSchur_D_zero_zero z (ne_of_gt hk)]
          refine LegalTrace.step (0 : Fin 2) 0 ?_ ?_ ?_
          · exact isCompletePivot_tail2_zero_zero z hz hs hsr ht
          · rw [tail2_zero_zero]
            exact ne_of_gt hz.r_pos
          · rw [pivotSchur_tail2_zero_zero z (ne_of_gt hz.r_pos)]
            refine LegalTrace.step (0 : Fin 1) 0 ?_ ?_ ?_
            · exact isCompletePivot_tail1_zero_zero z
            · exact tail1_ne_zero z hz hs ht
            · rw [pivotSchur_tail1_zero_zero z]
              exact LegalTrace.empty
  simpa [abs_reconstruct_zero_zero z, abs_firstStage_zero_zero z hp, abs_D_zero_zero z hk,
    abs_tail2_zero_zero z hz.r_pos, abs_tail1_zero_zero z hz hF] using h

/-- The same trace with the pivot values written as the frozen stage matrices: the
first entry is the maximum entry of the reconstructed matrix (D28) and the last is
the height coordinate. -/
theorem legalTrace_reconstruct_values (z : Point) (hz : Physical z) (hband : HeadBand z)
    (hp : 0 < p z) (hk : 0 < z 0) (hs : 0 ≤ z 2) (hsr : z 2 ≤ z 1) (ht : 0 ≤ z 3) :
    LegalTrace (reconstruct z) [Rho5.matrixEntryMax (reconstruct z), p z, z 0, z 1, z 23] := by
  rw [Rho5.Certificate.B24Reconstruction.matrixEntryMax_reconstruct z hz hband]
  exact legalTrace_reconstruct z hz hband hp hk hs hsr ht

end Rho5.Certificate.B24Trace
