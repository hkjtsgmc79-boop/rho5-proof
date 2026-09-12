import Rho5.Certificate.B24Extraction.Bands

/-!
# D37 / B24Extraction — the extracted matrix on the real legal trace and growth ratio

**Item 4 of the card.**  With the extra explicit bounds `0 ≤ s`, `0 ≤ t` the extracted
matrix `A` itself carries the five-step legal trace of D33:

`LegalTrace A [1, p A, k A, r A, F A]`,

obtained by instantiating D33's `legalTrace_reconstruct` at the extracted point and
rewriting with the proved identity `reconstruct (extract A) = A`.  The trace's values
are the extracted scalars, i.e. the actual successive pivot absolute values.

For the growth ratio only `F A ≤ growthRatio A [1, p A, k A, r A, F A]` is claimed:
equality would need the additional bounds `1, p, k, r ≤ F`, which are **not** part of
the extracted class and are therefore carried as explicit hypotheses in the
conditional statement `growthRatio_extract_eq`.

Nothing here claims that a matrix of this class exists, that every matrix can be
normalized into it, or anything about `alpha` / the global upper bound.
-/

namespace Rho5.Certificate.B24Extraction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage HeadBand beta)

/-- **Item 4 (legal trace).**  The extracted normalized balanced matrix carries the
real five-step D13 `LegalTrace` with the extracted pivot values.  Every hypothesis is
explicit and none of them is the conclusion. -/
theorem legalTrace_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0)
    (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (hS4 : Rho5.Pivot.IsCompletePivot (S4 A) 0 0)
    (hS3 : Rho5.Pivot.IsCompletePivot (S3 A) 0 0)
    (hT2 : Rho5.Pivot.IsCompletePivot (T2 A) 0 0)
    (hppos : 0 < p A) (hkpos : 0 < k A) (hrpos : 0 < r A)
    (hs : 0 ≤ s A) (ht : 0 ≤ t A) :
    Rho5.CompletePivotPath.LegalTrace A [1, p A, k A, r A, F A] := by
  have hband : HeadBand (extract A) := headBand_extract A h00 hpiv hS4 hppos
  have hphys : Physical (extract A) :=
    physical_extract A h00 hp hk htail hpiv hS4 hS3 hT2 hppos hkpos hrpos
  have hp' : 0 < Rho5.Certificate.B24Reconstruction.p (extract A) := by
    rw [p_extract]; exact hppos
  have hk' : 0 < extract A 0 := by rw [extract_zero]; exact hkpos
  have hs' : 0 ≤ extract A 2 := by rw [extract_two]; exact hs
  have hsr' : extract A 2 ≤ extract A 1 := by
    rw [extract_two, extract_one]
    have h := hT2 0 1
    have hrabs : |T2 A 0 0| = T2 A 0 0 := abs_of_pos hrpos
    rw [hrabs] at h
    exact (le_abs_self (s A)).trans (by simpa [s, r] using h)
  have ht' : 0 ≤ extract A 3 := by rw [extract_three]; exact ht
  have h := Rho5.Certificate.B24Trace.legalTrace_reconstruct (extract A) hphys hband
    hp' hk' hs' hsr' ht'
  simpa [reconstruct_extract A h00 hp hk htail, p_extract, extract_zero, extract_one,
    extract_twentythree] using h

/-- **Item 4 (growth bound).**  The height coordinate of the extracted matrix is
bounded by its actual growth ratio along that trace; equality is *not* claimed. -/
theorem le_growthRatio_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0)
    (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (hS4 : Rho5.Pivot.IsCompletePivot (S4 A) 0 0)
    (hS3 : Rho5.Pivot.IsCompletePivot (S3 A) 0 0)
    (hT2 : Rho5.Pivot.IsCompletePivot (T2 A) 0 0)
    (hppos : 0 < p A) (hkpos : 0 < k A) (hrpos : 0 < r A) :
    F A ≤ Rho5.GrowthModel.growthRatio A [1, p A, k A, r A, F A] := by
  have hband : HeadBand (extract A) := headBand_extract A h00 hpiv hS4 hppos
  have hphys : Physical (extract A) :=
    physical_extract A h00 hp hk htail hpiv hS4 hS3 hT2 hppos hkpos hrpos
  have h := Rho5.Certificate.B24Trace.le_growthRatio_z23 (extract A) hphys hband
  simpa [reconstruct_extract A h00 hp hk htail, p_extract, extract_zero, extract_one,
    extract_twentythree] using h

/-- **Item 4 (conditional equality).**  If the four other trace values are bounded by
`F A`, the growth ratio is exactly `F A`.  The four bounds are explicit hypotheses:
they are the missing ingredient for a *sourced* attainment witness and are not part
of the extracted class. -/
theorem growthRatio_extract_eq (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0)
    (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (hS4 : Rho5.Pivot.IsCompletePivot (S4 A) 0 0)
    (hS3 : Rho5.Pivot.IsCompletePivot (S3 A) 0 0)
    (hT2 : Rho5.Pivot.IsCompletePivot (T2 A) 0 0)
    (hppos : 0 < p A) (hkpos : 0 < k A) (hrpos : 0 < r A)
    (h1 : 1 ≤ F A) (h2 : p A ≤ F A) (h3 : k A ≤ F A) (h4 : r A ≤ F A) :
    Rho5.GrowthModel.growthRatio A [1, p A, k A, r A, F A] = F A := by
  have hband : HeadBand (extract A) := headBand_extract A h00 hpiv hS4 hppos
  have hphys : Physical (extract A) :=
    physical_extract A h00 hp hk htail hpiv hS4 hS3 hT2 hppos hkpos hrpos
  have h1' : 1 ≤ extract A 23 := by rw [extract_twentythree]; exact h1
  have h2' : Rho5.Certificate.B24Reconstruction.p (extract A) ≤ extract A 23 := by
    rw [p_extract, extract_twentythree]; exact h2
  have h3' : extract A 0 ≤ extract A 23 := by
    rw [extract_zero, extract_twentythree]; exact h3
  have h4' : extract A 1 ≤ extract A 23 := by
    rw [extract_one, extract_twentythree]; exact h4
  have h := Rho5.Certificate.B24Trace.growthRatio_eq_z23 (extract A) hphys hband
    h1' h2' h3' h4'
  simpa [reconstruct_extract A h00 hp hk htail, p_extract, extract_zero, extract_one,
    extract_twentythree] using h

end Rho5.Certificate.B24Extraction
