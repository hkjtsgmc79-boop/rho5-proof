/-
D22 — Goal 4: the `Matrix5` entry maximum and unit normalization are compatible
with row/column sign flips.

* `matrixEntryMax_signedEntries5` — the frozen entry maximum `Rho5.matrixEntryMax`
  is *unchanged* by a sign flip (immediate from the entrywise invariance and D08's
  `matrixEntryMax_scaledEntries`, reused rather than re-derived);
* `normalize_signedEntries5` — D08's unit normalization of the signed matrix is the
  sign flip of the unit normalization, i.e. `normalize` commutes with the sign
  transformation;
* `legalTrace_normalize_signed_iff` — combining both with the frozen D13
  `legalTrace_normalize_iff` gives the normalized trace equivalence for the signed
  matrix, up to the same explicit factor `(matrixEntryMax A)⁻¹`.

This is the entry point a later lane needs in order to normalize a matrix whose rows
and columns have already been sign-normalized.  Scope: no canonical-form search, no
continuous rotation, no arbitrary diagonal scaling, no growth-ratio statement (that
adapter is D17's and is not duplicated here).
-/
import Rho5.Shared.Conventions
import Rho5.Shared.MatrixNormalization
import Rho5.Shared.CompletePivotPath.Normalize
import Rho5.Shared.TraceSigns.Trace

namespace Rho5.TraceSigns

open Rho5

/-- The `Matrix5` sign flip, i.e. `signedEntries` at `n = 5`. -/
def signedEntries5 (A : Matrix5) (r c : Fin 5 → ℝ) : Matrix5 :=
  fun i j => r i * A i j * c j

@[simp] theorem signedEntries5_apply (A : Matrix5) (r c : Fin 5 → ℝ) (i j : Fin 5) :
    signedEntries5 A r c i j = r i * A i j * c j := rfl

/-- `signedEntries5` is `signedEntries` at `n = 5` (definitional, recorded for use
with the general lemmas). -/
theorem signedEntries5_eq_signedEntries (A : Matrix5) (r c : Fin 5 → ℝ) :
    signedEntries5 A r c = signedEntries A r c := rfl

/-- **Goal 4 (entry maximum).**  The frozen `matrixEntryMax` of a sign flip is the
`matrixEntryMax` of the original matrix.  The supremum is unfolded once; each entry
is compared through the entrywise invariance `abs_signedEntries`. -/
theorem matrixEntryMax_signedEntries5 (A : Matrix5) {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    matrixEntryMax (signedEntries5 A r c) = matrixEntryMax A := by
  have hle : ∀ i j : Fin 5, |signedEntries5 A r c i j| ≤ matrixEntryMax A := by
    intro i j
    have h1 : |signedEntries5 A r c i j| = |A i j| := abs_signedEntries (n := 5) A hr hc i j
    rw [h1]
    exact Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax A i j
  have hle' : ∀ i j : Fin 5, |A i j| ≤ matrixEntryMax (signedEntries5 A r c) := by
    intro i j
    have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax (signedEntries5 A r c) i j
    have h1 : |signedEntries5 A r c i j| = |A i j| := abs_signedEntries (n := 5) A hr hc i j
    rwa [h1] at h
  exact le_antisymm
    (Finset.sup'_le _ _ (fun ij _ => hle ij.1 ij.2))
    (Finset.sup'_le _ _ (fun ij _ => hle' ij.1 ij.2))

/-- The unit normalization of a sign flip is the sign flip of the unit
normalization: `normalize` commutes with row/column sign flips. -/
theorem normalize_signedEntries5 {A : Matrix5} {r c : Fin 5 → ℝ}
    (hr : IsSign r) (hc : IsSign c) :
    Rho5.MatrixNormalization.normalize (signedEntries5 A r c) =
      signedEntries5 (Rho5.MatrixNormalization.normalize A) r c := by
  have hmax := matrixEntryMax_signedEntries5 A hr hc
  funext i j
  rw [Rho5.MatrixNormalization.normalize_eq_inv_smul,
    Rho5.MatrixNormalization.normalize_eq_inv_smul, hmax]
  simp only [Rho5.MatrixNormalization.smul_apply_entry, signedEntries5_apply]
  ring

/-- **Goal 4 (normalized trace equivalence, signed matrix).**  For a nonzero
`5 × 5` matrix, normalizing the sign-flipped matrix does not change which lists are
legal traces, up to the explicit factor `(matrixEntryMax A)⁻¹`; and by the previous
theorem the normalized signed matrix is the sign flip of the normalized matrix.
Both directions, for every value list. -/
theorem legalTrace_normalize_signed_iff (A : Matrix5) (hA : A ≠ 0) (values : List ℝ)
    {r c : Fin 5 → ℝ} (hr : IsSign r) (hc : IsSign c) :
    Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize (signedEntries5 A r c))
        (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) ↔
      Rho5.CompletePivotPath.LegalTrace A values := by
  rw [normalize_signedEntries5 hr hc]
  exact (legalTrace_signed_iff' (Rho5.MatrixNormalization.normalize A) hr hc
    (values.map (fun v => (matrixEntryMax A)⁻¹ * v))).trans
    (Rho5.CompletePivotPath.legalTrace_normalize_iff A hA values)

end Rho5.TraceSigns
