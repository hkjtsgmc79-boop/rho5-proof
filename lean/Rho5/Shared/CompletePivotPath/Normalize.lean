/-
D13 — the `Matrix5` unit-normalized trace equivalence
=====================================================

**Goal 4.** For the pilot's `5 × 5` matrix, the whole-trace scaling equivalence is
instantiated at D08's unit normalization `(matrixEntryMax A)⁻¹ • A`:

  `LegalTrace (normalize A) (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) ↔ LegalTrace A values`

(the scalar is positive, so `|(matrixEntryMax A)⁻¹| = (matrixEntryMax A)⁻¹`; the
nonzero-matrix hypothesis is exactly what makes it invertible).

Consequences recorded here, all from the relation itself and the frozen norm:

* every trace of a `Matrix5` has length at most `5` (so a full run has at most five
  recorded stages);
* the head of a trace of a nonzero `Matrix5` is exactly `matrixEntryMax A`
  (Goal 2), and the head of a trace of its normalization is `1`.
-/
import Rho5.Shared.CompletePivotPath.Basic
import Rho5.Shared.CompletePivotPath.Head
import Rho5.Shared.CompletePivotPath.Scaling
import Rho5.Shared.MatrixNormalization

namespace Rho5.CompletePivotPath

open Rho5

/-- **Goal 4 (normalized trace equivalence).** For a nonzero `5 × 5` matrix,
normalizing does not change which lists are legal traces, up to the explicit factor
`(matrixEntryMax A)⁻¹`.  Both directions. -/
theorem legalTrace_normalize_iff (A : Matrix5) (hA : A ≠ 0) (values : List ℝ) :
    LegalTrace (Rho5.MatrixNormalization.normalize A)
        (values.map (fun v => (matrixEntryMax A)⁻¹ * v)) ↔ LegalTrace A values := by
  rw [Rho5.MatrixNormalization.normalize_eq_inv_smul]
  have hc : (matrixEntryMax A)⁻¹ ≠ 0 :=
    inv_ne_zero (Rho5.MatrixNormalization.matrixEntryMax_ne_zero A hA)
  have habs : |(matrixEntryMax A)⁻¹| = (matrixEntryMax A)⁻¹ :=
    abs_of_pos (inv_pos.mpr (Rho5.MatrixNormalization.matrixEntryMax_pos A hA))
  simpa only [habs] using legalTrace_smul_iff A values hc

/-- **Goal 4 (at most five stages).** A legal trace of a `5 × 5` matrix has at most
five recorded values. -/
theorem length_le_five {A : Matrix5} {values : List ℝ} (h : LegalTrace A values) :
    values.length ≤ 5 :=
  length_le h

/-- The same bound for a trace of the normalized matrix. -/
theorem normalize_length_le_five {A : Matrix5} {values : List ℝ}
    (h : LegalTrace (Rho5.MatrixNormalization.normalize A) values) : values.length ≤ 5 :=
  length_le h

/-- The normalization of a nonzero `Matrix5` is nonzero (the restoring identity
`matrixEntryMax A • normalize A = A` would otherwise force `A = 0`). -/
theorem normalize_ne_zero {A : Matrix5} (hA : A ≠ 0) :
    Rho5.MatrixNormalization.normalize A ≠ 0 := by
  intro h0
  have h1 := Rho5.MatrixNormalization.smul_normalize_eq_self A hA
  rw [h0, smul_zero] at h1
  exact hA h1.symm

/-- **Goal 4 (normalized head is `1`).** The first recorded value of any legal trace
of `normalize A` is `matrixEntryMax (normalize A) = 1`: normalization really does
put the frozen entry maximum at `1`. -/
theorem head_eq_one_of_normalize {A : Matrix5} (hA : A ≠ 0) {v : ℝ} {vs : List ℝ}
    (h : LegalTrace (Rho5.MatrixNormalization.normalize A) (v :: vs)) : v = 1 := by
  have h2 := head_eq_matrixEntryMax (normalize_ne_zero hA) h
  rwa [Rho5.MatrixNormalization.matrixEntryMax_normalize A hA] at h2

/-- The head of a trace of a nonzero `Matrix5` is the frozen entry maximum, written
as an equality of the two candidate descriptions (Goal 2 restated for comparison). -/
theorem head_eq_matrixEntryMax' {A : Matrix5} (hA : A ≠ 0) {v : ℝ} {vs : List ℝ}
    (h : LegalTrace A (v :: vs)) : v = matrixEntryMax A :=
  head_eq_matrixEntryMax hA h

/-- The normalized trace's head is the normalized entry maximum. -/
theorem head_eq_matrixEntryMax_of_normalize {A : Matrix5} (hA : A ≠ 0) {v : ℝ}
    {vs : List ℝ} (h : LegalTrace (Rho5.MatrixNormalization.normalize A) (v :: vs)) :
    v = matrixEntryMax (Rho5.MatrixNormalization.normalize A) :=
  head_eq_matrixEntryMax (normalize_ne_zero hA) h

end Rho5.CompletePivotPath
