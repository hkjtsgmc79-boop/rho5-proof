/-
D20 — the `Matrix5` instance and normalization compatibility
============================================================

**Item 4.** The permutation equivalence at the pilot's `5 × 5` matrix, together with
the two frozen objects the later reduction consumes: D08's unit normalization and
D08's entry maximum `Rho5.matrixEntryMax`.

Normalization commutes with permutation by D10's `normalize_reindexEntries` (cited,
not reproved), hence the *normalized* traces are permutation invariant as well — this
time with **no nonzero hypothesis**, because the trace equivalence of item 3 holds for
every matrix (unlike the value-scaling equivalence, which needs the scalar to be
invertible).
-/
import Rho5.Shared.TracePermutation.Trace
import Rho5.Shared.MatrixNormalization

namespace Rho5.TracePermutation

open Rho5

/-- **Item 4 (fixed 5×5 entry).** Row/column permutation of a `Matrix5` leaves the
legal traces unchanged, value list included. -/
theorem legalTrace_permute_iff5 (A : Matrix5) (r c : Equiv.Perm (Fin 5)) (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (permuteEntries A r c) values ↔
      Rho5.CompletePivotPath.LegalTrace A values :=
  legalTrace_permute_iff A r c values

/-- **Item 4 (entry maximum).** The frozen `Rho5.matrixEntryMax` is unchanged by
permutation (D10's invariance, restated for `permuteEntries`). -/
theorem matrixEntryMax_permuteEntries5 (A : Matrix5) (r c : Equiv.Perm (Fin 5)) :
    matrixEntryMax (permuteEntries A r c) = matrixEntryMax A :=
  matrixEntryMax_permuteEntries A r c

/-- **Item 4 (normalization commutes).** D08's unit normalization commutes with
row/column permutation: normalizing the permuted matrix is the same as permuting the
normalized matrix.  Cited from D10; no second normalization is introduced. -/
theorem normalize_permuteEntries (A : Matrix5) (r c : Equiv.Perm (Fin 5)) :
    Rho5.MatrixNormalization.normalize (permuteEntries A r c)
      = permuteEntries (Rho5.MatrixNormalization.normalize A) r c :=
  Rho5.PivotReindex.normalize_reindexEntries A r c

/-- **Item 4 (normalized traces are permutation invariant).** Combining the previous
identity with the fixed lemma: the legal traces of the normalized matrix are
unchanged by permutation, again with the value list held fixed and **without any
nonzero hypothesis**. -/
theorem legalTrace_normalize_permute_iff (A : Matrix5) (r c : Equiv.Perm (Fin 5))
    (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace
        (Rho5.MatrixNormalization.normalize (permuteEntries A r c)) values ↔
      Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A) values := by
  rw [normalize_permuteEntries, legalTrace_permute_iff]

/-- The same statement with the normalization performed first on both sides. -/
theorem legalTrace_permute_normalize_iff (A : Matrix5) (r c : Equiv.Perm (Fin 5))
    (values : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace
        (permuteEntries (Rho5.MatrixNormalization.normalize A) r c) values ↔
      Rho5.CompletePivotPath.LegalTrace (Rho5.MatrixNormalization.normalize A) values :=
  legalTrace_permute_iff (Rho5.MatrixNormalization.normalize A) r c values

end Rho5.TracePermutation
