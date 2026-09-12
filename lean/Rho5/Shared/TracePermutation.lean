/-
D20 — public aggregator: row/column permutation invariance of the complete legal trace.

`import Rho5.Shared.TracePermutation` gives the whole lane:

* `Permute`    — the fixed entry definition `permuteEntries`, its inverse / zero /
  nonzero laws, the absolute-value and pivot correspondence (item 1), and the
  invariance of D12's `stageEntryMax` and D08's `matrixEntryMax`;
* `Remaining`  — the remaining row/column bijection `remainingPerm` induced by a
  permutation after the pivot is removed, with its defining identity
  `remainingIndex_remainingPerm` (item 2);
* `Schur`      — the one-step correspondence
  `pivotSchur (permuteEntries A r c) p q = permuteEntries (pivotSchur A (r p) (c q))
  (remainingPerm r p) (remainingPerm c q)` (item 2);
* `Trace`      — the fixed lemma `legalTrace_permute_iff` (item 3), with the value
  list unchanged and no tie-break assumption;
* `Matrix5`    — the `5 × 5` instance and normalization compatibility (item 4).

Reused unchanged (read-only): `Rho5.CompletePivotPath.LegalTrace` and its constructors
(D13), `Rho5.PivotReindex.{reindexEntries, remainingEquiv, remainingIndex, pivotSchur,
isCompletePivot_reindexEntries_iff, normalize_reindexEntries, matrixEntryMax_reindexEntries}`
(D10), `Rho5.MatrixStage.stageEntryMax` (D12), `Rho5.MatrixNormalization.normalize`
(D08), `Rho5.Pivot.IsCompletePivot` (pilot).

Scope (frozen): permutation invariance only.  No orthogonal or general linear
transformations, no sign-normal-form search, no optimal alpha, no attainability, no
rewriting of `LegalTrace`; D17 is not imported.
-/
import Rho5.Shared.TracePermutation.Permute
import Rho5.Shared.TracePermutation.Remaining
import Rho5.Shared.TracePermutation.Schur
import Rho5.Shared.TracePermutation.Trace
import Rho5.Shared.TracePermutation.Matrix5
