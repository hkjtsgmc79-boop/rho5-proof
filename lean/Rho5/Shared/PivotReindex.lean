/-
D10 / N03b — public aggregator for the permutation / arbitrary-pivot /
one-step-elimination layer.

`import Rho5.Shared.PivotReindex` gives the whole lane:

* `Reindex`   — `reindexEntries`, inverse laws, `smul` commutation, pivot
  transport, `matrixEntryMax` invariance, `normalize` commutation;
* `MovePivot` — `movePivot`, `movePivot_zero_zero`, `isCompletePivot_movePivot_iff`,
  the zero/nonzero pivot qualification facts;
* `Remaining` — `remainingIndex`, never-the-pivot / injective / surjective,
  `remainingEquiv`;
* `Schur`     — `pivotSchur`, the entrywise formula at arbitrary `(p, q)`, and the
  one-step scaling law on top of D08's `fixedSchur_smul`;
* `Matrix5`   — the `Matrix5 → 4 × 4` alias `pivotSchur4`, worked evaluations, and
  the derived continuation precondition `PivotReady`.

Reused unchanged (read-only): `Rho5.Matrix5`, `Rho5.matrixEntryMax`,
`Rho5.Pivot.IsCompletePivot`, `Rho5.Pivot.zero_complete_pivot`,
`Rho5.Pivot.tied_pivot`, `Rho5.Pivot.fixedSchur`, and
`Rho5.MatrixNormalization.{smul_apply_entry, normalize, fixedSchur_smul}`.

Scope (frozen): permutations, an arbitrary pivot moved to `(0, 0)`, the remaining
index correspondence, and **one** Schur step with its scaling law.  No five-stage
recursion, no global growth rate, no determinant, rank or attainability claim.
-/
import Rho5.Shared.PivotReindex.Reindex
import Rho5.Shared.PivotReindex.MovePivot
import Rho5.Shared.PivotReindex.Remaining
import Rho5.Shared.PivotReindex.Schur
import Rho5.Shared.PivotReindex.Matrix5
