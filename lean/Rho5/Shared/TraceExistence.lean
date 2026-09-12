/-
D14 — public aggregator: existence of a complete legal elimination trace.

`import Rho5.Shared.TraceExistence` gives the whole lane:

* `Existence` — `exists_legalTrace` (every matrix has a trace), the arbitrary-first-pivot
  forms `exists_legalTrace_cons` / `exists_legalTrace_cons_of_isCompletePivot`, the
  nonempty and head-is-max forms;
* `Chosen`    — the noncomputable `chosenTrace` with its legality, length, endpoint and
  head specifications;
* `Matrix5`   — `exists_legalTrace5`, the nonzero head statement, and the normalized
  trace with head `1` (via D13's normalization equivalence).

Reused unchanged (read-only): `Rho5.CompletePivotPath.LegalTrace` and its structural /
head / scaling results (D13), `Rho5.MatrixStage.exists_nonzero_completePivot` and
`completePivot_ne_zero` (D12), `Rho5.PivotReindex.pivotSchur` (D10),
`Rho5.MatrixNormalization.normalize` (D08), `Rho5.Pivot.IsCompletePivot` (pilot).

Scope (frozen): existence of a complete legal trace only.  It does not pay an optimal
global RHO5 bound, matrix attainability, the per-stage coarse growth bound (D15), or
the growth-ratio interface (D17).
-/
import Rho5.Shared.TraceExistence.Existence
import Rho5.Shared.TraceExistence.Chosen
import Rho5.Shared.TraceExistence.Matrix5
