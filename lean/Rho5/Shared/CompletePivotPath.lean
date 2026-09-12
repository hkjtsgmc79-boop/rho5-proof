/-
D13 — public aggregator for the complete legal elimination trace.

`import Rho5.Shared.CompletePivotPath` gives the whole lane:

* `Basic`     — the inductive relation `LegalTrace` and its structural properties
                (length ≤ order, nonnegative entries, nonempty at positive order,
                the empty-trace characterisation, the genuine-step decomposition at a
                nonzero matrix, and the zero-matrix characterisation);
* `Head`      — the head of a trace is the largest absolute entry and is attained;
                for `Matrix5` it is exactly the frozen `Rho5.matrixEntryMax`;
* `Scaling`   — whole-trace scaling equivalence for every nonzero scalar, with the
                negative, positive and inverse forms made explicit;
* `Normalize` — the `Matrix5` unit-normalized equivalence, the five-stage length
                bound and the normalized head `1`.

Reused unchanged (read-only): `Rho5.Matrix5` / `Rho5.matrixEntryMax`,
`Rho5.Pivot.IsCompletePivot`, `Rho5.PivotReindex.pivotSchur`,
`Rho5.MatrixNormalization.{normalize, isCompletePivot_smul_iff, fixedSchur_smul,
matrixEntryMax_normalize, smul_normalize_eq_self}`.

Scope (frozen): the relation and its structural/scaling laws.  It is **not** proved
here that every matrix admits a trace — that existence statement is the next
dependency (D12's stagewise legal-pivot existence) and is deliberately absent.
No global optimal bound, no determinant, no rank, no attainability.
-/
import Rho5.Shared.CompletePivotPath.Basic
import Rho5.Shared.CompletePivotPath.Head
import Rho5.Shared.CompletePivotPath.Scaling
import Rho5.Shared.CompletePivotPath.Normalize
