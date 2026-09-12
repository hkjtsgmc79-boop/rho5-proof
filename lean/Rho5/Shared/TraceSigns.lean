/-
D22 — row/column sign-flip invariance of the complete legal elimination trace.

Entry point for the module family:

* `Rho5.Shared.TraceSigns.Definitions` — sign vectors, the signed matrix
  `signedEntries`, and the entry-level invariance (Goal 1);
* `Rho5.Shared.TraceSigns.Trace`       — the frozen `pivotSchur` transformation
  (Goal 2) and the fixed public lemma `legalTrace_signed_iff` (Goal 3);
* `Rho5.Shared.TraceSigns.Normalize`   — the `Matrix5` entry-maximum invariance,
  commutation of D08's `normalize` with sign flips, and the normalized trace
  equivalence (Goal 4);
* `Rho5.Shared.TraceSigns.Audit`       — the `#print axioms` audit.

Everything is read-only over the frozen `Rho5.Shared.{Conventions, Pivot,
MatrixNormalization, PivotReindex, CompletePivotPath}` modules.  Row/column
*permutations* are a different transformation and belong to D20; this lane performs
no permutation and no canonical-form search.
-/
import Rho5.Shared.TraceSigns.Definitions
import Rho5.Shared.TraceSigns.Trace
import Rho5.Shared.TraceSigns.Normalize
import Rho5.Shared.TraceSigns.Audit
