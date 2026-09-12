/-
D74 — the forward direction on the sorted four-boundary domain.

**Statement.**  If `rho5Trace ≤ T`, then the two D67 threshold inequalities hold on the
*restricted* domain: actual matrices with `M 0 0 = 1`, `PolyCP M`, a sorted non-negative
tail in D70's minor form, and D70's four-boundary predicate.

**Proof.**  The forward direction is the restriction of D69's global reduction: D69
already proves the conclusion for every `M` with `M 0 0 = 1` and `PolyCP M`, so the two
extra hypotheses (sortedness in minor form, boundary face) are simply not needed.  No
new mathematics is introduced here.

`Rho5.MinorCPDomain` is D62's one finite domain; the minors are D67's `B`/`C`; the sorted
and boundary predicates are D70's own (`BoundaryFace`, and the minor form
`0 ≤ m4 M 0 1 ∧ m4 M 0 1 ≤ m4 M 1 0` of `0 ≤ s M ≤ t M`).  D68 contributes only its
accepted stage-A `Core`/`Sorted` modules.
-/
import Rho5.Shared.GlobalMinorReduction
import Rho5.Shared.MinorBoundaryFaces
import Rho5.Shared.BoundaryMaximizer.Core
import Rho5.Shared.BoundaryMaximizer.Sorted

namespace Rho5.BoundaryUpperReduction

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- **Forward (restricted).**  A global bound forces both inequalities on the sorted
four-boundary domain. -/
theorem inequalities_of_rho5Trace_le_sorted {T : ℝ} (hT : 4 ≤ T)
    (hrho : Rho5.GrowthSupremum.rho5Trace ≤ T) :
    ∀ M : Matrix5, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
      0 ≤ Rho5.MinorCPDomain.m4 M 0 1 →
        Rho5.MinorCPDomain.m4 M 0 1 ≤ Rho5.MinorCPDomain.m4 M 1 0 →
          Rho5.MinorBoundaryFaces.BoundaryFace M →
            (Rho5.MinorGrowthThreshold.C M ≤ T * Rho5.MinorGrowthThreshold.B M ∧
              |M.det| ≤ T * Rho5.MinorGrowthThreshold.C M) :=
  fun M h00 hpoly _ _ _ =>
    Rho5.GlobalMinorReduction.inequalities_of_rho5Trace_le hT hrho M h00 hpoly

end Rho5.BoundaryUpperReduction
