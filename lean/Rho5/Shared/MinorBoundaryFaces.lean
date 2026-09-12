/-
D70 — `Rho5.Shared.MinorBoundaryFaces`, the entry module.

The four boundary faces and the tail order, stated in the original signed minors:

* `MinorBoundaryFaces/Defs.lean` — the four disjuncts `face1`–`face4` (original entry or a
  determinant of the frozen `m2`/`m3`/`m4` families), the four-disjunct `BoundaryFace`, and
  the Schur-side `SchurFaces` kept separately;
* `MinorBoundaryFaces/Equiv.lean` — `face1_iff`–`face4_iff` and the whole-predicate
  equivalence `BoundaryFace M ↔ SchurFaces M`, cancelling only proved positive factors;
* `MinorBoundaryFaces/TailOrder.lean` — `0 ≤ s M ↔ 0 ≤ m4 M 0 1`,
  `s M ≤ t M ↔ m4 M 0 1 ≤ m4 M 1 0` (non-strict, `s = 0`/`t = 0` included), D63's ordered
  witness transported into minors, and D59's paid strict branch recorded conditionally;
* `MinorBoundaryFaces/BalancedDet.lean` — the paid D56 condensation in minors,
  `B M * det M = C M * m4 1 1 - m4 0 1 * m4 1 0`, its fourth-face form
  `B M * det M = -(C M)^2 - m4 0 1 * m4 1 0`, and `det M < 0` /
  `|det M| * B M = (C M)^2 + m4 0 1 * m4 1 0` under nonnegative off-diagonals.

Every minor family and every Schur reading is imported from the accepted deliveries
(D61 `Rho5.PrefixBorderedMinors`, D62 `Rho5.MinorCPDomain`, D56 `Rho5.TailDeterminant`,
D59 `Rho5.DominantLastPivot`, D63 `Rho5.TailTransposeOrder`); this module redefines no
minor, proves no new symmetry framework, leaves `4 < rho5Trace` alone, and claims neither
global balance nor any face beyond the four listed.
-/
import Rho5.Shared.MinorBoundaryFaces.Defs
import Rho5.Shared.MinorBoundaryFaces.Equiv
import Rho5.Shared.MinorBoundaryFaces.TailOrder
import Rho5.Shared.MinorBoundaryFaces.BalancedDet

namespace Rho5.MinorBoundaryFaces

end Rho5.MinorBoundaryFaces
