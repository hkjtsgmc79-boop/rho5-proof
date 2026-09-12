/-
D54 — `Rho5.Shared.MinorThreeBound`, the entry module.

Two independent results, both for the fixed order `3`:

* **Item 1** (`MinorThreeBound/Vertex.lean`): for every real `3 × 3` matrix `K` whose
  entries all lie in `[-1, 1]`, `|det K| ≤ 4`.  The constant is sharp — the sign
  matrix `[[1,1,1],[1,1,-1],[1,-1,1]]` attains it.  This is the sharp determinant
  bound for the fixed cube, *not* a complete-pivot growth bound.

* **Items 2 and 3** (`MinorThreeBound/Block.lean`): for the actual leading `3 × 3`
  block `B3 M` of a `5 × 5` matrix, the signed Schur identities give
  `det (B3 M) = p M * k M` whenever `M 0 0 = 1` and `p M ≠ 0` (`k` unrestricted); with
  the entries normalized to the cube this yields the necessary constraint
  `p M * k M ≤ 4` on the original matrix and its first two pivots.

Not claimed here: `r ≤ 4`, global tail balancing, alpha sharpness, `rho5 = alpha`, the
fixed `4 × 4` determinant bound (D51), the four bordered `4 × 4` identities (D52), or
sign normalization (D53).
-/
import Rho5.Shared.MinorThreeBound.Core
import Rho5.Shared.MinorThreeBound.Vertex
import Rho5.Shared.MinorThreeBound.Block

namespace Rho5.MinorThreeBound

end Rho5.MinorThreeBound
