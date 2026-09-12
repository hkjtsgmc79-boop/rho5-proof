/-
D61 — `Rho5.Shared.PrefixBorderedMinors`, the entry module.

The fixed ordered bordered minors of the actual `5 × 5` matrix:

* `PrefixBorderedMinors/Defs.lean` — the two card-fixed embeddings `e2` (`[0, 1+i]`) and
  `e3` (`[0, 1, 2+i]`), the 16 signed `2 × 2` minors `m2` and the 9 signed `3 × 3` minors
  `m3`;
* `PrefixBorderedMinors/Identities.lean` — `m2 M i j = S4 M i j` (given `M 0 0 = 1`),
  `m3 M i j = p M * S3 M i j` (given `M 0 0 = 1` and `p M ≠ 0`), the corners
  `m2 M 0 0 = p M` and `m3 M 0 0 = p M * k M`, and the exact match
  `m3 M 0 0 = det (B3 M)` with D54's leading block.

This is a fixed finite-order family, not a generic embedding or submatrix framework.  It
does not redo D52's four `4 × 4` bordered identities or D54's bound, and it assumes no
complete pivot, balance, rank or sign premise.
-/
import Rho5.Shared.PrefixBorderedMinors.Defs
import Rho5.Shared.PrefixBorderedMinors.Identities

namespace Rho5.PrefixBorderedMinors

end Rho5.PrefixBorderedMinors
