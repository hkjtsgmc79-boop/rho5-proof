import Rho5.Shared.V43MatrixRoundTrip.Defs

/-!
# D143 / `Rho5.Shared.XSmallKSigns` — definitions for the small-`k` high-value sign normalization

The card works from the actual `SatFrame M` (D119) together with the two numeric inputs
`q_* = 1653/400 ≤ height M` and `k M ≤ 2`.  In the X case the tail is tied (`s M = t M = r M`), so
`F M = 2 * r M` and the fifth pivot is `delta M = w M - r M`, whence `height M = |w M - r M|`.

Nothing here is a new model: every symbol is a D119 reader of the actual matrix.
-/

noncomputable section

namespace Rho5.Shared.XSmallKSigns

open Rho5 (Matrix5)

/-- The paper's threshold `q_* = 1653/400`. -/
def qstar : ℝ := 1653 / 400

theorem qstar_gt_four : 4 < qstar := by norm_num [qstar]

theorem two_lt_qstar_half : 2 < qstar / 2 := by norm_num [qstar]

end Rho5.Shared.XSmallKSigns
