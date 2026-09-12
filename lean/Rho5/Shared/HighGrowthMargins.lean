/-
D58 — `Rho5.Shared.HighGrowthMargins`, the entry module.

Quantitative pivot margins in the actual high-growth domain, all conditional on
explicit hypotheses:

* **Item 1** (`HighGrowthMargins/OneStep.lean`): `p ≤ 2`, `k ≤ 2 * p`, `r ≤ 2 * k` from
  D15's complete-pivot one-step Schur bound, plus `k ≤ 4`, `r ≤ 8`.
* **Items 2 and 3** (`HighGrowthMargins/GrowthMargin.lean`): with
  `g = growthRatio M values`, the paid tail bound gives `g ≤ 2 * r`, hence
  `g / 2 ≤ r`, `g / 4 ≤ k`, `g / 8 ≤ p`; under the explicit hypothesis `4 < g` the
  strict margins `2 < r`, `1 < k`, `1/2 < p` and the products `p * k > 1/2`,
  `p * k * r > 1`.
* **Item 4** (`HighGrowthMargins/Package.lean`): the combined conditional
  actual-matrix package, including D54's accepted `p * k ≤ 4`.
* **Item 5** (`HighGrowthMargins/Witness.lean`): the corrected D53 canonical witness
  under `4 < rho5Trace`, with nonnegative tail signs and all of the above bounds.

These are denominator margins for the high-growth parameter domain.  They are **not** a
rank conclusion about the final pivot: `p`, `k`, `r` positive does not give five nonzero
pivots, and nothing here proves `r ≤ 4`, `4 < rho5Trace`, tail balance or alpha
sharpness.
-/
import Rho5.Shared.HighGrowthMargins.OneStep
import Rho5.Shared.HighGrowthMargins.GrowthMargin
import Rho5.Shared.HighGrowthMargins.Package
import Rho5.Shared.HighGrowthMargins.Witness

namespace Rho5.HighGrowthMargins

end Rho5.HighGrowthMargins
