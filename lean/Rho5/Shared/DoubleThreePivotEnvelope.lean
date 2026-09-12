import Rho5.Shared.DoubleThreePivotEnvelope.Scalar

/-!
# D85 — `Rho5.Shared.DoubleThreePivotEnvelope`

The pure scalar two-piece-envelope closure used by the fourth-pivot bound:

`phi(t) = if t ≤ 1 then 2*t else t*(3-t)`, and for `0 ≤ p ≤ 2`, `0 ≤ t ≤ 2` with the single
coupling hypothesis `p*t ≤ phi(p)` the product `p*phi(t)` is at most `4`.

This is a **scalar** statement only: no actual matrix, no `r ≤ 4`, no `PolyCP` hypothesis is
touched here.  See `results/DOUBLE_ENVELOPE_READY.json`.
-/

namespace Rho5.DoubleThreePivotEnvelope

end Rho5.DoubleThreePivotEnvelope
