/-
D67 — `Rho5.Shared.MinorGrowthThreshold`, the entry module.

The actual growth threshold expressed through two polynomial minor inequalities:

* `MinorGrowthThreshold/Defs.lean` — the four actual signed original-matrix minors
  `A = m2 M 0 0`, `B = m3 M 0 0`, `C = m4 M 0 0`, `D = M.det`, their readings through the
  paid D61/D62/D56 identities, positivity, and the two quotient identities
  `r = C / B`, `delta = D / C`;
* `MinorGrowthThreshold/Threshold.lean` — the equivalence

      growthRatio M [1, p M, k M, r M, |delta M|] ≤ T  ↔  C ≤ T * B ∧ |D| ≤ T * C

  for `T ≥ 4`, its strict-violation form
  `T < growth ↔ T * B < C ∨ T * C < |D|`, and the named conditional corollary for
  `det M ≤ 0`.

This pays the objective/threshold side only.  D62 owns the feasible-domain equivalence
and its `PolyCP` is neither consumed at stage B nor redefined here.  Not claimed: that
the two polynomial inequalities hold at alpha, any global sharp bound, critical-tuple
reconstruction, or global balance; no generic polynomial optimizer or arbitrary-size
minor framework is introduced.
-/
import Rho5.Shared.MinorGrowthThreshold.Defs
import Rho5.Shared.MinorGrowthThreshold.Threshold

namespace Rho5.MinorGrowthThreshold

end Rho5.MinorGrowthThreshold
