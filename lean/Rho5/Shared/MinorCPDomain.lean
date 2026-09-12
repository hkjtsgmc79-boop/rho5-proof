import Rho5.Shared.MinorCPDomain.Tail
import Rho5.Shared.MinorCPDomain.Poly

/-!
# D62 — `Rho5.Shared.MinorCPDomain`

Division-free actual first-four complete-pivot domain.

* `MinorCPDomain.Tail` — **stage A (complete):** the four bordered `4 × 4` minors
  `m4_ij = det (borderedMinor M i j)` of D52, the division-free identity
  `m4_ij = p M * k M * T2 M i j`, `C = m4_00 = p M * k M * r M`, and the equivalence
  `IsCompletePivot (T2 M) 0 0 ↔ ∀ i j, |m4 M i j| ≤ m4 M 0 0` for `M 0 0 = 1`,
  `p, k, r > 0`.
* `MinorCPDomain.Poly` — **stage B (complete):** `A = m2 0 0`, `B = m3 0 0`, `C = m4 0 0`
  from the actual D61 `m2`/`m3` and the D52 `m4`, the division-free polynomial domain
  `PolyCP` (25 entry bounds + 16 + 9 + 4 minor bounds + `A, B, C > 0`), the derived
  positivity `p > 0` from `A`, `k > 0` from `B = p * k`, `r > 0` from `C = p * k * r`,
  and the exact equivalence `PolyCP M ↔ (matrixEntryMax M = 1 ∧ 四个前导 CP ∧ p,k,r > 0)`.

Read-only inputs: D52 (`BorderedTailMinors`), D37 (`B24Extraction`), and through them the
frozen D10/D13/D17/pilot layers.  No upstream module is edited or recompiled.
-/

namespace Rho5.MinorCPDomain

end Rho5.MinorCPDomain
