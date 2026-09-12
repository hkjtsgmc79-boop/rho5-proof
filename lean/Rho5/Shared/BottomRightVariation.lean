import Rho5.Shared.BottomRightVariation.Basic
import Rho5.Shared.BottomRightVariation.Feasible
import Rho5.Shared.BottomRightVariation.Trace

/-!
# D55 — `Rho5.Shared.BottomRightVariation`

Legal bottom-right variation of the actual whole `5 × 5` matrix of the B24 lane.

* `BottomRightVariation.Basic` — the variation `shift M h` (only the original entry
  `(4,4)` moves) and the real `5 → 4 → 3 → 2` Schur bookkeeping on the actual D37
  readings `S4/S3/T2/p/k/r/s/t` and the actual D48 `delta`;
* `BottomRightVariation.Feasible` — the four actual entry constraints, the interval
  `[L, U]` with explicit nested `max`/`min` conventions, the equivalence with retaining
  normalization and the four leading complete pivots, `L ≤ 0 ≤ U`, feasibility of `L`,
  and the four-way boundary disjunction at `L`;
* `BottomRightVariation.Trace` — the actual D13 `LegalTrace` of a feasible shift (first
  four steps built here, `2 × 2` tail through D46's arbitrary-tail trace) and the D17
  growth ratio as the `tracePeak` of the same five values.

Read-only inputs: D37 (`B24Extraction`), D46 (`TailEnvelope`), D48 (`CanonicalTail`),
D10/D13/D17 through those deliveries.  No upstream module is edited or recompiled.
-/

namespace Rho5.BottomRightVariation

end Rho5.BottomRightVariation
