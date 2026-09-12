import Rho5.Shared.BHeadSign.Signs
import Rho5.Shared.BHeadSign.Action
import Rho5.Shared.BHeadSign.Matrix
import Rho5.Shared.BHeadSign.Representative

/-!
# D137 — `Rho5.Shared.BHeadSign` (aggregate)

The real second row/column sign flip, i.e. the remaining head normalization of a qualified
high-value B point:

* `Signs` — the sign vector `sgOf σ = diag(1,σ,1,1,1)`, the sign choice `headSigma` read off
  `z`, the flipped frame `headFrame`/`headEncode`, the flipped point `headPointOf`/`headPoint`
  and all 24 coordinate readings;
* `Action` — the real block equivariance: `D`, `S`, `O` invariant; `L_i ↦ σ L_i`,
  `P_j ↦ σ P_j`; `u, v` untouched; `x, q ↦ σ ·`;
* `Matrix` — the complete 25-entry identity
  `reconstruct (headEncode …) i j = sgOf σ i * reconstruct (encode …) i j * sgOf σ j`, and its
  transport to `z` itself through D120's `encode_decode`;
* `Representative` — `Qualified`/`NormalizedB` transfer field by field, the two exported
  theorems `qualified_head_has_normalized_representative` (premise `1 ≤ p`) and
  `qualified_high_head_has_normalized_representative` (the card's `1 < p`).
-/
