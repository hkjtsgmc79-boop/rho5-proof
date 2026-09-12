import Rho5.Shared.PaperB17Signs.Signs
import Rho5.Shared.PaperB17Signs.Action
import Rho5.Shared.PaperB17Signs.Matrix
import Rho5.Shared.PaperB17Signs.Representative

/-!
# D133 — `Rho5.Shared.PaperB17Signs` (aggregate)

The two real sign normalizations of a normalized B point, assembled:

* `Signs` — the sign vectors `tau = diag(ε, εη, εη)`, `sigma = diag(1,1,ε,εη,εη)` and the
  signed frame `signedFrame`;
* `Action` — the actual block equivariance `D, S, O ↦ tau_i tau_j ·`, `L_i ↦ tau_i · L_i`,
  `P_j ↦ tau_j · P_j`;
* `Matrix` — the complete reconstruction identity
  `reconstruct (signedFrame) i j = sigma i * reconstruct i j * sigma j`;
* `Representative` — transport of `Admissible`/`NormalizedB`, the sign choices
  `epsOf`/`etaOf`, the stage-A theorem `normalizedB_has_x0_nonneg_representative`, the
  coupling-band lemmas in the original coordinates, and the exported
  `normalizedB_has_sign_representative`.
-/
