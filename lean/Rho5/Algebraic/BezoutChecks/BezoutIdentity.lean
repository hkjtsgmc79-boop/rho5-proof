/-
D07 — the 19 Bézout coefficient identities and the assembled identity.

GENERATED FILE — do not edit by hand.  Produced by
`parallel/D07/scripts/gen_bezout_checks.py` from Great's audited integer
certificate
`great-algebraic-20260911/received/data/algebraic_certificate.json`.

Each `bezoutCoeff{k}` is the coefficient of `z^k` in `A * P + B * P'`; the
theorem says it equals `bezoutRHS g` for `k = 0` and `0` for `1 ≤ k ≤ 18`.
Every one of them is a *scalar* identity in an arbitrary commutative ring,
discharged by `ring` after unfolding the coefficient definitions — no
high-degree polynomial is expanded globally.

`bezout_identity` then applies the generic assembly lemma
`assemble_bezout` of `Assemble.lean`, whose hypotheses are exactly these 19
theorems.  Nothing is assumed: the 19 identities are proved here, and the
assembly consumes the proofs.
-/

import Rho5.Algebraic.BezoutChecks.Assemble
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C0
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C1
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C2
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C3
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C4
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C5
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C6
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C7
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C8
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C9
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C10
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C11
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C12
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C13
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C14
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C15
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C16
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C17
import Rho5.Algebraic.BezoutChecks.CoeffChecks.C18

namespace Rho5.Algebraic.BezoutChecks

noncomputable section

set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

/-! ### The assembled identity -/

/-- `A * P + B * (dP/dz) = 65536 (g-4)^8 (g-2)^2 P61(g)` over an
arbitrary commutative ring, with `P`, `dP/dz`, `A`, `B` as in
`Assemble.lean` and the coefficient data of `CoeffData.lean`.

The 19 coefficient identities are proved in
`Rho5.Algebraic.BezoutChecks.CoeffChecks.C0 .. C18`;
`assemble_bezout` consumes those proofs, so nothing is assumed here.

No resultant oracle, factorisation hypothesis, root assumption or
leading-coefficient nonvanishing is used. -/
theorem bezout_identity (z g : R) :
    Apoly z g * Ppoly z g + Bpoly z g * dPpoly z g =
      65536 * (g - 4) ^ 8 * (g - 2) ^ 2 * p61Formula g := by
  simpa only [bezoutRHS] using
    assemble_bezout z g (bezoutRHS g)
      (bezoutCoeff0 g)
      (bezoutCoeff1 g)
      (bezoutCoeff2 g)
      (bezoutCoeff3 g)
      (bezoutCoeff4 g)
      (bezoutCoeff5 g)
      (bezoutCoeff6 g)
      (bezoutCoeff7 g)
      (bezoutCoeff8 g)
      (bezoutCoeff9 g)
      (bezoutCoeff10 g)
      (bezoutCoeff11 g)
      (bezoutCoeff12 g)
      (bezoutCoeff13 g)
      (bezoutCoeff14 g)
      (bezoutCoeff15 g)
      (bezoutCoeff16 g)
      (bezoutCoeff17 g)
      (bezoutCoeff18 g)

end

end Rho5.Algebraic.BezoutChecks
