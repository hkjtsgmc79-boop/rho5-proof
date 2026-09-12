/-
D07 — Bézout coefficient identity #11.

GENERATED FILE — do not edit by hand.  Produced by
`parallel/D07/scripts/gen_bezout_checks.py` from Great's audited integer
certificate
`great-algebraic-20260911/received/data/algebraic_certificate.json`.

This is the coefficient of `z^11` in `A * P + B * P'`, a scalar identity in an
arbitrary commutative ring; it is discharged by `ring` after unfolding the
coefficient definitions of `CoeffData`.  The 19 coefficients live in separate
files so that each can be compiled on its own.
-/

import Rho5.Algebraic.BezoutChecks.CoeffData

namespace Rho5.Algebraic.BezoutChecks

noncomputable section

set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

/-- Coefficient of `z^11` in `A * P + B * P'`. -/
theorem bezoutCoeff11 (g : R) :
    ba1 g * pc10 g + ba2 g * pc9 g + ba3 g * pc8 g + ba4 g * pc7 g + ba5 g * pc6 g + ba6 g * pc5 g + ba7 g * pc4 g + ba8 g * pc3 g + bb2 g * (10 * pc10 g) + bb3 g * (9 * pc9 g) + bb4 g * (8 * pc8 g) + bb5 g * (7 * pc7 g) + bb6 g * (6 * pc6 g) + bb7 g * (5 * pc5 g) + bb8 g * (4 * pc4 g) + bb9 g * (3 * pc3 g) = 0 := by
  simp only [ba0, ba1, ba2, ba3, ba4, ba5, ba6, ba7, ba8, bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7, bb8, bb9, bezoutRHS, dpc0, dpc1, dpc2, dpc3, dpc4, dpc5, dpc6, dpc7, dpc8, dpc9, p61Formula, pc0, pc1, pc10, pc2, pc3, pc4, pc5, pc6, pc7, pc8, pc9]
  ring

end

end Rho5.Algebraic.BezoutChecks
