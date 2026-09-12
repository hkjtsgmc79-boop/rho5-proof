/-
D19 — real scalar bridge between the frozen independent Bézout certificate
(D07, `Rho5.Algebraic.BezoutChecks`) and the frozen actual RHO5 constant
(D09, `Rho5.Algebraic.AlphaRoot`).

This module is **scalar** and lives over `ℝ` only.  It

1. identifies the two frozen representations of the degree-61 factor
   `P61` (`BezoutChecks.p61Formula` and `AlphaRoot.rootPolynomial`),
2. eliminates the factor `65536·(g-4)^8·(g-2)^2` from the proved Bézout
   identity, so that a common real zero of `P` and `dP/dz` is a root of `P61`,
3. feeds that root into the frozen uniqueness theorem on `(4,5)` to conclude
   `g = AlphaRoot.alpha`.

Nothing here assumes a root-existence oracle: `AlphaRoot.alpha` is *defined* in
D09 from a proved intermediate-value statement, and `root_unique` is a proved
theorem.  No `RootSpec` parameter, no `Nonempty`-style witness, and no new axiom
is introduced.

Scope note (unchanged from the task card): the hypotheses `Ppoly z g = 0` and
`dPpoly z g = 0` are still *scalar* common-zero conditions.  This module does
not claim that the candidate system or any matrix supplies them, does not prove
critical-point existence (G04), and does not prove the final rho5 optimality or
attainment statements.
-/
import Rho5.Algebraic.BezoutChecks.BezoutIdentity
import Rho5.Algebraic.AlphaRoot.Root
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace Rho5.Algebraic.ScalarAlphaBridge

open Rho5.Algebraic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ### 1. The two frozen representations of `P61` agree -/

/--
The coefficient list of D09's `rootPolynomial` is exactly D07's `p61Formula`:
both are the degree-61 factor of the resultant, one written as a Horner
evaluation of the certified integer list, the other written out as a
power-basis polynomial.

Proof: unfold D07's coefficient polynomial (62 monomials) and rewrite D09's
Horner evaluation with its own proved power-basis formula
(`AlphaRoot.rootPolynomial_formula`); `ring` closes the resulting identity of
two explicit degree-61 polynomials.
-/
theorem p61Formula_eq_rootPolynomial (g : ℝ) :
    (BezoutChecks.p61Formula g : ℝ) = AlphaRoot.rootPolynomial g := by
  rw [AlphaRoot.rootPolynomial_formula]
  simp only [BezoutChecks.p61Formula]
  ring

/-- Evaluation form of `p61Formula_eq_rootPolynomial`, convenient for rewriting
a root condition on `P61` into a root condition on D09's `rootPolynomial`. -/
theorem rootPolynomial_eq_p61Formula (g : ℝ) :
    AlphaRoot.rootPolynomial g = (BezoutChecks.p61Formula g : ℝ) :=
  (p61Formula_eq_rootPolynomial g).symm

private theorem mul_ne_zero_four (g : ℝ) (h4 : g ≠ 4) : (65536 : ℝ) * (g - 4) ^ 8 ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero 8 (sub_ne_zero.mpr h4))

private theorem mul_ne_zero_two (g : ℝ) (h2 : g ≠ 2) : (g - 2) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (sub_ne_zero.mpr h2)

/-! ### 2. Eliminating the `(g-4)^8 (g-2)^2` factor -/

/--
**Bézout elimination.**  If `g ≠ 4`, `g ≠ 2` and `z` is a common real zero of
`Ppoly · g` and `dPpoly · g`, then `P61(g) = 0`.

The proof uses the *proved* Bézout identity
`bezout_identity : Apoly·Ppoly + Bpoly·dPpoly = 65536·(g-4)^8·(g-2)^2·p61Formula g`;
at a common zero its left-hand side vanishes, and the two explicit factors
`65536·(g-4)^8` and `(g-2)^2` are non-zero, so the remaining factor `p61Formula g`
must vanish.  No resultant oracle, factorisation hypothesis, root assumption or
leading-coefficient nonvanishing is used.
-/
theorem p61_eq_zero_of_common_root (z g : ℝ)
    (h4 : g ≠ 4) (h2 : g ≠ 2)
    (hP : BezoutChecks.Ppoly z g = 0) (hdP : BezoutChecks.dPpoly z g = 0) :
    BezoutChecks.p61Formula g = 0 := by
  have hbez := BezoutChecks.bezout_identity z g
  rw [hP, hdP] at hbez
  simp only [mul_zero, add_zero] at hbez
  -- At a common zero the proved Bézout identity reads
  -- `0 = 65536 * (g-4)^8 * (g-2)^2 * p61Formula g`.
  -- `mul_eq_zero` on the proved identity, with the two explicit factors non-zero.
  have hC : (65536 : ℝ) * (g - 4) ^ 8 ≠ 0 := mul_ne_zero_four g h4
  have hD : (g - 2) ^ 2 ≠ 0 := mul_ne_zero_two g h2
  rcases mul_eq_zero.mp hbez.symm with h1 | h1'
  · rcases mul_eq_zero.mp h1 with h2' | h3
    · exact absurd h2' hC
    · exact absurd h3 hD
  · exact h1'

/-! ### 3. The common zero is the actual constant `AlphaRoot.alpha` -/

/--
**Main result.**  A common real zero of `P` and `dP/dz` inside `(4,5)` is the
actual RHO5 constant `AlphaRoot.alpha`.

The type contains no `RootSpec`, no existence hypothesis for roots of
`rootPolynomial`, and no extra axiom: the only inputs are the two scalar common
zero conditions, the two interval bounds, and the frozen D07/D09 theorems. -/
theorem common_root_eq_actual_alpha (z g : ℝ)
    (hl : 4 < g) (hu : g < 5)
    (hP : BezoutChecks.Ppoly z g = 0) (hdP : BezoutChecks.dPpoly z g = 0) :
    g = AlphaRoot.alpha := by
  have h4 : g ≠ 4 := ne_of_gt hl
  have h2 : g ≠ 2 := by linarith
  have hp61 : BezoutChecks.p61Formula g = 0 :=
    p61_eq_zero_of_common_root z g h4 h2 hP hdP
  have hroot : AlphaRoot.rootPolynomial g = 0 := by
    rw [← p61Formula_eq_rootPolynomial g, hp61]
  exact AlphaRoot.root_unique g hl hu hroot

end Rho5.Algebraic.ScalarAlphaBridge
