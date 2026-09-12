/-
D34 — the D05 critical system meets the D19 real scalar alpha bridge
====================================================================

The G04 critical-point chain (D05) supplies, from the candidate box and the three
critical equations,

  `candidate_system_implies_elimP_and_derivative` :
    `ev (point x y z g) elimP = 0 ∧ ev (point x y z g) elimDP = 0`

and the D19 bridge turns a real common zero of the Bézout pair into the actual
constant,

  `ScalarAlphaBridge.common_root_eq_actual_alpha` :
    `4 < g → g < 5 → Ppoly z g = 0 → dPpoly z g = 0 → g = AlphaRoot.alpha`.

This module supplies the **only** missing link: the two *real evaluation* identities
between the D05 polynomials and the D07 Bézout pair,

* `eval_elimP_eq_Ppoly`  : `ev (point x y z g) elimP  = BezoutChecks.Ppoly z g`
* `eval_elimDP_eq_dPpoly`: `ev (point x y z g) elimDP = BezoutChecks.dPpoly z g`

and then composes everything into

* `candidate_system_eq_actual_alpha` : from `CandidateBox x y z g` and
  `P1 = P2 = P3 = J = 0`, conclude `g = AlphaRoot.alpha`.

Route note (why this is cheap where the old route was not).  The card forbids moving
the nineteen `ba`/`bb` `Poly` identities, and this module never mentions them.  It
evaluates at the point *first* and compares the two sides as real numbers: both sides
are the same 11 (resp. 10) `z^i` terms whose coefficients are the same `g`-polynomials.
Each coefficient identity is therefore a one-variable polynomial identity in `g`,
discharged by `simp only` + `ring` on `ℝ` — no `MvPolynomial` recursion, no 73-term
objects.  The coefficient lemmas live in `ScalarCandidateAlpha.CoeffBridge`, generated
from the audited certificate.

Scope: read-only over D05's prefix sources, the D07 Bézout lane, the D09 `AlphaRoot`
lane and the D19 bridge; nothing upstream is modified or rebuilt.  No `RootSpec`, no
root-existence hypothesis, no critical-point-existence hypothesis and no extra
non-vanishing assumption is added: the D05 `CandidateBox` and the four scalar
equations remain the only hypotheses of the final theorem.
-/
import Rho5.Algebraic.ScalarCandidateAlpha.CoeffBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

namespace Rho5.Algebraic.ScalarCandidateAlpha

open Rho5.Algebraic
open Rho5

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## The two real evaluation bridges -/

/-- `ev` is `MvPolynomial.eval₂Hom` at `RingHom.id`; this identity exposes the
library's `eval₂Hom` lemmas (`map_add`, `map_mul`, `eval₂Hom_X'`, …) for the D05
abbreviation `ev`. -/
theorem ev_eq_eval₂Hom (v : Point) : ev v = MvPolynomial.eval₂Hom (RingHom.id ℝ) v := rfl

/-- **Goal 1 (first bridge).**  The D05 elimination polynomial, evaluated at the point
`(x, y, z, g)`, equals D07's `P` polynomial in `(z, g)`.

Both sides are the same eleven `z^i` terms with the same `g`-coefficients: the ring
homomorphism is pushed through the additions and multiplications, the `z`/`g`
variables become the coordinates, and each coefficient is the corresponding identity
from `CoeffBridge`. -/
theorem eval_elimP_eq_Ppoly (x y z g : ℝ) :
    ev (point x y z g) elimP = BezoutChecks.Ppoly z g := by
  rw [elimP, BezoutChecks.Ppoly, ev_eq_eval₂Hom]
  simp only [map_add, map_mul, map_pow, zVar, MvPolynomial.eval₂Hom_X']
  simp only [point, Matrix.cons_val]
  -- restate the goal with `point` so the `CoeffBridge` lemmas (stated for `ev`) apply
  show ev (point x y z g) pc0 + ev (point x y z g) pc1 * z + ev (point x y z g) pc2 * z ^ 2
      + ev (point x y z g) pc3 * z ^ 3 + ev (point x y z g) pc4 * z ^ 4
      + ev (point x y z g) pc5 * z ^ 5 + ev (point x y z g) pc6 * z ^ 6
      + ev (point x y z g) pc7 * z ^ 7 + ev (point x y z g) pc8 * z ^ 8
      + ev (point x y z g) pc9 * z ^ 9 + ev (point x y z g) pc10 * z ^ 10
    = BezoutChecks.Ppoly z g
  rw [eval_pc0, eval_pc1, eval_pc2, eval_pc3, eval_pc4, eval_pc5, eval_pc6, eval_pc7,
    eval_pc8, eval_pc9, eval_pc10]
  rw [BezoutChecks.Ppoly]

/-- **Goal 1 (second bridge).**  The same for the formal `z`-derivative: the
coefficient of `z^i` is `(i+1) · pc_{i+1}` with the weight `(i : ℝ) + 1` from D05's
`elimDP`, matching D07's `dPpoly`.  Only the ten coefficients `pc1 … pc10` occur. -/
theorem eval_elimDP_eq_dPpoly (x y z g : ℝ) :
    ev (point x y z g) elimDP = BezoutChecks.dPpoly z g := by
  rw [elimDP, BezoutChecks.dPpoly, ev_eq_eval₂Hom]
  simp only [map_add, map_mul, map_pow, zVar, MvPolynomial.eval₂Hom_X']
  simp only [point, Matrix.cons_val]
  show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 1
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc1
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 2
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc2 * z
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 3
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc3 * z ^ 2
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 4
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc4 * z ^ 3
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 5
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc5 * z ^ 4
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 6
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc6 * z ^ 5
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 7
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc7 * z ^ 6
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 8
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc8 * z ^ 7
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 9
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc9 * z ^ 8
        + (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) 10
          * (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc10 * z ^ 9
      = BezoutChecks.dPpoly z g
  simp only [map_ofNat, Matrix.cons_val]
  simp only [show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc1
      = BezoutChecks.pc1 g from eval_pc1 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc2
      = BezoutChecks.pc2 g from eval_pc2 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc3
      = BezoutChecks.pc3 g from eval_pc3 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc4
      = BezoutChecks.pc4 g from eval_pc4 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc5
      = BezoutChecks.pc5 g from eval_pc5 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc6
      = BezoutChecks.pc6 g from eval_pc6 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc7
      = BezoutChecks.pc7 g from eval_pc7 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc8
      = BezoutChecks.pc8 g from eval_pc8 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc9
      = BezoutChecks.pc9 g from eval_pc9 x y z g,
    show (MvPolynomial.eval₂Hom (RingHom.id ℝ) (point x y z g)) pc10
      = BezoutChecks.pc10 g from eval_pc10 x y z g]
  norm_num
  simp only [BezoutChecks.dPpoly, BezoutChecks.dpc0, BezoutChecks.dpc1, BezoutChecks.dpc2,
    BezoutChecks.dpc3, BezoutChecks.dpc4, BezoutChecks.dpc5, BezoutChecks.dpc6,
    BezoutChecks.dpc7, BezoutChecks.dpc8, BezoutChecks.dpc9]
  ring_nf

/-! ## The candidate identification -/

/-- **Goal 2.**  The G04 critical equations, inside the D05 candidate box, identify the
candidate's `g` with the actual constant `AlphaRoot.alpha`.

Composition of the two already-proved interfaces:
`candidate_system_implies_elimP_and_derivative` (D05) gives the vanishing of `elimP`
and `elimDP` at the point; the two bridges above turn that into vanishing of D07's
`Ppoly`/`dPpoly`; `CandidateBox.coarse` supplies `4 < g < 5`; and
`ScalarAlphaBridge.common_root_eq_actual_alpha` (D19) concludes.

The statement adds no `RootSpec`, no root-existence hypothesis, no critical-point
existence hypothesis and no extra non-vanishing assumption: the box and the four
scalar equations are the only hypotheses, exactly as in the D05 interface. -/
theorem candidate_system_eq_actual_alpha (x y z g : ℝ) (hb : CandidateBox x y z g)
    (h1 : P1 x y z g = 0) (h2 : P2 x y z g = 0)
    (h3 : P3 x y z g = 0) (hJ : J x y z g = 0) :
    g = AlphaRoot.alpha := by
  obtain ⟨hP, hdP⟩ :=
    candidate_system_implies_elimP_and_derivative x y z g hb h1 h2 h3 hJ
  rw [eval_elimP_eq_Ppoly x y z g] at hP
  rw [eval_elimDP_eq_dPpoly x y z g] at hdP
  exact ScalarAlphaBridge.common_root_eq_actual_alpha z g
    hb.coarse.gl hb.coarse.gu hP hdP

end Rho5.Algebraic.ScalarCandidateAlpha
