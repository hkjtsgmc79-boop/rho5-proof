/-
D07 — generic assembly of the Bézout identity from its 19 coefficient
identities.

This is the *generic `CommRing`* layer: given the 19 scalar coefficient
identities of `A * P + B * P'`, conclude the full polynomial identity
`A * P + B * P' = rhs`.  Structurally this is Great's `assemble_bezout`
(`great-algebraic-20260911/received/lean_project/Rho5/Algebraic/BezoutData.lean`),
rewritten here in the `Rho5.Algebraic.BezoutChecks` namespace on top of the
independent coefficient data of `CoeffData.lean`.

The whole identity is the single `linear_combination`

  `h0 + z^1 * h1 + z^2 * h2 + ... + z^18 * h18`

i.e. the `z^k`-weighted sum of the coefficient identities *is* the expansion of
`A * P + B * P'`.  Nothing here expands any high-degree polynomial: all the
heavy `ring` work lives in the 19 scalar coefficient identities.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Rho5.Algebraic.BezoutChecks.CoeffData

namespace Rho5.Algebraic.BezoutChecks

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

variable {R : Type*} [CommRing R]

/-- `P(z,g) = Σ_{i<11} pc_i(g) z^i` — the singular-locus polynomial. -/
def Ppoly (z g : R) : R :=
    pc0 g + pc1 g * z + pc2 g * z ^ 2 + pc3 g * z ^ 3 + pc4 g * z ^ 4
      + pc5 g * z ^ 5 + pc6 g * z ^ 6 + pc7 g * z ^ 7 + pc8 g * z ^ 8
      + pc9 g * z ^ 9 + pc10 g * z ^ 10

/-- `dP/dz = Σ_{i<10} (i+1) pc_{i+1}(g) z^i` — the formal z-derivative. -/
def dPpoly (z g : R) : R :=
    dpc0 g + dpc1 g * z + dpc2 g * z ^ 2 + dpc3 g * z ^ 3 + dpc4 g * z ^ 4
      + dpc5 g * z ^ 5 + dpc6 g * z ^ 6 + dpc7 g * z ^ 7 + dpc8 g * z ^ 8
      + dpc9 g * z ^ 9

/-- `A(z,g) = Σ_{i<9} ba_i(g) z^i` — first Bézout multiplier. -/
def Apoly (z g : R) : R :=
    ba0 g + ba1 g * z + ba2 g * z ^ 2 + ba3 g * z ^ 3 + ba4 g * z ^ 4
      + ba5 g * z ^ 5 + ba6 g * z ^ 6 + ba7 g * z ^ 7 + ba8 g * z ^ 8

/-- `B(z,g) = Σ_{i<10} bb_i(g) z^i` — second Bézout multiplier. -/
def Bpoly (z g : R) : R :=
    bb0 g + bb1 g * z + bb2 g * z ^ 2 + bb3 g * z ^ 3 + bb4 g * z ^ 4
      + bb5 g * z ^ 5 + bb6 g * z ^ 6 + bb7 g * z ^ 7 + bb8 g * z ^ 8
      + bb9 g * z ^ 9

/--
Assembly of the Bézout identity from its 19 coefficient identities.

`h_n` is the coefficient of `z^n` in `A * P + B * P'`; it equals `rhs` for
`n = 0` and vanishes for `1 ≤ n ≤ 18`.  The conclusion is the polynomial
identity over an arbitrary commutative ring, so it can be instantiated at
`MvPolynomial (Fin 4) ℤ` (or any other coefficient ring) without change.
-/
theorem assemble_bezout (z g : R)
    (rhs : R)
    (h0 : ba0 g * pc0 g + bb0 g * (1 * pc1 g) = rhs)
    (h1 : ba0 g * pc1 g + ba1 g * pc0 g + bb0 g * (2 * pc2 g)
      + bb1 g * (1 * pc1 g) = 0)
    (h2 : ba0 g * pc2 g + ba1 g * pc1 g + ba2 g * pc0 g + bb0 g * (3 * pc3 g)
      + bb1 g * (2 * pc2 g) + bb2 g * (1 * pc1 g) = 0)
    (h3 : ba0 g * pc3 g + ba1 g * pc2 g + ba2 g * pc1 g + ba3 g * pc0 g
      + bb0 g * (4 * pc4 g) + bb1 g * (3 * pc3 g) + bb2 g * (2 * pc2 g)
      + bb3 g * (1 * pc1 g) = 0)
    (h4 : ba0 g * pc4 g + ba1 g * pc3 g + ba2 g * pc2 g + ba3 g * pc1 g
      + ba4 g * pc0 g + bb0 g * (5 * pc5 g) + bb1 g * (4 * pc4 g)
      + bb2 g * (3 * pc3 g) + bb3 g * (2 * pc2 g) + bb4 g * (1 * pc1 g) = 0)
    (h5 : ba0 g * pc5 g + ba1 g * pc4 g + ba2 g * pc3 g + ba3 g * pc2 g
      + ba4 g * pc1 g + ba5 g * pc0 g + bb0 g * (6 * pc6 g)
      + bb1 g * (5 * pc5 g) + bb2 g * (4 * pc4 g) + bb3 g * (3 * pc3 g)
      + bb4 g * (2 * pc2 g) + bb5 g * (1 * pc1 g) = 0)
    (h6 : ba0 g * pc6 g + ba1 g * pc5 g + ba2 g * pc4 g + ba3 g * pc3 g
      + ba4 g * pc2 g + ba5 g * pc1 g + ba6 g * pc0 g + bb0 g * (7 * pc7 g)
      + bb1 g * (6 * pc6 g) + bb2 g * (5 * pc5 g) + bb3 g * (4 * pc4 g)
      + bb4 g * (3 * pc3 g) + bb5 g * (2 * pc2 g) + bb6 g * (1 * pc1 g) = 0)
    (h7 : ba0 g * pc7 g + ba1 g * pc6 g + ba2 g * pc5 g + ba3 g * pc4 g
      + ba4 g * pc3 g + ba5 g * pc2 g + ba6 g * pc1 g + ba7 g * pc0 g
      + bb0 g * (8 * pc8 g) + bb1 g * (7 * pc7 g) + bb2 g * (6 * pc6 g)
      + bb3 g * (5 * pc5 g) + bb4 g * (4 * pc4 g) + bb5 g * (3 * pc3 g)
      + bb6 g * (2 * pc2 g) + bb7 g * (1 * pc1 g) = 0)
    (h8 : ba0 g * pc8 g + ba1 g * pc7 g + ba2 g * pc6 g + ba3 g * pc5 g
      + ba4 g * pc4 g + ba5 g * pc3 g + ba6 g * pc2 g + ba7 g * pc1 g
      + ba8 g * pc0 g + bb0 g * (9 * pc9 g) + bb1 g * (8 * pc8 g)
      + bb2 g * (7 * pc7 g) + bb3 g * (6 * pc6 g) + bb4 g * (5 * pc5 g)
      + bb5 g * (4 * pc4 g) + bb6 g * (3 * pc3 g) + bb7 g * (2 * pc2 g)
      + bb8 g * (1 * pc1 g) = 0)
    (h9 : ba0 g * pc9 g + ba1 g * pc8 g + ba2 g * pc7 g + ba3 g * pc6 g
      + ba4 g * pc5 g + ba5 g * pc4 g + ba6 g * pc3 g + ba7 g * pc2 g
      + ba8 g * pc1 g + bb0 g * (10 * pc10 g) + bb1 g * (9 * pc9 g)
      + bb2 g * (8 * pc8 g) + bb3 g * (7 * pc7 g) + bb4 g * (6 * pc6 g)
      + bb5 g * (5 * pc5 g) + bb6 g * (4 * pc4 g) + bb7 g * (3 * pc3 g)
      + bb8 g * (2 * pc2 g) + bb9 g * (1 * pc1 g) = 0)
    (h10 : ba0 g * pc10 g + ba1 g * pc9 g + ba2 g * pc8 g + ba3 g * pc7 g
      + ba4 g * pc6 g + ba5 g * pc5 g + ba6 g * pc4 g + ba7 g * pc3 g
      + ba8 g * pc2 g + bb1 g * (10 * pc10 g) + bb2 g * (9 * pc9 g)
      + bb3 g * (8 * pc8 g) + bb4 g * (7 * pc7 g) + bb5 g * (6 * pc6 g)
      + bb6 g * (5 * pc5 g) + bb7 g * (4 * pc4 g) + bb8 g * (3 * pc3 g)
      + bb9 g * (2 * pc2 g) = 0)
    (h11 : ba1 g * pc10 g + ba2 g * pc9 g + ba3 g * pc8 g + ba4 g * pc7 g
      + ba5 g * pc6 g + ba6 g * pc5 g + ba7 g * pc4 g + ba8 g * pc3 g
      + bb2 g * (10 * pc10 g) + bb3 g * (9 * pc9 g) + bb4 g * (8 * pc8 g)
      + bb5 g * (7 * pc7 g) + bb6 g * (6 * pc6 g) + bb7 g * (5 * pc5 g)
      + bb8 g * (4 * pc4 g) + bb9 g * (3 * pc3 g) = 0)
    (h12 : ba2 g * pc10 g + ba3 g * pc9 g + ba4 g * pc8 g + ba5 g * pc7 g
      + ba6 g * pc6 g + ba7 g * pc5 g + ba8 g * pc4 g + bb3 g * (10 * pc10 g)
      + bb4 g * (9 * pc9 g) + bb5 g * (8 * pc8 g) + bb6 g * (7 * pc7 g)
      + bb7 g * (6 * pc6 g) + bb8 g * (5 * pc5 g) + bb9 g * (4 * pc4 g) = 0)
    (h13 : ba3 g * pc10 g + ba4 g * pc9 g + ba5 g * pc8 g + ba6 g * pc7 g
      + ba7 g * pc6 g + ba8 g * pc5 g + bb4 g * (10 * pc10 g)
      + bb5 g * (9 * pc9 g) + bb6 g * (8 * pc8 g) + bb7 g * (7 * pc7 g)
      + bb8 g * (6 * pc6 g) + bb9 g * (5 * pc5 g) = 0)
    (h14 : ba4 g * pc10 g + ba5 g * pc9 g + ba6 g * pc8 g + ba7 g * pc7 g
      + ba8 g * pc6 g + bb5 g * (10 * pc10 g) + bb6 g * (9 * pc9 g)
      + bb7 g * (8 * pc8 g) + bb8 g * (7 * pc7 g) + bb9 g * (6 * pc6 g) = 0)
    (h15 : ba5 g * pc10 g + ba6 g * pc9 g + ba7 g * pc8 g + ba8 g * pc7 g
      + bb6 g * (10 * pc10 g) + bb7 g * (9 * pc9 g) + bb8 g * (8 * pc8 g)
      + bb9 g * (7 * pc7 g) = 0)
    (h16 : ba6 g * pc10 g + ba7 g * pc9 g + ba8 g * pc8 g + bb7 g * (10 * pc10 g)
      + bb8 g * (9 * pc9 g) + bb9 g * (8 * pc8 g) = 0)
    (h17 : ba7 g * pc10 g + ba8 g * pc9 g + bb8 g * (10 * pc10 g)
      + bb9 g * (9 * pc9 g) = 0)
    (h18 : ba8 g * pc10 g + bb9 g * (10 * pc10 g) = 0)
    : Apoly z g * Ppoly z g + Bpoly z g * dPpoly z g = rhs := by
  -- `dpc_i g` is definitionally `(i+1) * pc_{i+1} g`; unfold it so that the
  -- goal's monomials are the same atoms as the hypotheses'.
  simp only [Apoly, Bpoly, Ppoly, dPpoly, dpc0, dpc1, dpc2, dpc3, dpc4,
    dpc5, dpc6, dpc7, dpc8, dpc9]
  linear_combination h0 + z ^ 1 * h1 + z ^ 2 * h2 + z ^ 3 * h3 + z ^ 4 * h4
    + z ^ 5 * h5 + z ^ 6 * h6 + z ^ 7 * h7 + z ^ 8 * h8 + z ^ 9 * h9
    + z ^ 10 * h10 + z ^ 11 * h11 + z ^ 12 * h12 + z ^ 13 * h13
    + z ^ 14 * h14 + z ^ 15 * h15 + z ^ 16 * h16 + z ^ 17 * h17
    + z ^ 18 * h18

end

end Rho5.Algebraic.BezoutChecks
