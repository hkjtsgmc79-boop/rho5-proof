/-
D70 stage 4 — the balanced determinant identity of the fourth face, in original minors.

D56's paid condensation, read through the D62 minor readings, says exactly

`B M * det M = C M * m4 M 1 1 - m4 M 0 1 * m4 M 1 0`      (no division anywhere);

on the fourth face `m4 M 1 1 = -C M` this becomes the card's polynomial equality

`B M * det M = -(C M)^2 - m4 M 0 1 * m4 M 1 0`,

and with **nonnegative off-diagonals** plus `0 < B M`, `0 < C M` it gives

`det M < 0`  and  `|det M| * B M = (C M)^2 + m4 M 0 1 * m4 M 1 0`.

Only the fourth face is consumed here.  The first three faces are untouched: they stay as
the other three disjuncts of `BoundaryFace`, and `boundaryFace_iff_schurFaces` keeps all
four of them equivalent to the actual Schur faces.  This is a balanced *polynomial* equality
for that one face; it is not a proof that all faces balance, and it assumes no balance.
-/
import Rho5.Shared.MinorBoundaryFaces.Equiv
import Rho5.Shared.TailDeterminant

namespace Rho5.MinorBoundaryFaces

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.MinorCPDomain (A B C PolyCP m4)

/-- **D56's condensation in the original minors** (division-free, `p M`, `k M` only
assumed nonzero through the positive hypotheses the other theorems use):
`B M * det M = C M * m4 M 1 1 - m4 M 0 1 * m4 M 1 0`. -/
theorem B_mul_det_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    B M * M.det = C M * m4 M 1 1 - m4 M 0 1 * m4 M 1 0 := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hkne : k M ≠ 0 := ne_of_gt hk
  have hcond : m4 M 0 0 * m4 M 1 1 - m4 M 0 1 * m4 M 1 0 = p M * k M * M.det :=
    Rho5.TailDeterminant.bordered_condensation M h00 hpne hkne
  rw [Rho5.MinorCPDomain.B_eq M h00 hpne, Rho5.MinorCPDomain.C_eq M h00 hp hk,
    ← Rho5.MinorCPDomain.m4_00_eq M h00 hp hk]
  exact hcond.symm

/-- **The card's equality on the fourth face**:
`B M * det M = -(C M)^2 - m4 M 0 1 * m4 M 1 0`. -/
theorem B_mul_det_eq_of_face4 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hface : face4 M) : B M * M.det = -(C M) ^ 2 - m4 M 0 1 * m4 M 1 0 := by
  have h := B_mul_det_eq M h00 hp hk
  have h4 : m4 M 1 1 = -C M := hface
  rw [h4] at h
  rw [h]
  ring

/-- **The determinant consequence on the fourth face.**  Nonnegative off-diagonals and
`0 < B M`, `0 < C M` force `det M < 0`, and the same equality gives the absolute-value
form `|det M| * B M = (C M)^2 + m4 M 0 1 * m4 M 1 0`.  The strictness comes from
`0 < C M` (not from any non-strictness of the off-diagonals). -/
theorem det_neg_and_abs_of_face4 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hface : face4 M) (h01 : 0 ≤ m4 M 0 1) (h10 : 0 ≤ m4 M 1 0) (hB : 0 < B M)
    (hC : 0 < C M) :
    M.det < 0 ∧ |M.det| * B M = C M ^ 2 + m4 M 0 1 * m4 M 1 0 := by
  have hkey := B_mul_det_eq_of_face4 M h00 hp hk hface
  have hnn : 0 ≤ m4 M 0 1 * m4 M 1 0 := mul_nonneg h01 h10
  have hC2 : 0 < C M ^ 2 := by rw [pow_two]; exact mul_pos hC hC
  have hsum : 0 < C M ^ 2 + m4 M 0 1 * m4 M 1 0 := by linarith
  -- `hkey`'s right-hand side is `-(C^2) - off`; the two absolute-value steps need the
  -- single-negation shape `-(C^2 + off)`, so bridge it once (polynomial, no assumption).
  have hneg : -(C M ^ 2) - m4 M 0 1 * m4 M 1 0 = -(C M ^ 2 + m4 M 0 1 * m4 M 1 0) := by
    ring
  have hdet : M.det < 0 := by
    have hBdet : B M * M.det < B M * 0 := by
      rw [mul_zero, hkey, hneg]
      exact neg_lt_zero.mpr hsum
    exact lt_of_mul_lt_mul_left hBdet hB.le
  have hBabs : B M * |M.det| = |B M * M.det| := by rw [abs_mul, abs_of_pos hB]
  have hmain : B M * |M.det| = C M ^ 2 + m4 M 0 1 * m4 M 1 0 := by
    rw [hBabs, hkey, hneg, abs_neg, abs_of_nonneg hsum.le]
  exact ⟨hdet, by rw [mul_comm]; exact hmain⟩

/-- The same determinant consequence with `p`, `k`, `B`, `C` positivity taken from the
card's `PolyCP` domain (D62's `polyCP_iff_frame` and `p_pos_of_A`/`k_pos_of_B`). -/
theorem det_neg_and_abs_of_face4_of_polyCP (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M)
    (hface : face4 M) (h01 : 0 ≤ m4 M 0 1) (h10 : 0 ≤ m4 M 1 0) :
    M.det < 0 ∧ |M.det| * B M = C M ^ 2 + m4 M 0 1 * m4 M 1 0 := by
  obtain ⟨hA, hB, hC, -⟩ := hP
  have hp : 0 < p M := Rho5.MinorCPDomain.p_pos_of_A M h00 hA
  have hk : 0 < k M := Rho5.MinorCPDomain.k_pos_of_B M h00 hp hB
  exact det_neg_and_abs_of_face4 M h00 hp hk hface h01 h10 hB hC

end Rho5.MinorBoundaryFaces
