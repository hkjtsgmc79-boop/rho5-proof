/-
D54 — the sharp fixed `3 × 3` determinant bound on the unit cube, and the reduction
machinery it is proved with.

The card's item 1: for `K : Matrix (Fin 3) (Fin 3) ℝ` with every `|K i j| ≤ 1`,
prove `|K.det| ≤ 4`; this is the sharp bound for the fixed `3 × 3` cube (the 512
sign matrices attain 4), not a complete-pivot growth bound.

Route.  `det` is affine in each single entry, and an affine function on `[-1,1]` is
bounded in absolute value by the larger of its two endpoint values.  Reducing the
six entries of rows `1`, `2` to the endpoints leaves 64 vertices; at each vertex the
three `2 × 2` cofactors of row `0` are concrete, and the triangle inequality plus
`|K 0 j| ≤ 1` finishes.

No arbitrary-dimension convexity library is built: the two ingredients are the
one-dimensional convex-combination bound `abs_convex_le` and the fixed-order affine
expansion `det_setEntry_affine`, both proved here.  The 64-vertex reduction and the
sharpness witness live in `MinorThreeBound/Vertex.lean` (generated, genuinely
proved, no `native_decide`).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Rho5.MinorThreeBound

open Matrix

/-! ## 1. Overwriting a single entry -/

/-- `setEntry K i j x` is `K` with the `(i, j)` entry replaced by `x`.

The guard is written on `Fin.val` rather than on `Fin` equality itself: `Nat`
equalities on literals reduce definitionally, while `Fin` equalities carry proof
components that make `simp`/`norm_num` rewriting fragile in the expansions below. -/
def setEntry (K : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun a b => if a.val = i.val ∧ b.val = j.val then x else K a b

/-- Overwriting an entry with its own value changes nothing. -/
theorem setEntry_self (K : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    setEntry K i j (K i j) = K := by
  funext a b
  by_cases h : a.val = i.val ∧ b.val = j.val
  · rw [setEntry, if_pos h, Fin.ext h.1, Fin.ext h.2]
  · rw [setEntry, if_neg h]

/-- Overwriting one entry with a value of absolute value at most `1` preserves the
entrywise cube condition. -/
theorem abs_setEntry_le (K : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (c : ℝ)
    (hc : |c| ≤ 1) (h : ∀ a b, |K a b| ≤ 1) :
    ∀ a b, |setEntry K i j c a b| ≤ 1 := by
  intro a b
  by_cases hab : a.val = i.val ∧ b.val = j.val
  · rw [setEntry, if_pos hab]; exact hc
  · rw [setEntry, if_neg hab]; exact h a b

/-! ## 2. The one-dimensional endpoint bound -/

/-- A convex combination of two reals is bounded in absolute value by the larger of
their absolute values.  This is the `[-1, 1]` endpoint step: an affine function on
`[-1, 1]` written as a convex combination of its two endpoint values. -/
theorem abs_convex_le (a b P Q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    |a * P + b * Q| ≤ max |P| |Q| := by
  have hsplit : |a * P + b * Q| ≤ a * |P| + b * |Q| := by
    calc |a * P + b * Q| ≤ |a * P| + |b * Q| := abs_add_le _ _
      _ = a * |P| + b * |Q| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hM : (0 : ℝ) ≤ max |P| |Q| := le_trans (abs_nonneg P) (le_max_left _ _)
  refine hsplit.trans ?_
  calc a * |P| + b * |Q| ≤ a * max |P| |Q| + b * max |P| |Q| :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max |P| |Q| := by rw [← add_mul, hab, one_mul]

/-- `|x| ≤ 1` gives `-1 ≤ x`. -/
theorem neg_one_le_of_abs_le {x : ℝ} (h : |x| ≤ 1) : -1 ≤ x := by
  linarith [neg_abs_le x, le_abs_self x]

/-- `|x| ≤ 1` gives `x ≤ 1`. -/
theorem le_one_of_abs_le {x : ℝ} (h : |x| ≤ 1) : x ≤ 1 := by
  linarith [le_abs_self x, abs_nonneg x]

/-! ## 3. The determinant is affine in each single entry -/

/-- **Fixed-order affine expansion.**  `det` of a `3 × 3` matrix is affine in each
single entry, written as the convex combination of its values at `x = 1` and
`x = -1`.  Proved entry by entry for the nine positions; no general multilinearity
theory is introduced. -/
theorem det_setEntry_affine (K : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) (x : ℝ) :
    (setEntry K i j x).det
      = ((1 + x) / 2) * (setEntry K i j 1).det
        + ((1 - x) / 2) * (setEntry K i j (-1)).det := by
  fin_cases i <;> fin_cases j <;>
    simp only [setEntry, Matrix.det_fin_three, Fin.isValue] <;>
    norm_num <;>
    ring

/-- **One reduction step.**  For a matrix in the cube, the absolute determinant is
bounded by the larger of the two absolute determinants obtained by pushing a single
entry to `-1` and to `1`. -/
theorem abs_det_le_max_endpoints (K : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3)
    (h : ∀ a b, |K a b| ≤ 1) :
    |K.det| ≤ max |(setEntry K i j (-1)).det| |(setEntry K i j 1).det| := by
  have hx : |K i j| ≤ 1 := h i j
  have hlower : -1 ≤ K i j := neg_one_le_of_abs_le hx
  have hupper : K i j ≤ 1 := le_one_of_abs_le hx
  have haff := det_setEntry_affine K i j (K i j)
  rw [setEntry_self] at haff
  rw [haff]
  -- `abs_convex_le` produces `max |P| |Q|` with `P` the `x = 1` value; the statement
  -- above lists the `x = -1` value first, hence the `max_comm`.
  simpa only [max_comm] using
    abs_convex_le ((1 + K i j) / 2) ((1 - K i j) / 2)
      (setEntry K i j 1).det (setEntry K i j (-1)).det
      (by linarith) (by linarith) (by ring)

/-! ## 4. The vertex bound: triangle inequality on the row-`0` cofactors -/

/-- **Vertex bound.**  If row `0` is in the cube, the determinant is bounded by the
sum of the absolute `2 × 2` cofactors of row `0`.  At a vertex of rows `1`, `2`
those three cofactors are concrete integers, and their sum is at most `4` (this is
what `MinorThreeBound/Vertex.lean` checks). -/
theorem abs_det_le_minor_sum (K : Matrix (Fin 3) (Fin 3) ℝ)
    (h0 : |K 0 0| ≤ 1) (h1 : |K 0 1| ≤ 1) (h2 : |K 0 2| ≤ 1) :
    |K.det| ≤ |K 1 1 * K 2 2 - K 1 2 * K 2 1| + |K 1 0 * K 2 2 - K 1 2 * K 2 0|
      + |K 1 0 * K 2 1 - K 1 1 * K 2 0| := by
  set A := K 1 1 * K 2 2 - K 1 2 * K 2 1 with hA
  set B := K 1 0 * K 2 2 - K 1 2 * K 2 0 with hB
  set C := K 1 0 * K 2 1 - K 1 1 * K 2 0 with hC
  have hdet : K.det = K 0 0 * A - K 0 1 * B + K 0 2 * C := by
    rw [hA, hB, hC, Matrix.det_fin_three]; ring
  rw [hdet]
  have htri : |K 0 0 * A - K 0 1 * B + K 0 2 * C|
      ≤ |K 0 0 * A| + |K 0 1 * B| + |K 0 2 * C| := by
    have h1' : |K 0 0 * A - K 0 1 * B + K 0 2 * C|
        ≤ |K 0 0 * A - K 0 1 * B| + |K 0 2 * C| := abs_add_le _ _
    have h2' : |K 0 0 * A - K 0 1 * B| ≤ |K 0 0 * A| + |K 0 1 * B| := by
      simpa using abs_sub_le (K 0 0 * A) 0 (K 0 1 * B)
    linarith
  refine htri.trans ?_
  rw [abs_mul, abs_mul, abs_mul]
  calc |K 0 0| * |A| + |K 0 1| * |B| + |K 0 2| * |C|
      ≤ 1 * |A| + 1 * |B| + 1 * |C| := by gcongr
    _ = |A| + |B| + |C| := by ring

end Rho5.MinorThreeBound
