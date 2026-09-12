import Rho5.ExternalBFibreCapacity.Model
import Rho5.Certificate.B24Reconstruction.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# D137 — the real second row/column sign flip of the B24 reconstruction

D133 normalized `x0` and `A` by the two diagonal sign conjugations
`diag(1,1,ε,εη,εη)`.  The remaining head normalization is the *second* sign flip: the
simultaneous flip of **row `1` and column `1`** of the one real reconstructed matrix,
`S = diag(1,σ,1,1,1)`.  Reading the B24 coordinates off `S M S`:

* `e` and `β` are multiplied by `σ` (entries `M 0 1 = -e`, `M 1 0 = β`);
* `x` and `q` are multiplied by `σ` (entries `M (i+2) 1 = p x_i - e u_i`,
  `M 1 (j+2) = q_j + β v_j`);
* `u`, `v` and the whole `3 × 3` core `D` are untouched (so `k, A, B, c, d, r, s, t` and the
  height are untouched), while `p` is untouched as well (`M 1 1 = p - eβ` is invariant).

Because the two head signs move together, one *single* real operation makes both positive as
soon as the source gives `0 < e · β` (the paper's route: `F > 4` with `F ≤ 4p` gives `p > 1`,
and the head band gives `e β ≥ p - 1 > 0`).  That is exactly what this lane pays: from
`Qualified z`, `1 < z 8` and `0 < z 9 * z 10` it produces `z'` with `NormalizedB z'`, the same
height, the same `k, r, s, t, p, A, B, c, d`, both head coordinates positive, and the actual
matrix relation `reconstruct z' i j = sg i * reconstruct z i j * sg j` with
`sg = diag(1,σ,1,1,1)`.

This file fixes the vocabulary: the sign vector, the sign choice, the flipped frame and the
flipped point.
-/

namespace Rho5.Shared.BHeadSign

open Classical
open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail encode frameOf tailOf)

noncomputable section

/-! ## 1. The sign vector and the sign choice -/

/-- The sign vector of the second-row/column flip: `diag(1,σ,1,1,1)`. -/
def sgOf (sigma : ℝ) : Fin 5 → ℝ := ![1, sigma, 1, 1, 1]

/-- The sign chosen from `z` itself: `+1` when the head coordinate `e = z 9` is positive, else
`-1`.  Under `0 < e · β` this makes both `σ e` and `σ β` positive. -/
def headSigma (z : Point) : ℝ := if 0 < z 9 then 1 else -1

/-- Every entry of `sgOf` is `±1`. -/
theorem sgOf_eq_one_or_neg_one (sigma : ℝ) (h : sigma = 1 ∨ sigma = -1) (i : Fin 5) :
    sgOf sigma i = 1 ∨ sgOf sigma i = -1 := by
  rcases h with rfl | rfl <;> fin_cases i <;> simp [sgOf]

/-- The sign vector is unimodular. -/
theorem abs_sgOf (sigma : ℝ) (h : sigma = 1 ∨ sigma = -1) (i : Fin 5) :
    |sgOf sigma i| = 1 := by
  rcases h with rfl | rfl <;> fin_cases i <;> simp [sgOf]

theorem headSigma_eq_one_or_neg_one (z : Point) : headSigma z = 1 ∨ headSigma z = -1 := by
  unfold headSigma
  by_cases h : 0 < z 9
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem abs_headSigma (z : Point) : |headSigma z| = 1 := by
  rcases headSigma_eq_one_or_neg_one z with h | h <;> rw [h] <;> norm_num

theorem headSigma_mul_self (z : Point) : headSigma z * headSigma z = 1 := by
  rcases headSigma_eq_one_or_neg_one z with h | h <;> rw [h] <;> norm_num

/-- **The head sign makes `e` positive**: `0 < σ · z 9` as soon as `0 < z 9 * z 10`. -/
theorem headSigma_mul_pos_left (z : Point) (h : 0 < z 9 * z 10) : 0 < headSigma z * z 9 := by
  have he : z 9 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact (lt_irrefl 0) h
  rcases lt_or_gt_of_ne he with hneg | hpos
  · have hb : z 10 < 0 := by
      by_contra hc
      have hc' : 0 ≤ z 10 := le_of_not_gt hc
      nlinarith
    rw [headSigma, if_neg (not_lt.mpr (le_of_lt hneg))]
    nlinarith
  · rw [headSigma, if_pos hpos]
    simpa using hpos

/-- **The head sign makes `β` positive too**: `0 < σ · z 10` as soon as `0 < z 9 * z 10`; the
two head signs necessarily agree because their product is positive. -/
theorem headSigma_mul_pos_right (z : Point) (h : 0 < z 9 * z 10) : 0 < headSigma z * z 10 := by
  have he : z 9 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact (lt_irrefl 0) h
  rcases lt_or_gt_of_ne he with hneg | hpos
  · have hb : z 10 < 0 := by
      by_contra hc
      have hc' : 0 ≤ z 10 := le_of_not_gt hc
      nlinarith
    rw [headSigma, if_neg (not_lt.mpr (le_of_lt hneg))]
    nlinarith
  · have hb : 0 < z 10 := by nlinarith
    rw [headSigma, if_pos hpos]
    simpa using hb

/-! ## 2. The flipped frame and point -/

/-- The flipped B24 frame: `x` and `q` pick up `σ` componentwise, everything else (including the
whole core and the tail) is literally the original field. -/
def headFrame (f : Frame) (sigma : ℝ) : Frame where
  k := f.k
  A := f.A
  B := f.B
  c := f.c
  d := f.d
  u := f.u
  x := fun i => sigma * f.x i
  v := f.v
  q := fun i => sigma * f.q i

/-- The encoded point of the flipped frame, with the two head coordinates also multiplied by
`σ`: `encode (headFrame f σ) (σ β) p (σ e) t`. -/
def headEncode (f : Frame) (t : Tail) (b p e sigma : ℝ) : Point :=
  encode (headFrame f sigma) (sigma * b) p (sigma * e) t

/-- The flipped point of `z`, for an arbitrary sign `σ`. -/
def headPointOf (z : Point) (sigma : ℝ) : Point :=
  headEncode (frameOf z) (tailOf z) (z 10) (z 8) (z 9) sigma

/-- The canonical flipped point, with the sign read off `z`. -/
def headPoint (z : Point) : Point := headPointOf z (headSigma z)

/-! ## 3. Coordinate readings

Every coordinate of the flipped point, one lemma per index, all by `rfl`: the encoded frame is
the original frame with `x, q ↦ σ·` and the head coordinates `e, β ↦ σ·`, so `k, r, s, t,
A, B, c, d, p` and the whole tail are untouched while `u, v` are untouched and the height is
recomputed from the same tail. -/

@[simp] theorem headPointOf_zero (z : Point) (sigma : ℝ) : headPointOf z sigma 0 = z 0 := rfl

@[simp] theorem headPointOf_one (z : Point) (sigma : ℝ) : headPointOf z sigma 1 = z 1 := rfl

@[simp] theorem headPointOf_two (z : Point) (sigma : ℝ) : headPointOf z sigma 2 = z 2 := rfl

@[simp] theorem headPointOf_three (z : Point) (sigma : ℝ) : headPointOf z sigma 3 = z 3 := rfl

@[simp] theorem headPointOf_four (z : Point) (sigma : ℝ) : headPointOf z sigma 4 = z 4 := rfl

@[simp] theorem headPointOf_five (z : Point) (sigma : ℝ) : headPointOf z sigma 5 = z 5 := rfl

@[simp] theorem headPointOf_six (z : Point) (sigma : ℝ) : headPointOf z sigma 6 = z 6 := rfl

@[simp] theorem headPointOf_seven (z : Point) (sigma : ℝ) : headPointOf z sigma 7 = z 7 := rfl

@[simp] theorem headPointOf_eight (z : Point) (sigma : ℝ) : headPointOf z sigma 8 = z 8 := rfl

@[simp] theorem headPointOf_nine (z : Point) (sigma : ℝ) :
    headPointOf z sigma 9 = sigma * z 9 := rfl

@[simp] theorem headPointOf_ten (z : Point) (sigma : ℝ) :
    headPointOf z sigma 10 = sigma * z 10 := rfl

@[simp] theorem headPointOf_eleven (z : Point) (sigma : ℝ) : headPointOf z sigma 11 = z 11 := rfl

@[simp] theorem headPointOf_twelve (z : Point) (sigma : ℝ) : headPointOf z sigma 12 = z 12 := rfl

@[simp] theorem headPointOf_thirteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 13 = z 13 := rfl

@[simp] theorem headPointOf_fourteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 14 = sigma * z 14 := rfl

@[simp] theorem headPointOf_fifteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 15 = sigma * z 15 := rfl

@[simp] theorem headPointOf_sixteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 16 = sigma * z 16 := rfl

@[simp] theorem headPointOf_seventeen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 17 = z 17 := rfl

@[simp] theorem headPointOf_eighteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 18 = z 18 := rfl

@[simp] theorem headPointOf_nineteen (z : Point) (sigma : ℝ) :
    headPointOf z sigma 19 = z 19 := rfl

@[simp] theorem headPointOf_twenty (z : Point) (sigma : ℝ) :
    headPointOf z sigma 20 = sigma * z 20 := rfl

@[simp] theorem headPointOf_twentyone (z : Point) (sigma : ℝ) :
    headPointOf z sigma 21 = sigma * z 21 := rfl

@[simp] theorem headPointOf_twentytwo (z : Point) (sigma : ℝ) :
    headPointOf z sigma 22 = sigma * z 22 := rfl

/-- The height is recomputed from the same untouched tail, hence depends only on `z 1, z 2, z 3`. -/
@[simp] theorem headPointOf_twentythree (z : Point) (sigma : ℝ) :
    headPointOf z sigma 23 = z 1 + z 2 * z 3 / z 1 := rfl

end

end Rho5.Shared.BHeadSign
