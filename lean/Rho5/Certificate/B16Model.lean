import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Source-level model rows used by the actual depth-11 B16 sample.
The meaning of `Physical` is the explicit B24 physical inequality layer; proving
that normalized complete-pivot matrices map into it remains a separate task. -/
namespace Rho5.Certificate.B16
abbrev Point := Fin 24 → ℝ

def u (x : Point) : Fin 3 → ℝ := ![x 11, x 12, x 13]
def xv (x : Point) : Fin 3 → ℝ := ![x 14, x 15, x 16]
def v (x : Point) : Fin 3 → ℝ := ![x 17, x 18, x 19]
def q (x : Point) : Fin 3 → ℝ := ![x 20, x 21, x 22]
def D (x : Point) : Fin 3 → Fin 3 → ℝ :=
  ![![x 0, x 4, x 5],
    ![x 0 * x 6, x 1 + x 4 * x 6, x 2 + x 5 * x 6],
    ![x 0 * x 7, x 3 + x 4 * x 7, -x 1 + x 5 * x 7]]
def O (x : Point) (i j : Fin 3) := D x i j + u x i * v x j + xv x i * q x j
def S (x : Point) (i j : Fin 3) := D x i j + xv x i * q x j
def L (x : Point) (j : Fin 3) := x 8 * xv x j - x 9 * u x j
def P (x : Point) (j : Fin 3) := x 10 * v x j + q x j

structure Physical (x : Point) : Prop where
  d_bound : ∀ i j, |D x i j| ≤ x 0
  o_bound : ∀ i j, |O x i j| ≤ 1
  s_bound : ∀ i j, |S x i j| ≤ x 8
  l_bound : ∀ j, |L x j| ≤ 1
  p_bound : ∀ j, |P x j| ≤ 1
  q_bound : ∀ j, |q x j| ≤ x 8
  r_pos : 0 < x 1
  height : x 23 = x 1 + x 2 * x 3 / x 1
  order_t : x 3 ≤ x 1

theorem height_polynomial (x : Point) (h : Physical x) :
    x 1 * x 1 - x 1 * x 23 + x 2 * x 3 = 0 := by
  have hr : x 1 ≠ 0 := ne_of_gt h.r_pos
  have he : x 23 * x 1 = x 1 * x 1 + x 2 * x 3 := by
    rw [h.height, add_mul, div_mul_cancel₀ _ hr]
  nlinarith [he]

/-- All four McCormick rows, including the repeated-coordinate case, follow
from the actual product and the OLD box endpoints. -/
theorem mccormick (x y lx ux ly uy : ℝ)
    (hx : lx ≤ x ∧ x ≤ ux) (hy : ly ≤ y ∧ y ≤ uy) :
    (ly*x + lx*y - x*y ≤ lx*ly) ∧
    (uy*x + ux*y - x*y ≤ ux*uy) ∧
    (-uy*x - lx*y + x*y ≤ -lx*uy) ∧
    (-ly*x - ux*y + x*y ≤ -ux*ly) := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hy.1)]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hy.2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.1)]

/-- A normalized CHSH facet underlying the actual cycle rows. -/
theorem chsh (a b c d : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    a*c + a*d + b*c - b*d ≤ 2 := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  by_cases hcd : 0 ≤ c + d
  · by_cases hdiff : 0 ≤ c - d
    · have h1 := mul_le_mul_of_nonneg_right ha'.2 hcd
      have h2 := mul_le_mul_of_nonneg_right hb'.2 hdiff
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_right ha'.2 hcd
      have h2 := mul_le_mul_of_nonpos_right hb'.1 (le_of_not_ge hdiff)
      nlinarith
  · by_cases hdiff : 0 ≤ c - d
    · have h1 := mul_le_mul_of_nonpos_right ha'.1 (le_of_not_ge hcd)
      have h2 := mul_le_mul_of_nonneg_right hb'.2 hdiff
      nlinarith
    · have h1 := mul_le_mul_of_nonpos_right ha'.1 (le_of_not_ge hcd)
      have h2 := mul_le_mul_of_nonpos_right hb'.1 (le_of_not_ge hdiff)
      nlinarith

theorem centered_abs_le (x l u : ℝ) (hx : l ≤ x ∧ x ≤ u) :
    |2*x-l-u| ≤ u-l := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2]

theorem chsh_scaled (a b c d A B C D : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    a*c*B*D + a*d*B*C + b*c*A*D - b*d*A*C ≤ 2*A*B*C*D := by
  have hn (x X : ℝ) (hp : 0 < X) (hx : |x| ≤ X) : |x/X| ≤ 1 := by
    rw [abs_div, abs_of_pos hp]
    exact (div_le_one hp).2 hx
  have h := chsh (a/A) (b/B) (c/C) (d/D)
    (hn a A hA ha) (hn b B hB hb) (hn c C hC hc) (hn d D hD hd)
  have hm := mul_le_mul_of_nonneg_right h
    (le_of_lt (mul_pos (mul_pos (mul_pos hA hB) hC) hD))
  have he : (a/A*(c/C) + a/A*(d/D) + b/B*(c/C) - b/B*(d/D)) * (A*B*C*D) =
      a*c*B*D + a*d*B*C + b*c*A*D - b*d*A*C := by
    field_simp
    <;> ring
  rw [he] at hm
  nlinarith only [hm]

#print axioms height_polynomial
#print axioms mccormick
#print axioms chsh
#print axioms chsh_scaled
end Rho5.Certificate.B16
