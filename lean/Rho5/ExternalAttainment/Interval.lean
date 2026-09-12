import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
A small, proof-producing interval interface.  Every numeric side condition in
IntervalData is an ordinary `norm_num` proof.  There is no external Boolean
oracle and no change to the project's existing notions of a matrix or a path.
-/
namespace Rho5.ExternalAttainment

/-- A closed interval proposition, used only to derive entry inequalities. -/
def Bounds (l u v : ℝ) : Prop := l ≤ v ∧ v ≤ u

namespace Bounds

variable {a b c d l u x y : ℝ}

theorem widen (h : Bounds a b x) (hl : l ≤ a) (hu : b ≤ u) :
    Bounds l u x := ⟨hl.trans h.1, h.2.trans hu⟩

theorem add (hx : Bounds a b x) (hy : Bounds c d y)
    (hl : l ≤ a + c) (hu : b + d ≤ u) : Bounds l u (x + y) := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem sub (hx : Bounds a b x) (hy : Bounds c d y)
    (hl : l ≤ a - d) (hu : b - c ≤ u) : Bounds l u (x - y) := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem neg (hx : Bounds a b x) : Bounds (-b) (-a) (-x) := by
  constructor <;> linarith [hx.1, hx.2]

/-- An affine function on an interval is bounded by its two endpoint values. -/
theorem mul_from_endpoints (hx : Bounds a b x)
    (hla : l ≤ a * y) (hlb : l ≤ b * y)
    (hua : a * y ≤ u) (hub : b * y ≤ u) : Bounds l u (x * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨hla.trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans hub⟩
  · have hy' : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    exact ⟨hlb.trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans hua⟩

/-- Four-corner product enclosure, without a sign restriction on either factor. -/
theorem mul (hx : Bounds a b x) (hy : Bounds c d y)
    (hlac : l ≤ a*c) (hlad : l ≤ a*d)
    (hlbc : l ≤ b*c) (hlbd : l ≤ b*d)
    (huac : a*c ≤ u) (huad : a*d ≤ u)
    (hubc : b*c ≤ u) (hubd : b*d ≤ u) : Bounds l u (x*y) := by
  have ha : Bounds l u (a*y) := by
    have h := mul_from_endpoints hy
      (y := a) (l := l) (u := u)
      (by simpa only [mul_comm] using hlac)
      (by simpa only [mul_comm] using hlad)
      (by simpa only [mul_comm] using huac)
      (by simpa only [mul_comm] using huad)
    simpa only [mul_comm] using h
  have hb : Bounds l u (b*y) := by
    have h := mul_from_endpoints hy
      (y := b) (l := l) (u := u)
      (by simpa only [mul_comm] using hlbc)
      (by simpa only [mul_comm] using hlbd)
      (by simpa only [mul_comm] using hubc)
      (by simpa only [mul_comm] using hubd)
    simpa only [mul_comm] using h
  exact mul_from_endpoints hx ha.1 hb.1 ha.2 hb.2

theorem recip_pos_exact (hx : Bounds a b x) (ha : 0 < a) :
    Bounds (1/b) (1/a) (1/x) := by
  have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
  have hbpos : 0 < b := lt_of_lt_of_le hxpos hx.2
  constructor
  · exact (div_le_div_iff₀ hbpos hxpos).mpr (by simpa using hx.2)
  · exact (div_le_div_iff₀ hxpos ha).mpr (by simpa using hx.1)

theorem recip_neg_exact (hx : Bounds a b x) (hb : b < 0) :
    Bounds (1/b) (1/a) (1/x) := by
  have h := recip_pos_exact hx.neg (neg_pos.mpr hb)
  simp only [div_neg] at h
  constructor <;> linarith [h.1, h.2]

theorem recip_pos (hx : Bounds a b x) (ha : 0 < a)
    (hl : l ≤ 1/b) (hu : 1/a ≤ u) : Bounds l u (1/x) :=
  widen (recip_pos_exact hx ha) hl hu

theorem recip_neg (hx : Bounds a b x) (hb : b < 0)
    (hl : l ≤ 1/b) (hu : 1/a ≤ u) : Bounds l u (1/x) :=
  widen (recip_neg_exact hx hb) hl hu

theorem abs_le (hx : Bounds a b x) (ha : -u ≤ a) (hb : b ≤ u) : |x| ≤ u :=
  _root_.abs_le.mpr ⟨ha.trans hx.1, hx.2.trans hb⟩

end Bounds
end Rho5.ExternalAttainment
