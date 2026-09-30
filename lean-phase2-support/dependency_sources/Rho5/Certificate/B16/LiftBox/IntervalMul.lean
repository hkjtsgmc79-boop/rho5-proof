import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# Four-corner bounds for a product of two real interval members

No endpoint sign, interval width, or nonzero assumption is needed.
The intervals may cross zero or degenerate, and `y` and `z` may coincide.
-/

namespace Rho5.Certificate.B16.LiftBox

theorem mul_lo_of_corners {bl bu cl cu lo y z : ℝ}
    (hy : bl ≤ y ∧ y ≤ bu) (hz : cl ≤ z ∧ z ≤ cu)
    (h_ll : lo ≤ bl * cl) (h_lu : lo ≤ bl * cu)
    (h_ul : lo ≤ bu * cl) (h_uu : lo ≤ bu * cu) : lo ≤ y * z := by
  have hconst : ∀ a : ℝ, lo ≤ a * cl → lo ≤ a * cu → lo ≤ a * z := by
    intro a hal hau
    cases le_total (0 : ℝ) a with
    | inl ha =>
        exact le_trans hal (mul_le_mul_of_nonneg_left hz.1 ha)
    | inr ha =>
        exact le_trans hau (mul_le_mul_of_nonpos_left hz.2 ha)
  cases le_total (0 : ℝ) z with
  | inl hz0 =>
      exact le_trans (hconst bl h_ll h_lu)
        (mul_le_mul_of_nonneg_right hy.1 hz0)
  | inr hz0 =>
      exact le_trans (hconst bu h_ul h_uu)
        (mul_le_mul_of_nonpos_right hy.2 hz0)

theorem mul_hi_of_corners {bl bu cl cu hi y z : ℝ}
    (hy : bl ≤ y ∧ y ≤ bu) (hz : cl ≤ z ∧ z ≤ cu)
    (h_ll : bl * cl ≤ hi) (h_lu : bl * cu ≤ hi)
    (h_ul : bu * cl ≤ hi) (h_uu : bu * cu ≤ hi) : y * z ≤ hi := by
  have hconst : ∀ a : ℝ, a * cl ≤ hi → a * cu ≤ hi → a * z ≤ hi := by
    intro a hal hau
    cases le_total (0 : ℝ) a with
    | inl ha =>
        exact le_trans (mul_le_mul_of_nonneg_left hz.2 ha) hau
    | inr ha =>
        exact le_trans (mul_le_mul_of_nonpos_left hz.1 ha) hal
  cases le_total (0 : ℝ) z with
  | inl hz0 =>
      exact le_trans (mul_le_mul_of_nonneg_right hy.2 hz0)
        (hconst bu h_ul h_uu)
  | inr hz0 =>
      exact le_trans (mul_le_mul_of_nonpos_right hy.1 hz0)
        (hconst bl h_ll h_lu)

end Rho5.Certificate.B16.LiftBox
