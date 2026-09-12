import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert

/-!
C01: sharp three-pivot envelope. All files in this namespace are new.
Source-only delivery: these sources have NOT been compiled in the delivery
container. See BUILD_STATUS.json. The frozen Shared files are not modified.
-/
namespace Rho5.ExternalThreePivot

noncomputable def phi (t : ℝ) : ℝ :=
  if t ≤ 1 then 2 * t else t * (3 - t)

/-- Exactly the same-source domain, not an independent box relaxation. -/
structure SharedProductDomain (t s z r w : ℝ) : Prop where
  one_lt : 1 < t
  le_two : t ≤ 2
  s_nonneg : 0 ≤ s
  s_le_one : s ≤ 1
  z_nonneg : 0 ≤ z
  z_le_one : z ≤ 1
  r_nonneg : 0 ≤ r
  r_le_one : r ≤ 1
  w_nonneg : 0 ≤ w
  w_le_one : w ≤ 1
  head_lower : t - 1 ≤ w
  product_eq : s * z = w * r

structure TailIntervals (t s z r gamma eta zeta : ℝ) : Prop where
  gamma_lower : -(1 + min (t - 1) s) ≤ gamma
  gamma_upper : gamma ≤ 1 - s
  eta_lower : -(1 + min (t - 1) z) ≤ eta
  eta_upper : eta ≤ 1 - z
  zeta_lower : -(1 + min (t - 1) r) ≤ zeta
  zeta_upper : zeta ≤ 1 - r

/-- An actual normalized scalar head and its actual Schur entries.
The four original inner entries are xy+a, xv+b, uy+d, uv+e.
No desired upper bound is a field of this structure. -/
structure NormalizedHeadData (x u y v a b d e : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  x_le_one : x ≤ 1
  u_nonneg : 0 ≤ u
  u_le_one : u ≤ 1
  y_nonneg : 0 ≤ y
  y_le_one : y ≤ 1
  v_nonneg : 0 ≤ v
  v_le_one : v ≤ 1
  entry11 : |x * y + a| ≤ 1
  entry12 : |x * v + b| ≤ 1
  entry21 : |u * y + d| ≤ 1
  entry22 : |u * v + e| ≤ 1
  complete12 : |b| ≤ |a|
  complete21 : |d| ≤ |a|
  complete22 : |e| ≤ |a|

/-- Stop and pad by zero when the second pivot vanishes.
The accompanying zero-tail theorems justify this branch algorithmically. -/
noncomputable def stoppedSchur (a b d e : ℝ) : ℝ :=
  if a = 0 then 0 else |e - d * b / a|

theorem unit_interval_mul (a b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ a * b ∧ a * b ≤ 1 := by
  refine ⟨mul_nonneg ha0 hb0, ?_⟩
  calc
    a * b ≤ 1 * 1 := mul_le_mul ha1 hb1 hb0 (by norm_num)
    _ = 1 := by ring

theorem shared_domain_iff_spec (t s z r w : ℝ) :
    SharedProductDomain t s z r w ↔
      1 < t ∧ t ≤ 2 ∧
      0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ z ∧ z ≤ 1 ∧
      0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ w ∧ w ≤ 1 ∧
      t - 1 ≤ w ∧ s * z = w * r := by
  constructor
  · intro h
    exact ⟨h.one_lt, h.le_two, h.s_nonneg, h.s_le_one,
      h.z_nonneg, h.z_le_one, h.r_nonneg, h.r_le_one,
      h.w_nonneg, h.w_le_one, h.head_lower, h.product_eq⟩
  · rintro ⟨ht, ht2, hs0, hs1, hz0, hz1, hr0, hr1, hw0, hw1, hw, hp⟩
    exact ⟨ht, ht2, hs0, hs1, hz0, hz1, hr0, hr1, hw0, hw1, hw, hp⟩

theorem tail_intervals_iff_spec (t s z r gamma eta zeta : ℝ) :
    TailIntervals t s z r gamma eta zeta ↔
      -(1 + min (t - 1) s) ≤ gamma ∧ gamma ≤ 1 - s ∧
      -(1 + min (t - 1) z) ≤ eta ∧ eta ≤ 1 - z ∧
      -(1 + min (t - 1) r) ≤ zeta ∧ zeta ≤ 1 - r := by
  constructor
  · intro h
    exact ⟨h.gamma_lower, h.gamma_upper, h.eta_lower, h.eta_upper,
      h.zeta_lower, h.zeta_upper⟩
  · rintro ⟨hg0, hg1, he0, he1, hz0, hz1⟩
    exact ⟨hg0, hg1, he0, he1, hz0, hz1⟩

theorem SharedProductDomain.swap {t s z r w : ℝ}
    (h : SharedProductDomain t s z r w) : SharedProductDomain t z s r w := by
  refine ⟨h.one_lt, h.le_two, h.z_nonneg, h.z_le_one,
    h.s_nonneg, h.s_le_one, h.r_nonneg, h.r_le_one,
    h.w_nonneg, h.w_le_one, h.head_lower, ?_⟩
  calc z * s = s * z := mul_comm _ _
       _ = w * r := h.product_eq

theorem shared_domain_of_head_coordinates
    (t x u y v : ℝ)
    (ht : 1 < t) (ht2 : t ≤ 2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hw : t - 1 ≤ x * y) :
    SharedProductDomain t (x * v) (u * y) (u * v) (x * y) := by
  obtain ⟨hs0, hs1⟩ := unit_interval_mul x v hx0 hx1 hv0 hv1
  obtain ⟨hz0, hz1⟩ := unit_interval_mul u y hu0 hu1 hy0 hy1
  obtain ⟨hr0, hr1⟩ := unit_interval_mul u v hu0 hu1 hv0 hv1
  obtain ⟨hw0, hw1⟩ := unit_interval_mul x y hx0 hx1 hy0 hy1
  exact ⟨ht, ht2, hs0, hs1, hz0, hz1, hr0, hr1, hw0, hw1, hw, by ring⟩

/-- Original entry bounds intersect the CP bounds, with all endpoints closed. -/
theorem intersect_tail_bounds (t q zeta : ℝ)
    (hentry : |q + zeta| ≤ 1) (hcomplete : |zeta| ≤ t) :
    -(1 + min (t - 1) q) ≤ zeta ∧ zeta ≤ 1 - q := by
  obtain ⟨he0, he1⟩ := abs_le.mp hentry
  obtain ⟨hc0, hc1⟩ := abs_le.mp hcomplete
  constructor
  · by_cases hq : q ≤ t - 1
    · rw [min_eq_right hq]
      linarith only [he0]
    · have hq' : t - 1 ≤ q := le_of_lt (lt_of_not_ge hq)
      rw [min_eq_left hq']
      linarith only [hc0]
  · linarith only [he1]

end Rho5.ExternalThreePivot
