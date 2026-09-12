import Rho5.ExternalThreePivot.Definitions

namespace Rho5.ExternalThreePivot

/-- The first budget paid by the same-source identity. -/
theorem SharedProductDomain.product_le_r {t s z r w : ℝ}
    (h : SharedProductDomain t s z r w) : s * z ≤ r := by
  calc
    s * z = w * r := h.product_eq
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right h.w_le_one h.r_nonneg
    _ = r := one_mul _

theorem SharedProductDomain.c_mul_r_le_z {t s z r w : ℝ}
    (h : SharedProductDomain t s z r w) : (t - 1) * r ≤ z := by
  calc
    (t - 1) * r ≤ w * r :=
      mul_le_mul_of_nonneg_right h.head_lower h.r_nonneg
    _ = s * z := h.product_eq.symm
    _ ≤ 1 * z := mul_le_mul_of_nonneg_right h.s_le_one h.z_nonneg
    _ = z := one_mul _

/-- No division by s: includes s = 0, but requires the genuine high branch. -/
theorem SharedProductDomain.r_le_z_of_s_le_c {t s z r w : ℝ}
    (h : SharedProductDomain t s z r w) (hs : s ≤ t - 1) : r ≤ z := by
  have hc : 0 < t - 1 := sub_pos.mpr h.one_lt
  have hmul : (t - 1) * r ≤ (t - 1) * z := by
    calc
      (t - 1) * r ≤ w * r :=
        mul_le_mul_of_nonneg_right h.head_lower h.r_nonneg
      _ = s * z := h.product_eq.symm
      _ ≤ (t - 1) * z := mul_le_mul_of_nonneg_right hs h.z_nonneg
  exact le_of_mul_le_mul_left hmul hc

/-- Four polynomial certificates for budget I. -/
theorem upper_budget_core (c s z r : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hprod : s * z ≤ r) :
    (c + 1) * (1 - r) + (1 + min c s) * (1 + min c z) ≤
      (c + 1)^2 * (2 - c) := by
  have ht0 : 0 ≤ c + 1 := by linarith only [hc0]
  have hbase : 0 ≤ (c + 1) * (r - s * z) :=
    mul_nonneg ht0 (sub_nonneg.mpr hprod)
  by_cases hs : s ≤ c
  · rw [min_eq_right hs]
    by_cases hz : z ≤ c
    · rw [min_eq_right hz]
      have hcz1 : c * z ≤ 1 :=
        (unit_interval_mul c z hc0 hc1 hz0 hz1).2
      have hcc1 : c * c ≤ 1 :=
        (unit_interval_mul c c hc0 hc1 hc0 hc1).2
      have h1 : 0 ≤ (c - s) * (1 - c * z) :=
        mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hcz1)
      have h2 : 0 ≤ (c - z) * (1 - c * c) :=
        mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hcc1)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * (r - s * z) +
              (c - s) * (1 - c * z) + (c - z) * (1 - c * c) :=
          add_nonneg (add_nonneg hbase h1) h2
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 - r) + (1 + s) * (1 + z)) := by ring
    · have hcz : c ≤ z := le_of_lt (lt_of_not_ge hz)
      rw [min_eq_left hcz]
      have h1 : 0 ≤ (c - s) * (1 - z) :=
        mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hz1)
      have h2 : 0 ≤ c * (z - c) := mul_nonneg hc0 (sub_nonneg.mpr hcz)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * (r - s * z) +
              (c + 1) * ((c - s) * (1 - z) + c * (z - c)) :=
          add_nonneg hbase (mul_nonneg ht0 (add_nonneg h1 h2))
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 - r) + (1 + s) * (1 + c)) := by ring
  · have hcs : c ≤ s := le_of_lt (lt_of_not_ge hs)
    rw [min_eq_left hcs]
    by_cases hz : z ≤ c
    · rw [min_eq_right hz]
      have h1 : 0 ≤ (c - z) * (1 - s) :=
        mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hs1)
      have h2 : 0 ≤ c * (s - c) := mul_nonneg hc0 (sub_nonneg.mpr hcs)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * (r - s * z) +
              (c + 1) * ((c - z) * (1 - s) + c * (s - c)) :=
          add_nonneg hbase (mul_nonneg ht0 (add_nonneg h1 h2))
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 - r) + (1 + c) * (1 + z)) := by ring
    · have hcz : c ≤ z := le_of_lt (lt_of_not_ge hz)
      rw [min_eq_left hcz]
      have hp : c * c ≤ s * z := mul_le_mul hcs hcz hc0 hs0
      have h1 : 0 ≤ (c + 1) * (s * z - c * c) :=
        mul_nonneg ht0 (sub_nonneg.mpr hp)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * (r - s * z) + (c + 1) * (s * z - c * c) :=
          add_nonneg hbase h1
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 - r) + (1 + c) * (1 + c)) := by ring

/-- Four certificates for budget II. The additional inequalities here are
proved from SharedProductDomain by the public wrapper below. -/
theorem lower_budget_core (c s z r : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hs0 : 0 ≤ s) (hz1 : z ≤ 1) (hr1 : r ≤ 1)
    (hcrz : c * r ≤ z) (hsmall : s ≤ c → r ≤ z) :
    (c + 1) * (1 + min c r) + (1 + min c s) * (1 - z) ≤
      (c + 1)^2 * (2 - c) := by
  have ht0 : 0 ≤ c + 1 := by linarith only [hc0]
  have hcbar : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  have hbase : 0 ≤ (c + 1) * c * (1 - c) :=
    mul_nonneg (mul_nonneg ht0 hc0) hcbar
  by_cases hr : r ≤ c
  · rw [min_eq_right hr]
    by_cases hs : s ≤ c
    · rw [min_eq_right hs]
      have hrz : r ≤ z := hsmall hs
      have h1 : 0 ≤ (c - s) * (1 - r) :=
        mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hr1)
      have h2 : 0 ≤ (1 + s) * (z - r) :=
        mul_nonneg (by linarith only [hs0]) (sub_nonneg.mpr hrz)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * c * (1 - c) +
              (c - s) * (1 - r) + (1 + s) * (z - r) :=
          add_nonneg (add_nonneg hbase h1) h2
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 + r) + (1 + s) * (1 - z)) := by ring
    · have hcs : c ≤ s := le_of_lt (lt_of_not_ge hs)
      rw [min_eq_left hcs]
      have h1 : 0 ≤ (c - r) * (1 - c) :=
        mul_nonneg (sub_nonneg.mpr hr) hcbar
      have h2 : 0 ≤ z - c * r := sub_nonneg.mpr hcrz
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * ((c - r) * (1 - c) + (z - c * r)) :=
          mul_nonneg ht0 (add_nonneg h1 h2)
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 + r) + (1 + c) * (1 - z)) := by ring
  · have hrc : c ≤ r := le_of_lt (lt_of_not_ge hr)
    rw [min_eq_left hrc]
    by_cases hs : s ≤ c
    · rw [min_eq_right hs]
      have hcz : c ≤ z := hrc.trans (hsmall hs)
      have h1 : 0 ≤ (c - s) * (1 - z) :=
        mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hz1)
      have h2 : 0 ≤ (c + 1) * (z - c) :=
        mul_nonneg ht0 (sub_nonneg.mpr hcz)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * c * (1 - c) +
              (c - s) * (1 - z) + (c + 1) * (z - c) :=
          add_nonneg (add_nonneg hbase h1) h2
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 + c) + (1 + s) * (1 - z)) := by ring
    · have hcs : c ≤ s := le_of_lt (lt_of_not_ge hs)
      rw [min_eq_left hcs]
      have h1 : 0 ≤ z - c * r := sub_nonneg.mpr hcrz
      have h2 : 0 ≤ c * (r - c) := mul_nonneg hc0 (sub_nonneg.mpr hrc)
      apply sub_nonneg.mp
      calc
        0 ≤ (c + 1) * ((z - c * r) + c * (r - c)) :=
          mul_nonneg ht0 (add_nonneg h1 h2)
        _ = (c + 1)^2 * (2 - c) -
              ((c + 1) * (1 + c) + (1 + c) * (1 - z)) := by ring

theorem auxiliary_upper (t s z r w : ℝ)
    (h : SharedProductDomain t s z r w) :
    t * (1 - r) + (1 + min (t - 1) s) * (1 + min (t - 1) z) ≤
      t^2 * (3 - t) := by
  have hc0 : 0 ≤ t - 1 := le_of_lt (sub_pos.mpr h.one_lt)
  have hc1 : t - 1 ≤ 1 := by linarith only [h.le_two]
  have H := upper_budget_core (t - 1) s z r hc0 hc1
    h.s_nonneg h.s_le_one h.z_nonneg h.z_le_one h.product_le_r
  convert H using 1 <;> ring

theorem auxiliary_lower_left (t s z r w : ℝ)
    (h : SharedProductDomain t s z r w) :
    t * (1 + min (t - 1) r) + (1 + min (t - 1) s) * (1 - z) ≤
      t^2 * (3 - t) := by
  have hc0 : 0 ≤ t - 1 := le_of_lt (sub_pos.mpr h.one_lt)
  have hc1 : t - 1 ≤ 1 := by linarith only [h.le_two]
  have H := lower_budget_core (t - 1) s z r hc0 hc1
    h.s_nonneg h.z_le_one h.r_le_one h.c_mul_r_le_z
    (fun hs => h.r_le_z_of_s_le_c hs)
  convert H using 1 <;> ring

theorem auxiliary_lower_right (t s z r w : ℝ)
    (h : SharedProductDomain t s z r w) :
    t * (1 + min (t - 1) r) + (1 - s) * (1 + min (t - 1) z) ≤
      t^2 * (3 - t) := by
  have H := auxiliary_lower_left t z s r w h.swap
  simpa only [mul_comm (1 + min (t - 1) z) (1 - s)] using H

theorem high_budget_ge_t_add_one (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) :
    t + 1 ≤ t^2 * (3 - t) := by
  have hc0 : 0 ≤ t - 1 := by linarith only [ht]
  have hc1 : t - 1 ≤ 1 := by linarith only [ht2]
  have hsq : (t - 1) * (t - 1) ≤ 1 :=
    (unit_interval_mul (t - 1) (t - 1) hc0 hc1 hc0 hc1).2
  have hf : 0 ≤ 2 - (t - 1) * (t - 1) := by linarith only [hsq]
  have H := mul_nonneg hc0 hf
  nlinarith only [H]

end Rho5.ExternalThreePivot
