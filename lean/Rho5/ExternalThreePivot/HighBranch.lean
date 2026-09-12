import Rho5.ExternalThreePivot.ProductEnvelope

namespace Rho5.ExternalThreePivot

/-- A closed rectangle product bound, including zero and degenerate endpoints. -/
theorem interval_product_upper (a b c d x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx0 : -a ≤ x) (hx1 : x ≤ b) (hy0 : -c ≤ y) (hy1 : y ≤ d) :
    x * y ≤ max (a * c) (b * d) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact (mul_le_mul hx1 hy1 hy hb).trans (le_max_right _ _)
    · have hy' : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
      exact (mul_nonpos_of_nonneg_of_nonpos hx hy').trans
        ((mul_nonneg ha hc).trans (le_max_left _ _))
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    by_cases hy : 0 ≤ y
    · exact (mul_nonpos_of_nonpos_of_nonneg hx' hy).trans
        ((mul_nonneg ha hc).trans (le_max_left _ _))
    · have hy' : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
      have H : (-x) * (-y) ≤ a * c :=
        mul_le_mul (by linarith only [hx0]) (by linarith only [hy0])
          (by linarith only [hy']) ha
      have H' : x * y ≤ a * c := by nlinarith only [H]
      exact H'.trans (le_max_left _ _)

theorem interval_product_bounds (a b c d x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx0 : -a ≤ x) (hx1 : x ≤ b) (hy0 : -c ≤ y) (hy1 : y ≤ d) :
    x * y ≤ max (a * c) (b * d) ∧
      -(x * y) ≤ max (a * d) (b * c) := by
  refine ⟨interval_product_upper a b c d x y ha hb hc hd hx0 hx1 hy0 hy1, ?_⟩
  have H := interval_product_upper b a c d (-x) y hb ha hc hd
    (by linarith only [hx1]) (by linarith only [hx0]) hy0 hy1
  calc
    -(x * y) = (-x) * y := by ring
    _ ≤ max (b * c) (a * d) := H
    _ = max (a * d) (b * c) := max_comm _ _

theorem high_branch_abs_numerator
    (t s z r w gamma eta zeta : ℝ)
    (hdom : SharedProductDomain t s z r w)
    (htail : TailIntervals t s z r gamma eta zeta) :
    |t * zeta + gamma * eta| ≤ t^2 * (3 - t) := by
  have ht0 : 0 ≤ t := by linarith only [hdom.one_lt]
  have hc0 : 0 ≤ t - 1 := by linarith only [hdom.one_lt]
  have hAs : 0 ≤ 1 + min (t - 1) s := by
    have H : 0 ≤ min (t - 1) s := le_min hc0 hdom.s_nonneg
    linarith only [H]
  have hAz : 0 ≤ 1 + min (t - 1) z := by
    have H : 0 ≤ min (t - 1) z := le_min hc0 hdom.z_nonneg
    linarith only [H]
  have hBs : 0 ≤ 1 - s := sub_nonneg.mpr hdom.s_le_one
  have hBz : 0 ≤ 1 - z := sub_nonneg.mpr hdom.z_le_one
  obtain ⟨hplus, hminus⟩ := interval_product_bounds
    (1 + min (t - 1) s) (1 - s) (1 + min (t - 1) z) (1 - z)
    gamma eta hAs hBs hAz hBz
    htail.gamma_lower htail.gamma_upper htail.eta_lower htail.eta_upper
  have hI := auxiliary_upper t s z r w hdom
  have hII := auxiliary_lower_left t s z r w hdom
  have hIII := auxiliary_lower_right t s z r w hdom
  have hOther : t * (1 - r) + (1 - s) * (1 - z) ≤ t^2 * (3 - t) := by
    have hp : (1 - s) * (1 - z) ≤ 1 :=
      (unit_interval_mul (1 - s) (1 - z) hBs
        (by linarith only [hdom.s_nonneg]) hBz
        (by linarith only [hdom.z_nonneg])).2
    have hr : t * (1 - r) ≤ t := by
      have H := mul_nonneg ht0 hdom.r_nonneg
      nlinarith only [H]
    calc
      t * (1 - r) + (1 - s) * (1 - z) ≤ t + 1 := add_le_add hr hp
      _ ≤ t^2 * (3 - t) := high_budget_ge_t_add_one t hdom.one_lt hdom.le_two
  have hE : t * zeta + gamma * eta ≤ t^2 * (3 - t) := by
    calc
      t * zeta + gamma * eta ≤ t * (1 - r) +
          max ((1 + min (t - 1) s) * (1 + min (t - 1) z))
            ((1 - s) * (1 - z)) :=
        add_le_add (mul_le_mul_of_nonneg_left htail.zeta_upper ht0) hplus
      _ ≤ t^2 * (3 - t) := by
        rcases le_total ((1 + min (t - 1) s) * (1 + min (t - 1) z))
            ((1 - s) * (1 - z)) with h | h
        · rw [max_eq_right h]
          exact hOther
        · rw [max_eq_left h]
          exact hI
  have hnz : -zeta ≤ 1 + min (t - 1) r := by
    linarith only [htail.zeta_lower]
  have hNegE : -(t * zeta + gamma * eta) ≤ t^2 * (3 - t) := by
    calc
      -(t * zeta + gamma * eta) = t * (-zeta) + -(gamma * eta) := by ring
      _ ≤ t * (1 + min (t - 1) r) +
          max ((1 + min (t - 1) s) * (1 - z))
            ((1 - s) * (1 + min (t - 1) z)) :=
        add_le_add (mul_le_mul_of_nonneg_left hnz ht0) hminus
      _ ≤ t^2 * (3 - t) := by
        rcases le_total ((1 + min (t - 1) s) * (1 - z))
            ((1 - s) * (1 + min (t - 1) z)) with h | h
        · rw [max_eq_right h]
          exact hIII
        · rw [max_eq_left h]
          exact hII
  exact abs_le.mpr ⟨by linarith only [hNegE], hE⟩

theorem high_branch_quotient
    (t s z r w gamma eta zeta : ℝ)
    (hdom : SharedProductDomain t s z r w)
    (htail : TailIntervals t s z r gamma eta zeta) :
    |t * zeta + gamma * eta| / t ≤ t * (3 - t) := by
  have ht : 0 < t := by linarith only [hdom.one_lt]
  rw [div_le_iff₀ ht]
  have H := high_branch_abs_numerator t s z r w gamma eta zeta hdom htail
  convert H using 1 <;> ring

/-- The actual last Schur expression; division is used only after t > 0. -/
theorem negative_pivot_last_update (t b d e : ℝ) (ht : 0 < t) :
    |e - d * b / (-t)| = |t * e + b * d| / t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hfield : e - d * b / (-t) = (t * e + b * d) / t := by
    field_simp [ht0] <;> ring
  rw [hfield, abs_div, abs_of_pos ht]

end Rho5.ExternalThreePivot
