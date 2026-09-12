import Rho5.ExternalThreePivot.HighBranch
import Rho5.ExternalThreePivot.TailBounds

namespace Rho5.ExternalThreePivot

theorem phi_eq_low (t : ℝ) (ht : t ≤ 1) : phi t = 2 * t := by
  simp [phi, ht]

theorem phi_eq_high (t : ℝ) (ht : 1 ≤ t) : phi t = t * (3 - t) := by
  by_cases h : t ≤ 1
  · have heq : t = 1 := le_antisymm h ht
    subst t
    norm_num [phi]
  · simp [phi, h]

@[simp] theorem phi_zero : phi 0 = 0 := by norm_num [phi]
@[simp] theorem phi_one : phi 1 = 2 := by norm_num [phi]
@[simp] theorem phi_two : phi 2 = 2 := by norm_num [phi]

theorem phi_three_halves : phi ((3 : ℝ) / 2) = (9 : ℝ) / 4 := by
  norm_num [phi]

theorem phi_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) : 0 ≤ phi t := by
  by_cases ht : t ≤ 1
  · rw [phi_eq_low t ht]
    exact mul_nonneg (by norm_num) ht0
  · rw [phi_eq_high t (le_of_lt (lt_of_not_ge ht))]
    exact mul_nonneg ht0 (by linarith only [ht2])

theorem phi_le_nine_quarters (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    phi t ≤ (9 : ℝ) / 4 := by
  by_cases ht : t ≤ 1
  · rw [phi_eq_low t ht]
    linarith only [ht]
  · rw [phi_eq_high t (le_of_lt (lt_of_not_ge ht))]
    nlinarith only [sq_nonneg (t - (3 : ℝ) / 2)]

theorem phi_le_two_mul (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    phi t ≤ 2 * t := by
  by_cases ht : t ≤ 1
  · rw [phi_eq_low t ht]
  · rw [phi_eq_high t (le_of_lt (lt_of_not_ge ht))]
    have H : 0 ≤ t * (t - 1) :=
      mul_nonneg ht0 (sub_nonneg.mpr (le_of_lt (lt_of_not_ge ht)))
    nlinarith only [H]

/-- The first Schur entry lies in [-2,1] once the head is nonnegative. -/
theorem NormalizedHeadData.pivot_bounds {x u y v a b d e : ℝ}
    (h : NormalizedHeadData x u y v a b d e) : -2 ≤ a ∧ a ≤ 1 := by
  obtain ⟨hp0, hp1⟩ := unit_interval_mul x y h.x_nonneg h.x_le_one
    h.y_nonneg h.y_le_one
  obtain ⟨ha0, ha1⟩ := abs_le.mp h.entry11
  constructor <;> linarith only [hp0, hp1, ha0, ha1]

theorem NormalizedHeadData.second_le_two {x u y v a b d e : ℝ}
    (h : NormalizedHeadData x u y v a b d e) : |a| ≤ 2 := by
  obtain ⟨ha0, ha1⟩ := h.pivot_bounds
  exact abs_le.mpr ⟨ha0, by linarith only [ha1]⟩

theorem NormalizedHeadData.high_pivot_negative {x u y v a b d e : ℝ}
    (h : NormalizedHeadData x u y v a b d e) (ht : 1 < |a|) : a < 0 := by
  by_contra hneg
  have ha0 : 0 ≤ a := le_of_not_gt hneg
  rw [abs_of_nonneg ha0] at ht
  linarith only [ht, h.pivot_bounds.2]

theorem NormalizedHeadData.high_domain {x u y v a b d e : ℝ}
    (h : NormalizedHeadData x u y v a b d e) (ht : 1 < |a|) :
    SharedProductDomain |a| (x * v) (u * y) (u * v) (x * y) := by
  have hneg : a < 0 := h.high_pivot_negative ht
  have habs : |a| = -a := abs_of_neg hneg
  have hw : |a| - 1 ≤ x * y := by
    have H := (abs_le.mp h.entry11).1
    linarith only [H, habs]
  exact shared_domain_of_head_coordinates |a| x u y v ht h.second_le_two
    h.x_nonneg h.x_le_one h.u_nonneg h.u_le_one
    h.y_nonneg h.y_le_one h.v_nonneg h.v_le_one hw

theorem NormalizedHeadData.tail_intervals {x u y v a b d e : ℝ}
    (h : NormalizedHeadData x u y v a b d e) :
    TailIntervals |a| (x * v) (u * y) (u * v) b d e := by
  obtain ⟨hb0, hb1⟩ := intersect_tail_bounds |a| (x * v) b h.entry12 h.complete12
  obtain ⟨hd0, hd1⟩ := intersect_tail_bounds |a| (u * y) d h.entry21 h.complete21
  obtain ⟨he0, he1⟩ := intersect_tail_bounds |a| (u * v) e h.entry22 h.complete22
  exact ⟨hb0, hb1, hd0, hd1, he0, he1⟩

theorem normalized_head_zero_stop (x u y v a b d e : ℝ)
    (h : NormalizedHeadData x u y v a b d e) (ha : a = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 ∧ stoppedSchur a b d e = 0 := by
  obtain ⟨ha0, hb0, hd0, he0⟩ :=
    two_by_two_zero_tail a b d e ha h.complete12 h.complete21 h.complete22
  exact ⟨ha0, hb0, hd0, he0, by simp [stoppedSchur, ha]⟩

/-- Stage-one aggregate from actual raw entries and CP inequalities.
Neither branch of the desired envelope is an input assumption. -/
theorem scalar_three_pivot_envelope (x u y v a b d e : ℝ)
    (h : NormalizedHeadData x u y v a b d e) :
    0 ≤ |a| ∧ |a| ≤ 2 ∧ stoppedSchur a b d e ≤ phi |a| := by
  refine ⟨abs_nonneg _, h.second_le_two, ?_⟩
  by_cases ht : |a| ≤ 1
  · rw [phi_eq_low |a| ht]
    exact stoppedSchur_le_two_mul a b d e h.complete12 h.complete21 h.complete22
  · have hhigh : 1 < |a| := lt_of_not_ge ht
    have ha0 : a ≠ 0 := ne_of_lt (h.high_pivot_negative hhigh)
    have habs : a = -|a| := by
      rw [abs_of_neg (h.high_pivot_negative hhigh)]
      ring
    have hupdate : |e - d * b / a| = |(|a|) * e + b * d| / |a| := by
      calc
        |e - d * b / a| = |e - d * b / (-|a|)| := by rw [← habs]
        _ = |(|a|) * e + b * d| / |a| :=
          negative_pivot_last_update |a| b d e (abs_pos.mpr ha0)
    rw [stoppedSchur_of_ne_zero a b d e ha0, hupdate,
      phi_eq_high |a| (le_of_lt hhigh)]
    exact high_branch_quotient |a| (x * v) (u * y) (u * v) (x * y)
      b d e (h.high_domain hhigh) h.tail_intervals

theorem scalar_three_pivot_le_nine_quarters (x u y v a b d e : ℝ)
    (h : NormalizedHeadData x u y v a b d e) :
    stoppedSchur a b d e ≤ (9 : ℝ) / 4 := by
  obtain ⟨ht0, ht2, hg⟩ := scalar_three_pivot_envelope x u y v a b d e h
  exact hg.trans (phi_le_nine_quarters |a| ht0 ht2)

end Rho5.ExternalThreePivot
