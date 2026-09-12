import Rho5.ExternalThreePivot.Definitions

namespace Rho5.ExternalThreePivot

theorem two_by_two_pivot_ne_zero (t a : ℝ)
    (ht : 0 < t) (ha : |a| = t) : a ≠ 0 := by
  intro hzero
  rw [hzero, abs_zero] at ha
  linarith only [ht, ha]

theorem two_by_two_tail_bound (t a b d e : ℝ)
    (ht : 0 < t) (ha : |a| = t)
    (hb : |b| ≤ t) (hd : |d| ≤ t) (he : |e| ≤ t) :
    |e - d * b / a| ≤ 2 * t := by
  have hcorrection : |d * b / a| ≤ t := by
    rw [abs_div, abs_mul, ha, div_le_iff₀ ht]
    exact mul_le_mul hd hb (abs_nonneg _) (le_of_lt ht)
  obtain ⟨he0, he1⟩ := abs_le.mp he
  obtain ⟨hc0, hc1⟩ := abs_le.mp hcorrection
  apply abs_le.mpr
  constructor <;> linarith only [he0, he1, hc0, hc1]

/-- A zero complete pivot forces the ENTIRE two-by-two tail to vanish.
This statement does not contain division. -/
theorem two_by_two_zero_tail (a b d e : ℝ)
    (ha : a = 0) (hb : |b| ≤ |a|) (hd : |d| ≤ |a|) (he : |e| ≤ |a|) :
    a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 := by
  have hb0 : |b| = 0 := le_antisymm (by simpa [ha] using hb) (abs_nonneg _)
  have hd0 : |d| = 0 := le_antisymm (by simpa [ha] using hd) (abs_nonneg _)
  have he0 : |e| = 0 := le_antisymm (by simpa [ha] using he) (abs_nonneg _)
  exact ⟨ha, abs_eq_zero.mp hb0, abs_eq_zero.mp hd0, abs_eq_zero.mp he0⟩

theorem stoppedSchur_of_zero (b d e : ℝ) : stoppedSchur 0 b d e = 0 := by
  simp [stoppedSchur]

theorem stoppedSchur_of_ne_zero (a b d e : ℝ) (ha : a ≠ 0) :
    stoppedSchur a b d e = |e - d * b / a| := by
  simp [stoppedSchur, ha]

theorem stoppedSchur_nonneg (a b d e : ℝ) : 0 ≤ stoppedSchur a b d e := by
  by_cases ha : a = 0
  · simp [stoppedSchur, ha]
  · simp only [stoppedSchur, if_neg ha]
    exact abs_nonneg _

theorem stoppedSchur_le_two_mul (a b d e : ℝ)
    (hb : |b| ≤ |a|) (hd : |d| ≤ |a|) (he : |e| ≤ |a|) :
    stoppedSchur a b d e ≤ 2 * |a| := by
  by_cases ha : a = 0
  · have hzero := two_by_two_zero_tail a b d e ha hb hd he
    simp [stoppedSchur, hzero.1]
  · rw [stoppedSchur_of_ne_zero a b d e ha]
    exact two_by_two_tail_bound |a| a b d e (abs_pos.mpr ha) rfl hb hd he

end Rho5.ExternalThreePivot
