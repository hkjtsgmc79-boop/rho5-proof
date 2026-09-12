import Rho5.LocalAnalysis.MatrixBounds

namespace Rho5.LocalAnalysis
noncomputable section
open scoped BigOperators

/-- Sound centered lower enclosure for sparse degree-two polynomials. Indices
may repeat, so this covers squares as well as mixed monomials. -/
theorem centered_quadratic_lower {m n : ℕ} (b : ℝ)
    (a d : Fin m → ℝ) (q u v : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hd : ∀ i, |d i| ≤ ρ) (hu : ∀ i, |u i| ≤ ρ) (hv : ∀ i, |v i| ≤ ρ) :
    b - ρ * ∑ i, |a i| - ρ ^ 2 * ∑ i, |q i| ≤
      b + ∑ i, a i * d i + ∑ i, q i * u i * v i := by
  have hl : -(ρ * ∑ i, |a i|) ≤ ∑ i, a i * d i := by
    calc
      -(ρ * ∑ i, |a i|) = ∑ i, -(|a i| * ρ) := by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul, mul_comm ρ]
      _ ≤ ∑ i, a i * d i := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left (hd i) (abs_nonneg (a i))
        rw [← abs_mul] at h
        linarith [neg_abs_le (a i * d i)]
  have hq : -(ρ ^ 2 * ∑ i, |q i|) ≤ ∑ i, q i * u i * v i := by
    calc
      -(ρ ^ 2 * ∑ i, |q i|) = ∑ i, -(|q i| * ρ ^ 2) := by
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul, mul_comm (ρ ^ 2)]
      _ ≤ ∑ i, q i * u i * v i := by
        apply Finset.sum_le_sum
        intro i _
        have huv : |u i| * |v i| ≤ ρ ^ 2 := by
          nlinarith [mul_le_mul (hu i) (hv i) (abs_nonneg (v i)) hρ]
        have h := mul_le_mul_of_nonneg_left huv (abs_nonneg (q i))
        have h' : |q i * u i * v i| ≤ |q i| * ρ ^ 2 := by
          simpa only [abs_mul, mul_assoc] using h
        linarith [neg_abs_le (q i * u i * v i)]
  linarith

end
end Rho5.LocalAnalysis
