import Rho5.LocalAnalysis.InverseBound
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Normed.Group.Constructions

namespace Rho5.LocalAnalysis
noncomputable section
open scoped BigOperators

/-- Absolute row sums control matrix action in vector sup norm.
This deliberately does not use the entry-max matrix norm. -/
theorem row_sum_sup_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hrow : ∀ i, ∑ j, |A i j| ≤ q) (v : Fin n → ℝ) :
    ‖A.mulVec v‖ ≤ q * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg v))).mpr
  intro i
  change ‖∑ j, A i j * v j‖ ≤ q * ‖v‖
  calc
    ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
    _ = ∑ j, |A i j| * |v j| := by simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ ∑ j, |A i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
    _ = (∑ j, |A i j|) * ‖v‖ := (Finset.sum_mul ..).symm
    _ ≤ q * ‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

/-- Exact centered affine enclosure; the hypothesis is a coordinate cube. -/
theorem centered_affine_bound {n : ℕ} (a : ℝ) (b c z : Fin n → ℝ) {ρ : ℝ}
    (hz : ∀ k, |z k - c k| ≤ ρ) :
    |a + ∑ k, b k * (z k - c k)| ≤ |a| + ρ * ∑ k, |b k| := by
  calc
    |a + ∑ k, b k * (z k - c k)| ≤ |a| + |∑ k, b k * (z k - c k)| := abs_add_le _ _
    _ ≤ |a| + ∑ k, |b k * (z k - c k)| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ = |a| + ∑ k, |b k| * |z k - c k| := by simp only [abs_mul]
    _ ≤ |a| + ∑ k, |b k| * ρ := by
      gcongr with k
      exact hz k
    _ = |a| + ρ * ∑ k, |b k| := by rw [← Finset.sum_mul, mul_comm ρ]

/-- Semantic bridge for an affine residual matrix over a whole coordinate cube.
Generated exact coefficient/row inequalities can instantiate this theorem. -/
theorem affine_matrix_cube_bound {n d : ℕ}
    (E₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin n → Fin n → Fin d → ℝ) (c z : Fin d → ℝ) {ρ q : ℝ}
    (hq : 0 ≤ q) (hz : ∀ k, |z k - c k| ≤ ρ)
    (hrow : ∀ i, ∑ j, (|E₀ i j| + ρ * ∑ k, |A i j k|) ≤ q)
    (v : Fin n → ℝ) :
    ‖Matrix.mulVec (fun i j => E₀ i j + ∑ k, A i j k * (z k - c k)) v‖ ≤ q * ‖v‖ := by
  apply row_sum_sup_bound _ hq
  intro i
  exact (Finset.sum_le_sum (fun j _ => centered_affine_bound _ _ _ _ hz)).trans (hrow i)

end
end Rho5.LocalAnalysis
