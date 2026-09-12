import Rho5.LocalAnalysis.SampleData
import Mathlib.Data.Rat.Cast.Order

namespace Rho5.LocalAnalysis.V43
noncomputable section
abbrev ResidualTerm := ℚ × Fin 22 × Fin 21

def evalTerms (z : X) (v : Y) : List ResidualTerm → ℝ
  | [] => 0
  | a :: as => (a.1 : ℝ) * (z a.2.1 - center a.2.1) * v a.2.2 + evalTerms z v as

def massTerms : List ResidualTerm → ℚ
  | [] => 0
  | a :: as => |a.1| + massTerms as

theorem evalTerms_bound (z : X) (hz : z ∈ cube center radius) (v : Y)
    (ts : List ResidualTerm) :
    |evalTerms z v ts| ≤ (massTerms ts : ℝ) * radius * ‖v‖ := by
  induction ts with
  | nil => simp [evalTerms, massTerms]
  | cons a as ih =>
    have ht : |(a.1 : ℝ) * (z a.2.1 - center a.2.1) * v a.2.2| ≤
        (|a.1| : ℚ) * radius * ‖v‖ := by
      rw [abs_mul, abs_mul]
      have hv : |v a.2.2| ≤ ‖v‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm v a.2.2
      have hr : 0 ≤ radius := by norm_num [radius]
      have h1 := mul_le_mul_of_nonneg_left (hz a.2.1) (abs_nonneg (a.1 : ℝ))
      have h2 := mul_le_mul h1 hv (abs_nonneg _) (mul_nonneg (abs_nonneg _) hr)
      simpa only [Rat.cast_abs] using h2
    calc
      |evalTerms z v (a :: as)| ≤
          |(a.1 : ℝ) * (z a.2.1 - center a.2.1) * v a.2.2| + |evalTerms z v as| :=
        abs_add_le _ _
      _ ≤ (|a.1| : ℚ) * radius * ‖v‖ + (massTerms as : ℝ) * radius * ‖v‖ :=
        add_le_add ht ih
      _ = (massTerms (a :: as) : ℝ) * radius * ‖v‖ := by
        simp only [massTerms, Rat.cast_add, add_mul]

theorem checked_mass_bound (ts : List ResidualTerm)
    (h : massTerms ts * (3 / 1000 : ℚ) ≤
      2345456430874861887039843429154548149516713163290708869117520274418451088946911938485271 /
      13009317994696220855310763663665374324696846780979700802579677478003049405906060000000000)
    (z : X) (hz : z ∈ cube center radius) (v : Y) :
    |evalTerms z v ts| ≤ qBound * ‖v‖ := by
  have hm : (massTerms ts : ℝ) * radius ≤ qBound := by
    dsimp [radius, qBound]
    have hc := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hc
    exact hc
  exact (evalTerms_bound z hz v ts).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg v))

end
end Rho5.LocalAnalysis.V43
