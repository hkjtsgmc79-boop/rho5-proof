import Rho5.ExternalTailSaturation.FullMatrixContraction

/-! Qualified factor choices, including zero arms and the positive-product junction. -/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

-- Ratios of the actual T2 entries; no hidden factor k and no balanced-tail premise.
def sigma (M : Matrix5) : ℝ := |s M / r M|
def tau (M : Matrix5) : ℝ := |t M / r M|
def nu (M : Matrix5) : ℝ := |w M / r M|

theorem ratio_mul_abs (x y : ℝ) (hy : y ≠ 0) : |x / y| * |y| = |x| := by
  rw [abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hy)]

theorem ratio_zero_iff (x y : ℝ) (hy : y ≠ 0) : |x / y| = 0 ↔ x = 0 := by
  constructor
  · intro hz
    have h := ratio_mul_abs x y hy
    rw [hz, zero_mul] at h
    exact abs_eq_zero.mp h.symm
  · intro hz
    simp [hz]

theorem ratios_nonneg (M : Matrix5) :
    0 ≤ sigma M ∧ 0 ≤ tau M ∧ 0 ≤ nu M :=
  ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _⟩

theorem ratios_le_one {M : Matrix5} (h : LeadingInput M) :
    sigma M ≤ 1 ∧ tau M ≤ 1 ∧ nu M ≤ 1 := by
  have hr : 0 < |r M| := abs_pos.mpr (r_ne_zero h)
  rcases tail_bounds h with ⟨hs, ht, hw⟩
  refine ⟨?_, ?_, ?_⟩
  · change |s M / r M| ≤ 1
    rw [abs_div]
    exact (div_le_one hr).mpr hs
  · change |t M / r M| ≤ 1
    rw [abs_div]
    exact (div_le_one hr).mpr ht
  · change |w M / r M| ≤ 1
    rw [abs_div]
    exact (div_le_one hr).mpr hw

theorem sigma_mul_abs_r {M : Matrix5} (h : LeadingInput M) :
    sigma M * |r M| = |s M| := ratio_mul_abs _ _ (r_ne_zero h)
theorem tau_mul_abs_r {M : Matrix5} (h : LeadingInput M) :
    tau M * |r M| = |t M| := ratio_mul_abs _ _ (r_ne_zero h)
theorem nu_mul_abs_r {M : Matrix5} (h : LeadingInput M) :
    nu M * |r M| = |w M| := ratio_mul_abs _ _ (r_ne_zero h)

/-- Precisely the excluded degeneration; it does not assert zero last => zero tail. -/
theorem not_zero_bottom_and_product {M : Matrix5} (h : LeadingInput M) :
    ¬ (nu M = 0 ∧ sigma M * tau M = 0) := by
  rintro ⟨hw, hst⟩
  have hw0 : w M = 0 := (ratio_zero_iff _ _ (r_ne_zero h)).mp hw
  rcases mul_eq_zero.mp hst with hs | ht
  · have hs0 : s M = 0 := (ratio_zero_iff _ _ (r_ne_zero h)).mp hs
    exact h.delta_ne (by simp [delta, hw0, hs0])
  · have ht0 : t M = 0 := (ratio_zero_iff _ _ (r_ne_zero h)).mp ht
    exact h.delta_ne (by simp [delta, hw0, ht0])

def lambdaD (M : Matrix5) : ℝ := max (tau M) (nu M)
def muD (M : Matrix5) : ℝ := nu M / lambdaD M

def lambdaX (M : Matrix5) : ℝ := tau M
def muX (M : Matrix5) : ℝ := sigma M

/-- Internal arithmetic certificate, derived below from the untransformed input. -/
structure FactorCertificate (M : Matrix5) (lam mu : ℝ) : Prop where
  left_pos : 0 < lam
  right_pos : 0 < mu
  left_le_one : lam ≤ 1
  right_le_one : mu ≤ 1
  tau_le : tau M ≤ lam
  sigma_le : sigma M ≤ mu
  nu_le : nu M ≤ lam * mu
  face : lam * mu = nu M ∨ (lam = tau M ∧ mu = sigma M)

theorem D_bottom_pos {M : Matrix5} (h : LeadingInput M)
    (hD : sigma M * tau M ≤ nu M) : 0 < nu M := by
  have h0 := ratios_nonneg M
  by_contra hn
  have hw : nu M = 0 := le_antisymm (le_of_not_gt hn) h0.2.2
  have hp : sigma M * tau M = 0 :=
    le_antisymm (by simpa only [hw] using hD) (mul_nonneg h0.1 h0.2.1)
  exact not_zero_bottom_and_product h ⟨hw, hp⟩

theorem D_factor_certificate {M : Matrix5} (h : LeadingInput M)
    (hD : sigma M * tau M ≤ nu M) : FactorCertificate M (lambdaD M) (muD M) := by
  rcases ratios_nonneg M with ⟨hS0, hT0, hW0⟩
  rcases ratios_le_one h with ⟨hS1, hT1, hW1⟩
  have hWpos := D_bottom_pos h hD
  have hlam : 0 < lambdaD M := lt_of_lt_of_le hWpos (le_max_right _ _)
  have hlam1 : lambdaD M ≤ 1 := max_le hT1 hW1
  have hmu : 0 < muD M := div_pos hWpos hlam
  have hmu1 : muD M ≤ 1 := (div_le_one hlam).mpr (le_max_right _ _)
  have hprod : lambdaD M * muD M = nu M := by
    unfold muD
    field_simp [ne_of_gt hlam] <;> ring
  have hSlam : sigma M * lambdaD M ≤ nu M := by
    rcases le_total (tau M) (nu M) with ht | hw
    · rw [lambdaD, max_eq_right ht]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hS1 hW0
    · rw [lambdaD, max_eq_left hw]
      exact hD
  have hSmu : sigma M ≤ muD M := by
    have hmul : lambdaD M * sigma M ≤ lambdaD M * muD M := by
      calc lambdaD M * sigma M = sigma M * lambdaD M := mul_comm _ _
        _ ≤ nu M := hSlam
        _ = lambdaD M * muD M := hprod.symm
    exact le_of_mul_le_mul_left hmul hlam
  exact ⟨hlam, hmu, hlam1, hmu1, le_max_left _ _, hSmu, hprod.symm.le, Or.inl hprod⟩

theorem X_product_pos {M : Matrix5} (h : LeadingInput M)
    (hX : nu M ≤ sigma M * tau M) : 0 < sigma M * tau M := by
  rcases ratios_nonneg M with ⟨hS0, hT0, hW0⟩
  by_contra hn
  have hp : sigma M * tau M = 0 :=
    le_antisymm (le_of_not_gt hn) (mul_nonneg hS0 hT0)
  have hw : nu M = 0 := le_antisymm (by simpa only [hp] using hX) hW0
  exact not_zero_bottom_and_product h ⟨hw, hp⟩

theorem X_factor_certificate {M : Matrix5} (h : LeadingInput M)
    (hX : nu M ≤ sigma M * tau M) : FactorCertificate M (lambdaX M) (muX M) := by
  rcases ratios_nonneg M with ⟨hS0, hT0, hW0⟩
  rcases ratios_le_one h with ⟨hS1, hT1, hW1⟩
  have hp := X_product_pos h hX
  have hSpos : 0 < sigma M := by
    by_contra hn
    have hz : sigma M = 0 := le_antisymm (le_of_not_gt hn) hS0
    simp [hz] at hp
  have hTpos : 0 < tau M := by
    by_contra hn
    have hz : tau M = 0 := le_antisymm (le_of_not_gt hn) hT0
    simp [hz] at hp
  exact ⟨hTpos, hSpos, hT1, hS1, le_rfl, le_rfl,
    by simpa only [lambdaX, muX, mul_comm] using hX, Or.inr ⟨rfl, rfl⟩⟩

/-- Deterministic selector: the D branch includes equality. -/
def chosenLambda (M : Matrix5) : ℝ :=
  if sigma M * tau M ≤ nu M then lambdaD M else lambdaX M
def chosenMu (M : Matrix5) : ℝ :=
  if sigma M * tau M ≤ nu M then muD M else muX M

theorem chosen_factor_certificate {M : Matrix5} (h : LeadingInput M) :
    FactorCertificate M (chosenLambda M) (chosenMu M) := by
  by_cases hD : sigma M * tau M ≤ nu M
  · simpa only [chosenLambda, chosenMu, if_pos hD] using D_factor_certificate h hD
  · simpa only [chosenLambda, chosenMu, if_neg hD] using
      X_factor_certificate h (le_of_lt (lt_of_not_ge hD))

/-- No zero-product junction occurs here; the two full factor choices agree. -/
theorem positive_junction_factors {M : Matrix5} (h : LeadingInput M)
    (heq : nu M = sigma M * tau M) :
    lambdaD M = lambdaX M ∧ muD M = muX M := by
  have hc := X_factor_certificate h heq.le
  have hS1 := (ratios_le_one h).1
  have hT0 := (ratios_nonneg M).2.1
  have hle : nu M ≤ tau M := by
    rw [heq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hS1 hT0
  have hlam : lambdaD M = tau M := max_eq_left hle
  refine ⟨hlam, ?_⟩
  change nu M / lambdaD M = sigma M
  rw [hlam, heq]
  have hTne : tau M ≠ 0 := ne_of_gt hc.left_pos
  field_simp [hTne] <;> ring

end Rho5.ExternalTailSaturation
