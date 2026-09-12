import Rho5.ExternalTailSaturation.Saturation

/-! Same final height is unconditional here; same growth has four explicit premises. -/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.GrowthModel (growthRatio tracePeak)
open Rho5.CompletePivotPath (LegalTrace)

/-- An equality about the genuine leading trace under exactly the four dominance bounds. -/
theorem growth_eq_last {M : Matrix5} (h : LeadingInput M)
    (h1 : 1 ≤ height M) (hp : p M ≤ height M) (hk : k M ≤ height M)
    (hr : |r M| ≤ height M) :
    growthRatio M [1, p M, k M, |r M|, height M] = height M := by
  rw [Rho5.GrowthModel.growthRatio_eq, entryMax_eq_one M h.head h.cp0, div_one]
  change max 1 (max (p M) (max (k M) (max |r M| (max (height M) 0)))) = height M
  rw [show max (height M) 0 = height M from max_eq_left (abs_nonneg (delta M)),
    max_eq_right hr, max_eq_right hk, max_eq_right hp, max_eq_right h1]

theorem contract_growth_eq_last {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) (h1 : 1 ≤ height M) (hp : p M ≤ height M)
    (hk : k M ≤ height M) (hr : |r M| ≤ height M) :
    growthRatio (contract M lam mu) [1, p M, k M, |lam * mu * r M|, height M] = height M := by
  have hnew := contract_leadingInput h c
  have hh := contract_height h c
  have h1' : 1 ≤ height (contract M lam mu) := by rw [hh]; exact h1
  have hp' : p (contract M lam mu) ≤ height (contract M lam mu) := by rw [p_contract, hh]; exact hp
  have hk' : k (contract M lam mu) ≤ height (contract M lam mu) := by rw [k_contract, hh]; exact hk
  have hr' : |r (contract M lam mu)| ≤ height (contract M lam mu) := by
    rw [hh]
    exact (contract_fourth_le c).trans hr
  simpa only [p_contract, k_contract, r_contract, hh] using growth_eq_last hnew h1' hp' hk' hr'

/-- Both real traces and their equal growth, with the last-pivot dominance visible. -/
theorem same_growth_if_last_dominates {M : Matrix5} (h : LeadingInput M)
    (h1 : 1 ≤ height M) (hp : p M ≤ height M) (hk : k M ≤ height M)
    (hr : |r M| ≤ height M) :
    LegalTrace M [1, p M, k M, |r M|, height M] ∧
    LegalTrace (representative M)
      [1, p M, k M, |chosenLambda M * chosenMu M * r M|, height M] ∧
    growthRatio M [1, p M, k M, |r M|, height M] = height M ∧
    growthRatio (representative M)
      [1, p M, k M, |chosenLambda M * chosenMu M * r M|, height M] = height M := by
  exact ⟨leading_legalTrace h, contract_legalTrace h (chosen_factor_certificate h),
    growth_eq_last h h1 hp hk hr,
    contract_growth_eq_last h (chosen_factor_certificate h) h1 hp hk hr⟩

end Rho5.ExternalTailSaturation
