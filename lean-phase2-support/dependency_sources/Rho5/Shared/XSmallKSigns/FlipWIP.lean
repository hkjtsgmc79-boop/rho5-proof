import Rho5.Shared.XSmallKSigns.Flip

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.TraceSigns (signedEntries signedEntries5 signedEntries_apply IsSign)
open Rho5.Shared.V43MatrixRoundTrip

theorem sigma_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ * σ = 1 := by
  rcases hσ with h | h <;> simp [h]

theorem aX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : aX (flipMid σ M) = σ * aX M := by
  have h3 := S3_flipMid (M := M) hσ h00 hp
  simp only [aX, h3, signedEntries_apply, mid3_zero, mid3_one]
  ring

theorem bX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : bX (flipMid σ M) = σ * bX M := by
  have h3 := S3_flipMid (M := M) hσ h00 hp
  simp only [bX, h3, signedEntries_apply, mid3_zero, mid3_two]
  ring

theorem kX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : kX (flipMid σ M) = kX M := by
  have h3 := S3_flipMid (M := M) hσ h00 hp
  have hs2 : σ * σ = 1 := sigma_sq hσ
  simp only [kX, h3, signedEntries_apply, mid3_zero]
  calc σ * S3 M 0 0 * σ = (σ * σ) * S3 M 0 0 := by ring
    _ = S3 M 0 0 := by rw [hs2, one_mul]

theorem cX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : cX (flipMid σ M) = σ * cX M := by
  have h3 := S3_flipMid (M := M) hσ h00 hp
  have hden : S3 (flipMid σ M) 0 0 = S3 M 0 0 := by
    simpa only [kX] using (kX_flipMid (M := M) hσ h00 hp)
  have hnum : S3 (flipMid σ M) 1 0 = σ * S3 M 1 0 := by
    simp only [h3, signedEntries_apply, mid3_one, mid3_zero, one_mul, mul_one] <;> ring
  change S3 (flipMid σ M) 1 0 / S3 (flipMid σ M) 0 0 = σ * (S3 M 1 0 / S3 M 0 0)
  rw [hnum, hden]
  exact mul_div_assoc σ (S3 M 1 0) (S3 M 0 0)

theorem dX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : dX (flipMid σ M) = σ * dX M := by
  have h3 := S3_flipMid (M := M) hσ h00 hp
  have hden : S3 (flipMid σ M) 0 0 = S3 M 0 0 := by
    simpa only [kX] using (kX_flipMid (M := M) hσ h00 hp)
  have hnum : S3 (flipMid σ M) 2 0 = σ * S3 M 2 0 := by
    simp only [h3, signedEntries_apply, mid3_two, mid3_zero, one_mul, mul_one] <;> ring
  change S3 (flipMid σ M) 2 0 / S3 (flipMid σ M) 0 0 = σ * (S3 M 2 0 / S3 M 0 0)
  rw [hnum, hden]
  exact mul_div_assoc σ (S3 M 2 0) (S3 M 0 0)

theorem wX_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) : wX (flipMid σ M) = wX M := by
  simp only [wX, T2_flipMid (M := M) hσ h00 hp hk]


/-! ## 3. `SatFrame` is preserved, so the flipped frame is a real same-source representative -/

theorem h00_ne {M : Matrix5} (h : SatFrame M) : M 0 0 ≠ 0 := by rw [h.h00]; norm_num

theorem satFrame_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    SatFrame (flipMid σ M) where
  h00 := by
    simp only [flipMid, signedEntries_apply, mid5_zero, one_mul, mul_one]
    exact h.h00
  hmax := by
    rw [show flipMid σ M = signedEntries5 M (mid5 σ) (mid5 σ) from rfl,
      Rho5.TraceSigns.matrixEntryMax_signedEntries5 M (isSign_mid5 hσ) (isSign_mid5 hσ)]
    exact h.hmax
  cp1 := (Rho5.TraceSigns.isCompletePivot_signedEntries_iff M (isSign_mid5 hσ) (isSign_mid5 hσ)
    0 0).mpr h.cp1
  cp2 := by
    rw [show S4 (flipMid σ M) = signedEntries (S4 M) (mid4 σ) (mid4 σ) from
      S4_flipMid hσ (h00_ne h)]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S4 M) (isSign_mid4 hσ)
      (isSign_mid4 hσ) 0 0).mpr h.cp2
  cp3 := by
    rw [show S3 (flipMid σ M) = signedEntries (S3 M) (mid3 σ) (mid3 σ) from
      S3_flipMid hσ (h00_ne h) (ne_of_gt h.hp)]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S3 M) (isSign_mid3 hσ)
      (isSign_mid3 hσ) 0 0).mpr h.cp3
  cp4 := by
    rw [show T2 (flipMid σ M) = T2 M from
      T2_flipMid hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]
    exact h.cp4
  hp := by
    have h4 := S4_flipMid (M := M) hσ (h00_ne h)
    rw [show p (flipMid σ M) = p M from by
      simp only [p, h4, signedEntries_apply, mid4_zero, one_mul, mul_one]]
    exact h.hp
  hk := by
    have h3 := S3_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp)
    rw [show k (flipMid σ M) = k M from by
      simp only [k, h3, signedEntries_apply, mid3_zero]
      have hs2 : σ * σ = 1 := sigma_sq hσ
      calc σ * S3 M 0 0 * σ = (σ * σ) * S3 M 0 0 := by ring
        _ = S3 M 0 0 := by rw [hs2, one_mul]]
    exact h.hk
  hr := by
    have h2 := T2_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)
    rw [show r (flipMid σ M) = r M from by simp only [r, h2]]
    exact h.hr
  hs := by
    have h2 := T2_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)
    rw [show s (flipMid σ M) = s M from by simp only [s, h2],
      show r (flipMid σ M) = r M from by simp only [r, h2]]
    exact h.hs
  ht := by
    have h2 := T2_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)
    rw [show t (flipMid σ M) = t M from by simp only [t, h2],
      show r (flipMid σ M) = r M from by simp only [r, h2]]
    exact h.ht

/-! ## 4. The stage-A normalization: some `σ ∈ {1,-1}` gives `A, B < 0 < c, d` -/

theorem sign_normalization_exists {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ Rho5.ExternalTailSaturation.height M) (hk2 : k M ≤ 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SatFrame (flipMid σ M) ∧
      aX (flipMid σ M) < 0 ∧ bX (flipMid σ M) < 0 ∧
        0 < cX (flipMid σ M) ∧ 0 < dX (flipMid σ M) := by
  have h00 := h00_ne h
  have hd := sign_dichotomy (aX_mul_cX_neg h hq hk2) (bX_mul_cX_neg h hq hk2)
    (aX_mul_dX_neg h hq hk2)
  rcases hd with ⟨ha, hb, hc, hdd⟩ | ⟨ha, hb, hc, hdd⟩
  · have hS : SatFrame (flipMid 1 M) := satFrame_flipMid (Or.inl rfl) h
    have h1 : aX (flipMid 1 M) < 0 := by rwa [flipMid_one]
    have h2 : bX (flipMid 1 M) < 0 := by rwa [flipMid_one]
    have h3 : 0 < cX (flipMid 1 M) := by rwa [flipMid_one]
    have h4 : 0 < dX (flipMid 1 M) := by rwa [flipMid_one]
    exact ⟨1, Or.inl rfl, hS, h1, h2, h3, h4⟩
  · have hσn : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
    have hS : SatFrame (flipMid (-1) M) := satFrame_flipMid hσn h
    have h1 : aX (flipMid (-1) M) < 0 := by
      have := aX_flipMid (M := M) (σ := -1) hσn h00 (ne_of_gt h.hp)
      rw [this]; linarith
    have h2 : bX (flipMid (-1) M) < 0 := by
      have := bX_flipMid (M := M) (σ := -1) hσn h00 (ne_of_gt h.hp)
      rw [this]; linarith
    have h3 : 0 < cX (flipMid (-1) M) := by
      have := cX_flipMid (M := M) (σ := -1) hσn h00 (ne_of_gt h.hp)
      rw [this]; linarith
    have h4 : 0 < dX (flipMid (-1) M) := by
      have := dX_flipMid (M := M) (σ := -1) hσn h00 (ne_of_gt h.hp)
      rw [this]; linarith
    exact ⟨-1, hσn, hS, h1, h2, h3, h4⟩

end Rho5.Shared.XSmallKSigns
