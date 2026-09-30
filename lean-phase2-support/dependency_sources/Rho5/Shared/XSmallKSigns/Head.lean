import Rho5.Shared.XSmallKSigns.FlipWIP

/-!
# D143 stage B (head) — the second original row/column flip, `e, β > 0`

`signedEntries M (mid2nd σ) (mid2nd σ)` flips the **second** original row and column (index 1).
It flips `e = -M 0 1` and `β = M 1 0` (both get `σ`), while the whole `S3` layer is untouched:
after the first Schur step the flip acts on the `S4` index 0, and at the next step the transported
factors are all `1`, so `S3` (hence `A, B, c, d`, `k`, `p`) and `T2` (hence `r, s, t, w`, height)
are literally unchanged.  The head band `|p - e β| ≤ 1` (D119) with `p > 1` then gives
`e β > 0`, and `σ = ±1` decides the common sign.
-/

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.TraceSigns (signedEntries signedEntries5 signedEntries_apply IsSign)
open Rho5.Shared.V43MatrixRoundTrip

/-- Flip the second original row/column (0-based index 1). -/
def mid2nd (σ : ℝ) : Fin 5 → ℝ := fun i => if (i : ℕ) = 1 then σ else 1
/-- Its image on the first Schur layer. -/
def mid2nd4 (σ : ℝ) : Fin 4 → ℝ := fun i => if (i : ℕ) = 0 then σ else 1

theorem isSign_mid2nd {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (mid2nd σ) := by
  intro i; fin_cases i <;> simp [mid2nd] <;> exact hσ
theorem isSign_mid2nd4 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (mid2nd4 σ) := by
  intro i; fin_cases i <;> simp [mid2nd4] <;> exact hσ
theorem mid2nd_zero (σ : ℝ) : mid2nd σ 0 = 1 := by simp [mid2nd]
theorem mid2nd_one (σ : ℝ) : mid2nd σ 1 = σ := by simp [mid2nd]
theorem mid2nd4_zero (σ : ℝ) : mid2nd4 σ 0 = σ := by simp [mid2nd4]

/-- The head flip as a real matrix operation. -/
def flipSecond (σ : ℝ) (M : Matrix5) : Matrix5 := signedEntries M (mid2nd σ) (mid2nd σ)

theorem eX_flipSecond {M : Matrix5} (σ : ℝ) : eX (flipSecond σ M) = σ * eX M := by
  simp only [eX, flipSecond, signedEntries_apply, mid2nd_zero, mid2nd_one, one_mul] <;> ring

theorem betaX_flipSecond {M : Matrix5} (σ : ℝ) : betaX (flipSecond σ M) = σ * betaX M := by
  simp only [betaX, flipSecond, signedEntries_apply, mid2nd_zero, mid2nd_one, mul_one] <;> ring

theorem S4_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0) :
    S4 (flipSecond σ M) = signedEntries (S4 M) (mid2nd4 σ) (mid2nd4 σ) := by
  have h := Rho5.TraceSigns.pivotSchur_signedEntries M (isSign_mid2nd hσ) (isSign_mid2nd hσ) 0 0 h00
  have hfac : (fun i : Fin 4 => mid2nd σ (Rho5.PivotReindex.remainingIndex 0 i)) = mid2nd4 σ := by
    funext i; fin_cases i <;> simp [mid2nd, mid2nd4, Rho5.PivotReindex.remainingIndex_apply]
  simpa [S4, flipSecond, hfac] using h

theorem S3_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : S3 (flipSecond σ M) = S3 M := by
  have h4 := S4_flipSecond (M := M) hσ h00
  have h := Rho5.TraceSigns.pivotSchur_signedEntries (S4 M) (isSign_mid2nd4 hσ) (isSign_mid2nd4 hσ)
    0 0 hp
  have hfac : (fun i : Fin 3 => mid2nd4 σ (Rho5.PivotReindex.remainingIndex 0 i)) = fun _ => (1 : ℝ) := by
    funext i; fin_cases i <;> simp [mid2nd4, Rho5.PivotReindex.remainingIndex_apply]
  have hmain : Rho5.PivotReindex.pivotSchur
      (signedEntries (S4 M) (mid2nd4 σ) (mid2nd4 σ)) 0 0 = S3 M := by
    rw [h, hfac]
    exact Rho5.LeadingSigns.signedEntries_one_one (S3 M)
  rw [show S3 (flipSecond σ M) = Rho5.PivotReindex.pivotSchur (S4 (flipSecond σ M)) 0 0 from rfl,
    h4]
  exact hmain

theorem T2_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) : T2 (flipSecond σ M) = T2 M := by
  have h3 := S3_flipSecond (M := M) hσ h00 hp
  rw [show T2 (flipSecond σ M) = Rho5.PivotReindex.pivotSchur (S3 (flipSecond σ M)) 0 0 from rfl, h3]
  rw [show Rho5.PivotReindex.pivotSchur (S3 M) 0 0 = T2 M from rfl]

theorem aX_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : aX (flipSecond σ M) = aX M := by
  simp only [aX, S3_flipSecond (M := M) hσ h00 hp]
theorem bX_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : bX (flipSecond σ M) = bX M := by
  simp only [bX, S3_flipSecond (M := M) hσ h00 hp]
theorem cX_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : cX (flipSecond σ M) = cX M := by
  simp only [cX, S3_flipSecond (M := M) hσ h00 hp]
theorem dX_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : dX (flipSecond σ M) = dX M := by
  simp only [dX, S3_flipSecond (M := M) hσ h00 hp]

theorem satFrame_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    SatFrame (flipSecond σ M) where
  h00 := by simp only [flipSecond, signedEntries_apply, mid2nd_zero, one_mul, mul_one]; exact h.h00
  hmax := by
    rw [show flipSecond σ M = signedEntries5 M (mid2nd σ) (mid2nd σ) from rfl,
      Rho5.TraceSigns.matrixEntryMax_signedEntries5 M (isSign_mid2nd hσ) (isSign_mid2nd hσ)]
    exact h.hmax
  cp1 := (Rho5.TraceSigns.isCompletePivot_signedEntries_iff M (isSign_mid2nd hσ)
    (isSign_mid2nd hσ) 0 0).mpr h.cp1
  cp2 := by
    rw [show S4 (flipSecond σ M) = signedEntries (S4 M) (mid2nd4 σ) (mid2nd4 σ) from
      S4_flipSecond hσ (h00_ne h)]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S4 M) (isSign_mid2nd4 hσ)
      (isSign_mid2nd4 hσ) 0 0).mpr h.cp2
  cp3 := by
    rw [show S3 (flipSecond σ M) = S3 M from S3_flipSecond hσ (h00_ne h) (ne_of_gt h.hp)]
    exact h.cp3
  cp4 := by
    rw [show T2 (flipSecond σ M) = T2 M from
      T2_flipSecond hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]
    exact h.cp4
  hp := by
    rw [show p (flipSecond σ M) = p M from by
      simp only [p, S4_flipSecond (M := M) hσ (h00_ne h), signedEntries_apply, mid2nd4_zero]
      have hs2 : σ * σ = 1 := sigma_sq hσ
      calc σ * S4 M 0 0 * σ = (σ * σ) * S4 M 0 0 := by ring
        _ = S4 M 0 0 := by rw [hs2, one_mul]]
    exact h.hp
  hk := by
    rw [show k (flipSecond σ M) = k M from by
      simp only [k, S3_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp)]]
    exact h.hk
  hr := by
    rw [show r (flipSecond σ M) = r M from by
      simp only [r, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.hr
  hs := by
    rw [show s (flipSecond σ M) = s M from by
        simp only [s, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)],
      show r (flipSecond σ M) = r M from by
        simp only [r, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.hs
  ht := by
    rw [show t (flipSecond σ M) = t M from by
        simp only [t, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)],
      show r (flipSecond σ M) = r M from by
        simp only [r, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.ht

/-- The head band, read on the actual X frame: `p - 1 ≤ e * β`. -/
theorem eX_mul_betaX_ge {M : Matrix5} (h : SatFrame M) : pX M - 1 ≤ eX M * betaX M := by
  have hb := Rho5.Shared.V43MatrixRoundTrip.head_abs_le_one M h
  have h1 := (abs_le.mp hb).2
  linarith

/-- **Stage B head flip.**  Some `σ ∈ {1,-1}` makes `e, β > 0` on the flipped real frame, which
keeps `SatFrame`, the height, `p`, `k` and the stage-A signs `A, B < 0 < c, d`. -/
theorem flipSecond_one (M : Matrix5) : flipSecond 1 M = M := by
  ext i j; simp [flipSecond, signedEntries, mid2nd]

/-- **Stage B head flip.**  Given the stage-A signs, some `σ ∈ {1,-1}` makes `e, β > 0` while the
flipped frame keeps `SatFrame`, the height, `p`, `k` and the `A, B < 0 < c, d` signs. -/
theorem head_flip_normalization {M : Matrix5} (h : SatFrame M) (hp1 : 1 < p M)
    (hA : aX M < 0) (hB : bX M < 0) (hC : 0 < cX M) (hD : 0 < dX M) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SatFrame (flipSecond σ M) ∧
      aX (flipSecond σ M) < 0 ∧ bX (flipSecond σ M) < 0 ∧
        0 < cX (flipSecond σ M) ∧ 0 < dX (flipSecond σ M) ∧
          0 < eX (flipSecond σ M) ∧ 0 < betaX (flipSecond σ M) := by
  have h00 := h00_ne h
  have hpos : 0 < eX M * betaX M := by
    have hge := eX_mul_betaX_ge h
    have hpX : pX M = p M := rfl
    rw [hpX] at hge
    linarith
  rcases mul_pos_iff.mp hpos with ⟨he, hb⟩ | ⟨he, hb⟩
  · refine ⟨1, Or.inl rfl, satFrame_flipSecond (Or.inl rfl) h, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [flipSecond_one]
    · rwa [flipSecond_one]
    · rwa [flipSecond_one]
    · rwa [flipSecond_one]
    · rw [flipSecond_one]; exact he
    · rw [flipSecond_one]; exact hb
  · have hσn : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
    have hs : SatFrame (flipSecond (-1) M) := satFrame_flipSecond hσn h
    have h1 : aX (flipSecond (-1) M) < 0 := by
      rw [aX_flipSecond (σ := -1) hσn h00 (ne_of_gt h.hp)]; exact hA
    have h2 : bX (flipSecond (-1) M) < 0 := by
      rw [bX_flipSecond (σ := -1) hσn h00 (ne_of_gt h.hp)]; exact hB
    have h3 : 0 < cX (flipSecond (-1) M) := by
      rw [cX_flipSecond (σ := -1) hσn h00 (ne_of_gt h.hp)]; exact hC
    have h4 : 0 < dX (flipSecond (-1) M) := by
      rw [dX_flipSecond (σ := -1) hσn h00 (ne_of_gt h.hp)]; exact hD
    have h5 : 0 < eX (flipSecond (-1) M) := by
      rw [eX_flipSecond]; linarith
    have h6 : 0 < betaX (flipSecond (-1) M) := by
      rw [betaX_flipSecond]; linarith
    exact ⟨-1, hσn, hs, h1, h2, h3, h4, h5, h6⟩

end Rho5.Shared.XSmallKSigns
