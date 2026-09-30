import Rho5.Shared.XSmallKSigns.Adapt

/-!
# D143 stage C — the three-step real representative `N`

`N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))`: the third original row/column flip (stage A)
followed by the second (`e, β > 0`) and then the last three (`u₀ ≥ 0`).

Each step is a genuine `signedEntries` row/column scaling of the **same** matrix `M`, so `N` is a
real `5 × 5` matrix of the same source, not a chart-level substitution.  This module records the
invariance of `height`, `p`, `k`, `r`, `w` through all three steps and composes the three
normalizations into one representative carrying every sign at once.
-/

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.ExternalTailSaturation (w delta height)
open Rho5.TraceSigns (signedEntries signedEntries_apply IsSign)
open Rho5.Shared.V43MatrixRoundTrip

/-! ## 1. Invariance of `p, k, r, w, height` through the middle (stage-A) flip -/

theorem p_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    p (flipMid σ M) = p M := by
  simp only [p, S4_flipMid (M := M) hσ (h00_ne h), signedEntries_apply, mid4_zero, one_mul, mul_one]

theorem k_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    k (flipMid σ M) = k M := by
  simpa only [kX, k] using kX_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp)

theorem r_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    r (flipMid σ M) = r M := by
  simp only [r, T2_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

theorem w_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    w (flipMid σ M) = w M := by
  simp only [w, T2_flipMid (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

theorem height_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    height (flipMid σ M) = height M := by
  have hN := satFrame_flipMid hσ h
  unfold height
  rw [delta_eq hN, delta_eq h, w_flipMid hσ h, r_flipMid hσ h]

/-! ## 2. Invariance through the head (second row/column) flip -/

theorem p_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    p (flipSecond σ M) = p M := by
  simp only [p, S4_flipSecond (M := M) hσ (h00_ne h), signedEntries_apply, mid2nd4_zero]
  have hs2 : σ * σ = 1 := sigma_sq hσ
  calc σ * S4 M 0 0 * σ = (σ * σ) * S4 M 0 0 := by ring
    _ = S4 M 0 0 := by rw [hs2, one_mul]

theorem k_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    k (flipSecond σ M) = k M := by
  simp only [k, S3_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp)]

theorem r_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    r (flipSecond σ M) = r M := by
  simp only [r, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

theorem w_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    w (flipSecond σ M) = w M := by
  simp only [w, T2_flipSecond (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

theorem height_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    height (flipSecond σ M) = height M := by
  have hN := satFrame_flipSecond hσ h
  unfold height
  rw [delta_eq hN, delta_eq h, w_flipSecond hσ h, r_flipSecond hσ h]

/-! ## 2b. The head flip's action on the `u, v, q, x` readers

The head flip only touches index 1, so `u` and `v` (indices `≥ 2` and row 0) are literally
unchanged while `q` and `x` — whose definitions carry `β` and `e` — pick up `σ`.  These are the
readers the card requires not to be dropped. -/

/-- The second original row/column sign is `1` on every index `≥ 2` (the whole `u` range). -/
theorem mid2nd_succ_succ {σ : ℝ} (i : Fin 3) : mid2nd σ i.succ.succ = 1 := by
  have h : ((i.succ.succ : Fin 5) : ℕ) = (i : ℕ) + 2 := rfl
  have hne : ¬ (((i.succ.succ : Fin 5) : ℕ) = 1) := by
    rw [h]
    intro hc
    exact Nat.succ_ne_zero (i : ℕ) (Nat.succ.inj hc)
  unfold mid2nd
  rw [if_neg hne]

theorem uX_flipSecond {M : Matrix5} (σ : ℝ) (i : Fin 3) :
    uX (flipSecond σ M) i = uX M i := by
  simp only [uX, flipSecond, signedEntries_apply, mid2nd_zero, mid2nd_succ_succ (σ := σ) i,
    one_mul, mul_one]

theorem vX_flipSecond {M : Matrix5} (σ : ℝ) (j : Fin 3) :
    vX (flipSecond σ M) j = vX M j := by
  simp only [vX, flipSecond, signedEntries_apply, mid2nd_zero, mid2nd_succ_succ (σ := σ) j,
    one_mul, mul_one]

theorem qX_flipSecond {M : Matrix5} (σ : ℝ) (j : Fin 3) :
    qX (flipSecond σ M) j = σ * qX M j := by
  have hb : betaX (flipSecond σ M) = σ * betaX M := betaX_flipSecond (M := M) σ
  have hv : vX (flipSecond σ M) j = vX M j := vX_flipSecond (M := M) σ j
  have hm : (flipSecond σ M) 1 j.succ.succ = σ * M 1 j.succ.succ := by
    simp only [flipSecond, signedEntries_apply, mid2nd_one, mid2nd_succ_succ (σ := σ) j, mul_one]
  unfold qX
  rw [hm, hb, hv]
  ring

theorem xX_flipSecond {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) (i : Fin 3) :
    xX (flipSecond σ M) i = σ * xX M i := by
  have hpp : pX (flipSecond σ M) = pX M := p_flipSecond hσ h
  have he : eX (flipSecond σ M) = σ * eX M := eX_flipSecond (M := M) σ
  have hu : uX (flipSecond σ M) i = uX M i := uX_flipSecond (M := M) σ i
  have hm : (flipSecond σ M) i.succ.succ 1 = σ * M i.succ.succ 1 := by
    simp only [flipSecond, signedEntries_apply, mid2nd_one, mid2nd_succ_succ (σ := σ) i, one_mul]
    ring
  unfold xX
  rw [hm, he, hu, hpp, ← mul_div_assoc]
  ring

/-! ## 3. The composed representative -/

/-- **D143 main theorem.**  From the actual `SatFrame M` with the card's two numeric inputs
(`q_* ≤ height M`, `k M ≤ 2`) there are signs `σ₁, σ₂, σ₃ ∈ {1,-1}` such that the real matrix

`N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))`

is again a `SatFrame` of the same height with the same `p, k, r, w`, carries the stage-A signs
`A, B < 0 < c, d`, the head signs `e, β > 0`, and `u₀ ≥ 0` — the exact interface D136 consumes.
No sign, no root membership and no chart-level property is assumed: every field is proved about the
actual matrix `N`. -/
theorem sign_representative_exists {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ height M) (hk2 : k M ≤ 2) :
    ∃ σ₁ σ₂ σ₃ : ℝ, (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧ (σ₃ = 1 ∨ σ₃ = -1) ∧
      SatFrame (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ∧
      height (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) = height M ∧
      p (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) = p M ∧
      k (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) = k M ∧
      r (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) = r M ∧
      w (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) = w M ∧
      aX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) < 0 ∧
      bX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) < 0 ∧
      0 < cX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ∧
      0 < dX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ∧
      0 < eX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ∧
      0 < betaX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) ∧
      0 ≤ uX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) 0 := by
  obtain ⟨σ₁, hσ₁, hS1, hA1, hB1, hC1, hD1⟩ := sign_normalization_exists h hq hk2
  have hp1 : 1 < p (flipMid σ₁ M) := by rw [p_flipMid hσ₁ h]; exact one_lt_p_of_height h hq
  obtain ⟨σ₂, hσ₂, hS2, hA2, hB2, hC2, hD2, he2, hb2⟩ :=
    head_flip_normalization hS1 hp1 hA1 hB1 hC1 hD1
  obtain ⟨σ₃, hσ₃, hS3, hA3, hB3, hC3, hD3, he3, hb3, hu3⟩ :=
    tail_flip_normalization hS2 hA2 hB2 hC2 hD2 he2 hb2
  refine ⟨σ₁, σ₂, σ₃, hσ₁, hσ₂, hσ₃, hS3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [height_flipLast3 hσ₃ hS2, height_flipSecond hσ₂ hS1, height_flipMid hσ₁ h]
  · rw [p_flipLast3 hσ₃ hS2, p_flipSecond hσ₂ hS1, p_flipMid hσ₁ h]
  · rw [k_flipLast3 hσ₃ hS2, k_flipSecond hσ₂ hS1, k_flipMid hσ₁ h]
  · rw [r_flipLast3 hσ₃ hS2, r_flipSecond hσ₂ hS1, r_flipMid hσ₁ h]
  · rw [w_flipLast3 hσ₃ hS2, w_flipSecond hσ₂ hS1, w_flipMid hσ₁ h]
  · exact hA3
  · exact hB3
  · exact hC3
  · exact hD3
  · exact he3
  · exact hb3
  · exact hu3

/-- The representative's `u`-coordinates: the head flip leaves `u` alone and the last-three flip
multiplies the whole triple by `σ₃`. -/
theorem representative_uX (σ₁ σ₂ σ₃ : ℝ) (M : Matrix5) (i : Fin 3) :
    uX (flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M))) i = σ₃ * uX (flipMid σ₁ M) i := by
  rw [uX_flipLast3 (M := flipSecond σ₂ (flipMid σ₁ M)) σ₃ i,
    uX_flipSecond (M := flipMid σ₁ M) σ₂ i]

end Rho5.Shared.XSmallKSigns
