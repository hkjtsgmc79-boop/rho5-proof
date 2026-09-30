import Rho5.Shared.XSmallKSigns.Head

/-!
# D143 stage B (tail) — the last-three rows/columns flip, `u0 ≥ 0`

`signedEntries M (midLast3 σ) (midLast3 σ)` flips the last three original rows and columns
(indices 2, 3, 4).  Every `u, x, v, q` coordinate picks up exactly one flipped index, so all of
them get `σ`; the `S3` layer (hence `A, B, c, d`, `k`) and `T2` (hence `r, s, t, w`, height) only
see `σ² = 1` and are unchanged, and `e`, `β` (indices 0, 1) are untouched.  So the last flip can
choose the sign of `u0` without disturbing anything proved before.
-/

noncomputable section
namespace Rho5.Shared.XSmallKSigns
open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.ExternalTailSaturation (w delta height)
open Rho5.TraceSigns (signedEntries signedEntries5 signedEntries_apply IsSign)
open Rho5.Shared.V43MatrixRoundTrip

/-- Flip the last three original rows/columns (indices 2, 3, 4). -/
def midLast3 (σ : ℝ) : Fin 5 → ℝ := fun i => if 2 ≤ (i : ℕ) then σ else 1
/-- Its image on the first Schur layer (`S4` index `i` is the original index `i + 1`). -/
def midLast4 (σ : ℝ) : Fin 4 → ℝ := fun i => if 1 ≤ (i : ℕ) then σ else 1

theorem isSign_midLast3 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (midLast3 σ) := by
  intro i
  unfold midLast3
  by_cases h : 2 ≤ (i : ℕ)
  · rw [if_pos h]; exact hσ
  · rw [if_neg h]; exact Or.inl rfl
theorem isSign_midLast4 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (midLast4 σ) := by
  intro i
  unfold midLast4
  by_cases h : 1 ≤ (i : ℕ)
  · rw [if_pos h]; exact hσ
  · rw [if_neg h]; exact Or.inl rfl
theorem midLast3_zero (σ : ℝ) : midLast3 σ 0 = 1 := by unfold midLast3; rw [if_neg (by norm_num)]
theorem midLast3_one (σ : ℝ) : midLast3 σ 1 = 1 := by unfold midLast3; rw [if_neg (by norm_num)]
/-- The first `S4` index is the original index 1, which is **not** flipped. -/
theorem midLast4_zero (σ : ℝ) : midLast4 σ 0 = 1 := by unfold midLast4; rw [if_neg (by norm_num)]
/-- Every `u, x, v, q` index (`i + 2`) **is** flipped. -/
theorem midLast3_succ_succ {σ : ℝ} (i : Fin 3) : midLast3 σ i.succ.succ = σ := by
  have h : ((i.succ.succ : Fin 5) : ℕ) = (i : ℕ) + 2 := rfl
  have h2 : 2 ≤ ((i.succ.succ : Fin 5) : ℕ) := by rw [h]; exact Nat.le_add_left 2 (i : ℕ)
  unfold midLast3
  rw [if_pos h2]

/-- The tail flip as a real matrix operation. -/
def flipLast3 (σ : ℝ) (M : Matrix5) : Matrix5 := signedEntries M (midLast3 σ) (midLast3 σ)

theorem flipLast3_one (M : Matrix5) : flipLast3 1 M = M := by
  ext i j; simp [flipLast3, signedEntries, midLast3]

/-- Conjugating by a constant `±1` sign vector is the identity on entries. -/
theorem signedEntries_const_self {n : ℕ} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (N : Matrix (Fin n) (Fin n) ℝ) :
    signedEntries N (fun _ => σ) (fun _ => σ) = N := by
  ext i j
  simp only [signedEntries_apply]
  calc σ * N i j * σ = (σ * σ) * N i j := by ring
    _ = N i j := by rw [sigma_sq hσ, one_mul]

theorem S4_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0) :
    S4 (flipLast3 σ M) = signedEntries (S4 M) (midLast4 σ) (midLast4 σ) := by
  have h := Rho5.TraceSigns.pivotSchur_signedEntries M (isSign_midLast3 hσ) (isSign_midLast3 hσ)
    0 0 h00
  have hfac : (fun i : Fin 4 => midLast3 σ (Rho5.PivotReindex.remainingIndex 0 i)) = midLast4 σ := by
    funext i
    by_cases h : 1 ≤ (i : ℕ) <;> simp [midLast3, midLast4, Rho5.PivotReindex.remainingIndex_apply, h]
  simpa [S4, flipLast3, hfac] using h

theorem S3_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) :
    S3 (flipLast3 σ M) = signedEntries (S3 M) (fun _ : Fin 3 => σ) (fun _ : Fin 3 => σ) := by
  have h4 := S4_flipLast3 (M := M) hσ h00
  have h := Rho5.TraceSigns.pivotSchur_signedEntries (S4 M) (isSign_midLast4 hσ) (isSign_midLast4 hσ)
    0 0 hp
  have hfac : (fun i : Fin 3 => midLast4 σ (Rho5.PivotReindex.remainingIndex 0 i)) = fun _ => σ := by
    funext i
    have : 1 ≤ ((i : Fin 3) : ℕ) + 1 := Nat.succ_le_succ (Nat.zero_le _)
    simp [midLast4, Rho5.PivotReindex.remainingIndex_apply, this]
  have hmain : Rho5.PivotReindex.pivotSchur
      (signedEntries (S4 M) (midLast4 σ) (midLast4 σ)) 0 0
      = signedEntries (S3 M) (fun _ : Fin 3 => σ) (fun _ : Fin 3 => σ) := by
    rw [h, hfac]
    rfl
  rw [show S3 (flipLast3 σ M) = Rho5.PivotReindex.pivotSchur (S4 (flipLast3 σ M)) 0 0 from rfl, h4]
  exact hmain

theorem T2_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    T2 (flipLast3 σ M) = signedEntries (T2 M) (fun _ : Fin 2 => σ) (fun _ : Fin 2 => σ) := by
  have h3 := S3_flipLast3 (M := M) hσ h00 hp
  have hsign : IsSign (fun _ : Fin 3 => σ) := fun _ => hσ
  have h := Rho5.TraceSigns.pivotSchur_signedEntries (S3 M) hsign hsign 0 0 hk
  rw [show T2 (flipLast3 σ M) = Rho5.PivotReindex.pivotSchur (S3 (flipLast3 σ M)) 0 0 from rfl, h3]
  exact h

/-- The whole `S3` layer is literally unchanged by the tail flip. -/
theorem S3_flipLast3_eq {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : S3 (flipLast3 σ M) = S3 M := by
  rw [S3_flipLast3 (M := M) hσ h00 hp,
    show signedEntries (S3 M) (fun _ : Fin 3 => σ) (fun _ : Fin 3 => σ) = S3 M from
      signedEntries_const_self hσ (S3 M)]

/-- The whole `T2` layer is literally unchanged by the tail flip. -/
theorem T2_flipLast3_eq {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) : T2 (flipLast3 σ M) = T2 M := by
  rw [T2_flipLast3 (M := M) hσ h00 hp hk,
    show signedEntries (T2 M) (fun _ : Fin 2 => σ) (fun _ : Fin 2 => σ) = T2 M from
      signedEntries_const_self hσ (T2 M)]

/-! ## 1. The readers: `u, x, v, q` get `σ`; everything else is unchanged -/

theorem uX_flipLast3 {M : Matrix5} (σ : ℝ) (i : Fin 3) :
    uX (flipLast3 σ M) i = σ * uX M i := by
  simp only [uX, flipLast3, signedEntries_apply, midLast3_zero, midLast3_succ_succ (σ := σ) i]
  ring

theorem vX_flipLast3 {M : Matrix5} (σ : ℝ) (j : Fin 3) :
    vX (flipLast3 σ M) j = σ * vX M j := by
  simp only [vX, flipLast3, signedEntries_apply, midLast3_zero, midLast3_succ_succ (σ := σ) j]
  ring

theorem eX_flipLast3 {M : Matrix5} (σ : ℝ) : eX (flipLast3 σ M) = eX M := by
  simp only [eX, flipLast3, signedEntries_apply, midLast3_zero, midLast3_one, one_mul, mul_one]

theorem betaX_flipLast3 {M : Matrix5} (σ : ℝ) : betaX (flipLast3 σ M) = betaX M := by
  simp only [betaX, flipLast3, signedEntries_apply, midLast3_zero, midLast3_one, one_mul, mul_one]

theorem kX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : kX (flipLast3 σ M) = kX M := by
  simp only [kX, S3_flipLast3_eq (M := M) hσ h00 hp]

theorem aX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : aX (flipLast3 σ M) = aX M := by
  simp only [aX, S3_flipLast3_eq (M := M) hσ h00 hp]

theorem bX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : bX (flipLast3 σ M) = bX M := by
  simp only [bX, S3_flipLast3_eq (M := M) hσ h00 hp]

theorem cX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : cX (flipLast3 σ M) = cX M := by
  simp only [cX, S3_flipLast3_eq (M := M) hσ h00 hp]

theorem dX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) : dX (flipLast3 σ M) = dX M := by
  simp only [dX, S3_flipLast3_eq (M := M) hσ h00 hp]

theorem pX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0) :
    pX (flipLast3 σ M) = pX M := by
  simp only [pX, S4_flipLast3 (M := M) hσ h00, signedEntries_apply, midLast4_zero, one_mul, mul_one]

theorem rX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) : rX (flipLast3 σ M) = rX M := by
  simp only [rX, T2_flipLast3_eq (M := M) hσ h00 hp hk]

theorem wX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) : wX (flipLast3 σ M) = wX M := by
  simp only [wX, T2_flipLast3_eq (M := M) hσ h00 hp hk]

theorem qX_flipLast3 {M : Matrix5} (σ : ℝ) (j : Fin 3) :
    qX (flipLast3 σ M) j = σ * qX M j := by
  have hb : betaX (flipLast3 σ M) = betaX M := betaX_flipLast3 (M := M) σ
  have hv : vX (flipLast3 σ M) j = σ * vX M j := vX_flipLast3 (M := M) σ j
  have hm : (flipLast3 σ M) 1 j.succ.succ = σ * M 1 j.succ.succ := by
    simp only [flipLast3, signedEntries_apply, midLast3_one, one_mul, midLast3_succ_succ (σ := σ) j]
    ring
  unfold qX
  rw [hm, hb, hv]
  ring

theorem xX_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0) (i : Fin 3) :
    xX (flipLast3 σ M) i = σ * xX M i := by
  have hpp : pX (flipLast3 σ M) = pX M := pX_flipLast3 (M := M) hσ h00
  have he : eX (flipLast3 σ M) = eX M := eX_flipLast3 (M := M) σ
  have hu : uX (flipLast3 σ M) i = σ * uX M i := uX_flipLast3 (M := M) σ i
  have hm : (flipLast3 σ M) i.succ.succ 1 = σ * M i.succ.succ 1 := by
    simp only [flipLast3, signedEntries_apply, midLast3_one, mul_one, midLast3_succ_succ (σ := σ) i]
  unfold xX
  rw [hm, he, hu, hpp, ← mul_div_assoc]
  ring

/-! ## 2. `SatFrame`, the height, `p`, `k`, `r`, `w` are preserved -/

theorem satFrame_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    SatFrame (flipLast3 σ M) where
  h00 := by simp only [flipLast3, signedEntries_apply, midLast3_zero, one_mul, mul_one]; exact h.h00
  hmax := by
    rw [show flipLast3 σ M = signedEntries5 M (midLast3 σ) (midLast3 σ) from rfl,
      Rho5.TraceSigns.matrixEntryMax_signedEntries5 M (isSign_midLast3 hσ) (isSign_midLast3 hσ)]
    exact h.hmax
  cp1 := (Rho5.TraceSigns.isCompletePivot_signedEntries_iff M (isSign_midLast3 hσ)
    (isSign_midLast3 hσ) 0 0).mpr h.cp1
  cp2 := by
    rw [show S4 (flipLast3 σ M) = signedEntries (S4 M) (midLast4 σ) (midLast4 σ) from
      S4_flipLast3 hσ (h00_ne h)]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S4 M) (isSign_midLast4 hσ)
      (isSign_midLast4 hσ) 0 0).mpr h.cp2
  cp3 := by
    rw [show S3 (flipLast3 σ M) = S3 M from S3_flipLast3_eq hσ (h00_ne h) (ne_of_gt h.hp)]
    exact h.cp3
  cp4 := by
    rw [show T2 (flipLast3 σ M) = T2 M from
      T2_flipLast3_eq hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]
    exact h.cp4
  hp := by
    rw [show p (flipLast3 σ M) = p M from by
      simp only [p, S4_flipLast3 (M := M) hσ (h00_ne h), signedEntries_apply, midLast4_zero,
        one_mul, mul_one]]
    exact h.hp
  hk := by
    rw [show k (flipLast3 σ M) = k M from by
      simp only [k, S3_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp)]]
    exact h.hk
  hr := by
    rw [show r (flipLast3 σ M) = r M from by
      simp only [r, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.hr
  hs := by
    rw [show s (flipLast3 σ M) = s M from by
        simp only [s, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)],
      show r (flipLast3 σ M) = r M from by
        simp only [r, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.hs
  ht := by
    rw [show t (flipLast3 σ M) = t M from by
        simp only [t, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)],
      show r (flipLast3 σ M) = r M from by
        simp only [r, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]]
    exact h.ht

theorem height_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    Rho5.ExternalTailSaturation.height (flipLast3 σ M) = Rho5.ExternalTailSaturation.height M := by
  have hN := satFrame_flipLast3 hσ h
  have h00 := h00_ne h
  have hp := ne_of_gt h.hp
  have hk := ne_of_gt h.hk
  rw [Rho5.ExternalTailSaturation.height, Rho5.ExternalTailSaturation.height]
  rw [delta_eq hN, delta_eq h]
  rw [show w (flipLast3 σ M) = w M from by
      simp only [w, T2_flipLast3_eq (M := M) hσ h00 hp hk],
    show r (flipLast3 σ M) = r M from by
      simp only [r, T2_flipLast3_eq (M := M) hσ h00 hp hk]]

theorem p_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    p (flipLast3 σ M) = p M := by
  simp only [p, S4_flipLast3 (M := M) hσ (h00_ne h), signedEntries_apply, midLast4_zero,
    one_mul, mul_one]

theorem k_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    k (flipLast3 σ M) = k M := by
  simp only [k, S3_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp)]

theorem r_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    r (flipLast3 σ M) = r M := by
  simp only [r, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

theorem w_flipLast3 {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : SatFrame M) :
    w (flipLast3 σ M) = w M := by
  simp only [w, T2_flipLast3_eq (M := M) hσ (h00_ne h) (ne_of_gt h.hp) (ne_of_gt h.hk)]

/-! ## 3. The tail normalization: `u0 ≥ 0` while every earlier sign survives -/

/-- **Stage B tail flip.**  Given the stage-A signs and the head flip's `e, β > 0`, some
`σ ∈ {1,-1}` makes `u0 ≥ 0` on the flipped real frame, which keeps `SatFrame`, the height, `p`,
`k` and every earlier sign. -/
theorem tail_flip_normalization {M : Matrix5} (h : SatFrame M)
    (hA : aX M < 0) (hB : bX M < 0) (hC : 0 < cX M) (hD : 0 < dX M)
    (he : 0 < eX M) (hb : 0 < betaX M) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SatFrame (flipLast3 σ M) ∧
      aX (flipLast3 σ M) < 0 ∧ bX (flipLast3 σ M) < 0 ∧
        0 < cX (flipLast3 σ M) ∧ 0 < dX (flipLast3 σ M) ∧
          0 < eX (flipLast3 σ M) ∧ 0 < betaX (flipLast3 σ M) ∧
            0 ≤ uX (flipLast3 σ M) 0 := by
  have h00 := h00_ne h
  have hp := ne_of_gt h.hp
  by_cases h0 : 0 ≤ uX M 0
  · refine ⟨1, Or.inl rfl, satFrame_flipLast3 (Or.inl rfl) h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rwa [flipLast3_one]
    · rwa [flipLast3_one]
    · rwa [flipLast3_one]
    · rwa [flipLast3_one]
    · rwa [flipLast3_one]
    · rwa [flipLast3_one]
    · rw [flipLast3_one]; exact h0
  · have h0' : uX M 0 < 0 := not_le.mp h0
    have hσn : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
    refine ⟨-1, hσn, satFrame_flipLast3 hσn h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [aX_flipLast3 (M := M) (σ := -1) hσn h00 hp]; exact hA
    · rw [bX_flipLast3 (M := M) (σ := -1) hσn h00 hp]; exact hB
    · rw [cX_flipLast3 (M := M) (σ := -1) hσn h00 hp]; exact hC
    · rw [dX_flipLast3 (M := M) (σ := -1) hσn h00 hp]; exact hD
    · rw [eX_flipLast3 (M := M) (-1)]; exact he
    · rw [betaX_flipLast3 (M := M) (-1)]; exact hb
    · rw [uX_flipLast3 (M := M) (-1) 0]; linarith
end Rho5.Shared.XSmallKSigns
