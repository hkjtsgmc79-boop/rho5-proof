import Rho5.Shared.XHighRSource.SchurTransport

/-!
# D145 stage B — the actual coordinate transforms of the real transpose

This module pays the coordinate half of `TRANSPOSE_INTERFACE.md` **on the actual X22 readers of
D119**, beyond the raw-entry identities already frozen in `Transpose.lean`:

* `A_new = -(k c)`, `B_new = -(k d)`, `c_new = -(A/k)`, `d_new = -(B/k)`;
* `x_new = -(Z q)/p`, `q_new = -p (Z x)` with `Z = diag(1,-1,-1) = sgnZ`;
* the `S` / `O` block conjugations `S_new = Z (S M)^T Z`, `O_new = Z (O M)^T Z`, read through
  D119's `SX_eq_S4` and `OX_eq_entry` (the latter needed `SatFrame (transX M)`, which
  `SchurTransport.satFrame_transX` pays);
* the high-sign restoration: `HighRSigns` is invariant, because the coordinate transform exchanges
  the `A,B` signs with the `c,d` signs.

Nothing here assumes a model row or a diagram; those remain the last stage-B item.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-! ## 1. Sign readings -/

/-- `sgnZ4` restricted to the tail is D145's `Z = diag(1,-1,-1)`. -/
theorem sgnZ4_succ (i : Fin 3) : sgnZ4 i.succ = sgnZ i := by
  fin_cases i <;> simp [sgnZ4, sgnZ]

/-- `sgnD` on the tail indices is the same `Z`. -/
theorem sgnD_tail (i : Fin 3) : sgnD i.succ.succ = sgnZ i := by
  fin_cases i <;> simp [sgnD, sgnQ, sgnJ, sgnZ]

/-- The two tail entries of `transX M` used by the `A,B,c,d` readers. -/
theorem entry_tail_col0 (M : M5) (i : Fin 3) :
    (transX M) i.succ.succ 0 = sgnZ i * M 0 i.succ.succ := by
  fin_cases i <;> simp [transX, sgnD, sgnQ, sgnJ, sgnZ]

theorem entry_tail_row1 (M : M5) (i : Fin 3) :
    (transX M) i.succ.succ 1 = -(sgnZ i * M 1 i.succ.succ) := by
  fin_cases i <;> simp [transX, sgnD, sgnQ, sgnJ, sgnZ]

theorem entry_tail_row0 (M : M5) (i : Fin 3) :
    (transX M) 0 i.succ.succ = sgnZ i * M i.succ.succ 0 := by
  fin_cases i <;> simp [transX, sgnD, sgnQ, sgnJ, sgnZ]

theorem entry_tail_row1' (M : M5) (i : Fin 3) :
    (transX M) 1 i.succ.succ = -(sgnZ i * M i.succ.succ 1) := by
  fin_cases i <;> simp [transX, sgnD, sgnQ, sgnJ, sgnZ]

/-- All nine tail entries at once, in the shape of the block conjugations. -/
theorem entry_tail_tail (M : M5) (i j : Fin 3) :
    (transX M) i.succ.succ j.succ.succ =
      sgnZ i * M j.succ.succ i.succ.succ * sgnZ j := by
  fin_cases i <;> fin_cases j <;> simp [transX, sgnD, sgnQ, sgnJ, sgnZ]

/-! ## 2. The `A,B,c,d` transforms -/

theorem kX_mul_cX (M : M5) (h : SatFrame M) : kX M * cX M = S3 M 1 0 := by
  have hk : S3 M 0 0 ≠ 0 := ne_of_gt h.hk
  simp only [kX, cX]
  field_simp [hk]

theorem kX_mul_dX (M : M5) (h : SatFrame M) : kX M * dX M = S3 M 2 0 := by
  have hk : S3 M 0 0 ≠ 0 := ne_of_gt h.hk
  simp only [kX, dX]
  field_simp [hk]

/-- `A_new = -(k c)`. -/
theorem aX_transX (M : M5) (h : SatFrame M) : aX (transX M) = -(kX M * cX M) := by
  simp only [aX]
  rw [S3_transX M h]
  norm_num [sgnZ3]
  rw [kX_mul_cX M h]

/-- `B_new = -(k d)`. -/
theorem bX_transX (M : M5) (h : SatFrame M) : bX (transX M) = -(kX M * dX M) := by
  simp only [bX]
  rw [S3_transX M h]
  norm_num [sgnZ3]
  rw [kX_mul_dX M h]

/-- `c_new = -(A/k)`. -/
theorem cX_transX (M : M5) (h : SatFrame M) : cX (transX M) = -(aX M / kX M) := by
  have hk : S3 M 0 0 ≠ 0 := ne_of_gt h.hk
  simp only [cX, aX, kX]
  simp only [S3_transX M h]
  norm_num [sgnZ3]
  field_simp [hk]

/-- `d_new = -(B/k)`. -/
theorem dX_transX (M : M5) (h : SatFrame M) : dX (transX M) = -(bX M / kX M) := by
  have hk : S3 M 0 0 ≠ 0 := ne_of_gt h.hk
  simp only [dX, bX, kX]
  simp only [S3_transX M h]
  norm_num [sgnZ3]
  field_simp [hk]

/-! ## 3. The `x` / `q` transforms (they divide by `p`) -/

theorem pX_transX (M : M5) (h : SatFrame M) : pX (transX M) = pX M := p_transX M h

/-- `p * x_i` is the raw numerator, with the division cleared. -/
theorem pX_mul_xX (M : M5) (h : SatFrame M) (i : Fin 3) :
    pX M * xX M i = M i.succ.succ 1 + eX M * uX M i := by
  simp only [xX]
  field_simp [pX_ne_zero M h]

/-- `x_new = -(Z q)/p`. -/
theorem xX_transX (M : M5) (h : SatFrame M) (i : Fin 3) :
    xX (transX M) i = -(sgnZ i * qX M i) / pX M := by
  simp only [xX]
  rw [pX_transX M h, entry_tail_row1 M i, eX_transX M, uX_transX M i]
  simp only [qX]
  ring

/-- `q_new = -p (Z x)`. -/
theorem qX_transX (M : M5) (h : SatFrame M) (i : Fin 3) :
    qX (transX M) i = -(pX M * (sgnZ i * xX M i)) := by
  have hpx : pX M * (sgnZ i * xX M i) = sgnZ i * (M i.succ.succ 1 + eX M * uX M i) := by
    rw [← pX_mul_xX M h i]
    ring
  simp only [qX]
  rw [entry_tail_row1' M i, betaX_transX M, vX_transX M i, hpx]
  ring

/-! ## 4. The `S` / `O` block conjugations -/

/-- `S_new = Z (S M)^T Z`, through D119's actual reading `SX = S4` on the tail. -/
theorem SX_transX (M : M5) (h : SatFrame M) (i j : Fin 3) :
    SX (transX M) i j = sgnZ i * sgnZ j * SX M j i := by
  rw [SX_eq_S4 (transX M) (satFrame_transX M h) i j, S4_transX M h i.succ j.succ]
  simp only [sgnZ4_succ]
  rw [SX_eq_S4 M h j i]

/-- `O_new = Z (O M)^T Z`, through D119's actual reading `OX = M` on the tail. -/
theorem OX_transX (M : M5) (h : SatFrame M) (i j : Fin 3) :
    OX (transX M) i j = sgnZ i * sgnZ j * OX M j i := by
  rw [OX_eq_entry (transX M) (satFrame_transX M h) i j, OX_eq_entry M h j i]
  rw [entry_tail_tail M i j]
  ring

/-! ## 5. High-sign restoration -/

/-- **The high core signs are restored, not merely transported**: the transform exchanges the
`A,B` half with the `c,d` half, so `HighRSigns` holds on the transposed source exactly when it
holds on the source. -/
theorem highRSigns_transX_iff (M : M5) (h : SatFrame M) :
    HighRSigns (extractX (transX M)) ↔ HighRSigns (extractX M) := by
  have hk : 0 < kX M := h.hk
  have hA := aX_transX M h
  have hB := bX_transX M h
  have hc := cX_transX M h
  have hd := dX_transX M h
  simp only [HighRSigns, extractX_3, extractX_4, extractX_5, extractX_6]
  rw [hA, hB, hc, hd]
  constructor
  · intro hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    have hc' : 0 ≤ cX M := by nlinarith [hk, h1]
    have hd' : 0 ≤ dX M := by nlinarith [hk, h2]
    have ha' : aX M ≤ 0 := by
      have h5 : 0 ≤ (-aX M) / kX M := by
        rw [← neg_div] at h3
        exact h3
      have h6 : 0 ≤ -aX M := by
        have hmul : 0 ≤ (-aX M) / kX M * kX M := mul_nonneg h5 hk.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hk)] at hmul
      linarith
    have hb' : bX M ≤ 0 := by
      have h5 : 0 ≤ (-bX M) / kX M := by
        rw [← neg_div] at h4
        exact h4
      have h6 : 0 ≤ -bX M := by
        have hmul : 0 ≤ (-bX M) / kX M * kX M := mul_nonneg h5 hk.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hk)] at hmul
      linarith
    exact ⟨ha', hb', hc', hd'⟩
  · intro hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [hk, h3]
    · nlinarith [hk, h4]
    · rw [← neg_div]; exact div_nonneg (by linarith) hk.le
    · rw [← neg_div]; exact div_nonneg (by linarith) hk.le

end

end Rho5.Shared.XHighRSource
