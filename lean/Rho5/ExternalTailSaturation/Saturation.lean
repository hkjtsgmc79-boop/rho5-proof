import Rho5.ExternalTailSaturation.FactorChoice

/-!
T1+T2: every witness is the explicitly contracted full Matrix5, its four CP
conditions are proved, and the signed fifth pivot and genuine legal trace are paid.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.CompletePivotPath (LegalTrace)

/-- Absolute D geometry on an actual matrix; legal inequalities live in LeadingInput. -/
def DFace (M : Matrix5) : Prop := |w M| = |r M|
/-- Absolute X geometry on an actual matrix. -/
def XFace (M : Matrix5) : Prop := |s M| = |r M| ∧ |t M| = |r M|

theorem contract_r_abs (M : Matrix5) (lam mu : ℝ) (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    |r (contract M lam mu)| = lam * mu * |r M| := by
  rw [r_contract, abs_mul, abs_mul, abs_of_nonneg hlam, abs_of_nonneg hmu]

theorem contract_s_abs (M : Matrix5) (lam mu : ℝ) (hlam : 0 ≤ lam) :
    |s (contract M lam mu)| = lam * |s M| := by
  rw [s_contract, abs_mul, abs_of_nonneg hlam]

theorem contract_t_abs (M : Matrix5) (lam mu : ℝ) (hmu : 0 ≤ mu) :
    |t (contract M lam mu)| = mu * |t M| := by
  rw [t_contract, abs_mul, abs_of_nonneg hmu]

/-- CP of a 2-by-2 actual tail is exactly its three competitor inequalities. -/
theorem tail_cp_of_bounds (M : Matrix5) (hs : |s M| ≤ |r M|)
    (ht : |t M| ≤ |r M|) (hw : |w M| ≤ |r M|) : IsCompletePivot (T2 M) 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact hs
  · exact ht
  · exact hw

/-- Fourth-step legality is paid from the selected branch's inequalities. -/
theorem contract_fourth_cp {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) : IsCompletePivot (T2 (contract M lam mu)) 0 0 := by
  have hlam := le_of_lt c.left_pos
  have hmu := le_of_lt c.right_pos
  have hR : 0 ≤ |r M| := abs_nonneg _
  apply tail_cp_of_bounds
  · rw [contract_s_abs M lam mu hlam, contract_r_abs M lam mu hlam hmu,
      ← sigma_mul_abs_r h]
    calc lam * (sigma M * |r M|) ≤ lam * (mu * |r M|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c.sigma_le hR) hlam
      _ = lam * mu * |r M| := by ring
  · rw [contract_t_abs M lam mu hmu, contract_r_abs M lam mu hlam hmu,
      ← tau_mul_abs_r h]
    calc mu * (tau M * |r M|) ≤ mu * (lam * |r M|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right c.tau_le hR) hmu
      _ = lam * mu * |r M| := by ring
  · rw [w_contract, contract_r_abs M lam mu hlam hmu, ← nu_mul_abs_r h]
    exact mul_le_mul_of_nonneg_right c.nu_le hR

/-- The new fourth pivot is qualified, even when the original one was negative. -/
theorem contract_fourth_ne_zero {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) : r (contract M lam mu) ≠ 0 := by
  rw [r_contract]
  exact mul_ne_zero (mul_ne_zero (ne_of_gt c.left_pos) (ne_of_gt c.right_pos)) (r_ne_zero h)

/-- All original-domain conditions proved for the *same* contracted Matrix5. -/
theorem contract_leadingInput {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) : LeadingInput (contract M lam mu) := by
  have hcp := contract_early_cp h lam mu (le_of_lt c.left_pos) c.left_le_one
    (le_of_lt c.right_pos) c.right_le_one
  refine ⟨?_, hcp.1, hcp.2.1, hcp.2.2, contract_fourth_cp h c, ?_, ?_, ?_⟩
  · simpa only [contract_head] using h.head
  · simpa only [p_contract] using h.p_pos
  · simpa only [k_contract] using h.k_pos
  · rw [delta_contract M lam mu (ne_of_gt c.left_pos) (ne_of_gt c.right_pos) (r_ne_zero h)]
    exact h.delta_ne

theorem contract_height {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) : height (contract M lam mu) = height M := by
  unfold height
  rw [delta_contract M lam mu (ne_of_gt c.left_pos) (ne_of_gt c.right_pos) (r_ne_zero h)]

theorem contract_fourth_le {M : Matrix5} {lam mu : ℝ} (c : FactorCertificate M lam mu) :
    |r (contract M lam mu)| ≤ |r M| := by
  rw [contract_r_abs M lam mu (le_of_lt c.left_pos) (le_of_lt c.right_pos)]
  have hp : lam * mu ≤ 1 := by
    calc lam * mu ≤ 1 * 1 := mul_le_mul c.left_le_one c.right_le_one (le_of_lt c.right_pos) (by norm_num)
      _ = 1 := by ring
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (abs_nonneg (r M))

/-- The exact value list required by the task, connected through the real 0-by-0 end. -/
theorem contract_legalTrace {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) :
    LegalTrace (contract M lam mu) [1, p M, k M, |lam * mu * r M|, height M] := by
  simpa only [p_contract, k_contract, r_contract, contract_height h c] using
    leading_legalTrace (contract_leadingInput h c)

/-- D equality from the branch product; includes zero arms. -/
theorem contract_DFace {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) (hD : lam * mu = nu M) : DFace (contract M lam mu) := by
  change |w (contract M lam mu)| = |r (contract M lam mu)|
  rw [w_contract, contract_r_abs M lam mu (le_of_lt c.left_pos) (le_of_lt c.right_pos), hD]
  exact (nu_mul_abs_r h).symm

/-- Both X equalities from the chosen ratios, not from independently picked lifts. -/
theorem contract_XFace {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) (hlam : lam = tau M) (hmu : mu = sigma M) :
    XFace (contract M lam mu) := by
  constructor
  · rw [contract_s_abs M lam mu (le_of_lt c.left_pos),
      contract_r_abs M lam mu (le_of_lt c.left_pos) (le_of_lt c.right_pos),
      ← sigma_mul_abs_r h, ← hmu]
    ring
  · rw [contract_t_abs M lam mu (le_of_lt c.right_pos),
      contract_r_abs M lam mu (le_of_lt c.left_pos) (le_of_lt c.right_pos),
      ← tau_mul_abs_r h, ← hlam]
    ring

theorem contract_saturated {M : Matrix5} (h : LeadingInput M) {lam mu : ℝ}
    (c : FactorCertificate M lam mu) : DFace (contract M lam mu) ∨ XFace (contract M lam mu) := by
  rcases c.face with hd | ⟨hl, hm⟩
  · exact Or.inl (contract_DFace h c hd)
  · exact Or.inr (contract_XFace h c hl hm)

/-- Explicit full-matrix representative, with a common deterministic branch choice. -/
def representative (M : Matrix5) : Matrix5 := contract M (chosenLambda M) (chosenMu M)

/-- T1+T2, concrete rather than merely existential. -/
theorem representative_spec {M : Matrix5} (h : LeadingInput M) :
    LeadingInput (representative M) ∧
    p (representative M) = p M ∧ k (representative M) = k M ∧
    delta (representative M) = delta M ∧
    height (representative M) = height M ∧
    |r (representative M)| ≤ |r M| ∧
    matrixEntryMax (representative M) = 1 ∧
    (DFace (representative M) ∨ XFace (representative M)) ∧
    LegalTrace (representative M)
      [1, p M, k M, |chosenLambda M * chosenMu M * r M|, height M] := by
  have c := chosen_factor_certificate h
  refine ⟨contract_leadingInput h c, p_contract _ _ _, k_contract _ _ _,
    delta_contract _ _ _ (ne_of_gt c.left_pos) (ne_of_gt c.right_pos) (r_ne_zero h),
    contract_height h c, contract_fourth_le c, ?_, contract_saturated h c,
    contract_legalTrace h c⟩
  exact entryMax_contract h _ _ (le_of_lt c.left_pos) c.left_le_one
    (le_of_lt c.right_pos) c.right_le_one

/-- Public existential theorem with all actual-input hypotheses displayed. -/
theorem exists_same_fifth_D_or_X (M : Matrix5) (h00 : M 0 0 = 1)
    (h0 : IsCompletePivot M 0 0) (h1 : IsCompletePivot (S4 M) 0 0)
    (h2 : IsCompletePivot (S3 M) 0 0) (h3 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hd : delta M ≠ 0) :
    ∃ (lam mu : ℝ) (M' : Matrix5),
      0 < lam ∧ lam ≤ 1 ∧ 0 < mu ∧ mu ≤ 1 ∧ M' = contract M lam mu ∧
      LeadingInput M' ∧ p M' = p M ∧ k M' = k M ∧ delta M' = delta M ∧
      height M' = height M ∧ |r M'| ≤ |r M| ∧ matrixEntryMax M' = 1 ∧
      (DFace M' ∨ XFace M') ∧
      LegalTrace M' [1, p M, k M, |lam * mu * r M|, height M] := by
  have h : LeadingInput M := ⟨h00, h0, h1, h2, h3, hp, hk, hd⟩
  have c := chosen_factor_certificate h
  exact ⟨chosenLambda M, chosenMu M, representative M,
    c.left_pos, c.left_le_one, c.right_pos, c.right_le_one, rfl, representative_spec h⟩

/-- Separate D branch entry point, for a coordinator that has already split the chart. -/
theorem D_branch_spec {M : Matrix5} (h : LeadingInput M)
    (hD : sigma M * tau M ≤ nu M) :
    LeadingInput (contract M (lambdaD M) (muD M)) ∧
    DFace (contract M (lambdaD M) (muD M)) ∧
    delta (contract M (lambdaD M) (muD M)) = delta M ∧
    LegalTrace (contract M (lambdaD M) (muD M))
      [1, p M, k M, |lambdaD M * muD M * r M|, height M] := by
  have c := D_factor_certificate h hD
  have hprod : lambdaD M * muD M = nu M := by
    unfold muD
    field_simp [ne_of_gt c.left_pos] <;> ring
  exact ⟨contract_leadingInput h c, contract_DFace h c hprod,
    delta_contract _ _ _ (ne_of_gt c.left_pos) (ne_of_gt c.right_pos) (r_ne_zero h),
    contract_legalTrace h c⟩

/-- Separate X entry point, valid also at the positive-product equality boundary. -/
theorem X_branch_spec {M : Matrix5} (h : LeadingInput M)
    (hX : nu M ≤ sigma M * tau M) :
    LeadingInput (contract M (lambdaX M) (muX M)) ∧
    XFace (contract M (lambdaX M) (muX M)) ∧
    delta (contract M (lambdaX M) (muX M)) = delta M ∧
    LegalTrace (contract M (lambdaX M) (muX M))
      [1, p M, k M, |lambdaX M * muX M * r M|, height M] := by
  have c := X_factor_certificate h hX
  exact ⟨contract_leadingInput h c, contract_XFace h c rfl rfl,
    delta_contract _ _ _ (ne_of_gt c.left_pos) (ne_of_gt c.right_pos) (r_ne_zero h),
    contract_legalTrace h c⟩

end Rho5.ExternalTailSaturation
