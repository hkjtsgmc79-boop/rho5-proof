import Rho5.ExternalTailSaturation.Basic

/-!
Full-matrix diagonal actions and three *actual* Schur covariance identities.
The head factors are one, so these algebraic covariance identities do not divide
by a scaling parameter.  Qualifications for physical elimination are paid later.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.TraceSigns (signedEntries)

-- Factors for full last-two-row/column operations, also used by the sign module.
def factors5 (a b : ℝ) : Fin 5 → ℝ := ![1, 1, 1, a, b]
def factors4 (a b : ℝ) : Fin 4 → ℝ := ![1, 1, a, b]
def factors3 (a b : ℝ) : Fin 3 → ℝ := ![1, a, b]
def factors2 (a b : ℝ) : Fin 2 → ℝ := ![a, b]

@[simp] theorem factors5_succ (a b : ℝ) (i : Fin 4) :
    factors5 a b i.succ = factors4 a b i := by
  fin_cases i <;> simp [factors5, factors4]
@[simp] theorem factors4_succ (a b : ℝ) (i : Fin 3) :
    factors4 a b i.succ = factors3 a b i := by
  fin_cases i <;> simp [factors4, factors3]
@[simp] theorem factors3_succ (a b : ℝ) (i : Fin 2) :
    factors3 a b i.succ = factors2 a b i := by
  fin_cases i <;> simp [factors3, factors2]

/-- Full operation on the last two rows and columns, not an abstract tail edit. -/
def tailScale (M : Matrix5) (a b c d : ℝ) : Matrix5 :=
  signedEntries M (factors5 a b) (factors5 c d)

/-- The prescribed operation in the task, with zero-based fourth index 3. -/
def rowFactor (lam : ℝ) (i : Fin 5) : ℝ := if i = 3 then lam else 1
def colFactor (mu : ℝ) (j : Fin 5) : ℝ := if j = 3 then mu else 1
def contract (M : Matrix5) (lam mu : ℝ) : Matrix5 :=
  fun i j => rowFactor lam i * M i j * colFactor mu j

theorem contract_eq_tailScale (M : Matrix5) (lam mu : ℝ) :
    contract M lam mu = tailScale M lam 1 mu 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [contract, rowFactor, colFactor, tailScale, signedEntries, factors5]

/-- Literal left/right multiplication by diagonal matrices. -/
theorem contract_eq_diagonal (M : Matrix5) (lam mu : ℝ) :
    contract M lam mu = Matrix.diagonal (rowFactor lam) * M * Matrix.diagonal (colFactor mu) := by
  funext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem tailScale_eq_diagonal (M : Matrix5) (a b c d : ℝ) :
    tailScale M a b c d =
      Matrix.diagonal (factors5 a b) * M * Matrix.diagonal (factors5 c d) := by
  funext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- Generic one-step covariance when the selected row and column factors are 1. -/
theorem schur_head_scale {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a b : Fin (n + 1) → ℝ) (ha : a 0 = 1) (hb : b 0 = 1) :
    Rho5.PivotReindex.pivotSchur (signedEntries A a b) 0 0 =
      signedEntries (Rho5.PivotReindex.pivotSchur A 0 0)
        (fun i => a i.succ) (fun j => b j.succ) := by
  funext i j
  simp only [Rho5.PivotReindex.pivotSchur,
    Rho5.PivotReindex.movePivot_zero_zero_eq, Rho5.Pivot.fixedSchur,
    signedEntries, ha, hb, one_mul, mul_one, div_eq_mul_inv]
  ring

/-- First actual Schur update of the same full matrix. -/
theorem S4_tailScale (M : Matrix5) (a b c d : ℝ) :
    S4 (tailScale M a b c d) = signedEntries (S4 M) (factors4 a b) (factors4 c d) := by
  change Rho5.PivotReindex.pivotSchur (signedEntries M (factors5 a b) (factors5 c d)) 0 0 = _
  simpa only [factors5_succ] using
    schur_head_scale M (factors5 a b) (factors5 c d) (by simp [factors5]) (by simp [factors5])

/-- Second actual Schur update. -/
theorem S3_tailScale (M : Matrix5) (a b c d : ℝ) :
    S3 (tailScale M a b c d) = signedEntries (S3 M) (factors3 a b) (factors3 c d) := by
  unfold S3
  rw [S4_tailScale]
  simpa only [factors4_succ] using
    schur_head_scale (S4 M) (factors4 a b) (factors4 c d)
      (by simp [factors4]) (by simp [factors4])

/-- Third actual Schur update, now containing all four transformed tail entries. -/
theorem T2_tailScale (M : Matrix5) (a b c d : ℝ) :
    T2 (tailScale M a b c d) = signedEntries (T2 M) (factors2 a b) (factors2 c d) := by
  unfold T2
  rw [S3_tailScale]
  simpa only [factors3_succ] using
    schur_head_scale (S3 M) (factors3 a b) (factors3 c d)
      (by simp [factors3]) (by simp [factors3])

@[simp] theorem tailScale_head (M : Matrix5) (a b c d : ℝ) :
    tailScale M a b c d 0 0 = M 0 0 := by
  simp [tailScale, signedEntries, factors5]
@[simp] theorem p_tailScale (M : Matrix5) (a b c d : ℝ) :
    p (tailScale M a b c d) = p M := by
  simp [p, S4_tailScale, signedEntries, factors4]
@[simp] theorem k_tailScale (M : Matrix5) (a b c d : ℝ) :
    k (tailScale M a b c d) = k M := by
  simp [k, S3_tailScale, signedEntries, factors3]
@[simp] theorem r_tailScale (M : Matrix5) (a b c d : ℝ) :
    r (tailScale M a b c d) = a * r M * c := by
  simp [r, T2_tailScale, signedEntries, factors2]
@[simp] theorem s_tailScale (M : Matrix5) (a b c d : ℝ) :
    s (tailScale M a b c d) = a * s M * d := by
  simp [s, T2_tailScale, signedEntries, factors2]
@[simp] theorem t_tailScale (M : Matrix5) (a b c d : ℝ) :
    t (tailScale M a b c d) = b * t M * c := by
  simp [t, T2_tailScale, signedEntries, factors2]
@[simp] theorem w_tailScale (M : Matrix5) (a b c d : ℝ) :
    w (tailScale M a b c d) = b * w M * d := by
  simp [w, T2_tailScale, signedEntries, factors2]

theorem S4_contract (M : Matrix5) (lam mu : ℝ) :
    S4 (contract M lam mu) = signedEntries (S4 M) (factors4 lam 1) (factors4 mu 1) := by
  rw [contract_eq_tailScale, S4_tailScale]
theorem S3_contract (M : Matrix5) (lam mu : ℝ) :
    S3 (contract M lam mu) = signedEntries (S3 M) (factors3 lam 1) (factors3 mu 1) := by
  rw [contract_eq_tailScale, S3_tailScale]
theorem T2_contract (M : Matrix5) (lam mu : ℝ) :
    T2 (contract M lam mu) = signedEntries (T2 M) (factors2 lam 1) (factors2 mu 1) := by
  rw [contract_eq_tailScale, T2_tailScale]

@[simp] theorem contract_head (M : Matrix5) (lam mu : ℝ) :
    contract M lam mu 0 0 = M 0 0 := by simp [contract_eq_tailScale]
@[simp] theorem p_contract (M : Matrix5) (lam mu : ℝ) : p (contract M lam mu) = p M := by
  simp [contract_eq_tailScale]
@[simp] theorem k_contract (M : Matrix5) (lam mu : ℝ) : k (contract M lam mu) = k M := by
  simp [contract_eq_tailScale]
@[simp] theorem r_contract (M : Matrix5) (lam mu : ℝ) :
    r (contract M lam mu) = lam * mu * r M := by simp [contract_eq_tailScale]; ring
@[simp] theorem s_contract (M : Matrix5) (lam mu : ℝ) :
    s (contract M lam mu) = lam * s M := by simp [contract_eq_tailScale]
@[simp] theorem t_contract (M : Matrix5) (lam mu : ℝ) :
    t (contract M lam mu) = mu * t M := by simp [contract_eq_tailScale]; ring
@[simp] theorem w_contract (M : Matrix5) (lam mu : ℝ) :
    w (contract M lam mu) = w M := by simp [contract_eq_tailScale]

/-- Qualified cancellation also useful for later full sign operations. -/
theorem delta_tailScale (M : Matrix5) (a b c d : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hr : r M ≠ 0) :
    delta (tailScale M a b c d) = b * d * delta M := by
  simp only [delta, w_tailScale, t_tailScale, s_tailScale, r_tailScale]
  field_simp [ha, hc, hr] <;> ring

/-- Same signed last pivot; no sign restriction on r. -/
theorem delta_contract (M : Matrix5) (lam mu : ℝ)
    (hlam : lam ≠ 0) (hmu : mu ≠ 0) (hr : r M ≠ 0) :
    delta (contract M lam mu) = delta M := by
  rw [contract_eq_tailScale, delta_tailScale M lam 1 mu 1 hlam hmu hr]
  ring

private theorem abs_scale_le (a x b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * x * b| ≤ |x| := by
  rw [abs_mul, abs_mul]
  calc |a| * |x| * |b| ≤ (1 * |x|) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right ha (abs_nonneg x)) hb
        (abs_nonneg b) (by positivity)
    _ = |x| := by ring

/-- Entrywise contraction with absolute-factor hypotheses; allows endpoints 0. -/
theorem abs_signedEntries_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (a b : Fin n → ℝ) (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1) (i j : Fin n) :
    |signedEntries A a b i j| ≤ |A i j| :=
  abs_scale_le _ _ _ (ha i) (hb j)

/-- CP is preserved only when the selected pivot factors are exactly one. -/
theorem cp_head_scale {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a b : Fin (n + 1) → ℝ) (ha : ∀ i, |a i| ≤ 1) (hb : ∀ j, |b j| ≤ 1)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) (hcp : IsCompletePivot A 0 0) :
    IsCompletePivot (signedEntries A a b) 0 0 := by
  intro i j
  calc |signedEntries A a b i j| ≤ |A i j| := abs_signedEntries_le A a b ha hb i j
    _ ≤ |A 0 0| := hcp i j
    _ = |signedEntries A a b 0 0| := by simp [signedEntries, ha0, hb0]

private theorem factors5_abs_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : Fin 5) :
    |factors5 a 1 i| ≤ 1 := by
  fin_cases i <;> simp [factors5, abs_of_nonneg ha0, ha1]
private theorem factors4_abs_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : Fin 4) :
    |factors4 a 1 i| ≤ 1 := by
  fin_cases i <;> simp [factors4, abs_of_nonneg ha0, ha1]
private theorem factors3_abs_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (i : Fin 3) :
    |factors3 a 1 i| ≤ 1 := by
  fin_cases i <;> simp [factors3, abs_of_nonneg ha0, ha1]

/-- All 25 original entries contract; the whole source is transformed at once. -/
theorem contract_abs_le (M : Matrix5) (lam mu : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (i j : Fin 5) :
    |contract M lam mu i j| ≤ |M i j| := by
  rw [contract_eq_tailScale]
  exact abs_signedEntries_le M _ _ (factors5_abs_le lam hlam0 hlam1) (factors5_abs_le mu hmu0 hmu1) i j

theorem S4_contract_abs_le (M : Matrix5) (lam mu : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (i j : Fin 4) :
    |S4 (contract M lam mu) i j| ≤ |S4 M i j| := by
  rw [S4_contract]
  exact abs_signedEntries_le (S4 M) _ _ (factors4_abs_le lam hlam0 hlam1) (factors4_abs_le mu hmu0 hmu1) i j

theorem S3_contract_abs_le (M : Matrix5) (lam mu : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) (i j : Fin 3) :
    |S3 (contract M lam mu) i j| ≤ |S3 M i j| := by
  rw [S3_contract]
  exact abs_signedEntries_le (S3 M) _ _ (factors3_abs_le lam hlam0 hlam1) (factors3_abs_le mu hmu0 hmu1) i j

/-- T1 early legality.  Deliberately does NOT assert fourth-step CP. -/
theorem contract_early_cp {M : Matrix5} (h : LeadingInput M) (lam mu : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    IsCompletePivot (contract M lam mu) 0 0 ∧
    IsCompletePivot (S4 (contract M lam mu)) 0 0 ∧
    IsCompletePivot (S3 (contract M lam mu)) 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contract_eq_tailScale]
    exact cp_head_scale M _ _ (factors5_abs_le lam hlam0 hlam1) (factors5_abs_le mu hmu0 hmu1)
      (by simp [factors5]) (by simp [factors5]) h.cp0
  · rw [S4_contract]
    exact cp_head_scale (S4 M) _ _ (factors4_abs_le lam hlam0 hlam1) (factors4_abs_le mu hmu0 hmu1)
      (by simp [factors4]) (by simp [factors4]) h.cp1
  · rw [S3_contract]
    exact cp_head_scale (S3 M) _ _ (factors3_abs_le lam hlam0 hlam1) (factors3_abs_le mu hmu0 hmu1)
      (by simp [factors3]) (by simp [factors3]) h.cp2

theorem entryMax_contract {M : Matrix5} (h : LeadingInput M) (lam mu : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    matrixEntryMax (contract M lam mu) = 1 :=
  entryMax_eq_one _ (by simpa only [contract_head] using h.head)
    (contract_early_cp h lam mu hlam0 hlam1 hmu0 hmu1).1

end Rho5.ExternalTailSaturation
