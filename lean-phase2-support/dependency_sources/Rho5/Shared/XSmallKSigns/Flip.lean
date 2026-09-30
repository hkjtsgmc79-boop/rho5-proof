import Rho5.Shared.XSmallKSigns.Signs
import Rho5.Shared.TraceSigns.Normalize

/-!
# D143 stage A (second half) — the real third-row/column sign flip `diag(1,1,σ,1,1)`

The operation is `signedEntries M (mid5 σ) (mid5 σ)` with `mid5 σ i = if i = 2 then σ else 1`, i.e.
the simultaneous sign flip of the third **original** row and column (`σ = ±1`).  It is transported
through the real Schur chain by D22's generic `pivotSchur_signedEntries`:

* `S4` gets `mid4`, `S3` gets `mid3`, and `T2` is untouched (its indices are the original 3 and 4);
* hence `kX`, `rX`, `wX`, `pX` are invariant while `aX`, `bX`, `cX`, `dX` all pick up `σ` —
  matching the corrected reading (`D01, D02, D10, D20` scale by `σ`, `k` is a Schur invariant so
  `σ^2 = 1` leaves it fixed);
* `SatFrame` is preserved (`h00`, `hmax`, the four complete pivots, the positive pivots, `s = t = r`).

Consequently `∃ σ ∈ {1,-1}` normalizes the real frame to `A, B < 0 < c, d`.
-/

noncomputable section

namespace Rho5.Shared.XSmallKSigns

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.TraceSigns (signedEntries signedEntries5 signedEntries_apply IsSign)
open Rho5.Shared.V43MatrixRoundTrip

/-- The sign vector flipping the third original row/column (0-based index 2). -/
def mid5 (σ : ℝ) : Fin 5 → ℝ := fun i => if (i : ℕ) = 2 then σ else 1
/-- Its restriction to the first Schur layer. -/
def mid4 (σ : ℝ) : Fin 4 → ℝ := fun i => if (i : ℕ) = 1 then σ else 1
/-- Its restriction to the second Schur layer. -/
def mid3 (σ : ℝ) : Fin 3 → ℝ := fun i => if (i : ℕ) = 0 then σ else 1

theorem isSign_mid5 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (mid5 σ) := by
  intro i; fin_cases i <;> simp [mid5] <;> exact hσ

theorem isSign_mid4 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (mid4 σ) := by
  intro i; fin_cases i <;> simp [mid4] <;> exact hσ

theorem isSign_mid3 {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : IsSign (mid3 σ) := by
  intro i; fin_cases i <;> simp [mid3] <;> exact hσ

theorem mid5_zero (σ : ℝ) : mid5 σ 0 = 1 := by simp [mid5]
theorem mid5_two (σ : ℝ) : mid5 σ 2 = σ := by simp [mid5]
theorem mid4_zero (σ : ℝ) : mid4 σ 0 = 1 := by simp [mid4]
theorem mid4_one (σ : ℝ) : mid4 σ 1 = σ := by simp [mid4]
theorem mid3_zero (σ : ℝ) : mid3 σ 0 = σ := by simp [mid3]
theorem mid3_one (σ : ℝ) : mid3 σ 1 = 1 := by simp [mid3]
theorem mid3_two (σ : ℝ) : mid3 σ 2 = 1 := by simp [mid3]
theorem mid5_succ_eq_mid4 (σ : ℝ) : (fun i : Fin 4 => mid5 σ i.succ) = mid4 σ := by
  funext i; fin_cases i <;> simp [mid5, mid4]
theorem mid4_succ_eq_mid3 (σ : ℝ) : (fun i : Fin 3 => mid4 σ i.succ) = mid3 σ := by
  funext i; fin_cases i <;> simp [mid4, mid3]

/-- The flip as a real matrix operation. -/
def flipMid (σ : ℝ) (M : Matrix5) : Matrix5 := signedEntries M (mid5 σ) (mid5 σ)

theorem flipMid_one (M : Matrix5) : flipMid 1 M = M := by
  ext i j
  simp [flipMid, signedEntries, mid5]

/-! ## 1. Transport through the real Schur chain -/

theorem S4_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0) :
    S4 (flipMid σ M) = signedEntries (S4 M) (mid4 σ) (mid4 σ) := by
  have h := Rho5.TraceSigns.pivotSchur_signedEntries M (isSign_mid5 hσ) (isSign_mid5 hσ) 0 0 h00
  simpa [S4, flipMid, Rho5.LeadingTrace.remainingIndex_zero, mid5_succ_eq_mid4] using h

theorem S3_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) :
    S3 (flipMid σ M) = signedEntries (S3 M) (mid3 σ) (mid3 σ) := by
  have h4 : S4 (flipMid σ M) = signedEntries (S4 M) (mid4 σ) (mid4 σ) := S4_flipMid hσ h00
  have h := Rho5.TraceSigns.pivotSchur_signedEntries (S4 M) (isSign_mid4 hσ) (isSign_mid4 hσ)
    0 0 hp
  simpa [S3, h4, Rho5.LeadingTrace.remainingIndex_zero, mid4_succ_eq_mid3] using h

theorem T2_flipMid {M : Matrix5} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h00 : M 0 0 ≠ 0)
    (hp : S4 M 0 0 ≠ 0) (hk : S3 M 0 0 ≠ 0) :
    T2 (flipMid σ M) = T2 M := by
  have h3 : S3 (flipMid σ M) = signedEntries (S3 M) (mid3 σ) (mid3 σ) := S3_flipMid hσ h00 hp
  have h := Rho5.TraceSigns.pivotSchur_signedEntries (S3 M) (isSign_mid3 hσ) (isSign_mid3 hσ)
    0 0 hk
  have hgoal : T2 (flipMid σ M)
      = signedEntries (T2 M) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := by
    simpa [T2, h3, Rho5.LeadingTrace.remainingIndex_zero,
      show (fun i : Fin 2 => mid3 σ i.succ) = fun _ => (1 : ℝ) from by
        funext i; fin_cases i <;> simp [mid3]] using h
  rw [hgoal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signedEntries]

end Rho5.Shared.XSmallKSigns
