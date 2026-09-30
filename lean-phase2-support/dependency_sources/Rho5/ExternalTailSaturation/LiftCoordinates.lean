import Rho5.ExternalTailSaturation.FullMatrixContraction

/-!
The general same-source lift coordinates, read directly from the actual matrix.
This does not create a second B24 model: no balanced-tail condition is imposed,
and all four vectors and the whole core are tied to the one source M.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.TraceSigns (signedEntries)

def liftE (M : Matrix5) : ℝ := -M 0 1
def liftBeta (M : Matrix5) : ℝ := M 1 0
def liftU (M : Matrix5) (i : Fin 3) : ℝ := M i.succ.succ 0
def liftX (M : Matrix5) (i : Fin 3) : ℝ := S4 M i.succ 0 / p M
def liftV (M : Matrix5) (j : Fin 3) : ℝ := M 0 j.succ.succ
def liftQ (M : Matrix5) (j : Fin 3) : ℝ := S4 M 0 j.succ
/-- General core: unlike the restricted B16.D this has arbitrary bottom-right entry. -/
def liftC (M : Matrix5) (i j : Fin 3) : ℝ := S3 M i j / k M

@[simp] theorem liftE_contract (M : Matrix5) (lam mu : ℝ) :
    liftE (contract M lam mu) = liftE M := by
  simp [liftE, contract, rowFactor, colFactor]
@[simp] theorem liftBeta_contract (M : Matrix5) (lam mu : ℝ) :
    liftBeta (contract M lam mu) = liftBeta M := by
  simp [liftBeta, contract, rowFactor, colFactor]

theorem liftU_contract (M : Matrix5) (lam mu : ℝ) (i : Fin 3) :
    liftU (contract M lam mu) i = factors3 lam 1 i * liftU M i := by
  fin_cases i <;> simp [liftU, contract, rowFactor, colFactor, factors3]

theorem liftX_contract (M : Matrix5) (lam mu : ℝ) (i : Fin 3) :
    liftX (contract M lam mu) i = factors3 lam 1 i * liftX M i := by
  unfold liftX
  rw [p_contract, S4_contract]
  fin_cases i <;> simp [signedEntries, factors4, factors3, div_eq_mul_inv] <;> ring

theorem liftV_contract (M : Matrix5) (lam mu : ℝ) (j : Fin 3) :
    liftV (contract M lam mu) j = factors3 mu 1 j * liftV M j := by
  fin_cases j <;> simp [liftV, contract, rowFactor, colFactor, factors3] <;> ring

theorem liftQ_contract (M : Matrix5) (lam mu : ℝ) (j : Fin 3) :
    liftQ (contract M lam mu) j = factors3 mu 1 j * liftQ M j := by
  unfold liftQ
  rw [S4_contract]
  fin_cases j <;> simp [signedEntries, factors4, factors3] <;> ring

theorem liftC_contract (M : Matrix5) (lam mu : ℝ) (i j : Fin 3) :
    liftC (contract M lam mu) i j = factors3 lam 1 i * liftC M i j * factors3 mu 1 j := by
  unfold liftC
  rw [k_contract, S3_contract]
  simp only [signedEntries, div_eq_mul_inv]
  ring

/-- General complete reconstruction identity for the lower block, read from M. -/
theorem source_lower_block (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0)
    (hk : k M ≠ 0) (i j : Fin 3) :
    M i.succ.succ j.succ.succ =
      k M * liftC M i j + liftX M i * liftQ M j + liftU M i * liftV M j := by
  rw [Rho5.Certificate.B24Extraction.A_block M h00 hp i j]
  unfold liftC liftX liftQ liftU liftV
  field_simp [hp, hk] <;> ring

/-- Both lifted outer products transform together with the same core. -/
theorem complete_lift_contract (M : Matrix5) (lam mu : ℝ) (i j : Fin 3) :
    k (contract M lam mu) * liftC (contract M lam mu) i j +
        liftX (contract M lam mu) i * liftQ (contract M lam mu) j +
        liftU (contract M lam mu) i * liftV (contract M lam mu) j =
      factors3 lam 1 i *
        (k M * liftC M i j + liftX M i * liftQ M j + liftU M i * liftV M j) *
          factors3 mu 1 j := by
  rw [k_contract, liftC_contract, liftX_contract, liftQ_contract, liftU_contract, liftV_contract]
  ring

/-- The px-eu side band transforms with its source row, not with a new witness. -/
theorem row_band_contract (M : Matrix5) (lam mu : ℝ) (i : Fin 3) :
    p (contract M lam mu) * liftX (contract M lam mu) i -
        liftE (contract M lam mu) * liftU (contract M lam mu) i =
      factors3 lam 1 i * (p M * liftX M i - liftE M * liftU M i) := by
  rw [p_contract, liftX_contract, liftE_contract, liftU_contract]
  ring

/-- The q+beta*v side band transforms with its source column. -/
theorem column_band_contract (M : Matrix5) (lam mu : ℝ) (j : Fin 3) :
    liftQ (contract M lam mu) j + liftBeta (contract M lam mu) * liftV (contract M lam mu) j =
      factors3 mu 1 j * (liftQ M j + liftBeta M * liftV M j) := by
  rw [liftQ_contract, liftBeta_contract, liftV_contract]
  ring

end Rho5.ExternalTailSaturation
