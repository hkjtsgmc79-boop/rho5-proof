import Rho5.Shared.XSmallKBranch.PhysicalBridge
import Rho5.Shared.MainlineTreeCover.V31Batch.Model

/-!
# D148 stage A — the actual matrix point and its lifted model state

`matrixPoint N : Fin 22 → ℝ` is the M02 model point read off the **actual** matrix `N` through
D136's `chartState` (its first 22 coordinates, in the frozen order
`k r w A B c d p e be u0 u1 u2 x0 x1 x2 v0 v1 v2 q0 q1 q2`).

The main fact here is definitional rather than assumed: M02's `Model.liftedPoint` applied to
`matrixPoint N` is exactly D136's `chartState N`, i.e. the 35 shared product slots of the model are
the **actual products** of the actual coordinates in M02's frozen `actualPairs` order.  No free
lifting variable is introduced and no product order is changed.
-/

noncomputable section
namespace Rho5.Shared.XV31ModelEntry

open Rho5
open Rho5.Shared.XSmallKBranch
open Rho5.Shared.MainlineTreeCover
open Rho5.Shared.MainlineTreeCover.V31Batch

/-- The 22 actual model coordinates of a matrix, in the frozen `Model.variableNames` order. -/
def matrixPoint (N : Matrix5) : Fin 22 → ℝ :=
  fun j => chartState N (Fin.castLE (by norm_num) j)

@[simp] theorem matrixPoint_apply (N : Matrix5) (j : Fin 22) :
    matrixPoint N j = chartState N (Fin.castLE (by norm_num) j) := rfl

/-- Componentwise identity with D136's `chartState` on the first 22 indices. -/
theorem matrixPoint_eq_chartState (N : Matrix5) (j : Fin 22) :
    matrixPoint N j = chartState N ⟨j.1, by omega⟩ := rfl

/-! ## The 22 coordinates, by name (all `rfl`, reusing D136's `chartState_k` readings) -/

theorem matrixPoint_0 (N : Matrix5) : matrixPoint N 0 = kk (chartState N) := rfl
theorem matrixPoint_1 (N : Matrix5) : matrixPoint N 1 = rr (chartState N) := rfl
theorem matrixPoint_2 (N : Matrix5) : matrixPoint N 2 = ww (chartState N) := rfl
theorem matrixPoint_3 (N : Matrix5) : matrixPoint N 3 = AA (chartState N) := rfl
theorem matrixPoint_4 (N : Matrix5) : matrixPoint N 4 = BB (chartState N) := rfl
theorem matrixPoint_5 (N : Matrix5) : matrixPoint N 5 = cc (chartState N) := rfl
theorem matrixPoint_6 (N : Matrix5) : matrixPoint N 6 = dd (chartState N) := rfl
theorem matrixPoint_7 (N : Matrix5) : matrixPoint N 7 = pp (chartState N) := rfl
theorem matrixPoint_8 (N : Matrix5) : matrixPoint N 8 = ee (chartState N) := rfl
theorem matrixPoint_9 (N : Matrix5) : matrixPoint N 9 = be (chartState N) := rfl
theorem matrixPoint_10 (N : Matrix5) : matrixPoint N 10 = uu (chartState N) 0 := rfl
theorem matrixPoint_11 (N : Matrix5) : matrixPoint N 11 = uu (chartState N) 1 := rfl
theorem matrixPoint_12 (N : Matrix5) : matrixPoint N 12 = uu (chartState N) 2 := rfl
theorem matrixPoint_13 (N : Matrix5) : matrixPoint N 13 = xx (chartState N) 0 := rfl
theorem matrixPoint_14 (N : Matrix5) : matrixPoint N 14 = xx (chartState N) 1 := rfl
theorem matrixPoint_15 (N : Matrix5) : matrixPoint N 15 = xx (chartState N) 2 := rfl
theorem matrixPoint_16 (N : Matrix5) : matrixPoint N 16 = vv (chartState N) 0 := rfl
theorem matrixPoint_17 (N : Matrix5) : matrixPoint N 17 = vv (chartState N) 1 := rfl
theorem matrixPoint_18 (N : Matrix5) : matrixPoint N 18 = vv (chartState N) 2 := rfl
theorem matrixPoint_19 (N : Matrix5) : matrixPoint N 19 = qq (chartState N) 0 := rfl
theorem matrixPoint_20 (N : Matrix5) : matrixPoint N 20 = qq (chartState N) 1 := rfl
theorem matrixPoint_21 (N : Matrix5) : matrixPoint N 21 = qq (chartState N) 2 := rfl

/-- **The 35 shared product slots are the actual products.**  M02's lifting of `matrixPoint N` is
literally D136's `chartState N` — same 22 coordinates, same `actualPairs` order, real products. -/
theorem liftedPoint_matrixPoint (N : Matrix5) :
    Model.liftedPoint (matrixPoint N) = chartState N := by
  funext i
  rw [Model.liftedPoint, Rho5.Shared.CertificateContraction.liftPoint, Fin.addCases]
  fin_cases i <;>
    simp [Model.actualPairs, matrixPoint, chartState]

/-- Reading the lift back: the first 22 coordinates of the lifted point are `matrixPoint N`. -/
theorem projectPoint_liftedPoint_matrixPoint (N : Matrix5) :
    Rho5.Shared.CertificateContraction.projectPoint (n := 22) (k := 35)
      (Model.liftedPoint (matrixPoint N)) = matrixPoint N :=
  Rho5.Shared.CertificateContraction.project_lift Model.actualPairs (matrixPoint N)

end Rho5.Shared.XV31ModelEntry
