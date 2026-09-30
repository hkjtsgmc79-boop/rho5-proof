import Rho5.Shared.V43MatrixRoundTrip
import Rho5.Shared.TailTransposeOrder
import Mathlib.Tactic.Linarith

/-!
# D145 — the original X strict high-r source: coordinates, domain, real transpose

Stage A of the V34 high-r intake.  Everything is stated on the **actual** X22 point
`extractX M` of D119's accepted matrix/X round trip (`k,r,w,A,B,c,d,p,e,beta,u,x,v,q`), and on
the **actual** matrix transpose.  Nothing here assumes the two high diagrams' rows: they are
Stage B.

Key coordinate discipline (card): the high-value reading is the frozen height
`Rho5.LocalAnalysis.height x = x 1 - x 2 = r - w`, **not** a `2r` reading.

The real high-branch transpose of `TRANSPOSE_INTERFACE.md` is `Q J0 M^T J0 Q` with
`J0 = diag(1,-1,1,1,1)`, `Q = diag(1,1,1,-1,-1)`.  Since `Q` and `J0` are diagonal they commute,
so the whole transform is the single diagonal conjugation `D M^T D` with
`D = Q * J0 = diag(1,-1,1,-1,-1)`; `transX` below is its closed entry form
`(transX M) i j = D i * M j i * D j`.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5

abbrev M5 := Rho5.Matrix5
abbrev X := Rho5.LocalAnalysis.X

open Rho5.Shared.V43MatrixRoundTrip

/-- The V34 high-branch high-value target `gamma = 4132517/1000000`. -/
def gamma : ℝ := 4132517 / 1000000

/-- `J0 = diag(1,-1,1,1,1)`. -/
def sgnJ (i : Fin 5) : ℝ := if (i : ℕ) = 1 then -1 else 1

/-- `Q = diag(1,1,1,-1,-1)`. -/
def sgnQ (i : Fin 5) : ℝ := if (i : ℕ) = 3 ∨ (i : ℕ) = 4 then -1 else 1

/-- `D = Q * J0 = diag(1,-1,1,-1,-1)`. -/
def sgnD (i : Fin 5) : ℝ := sgnQ i * sgnJ i

/-- `Z = diag(1,-1,-1)` on the three-index (the native transform's block signs). -/
def sgnZ (i : Fin 3) : ℝ := if (i : ℕ) = 0 then 1 else -1

/-- **The real high-branch transpose** `Q J0 M^T J0 Q`, in closed entry form. -/
def transX (M : M5) : M5 := fun i j => sgnD i * M j i * sgnD j

/-! ## The domains (actual, strict) and the closed outer box -/

/-- The high-branch sign datum actually used by the two high models
(`A,B ≤ 0 ≤ c,d`); the strict versions are the source's own signs. -/
def HighRSigns (x : X) : Prop := x 3 ≤ 0 ∧ x 4 ≤ 0 ∧ 0 ≤ x 5 ∧ 0 ≤ x 6

/-- **The actual strict high-r domain**: `2 < k ≤ 21/10`, `r > k`, `F = height ≥ gamma`. -/
def HighRDomain (x : X) : Prop :=
  2 < x 0 ∧ x 0 ≤ 21 / 10 ∧ x 0 < x 1 ∧ gamma ≤ Rho5.LocalAnalysis.height x

/-- The **closed outer box** the models are compiled with (`2 ≤ k`, `k ≤ r`): it contains the
actual domain but does not by itself give any `r = k` source high-branch qualification. -/
def HighRClosedDomain (x : X) : Prop :=
  2 ≤ x 0 ∧ x 0 ≤ 21 / 10 ∧ x 0 ≤ x 1 ∧ gamma ≤ Rho5.LocalAnalysis.height x

/-- The real head product `G = e * u0` of the actual source. -/
def Ghead (M : M5) : ℝ := eX M * uX M 0

/-- The same product read on the transposed source: `e_new * u0_new = beta * v0`. -/
def GheadTranspose (M : M5) : ℝ := betaX M * vX M 0

end

end Rho5.Shared.XHighRSource
