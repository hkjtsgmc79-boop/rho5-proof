import Rho5.Shared.XV31ModelEntry.Coordinates
import Rho5.Shared.XSmallKBranch.SourceSystem

/-!
# D148 stage A — the 106 actual source rows

D136's `RowProp i (chartState N)` is the LP semantics of the `i`-th original V31 source row on the
lifted state.  M02's `Model.SameSource x` asks for the 106 **original polynomial** non-negativities
on the 22-dimensional point `x`, with the shared products rebuilt from `Model.actualPairs`.

This module proves, row by row (all 106, including `96/Fcore` and `98/det3`):

* `rowProp_iff_toRow` — D136's row semantics is exactly C03's sparse row of M02's integer basis;
* `eval_nonneg_of_rowProp` — hence the original polynomial is non-negative (via C03's
  `quadratic_row_identity` and the `liftedPoint` identity of `Coordinates.lean`);
* `sameSource_of_rows` / `sameSource_of_satFrame` — `Model.SameSource (matrixPoint N)`.

Nothing is assumed about `SameSource` itself: it is the conclusion, and the two matrix rows are the
ones D136 already paid.
-/

noncomputable section
namespace Rho5.Shared.XV31ModelEntry

open Rho5
open Rho5.Shared.XSmallKBranch
open Rho5.Shared.V43MatrixRoundTrip
open Rho5.Shared.MainlineTreeCover
open Rho5.Shared.MainlineTreeCover.V31Batch
open Rho5.Shared.CertificateContraction

/-- Every index below 106 is either in D136's `paidIdx` or one of the two matrix rows 96/98. -/
theorem mem_paidIdx_or_matrix (i : Fin 106) : i.val ∈ paidIdx ∨ i.val = 96 ∨ i.val = 98 := by
  fin_cases i <;> decide

/-- **Row agreement.**  D136's `RowProp` on the lifted state is literally C03's sparse row built
from M02's integer basis (same index, same coefficients up to the proven positive `1600`). -/
theorem rowProp_iff_toRow (i : Fin 106) (z : Z) :
    RowProp i.val z ↔ (Model.integerPolynomials i).toRow.Holds z := by
  fin_cases i <;>
    simp only [RowProp, Model.integerPolynomials, QPolynomial.toRow, SparseRow.Holds, sparseEval,
      List.map_cons, List.map_nil] <;>
    norm_num <;>
    constructor <;> intro h <;> · simp at h ⊢; linarith

/-- **One row, paid.**  D136's row semantics at the actual state gives the non-negativity of M02's
original polynomial at the actual 22-dimensional point. -/
theorem eval_nonneg_of_rowProp {N : Matrix5} (i : Fin 106) (h : RowProp i.val (chartState N)) :
    0 ≤ (Model.polynomials i).eval Model.actualPairs (matrixPoint N) := by
  have hrow : (Model.integerPolynomials i).toRow.Holds (chartState N) :=
    (rowProp_iff_toRow i (chartState N)).mp h
  have hlift : Rho5.Shared.CertificateContraction.liftPoint Model.actualPairs (matrixPoint N) =
      chartState N := liftedPoint_matrixPoint N
  rw [← hlift] at hrow
  unfold SparseRow.Holds at hrow
  rw [quadratic_row_identity Model.actualPairs (Model.integerPolynomials i) (matrixPoint N)] at hrow
  have hnonneg : 0 ≤ (Model.integerPolynomials i).eval Model.actualPairs (matrixPoint N) := by
    linarith
  rw [Model.polynomial_eval_eq_integer_div]
  linarith

/-- **The 106-row bridge.**  D136's already-paid rows (104 frozen + `96/Fcore` + `98/det3`) give
M02's actual `SameSource` at the actual matrix point. -/
theorem sameSource_of_rows {N : Matrix5}
    (hrows : ∀ i, i ∈ paidIdx ∨ i = 96 ∨ i = 98 → RowProp i (chartState N)) :
    Model.SameSource (matrixPoint N) := by
  intro r
  exact eval_nonneg_of_rowProp r (hrows r.val (mem_paidIdx_or_matrix r))

/-- **Convenience interface under D136's own explicit premises.**  With D136's inputs
(`NormalizedSigns`, `PosSigns`, `0 ≤ u₀`, `HighValue`, `k ≤ 2`) the source system is D136's
`sourceSystem_of_satFrame`, and its rows give `SameSource` on the actual point. -/
theorem sameSource_of_satFrame (N : Matrix5) (h : SatFrame N)
    (hs : NormalizedSigns (chartState N)) (hpos : PosSigns (chartState N))
    (hu0 : 0 ≤ uu (chartState N) 0) (hF : HighValue (chartState N))
    (hk2 : SmallThirdPivot (chartState N)) :
    Model.SameSource (matrixPoint N) :=
  sameSource_of_rows (sourceSystem_of_satFrame N h hs hpos hu0 hF hk2).rows

end Rho5.Shared.XV31ModelEntry
