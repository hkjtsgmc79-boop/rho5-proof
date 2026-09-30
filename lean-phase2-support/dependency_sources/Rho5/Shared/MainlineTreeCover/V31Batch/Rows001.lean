import Rho5.Shared.MainlineTreeCover.V31Batch.Leaf001
import Rho5.Shared.MainlineTreeCover.V31Batch.GeometryBoxes
import Rho5.Shared.MainlineTreeCover.V31Batch.Model
import Rho5.Shared.MainlineTreeCover.V31Batch.SparseIntegerScaling

/-! Exact selected-row bindings for original C record 11.
Integer dense/sparse identities are kernel-decided; rational normalization is
proved only on the actual sparse contributions. Repeated columns accumulate.
The polynomial row order, McCormick quadrant and current leaf endpoints are
all consumed below as concrete identities, never as source-row assumptions. -/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Rows001
open Rho5.Shared.CertificateContraction
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def selectedId (i : Fin 1) : Fin 246 :=
  ⟨Leaf001.supportIds.getD i.val 0, by fin_cases i <;> decide⟩

theorem row0 (j : Fin 57) :
    Leaf001.rationalSystem.rows 0 j =
      (Model.generatedSystem GeometryBindings.flatBox1).a 21 j := by
  have hd : ∀ j : Fin 57, ([7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf001.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox1 21).terms := by
    change ([(⟨0, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨30, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨39, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((-1600 : ℚ))), (⟨30, by decide⟩, -((-1600 : ℚ))), (⟨39, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox1]
  exact scaled_dense_eq_sparse _ _ Leaf001.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs0 :
    Leaf001.rationalSystem.rhs 0 =
      (Model.generatedSystem GeometryBindings.flatBox1).rhs 21 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox1]

theorem all_rows (i : Fin 1) (j : Fin 57) :
    Leaf001.rationalSystem.rows i j =
      (Model.generatedSystem GeometryBindings.flatBox1).a (selectedId i) j := by
  fin_cases i
  · exact row0 j

theorem all_rhs (i : Fin 1) :
    Leaf001.rationalSystem.rhs i =
      (Model.generatedSystem GeometryBindings.flatBox1).rhs (selectedId i) := by
  fin_cases i
  · exact rhs0

end Rho5.Shared.MainlineTreeCover.V31Batch.Rows001
