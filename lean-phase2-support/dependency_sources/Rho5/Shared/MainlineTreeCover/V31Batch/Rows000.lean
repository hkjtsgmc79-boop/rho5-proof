import Rho5.Shared.MainlineTreeCover.V31Batch.Leaf000
import Rho5.Shared.MainlineTreeCover.V31Batch.GeometryBoxes
import Rho5.Shared.MainlineTreeCover.V31Batch.Model
import Rho5.Shared.MainlineTreeCover.V31Batch.SparseIntegerScaling

/-! Exact selected-row bindings for original C record 10.
Integer dense/sparse identities are kernel-decided; rational normalization is
proved only on the actual sparse contributions. Repeated columns accumulate.
The polynomial row order, McCormick quadrant and current leaf endpoints are
all consumed below as concrete identities, never as source-row assumptions. -/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Rows000
open Rho5.Shared.CertificateContraction
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def selectedId (i : Fin 28) : Fin 246 :=
  ⟨Leaf000.supportIds.getD i.val 0, by fin_cases i <;> decide⟩

theorem row0 (j : Fin 57) :
    Leaf000.rationalSystem.rows 0 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 4 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨7, by decide⟩, 7680000), (⟨46, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨7, by decide⟩, 7680000), (⟨46, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 4).terms := by
    change ([(⟨7, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨46, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨7, by decide⟩, -((-1600 : ℚ))), (⟨46, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs0 :
    Leaf000.rationalSystem.rhs 0 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 4 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row1 (j : Fin 57) :
    Leaf000.rationalSystem.rows 1 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 19 j := by
  have hd : ∀ j : Fin 57, ([7680000, 0, 0, 0, 0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 7680000), (⟨7, by decide⟩, -7680000), (⟨30, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 7680000), (⟨7, by decide⟩, -7680000), (⟨30, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 19).terms := by
    change ([(⟨0, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨7, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨30, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((-1600 : ℚ))), (⟨7, by decide⟩, -((1600 : ℚ))), (⟨30, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs1 :
    Leaf000.rationalSystem.rhs 1 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 19 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox0]

theorem row2 (j : Fin 57) :
    Leaf000.rationalSystem.rows 2 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 21 j := by
  have hd : ∀ j : Fin 57, ([7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 21).terms := by
    change ([(⟨0, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨30, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨39, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((-1600 : ℚ))), (⟨30, by decide⟩, -((-1600 : ℚ))), (⟨39, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs2 :
    Leaf000.rationalSystem.rhs 2 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 21 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row3 (j : Fin 57) :
    Leaf000.rationalSystem.rows 3 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 24 j := by
  have hd : ∀ j : Fin 57, ([-7680000, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, -7680000), (⟨3, by decide⟩, -7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, -7680000), (⟨3, by decide⟩, -7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 24).terms := by
    change ([(⟨0, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨3, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((1600 : ℚ))), (⟨3, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs3 :
    Leaf000.rationalSystem.rhs 3 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 24 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox0]

theorem row4 (j : Fin 57) :
    Leaf000.rationalSystem.rows 4 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 63 j := by
  have hd : ∀ j : Fin 57, ([0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, 7680000), (⟨25, by decide⟩, 1600), (⟨34, by decide⟩, 1600), (⟨51, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, 7680000), (⟨25, by decide⟩, 1600), (⟨34, by decide⟩, 1600), (⟨51, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 63).terms := by
    change ([(⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨25, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨34, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨51, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((-1600 : ℚ))), (⟨25, by decide⟩, -((-1600 : ℚ))), (⟨34, by decide⟩, -((-1600 : ℚ))), (⟨51, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs4 :
    Leaf000.rationalSystem.rhs 4 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 63 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row5 (j : Fin 57) :
    Leaf000.rationalSystem.rows 5 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 76 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨21, by decide⟩, -7680000), (⟨40, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨21, by decide⟩, -7680000), (⟨40, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 76).terms := by
    change ([(⟨21, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨40, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨21, by decide⟩, -((1600 : ℚ))), (⟨40, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs5 :
    Leaf000.rationalSystem.rhs 5 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 76 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row6 (j : Fin 57) :
    Leaf000.rationalSystem.rows 6 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 81 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨24, by decide⟩, 1600), (⟨33, by decide⟩, 1600), (⟨55, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨24, by decide⟩, 1600), (⟨33, by decide⟩, 1600), (⟨55, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 81).terms := by
    change ([(⟨24, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨33, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨55, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨24, by decide⟩, -((-1600 : ℚ))), (⟨33, by decide⟩, -((-1600 : ℚ))), (⟨55, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs6 :
    Leaf000.rationalSystem.rhs 6 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 81 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row7 (j : Fin 57) :
    Leaf000.rationalSystem.rows 7 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 87 j := by
  have hd : ∀ j : Fin 57, ([0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, 7680000), (⟨23, by decide⟩, 1600), (⟨32, by decide⟩, 1600), (⟨52, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, 7680000), (⟨23, by decide⟩, 1600), (⟨32, by decide⟩, 1600), (⟨52, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 87).terms := by
    change ([(⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨23, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨32, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨52, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((-1600 : ℚ))), (⟨23, by decide⟩, -((-1600 : ℚ))), (⟨32, by decide⟩, -((-1600 : ℚ))), (⟨52, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs7 :
    Leaf000.rationalSystem.rhs 7 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 87 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row8 (j : Fin 57) :
    Leaf000.rationalSystem.rows 8 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 90 j := by
  have hd : ∀ j : Fin 57, ([-7680000, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, -7680000), (⟨2, by decide⟩, -7680000), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, -7680000), (⟨2, by decide⟩, -7680000), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 90).terms := by
    change ([(⟨0, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨50, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((1600 : ℚ))), (⟨2, by decide⟩, -((1600 : ℚ))), (⟨50, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs8 :
    Leaf000.rationalSystem.rhs 8 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 90 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox0]

theorem row9 (j : Fin 57) :
    Leaf000.rationalSystem.rows 9 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 94 j := by
  have hd : ∀ j : Fin 57, ([0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨2, by decide⟩, -7680000), (⟨22, by decide⟩, -1600), (⟨31, by decide⟩, -1600), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨2, by decide⟩, -7680000), (⟨22, by decide⟩, -1600), (⟨31, by decide⟩, -1600), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 94).terms := by
    change ([(⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨22, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000), (⟨31, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000), (⟨50, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨2, by decide⟩, -((1600 : ℚ))), (⟨22, by decide⟩, -((1600 : ℚ))), (⟨31, by decide⟩, -((1600 : ℚ))), (⟨50, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs9 :
    Leaf000.rationalSystem.rhs 9 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 94 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row10 (j : Fin 57) :
    Leaf000.rationalSystem.rows 10 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 95 j := by
  have hd : ∀ j : Fin 57, ([0, -7680000, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, -7680000), (⟨2, by decide⟩, 7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, -7680000), (⟨2, by decide⟩, 7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 95).terms := by
    change ([(⟨1, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((1600 : ℚ))), (⟨2, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs10 :
    Leaf000.rationalSystem.rhs 10 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 95 := by
  change (-152340480000 : ℚ) / 23040000 = (-6612 : ℚ) + 0
  norm_num [GeometryBindings.flatBox0]

theorem row11 (j : Fin 57) :
    Leaf000.rationalSystem.rows 11 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 104 j := by
  have hd : ∀ j : Fin 57, ([-15360000, 7680000, -7680000, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, -15360000), (⟨1, by decide⟩, 7680000), (⟨2, by decide⟩, -7680000), (⟨4, by decide⟩, 7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, -15360000), (⟨1, by decide⟩, 7680000), (⟨2, by decide⟩, -7680000), (⟨4, by decide⟩, 7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 104).terms := by
    change ([(⟨0, by decide⟩, ((-15360000 : ℚ) * 4800) / 23040000), (⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨4, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((3200 : ℚ))), (⟨1, by decide⟩, -((-1600 : ℚ))), (⟨2, by decide⟩, -((1600 : ℚ))), (⟨4, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs11 :
    Leaf000.rationalSystem.rhs 11 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 104 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox0]

theorem row12 (j : Fin 57) :
    Leaf000.rationalSystem.rows 12 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 108 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨15, by decide⟩, 0), (⟨21, by decide⟩, 4800), (⟨22, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨15, by decide⟩, 0), (⟨21, by decide⟩, 4800), (⟨22, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 108).terms := by
    change ([(⟨15, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨21, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨22, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨15, by decide⟩, -(GeometryBindings.flatBox0.hi ⟨21, by decide⟩)), (⟨21, by decide⟩, -(GeometryBindings.flatBox0.lo ⟨15, by decide⟩)), (⟨22, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs12 :
    Leaf000.rationalSystem.rhs 12 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 108 := by
  change (0 : ℚ) / 23040000 = -(GeometryBindings.flatBox0.lo ⟨15, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨21, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row13 (j : Fin 57) :
    Leaf000.rationalSystem.rows 13 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 145 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, 4800), (⟨18, by decide⟩, 0), (⟨31, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, 4800), (⟨18, by decide⟩, 0), (⟨31, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 145).terms := by
    change ([(⟨12, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨31, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, -(GeometryBindings.flatBox0.lo ⟨18, by decide⟩)), (⟨18, by decide⟩, -(GeometryBindings.flatBox0.hi ⟨12, by decide⟩)), (⟨31, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs13 :
    Leaf000.rationalSystem.rhs 13 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 145 := by
  change (0 : ℚ) / 23040000 = -(GeometryBindings.flatBox0.hi ⟨12, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row14 (j : Fin 57) :
    Leaf000.rationalSystem.rows 14 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 147 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, 4800), (⟨17, by decide⟩, 0), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, 4800), (⟨17, by decide⟩, 0), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 147).terms := by
    change ([(⟨12, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨17, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨32, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, (GeometryBindings.flatBox0.hi ⟨17, by decide⟩)), (⟨17, by decide⟩, (GeometryBindings.flatBox0.hi ⟨12, by decide⟩)), (⟨32, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs14 :
    Leaf000.rationalSystem.rhs 14 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 147 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨12, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨17, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row15 (j : Fin 57) :
    Leaf000.rationalSystem.rows 15 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 150 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, -4800), (⟨16, by decide⟩, -4800), (⟨33, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, -4800), (⟨16, by decide⟩, -4800), (⟨33, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 150).terms := by
    change ([(⟨12, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨16, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨33, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, (GeometryBindings.flatBox0.lo ⟨16, by decide⟩)), (⟨16, by decide⟩, (GeometryBindings.flatBox0.lo ⟨12, by decide⟩)), (⟨33, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs15 :
    Leaf000.rationalSystem.rhs 15 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 150 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox0.lo ⟨12, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨16, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row16 (j : Fin 57) :
    Leaf000.rationalSystem.rows 16 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 154 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨11, by decide⟩, -4800), (⟨18, by decide⟩, 0), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨11, by decide⟩, -4800), (⟨18, by decide⟩, 0), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 154).terms := by
    change ([(⟨11, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨34, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨11, by decide⟩, (GeometryBindings.flatBox0.lo ⟨18, by decide⟩)), (⟨18, by decide⟩, (GeometryBindings.flatBox0.lo ⟨11, by decide⟩)), (⟨34, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs16 :
    Leaf000.rationalSystem.rhs 16 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 154 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox0.lo ⟨11, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row17 (j : Fin 57) :
    Leaf000.rationalSystem.rows 17 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 155 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨11, by decide⟩, 4800), (⟨18, by decide⟩, 4800), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨11, by decide⟩, 4800), (⟨18, by decide⟩, 4800), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 155).terms := by
    change ([(⟨11, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨34, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨11, by decide⟩, (GeometryBindings.flatBox0.hi ⟨18, by decide⟩)), (⟨18, by decide⟩, (GeometryBindings.flatBox0.hi ⟨11, by decide⟩)), (⟨34, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs17 :
    Leaf000.rationalSystem.rhs 17 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 155 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨11, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row18 (j : Fin 57) :
    Leaf000.rationalSystem.rows 18 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 162 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨11, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨36, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨11, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨36, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 162).terms := by
    change ([(⟨11, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨16, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨36, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨11, by decide⟩, (GeometryBindings.flatBox0.lo ⟨16, by decide⟩)), (⟨16, by decide⟩, (GeometryBindings.flatBox0.lo ⟨11, by decide⟩)), (⟨36, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs18 :
    Leaf000.rationalSystem.rhs 18 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 162 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox0.lo ⟨11, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨16, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row19 (j : Fin 57) :
    Leaf000.rationalSystem.rows 19 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 175 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨10, by decide⟩, 0), (⟨16, by decide⟩, 4800), (⟨39, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨10, by decide⟩, 0), (⟨16, by decide⟩, 4800), (⟨39, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 175).terms := by
    change ([(⟨10, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨16, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨39, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨10, by decide⟩, (GeometryBindings.flatBox0.hi ⟨16, by decide⟩)), (⟨16, by decide⟩, (GeometryBindings.flatBox0.hi ⟨10, by decide⟩)), (⟨39, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs19 :
    Leaf000.rationalSystem.rhs 19 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 175 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨10, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨16, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row20 (j : Fin 57) :
    Leaf000.rationalSystem.rows 20 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 181 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨9, by decide⟩, 4800), (⟨18, by decide⟩, -4800), (⟨40, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨9, by decide⟩, 4800), (⟨18, by decide⟩, -4800), (⟨40, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 181).terms := by
    change ([(⟨9, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨40, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨9, by decide⟩, -(GeometryBindings.flatBox0.lo ⟨18, by decide⟩)), (⟨18, by decide⟩, -(GeometryBindings.flatBox0.hi ⟨9, by decide⟩)), (⟨40, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs20 :
    Leaf000.rationalSystem.rhs 20 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 181 := by
  change (23040000 : ℚ) / 23040000 = -(GeometryBindings.flatBox0.hi ⟨9, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row21 (j : Fin 57) :
    Leaf000.rationalSystem.rows 21 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 205 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, -159, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨8, by decide⟩, -159), (⟨9, by decide⟩, -4800), (⟨46, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨8, by decide⟩, -159), (⟨9, by decide⟩, -4800), (⟨46, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 205).terms := by
    change ([(⟨8, by decide⟩, ((-159 : ℚ) * 4800) / 23040000), (⟨9, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨46, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨8, by decide⟩, -(GeometryBindings.flatBox0.lo ⟨9, by decide⟩)), (⟨9, by decide⟩, -(GeometryBindings.flatBox0.hi ⟨8, by decide⟩)), (⟨46, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs21 :
    Leaf000.rationalSystem.rhs 21 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 205 := by
  change (-763200 : ℚ) / 23040000 = -(GeometryBindings.flatBox0.hi ⟨8, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨9, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row22 (j : Fin 57) :
    Leaf000.rationalSystem.rows 22 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 221 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, -318, 0, 636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨4, by decide⟩, -318), (⟨6, by decide⟩, 636), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨4, by decide⟩, -318), (⟨6, by decide⟩, 636), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 221).terms := by
    change ([(⟨4, by decide⟩, ((-318 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((636 : ℚ) * 4800) / 23040000), (⟨50, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨4, by decide⟩, -(GeometryBindings.flatBox0.lo ⟨6, by decide⟩)), (⟨6, by decide⟩, -(GeometryBindings.flatBox0.hi ⟨4, by decide⟩)), (⟨50, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs22 :
    Leaf000.rationalSystem.rhs 22 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 221 := by
  change (202248 : ℚ) / 23040000 = -(GeometryBindings.flatBox0.hi ⟨4, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row23 (j : Fin 57) :
    Leaf000.rationalSystem.rows 23 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 223 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 4800, -636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨4, by decide⟩, 4800), (⟨5, by decide⟩, -636), (⟨51, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨4, by decide⟩, 4800), (⟨5, by decide⟩, -636), (⟨51, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 223).terms := by
    change ([(⟨4, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨5, by decide⟩, ((-636 : ℚ) * 4800) / 23040000), (⟨51, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨4, by decide⟩, (GeometryBindings.flatBox0.hi ⟨5, by decide⟩)), (⟨5, by decide⟩, (GeometryBindings.flatBox0.hi ⟨4, by decide⟩)), (⟨51, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs23 :
    Leaf000.rationalSystem.rhs 23 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 223 := by
  change (-3052800 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨4, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨5, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row24 (j : Fin 57) :
    Leaf000.rationalSystem.rows 24 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 226 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 318, 0, 0, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨3, by decide⟩, 318), (⟨6, by decide⟩, -9600), (⟨52, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨3, by decide⟩, 318), (⟨6, by decide⟩, -9600), (⟨52, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 226).terms := by
    change ([(⟨3, by decide⟩, ((318 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((-9600 : ℚ) * 4800) / 23040000), (⟨52, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨3, by decide⟩, (GeometryBindings.flatBox0.lo ⟨6, by decide⟩)), (⟨6, by decide⟩, (GeometryBindings.flatBox0.lo ⟨3, by decide⟩)), (⟨52, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs24 :
    Leaf000.rationalSystem.rhs 24 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 226 := by
  change (-3052800 : ℚ) / 23040000 = (GeometryBindings.flatBox0.lo ⟨3, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row25 (j : Fin 57) :
    Leaf000.rationalSystem.rows 25 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 238 j := by
  have hd : ∀ j : Fin 57, ([318, 0, 0, 0, 0, 0, 8816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 318), (⟨6, by decide⟩, 8816), (⟨55, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 318), (⟨6, by decide⟩, 8816), (⟨55, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 238).terms := by
    change ([(⟨0, by decide⟩, ((318 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((8816 : ℚ) * 4800) / 23040000), (⟨55, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, (GeometryBindings.flatBox0.lo ⟨6, by decide⟩)), (⟨6, by decide⟩, (GeometryBindings.flatBox0.lo ⟨0, by decide⟩)), (⟨55, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs25 :
    Leaf000.rationalSystem.rhs 25 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 238 := by
  change (2803488 : ℚ) / 23040000 = (GeometryBindings.flatBox0.lo ⟨0, by decide⟩) * (GeometryBindings.flatBox0.lo ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row26 (j : Fin 57) :
    Leaf000.rationalSystem.rows 26 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 239 j := by
  have hd : ∀ j : Fin 57, ([4482, 0, 0, 0, 0, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 4482), (⟨6, by decide⟩, 9600), (⟨55, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 4482), (⟨6, by decide⟩, 9600), (⟨55, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 239).terms := by
    change ([(⟨0, by decide⟩, ((4482 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨55, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, (GeometryBindings.flatBox0.hi ⟨6, by decide⟩)), (⟨6, by decide⟩, (GeometryBindings.flatBox0.hi ⟨0, by decide⟩)), (⟨55, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs26 :
    Leaf000.rationalSystem.rhs 26 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 239 := by
  change (43027200 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨0, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem row27 (j : Fin 57) :
    Leaf000.rationalSystem.rows 27 j =
      (Model.generatedSystem GeometryBindings.flatBox0).a 243 j := by
  have hd : ∀ j : Fin 57, ([4800, 0, 0, 0, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 4800), (⟨5, by decide⟩, 9600), (⟨56, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 4800), (⟨5, by decide⟩, 9600), (⟨56, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf000.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox0 243).terms := by
    change ([(⟨0, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨5, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨56, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, (GeometryBindings.flatBox0.hi ⟨5, by decide⟩)), (⟨5, by decide⟩, (GeometryBindings.flatBox0.hi ⟨0, by decide⟩)), (⟨56, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox0]
  exact scaled_dense_eq_sparse _ _ Leaf000.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs27 :
    Leaf000.rationalSystem.rhs 27 =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs 243 := by
  change (46080000 : ℚ) / 23040000 = (GeometryBindings.flatBox0.hi ⟨0, by decide⟩) * (GeometryBindings.flatBox0.hi ⟨5, by decide⟩)
  norm_num [GeometryBindings.flatBox0]

theorem all_rows (i : Fin 28) (j : Fin 57) :
    Leaf000.rationalSystem.rows i j =
      (Model.generatedSystem GeometryBindings.flatBox0).a (selectedId i) j := by
  fin_cases i
  · exact row0 j
  · exact row1 j
  · exact row2 j
  · exact row3 j
  · exact row4 j
  · exact row5 j
  · exact row6 j
  · exact row7 j
  · exact row8 j
  · exact row9 j
  · exact row10 j
  · exact row11 j
  · exact row12 j
  · exact row13 j
  · exact row14 j
  · exact row15 j
  · exact row16 j
  · exact row17 j
  · exact row18 j
  · exact row19 j
  · exact row20 j
  · exact row21 j
  · exact row22 j
  · exact row23 j
  · exact row24 j
  · exact row25 j
  · exact row26 j
  · exact row27 j

theorem all_rhs (i : Fin 28) :
    Leaf000.rationalSystem.rhs i =
      (Model.generatedSystem GeometryBindings.flatBox0).rhs (selectedId i) := by
  fin_cases i
  · exact rhs0
  · exact rhs1
  · exact rhs2
  · exact rhs3
  · exact rhs4
  · exact rhs5
  · exact rhs6
  · exact rhs7
  · exact rhs8
  · exact rhs9
  · exact rhs10
  · exact rhs11
  · exact rhs12
  · exact rhs13
  · exact rhs14
  · exact rhs15
  · exact rhs16
  · exact rhs17
  · exact rhs18
  · exact rhs19
  · exact rhs20
  · exact rhs21
  · exact rhs22
  · exact rhs23
  · exact rhs24
  · exact rhs25
  · exact rhs26
  · exact rhs27

end Rho5.Shared.MainlineTreeCover.V31Batch.Rows000
