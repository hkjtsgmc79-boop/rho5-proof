import Rho5.Shared.MainlineTreeCover.V31Batch.Leaf004
import Rho5.Shared.MainlineTreeCover.V31Batch.GeometryBoxes
import Rho5.Shared.MainlineTreeCover.V31Batch.Model
import Rho5.Shared.MainlineTreeCover.V31Batch.SparseIntegerScaling

/-! Exact selected-row bindings for original C record 16.
Integer dense/sparse identities are kernel-decided; rational normalization is
proved only on the actual sparse contributions. Repeated columns accumulate.
The polynomial row order, McCormick quadrant and current leaf endpoints are
all consumed below as concrete identities, never as source-row assumptions. -/
namespace Rho5.Shared.MainlineTreeCover.V31Batch.Rows004
open Rho5.Shared.CertificateContraction
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def selectedId (i : Fin 33) : Fin 246 :=
  ⟨Leaf004.supportIds.getD i.val 0, by fin_cases i <;> decide⟩

theorem row0 (j : Fin 57) :
    Leaf004.rationalSystem.rows 0 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 2 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨9, by decide⟩, 7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨9, by decide⟩, 7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 2).terms := by
    change ([(⟨9, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨9, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs0 :
    Leaf004.rationalSystem.rhs 0 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 2 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row1 (j : Fin 57) :
    Leaf004.rationalSystem.rows 1 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 4 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨7, by decide⟩, 7680000), (⟨46, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨7, by decide⟩, 7680000), (⟨46, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 4).terms := by
    change ([(⟨7, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨46, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨7, by decide⟩, -((-1600 : ℚ))), (⟨46, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs1 :
    Leaf004.rationalSystem.rhs 1 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 4 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row2 (j : Fin 57) :
    Leaf004.rationalSystem.rows 2 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 15 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨45, by decide⟩, 1600), (⟨49, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨45, by decide⟩, 1600), (⟨49, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 15).terms := by
    change ([(⟨45, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨49, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨45, by decide⟩, -((-1600 : ℚ))), (⟨49, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs2 :
    Leaf004.rationalSystem.rhs 2 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 15 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row3 (j : Fin 57) :
    Leaf004.rationalSystem.rows 3 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 19 j := by
  have hd : ∀ j : Fin 57, ([7680000, 0, 0, 0, 0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 7680000), (⟨7, by decide⟩, -7680000), (⟨30, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 7680000), (⟨7, by decide⟩, -7680000), (⟨30, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 19).terms := by
    change ([(⟨0, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨7, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨30, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((-1600 : ℚ))), (⟨7, by decide⟩, -((1600 : ℚ))), (⟨30, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs3 :
    Leaf004.rationalSystem.rhs 3 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 19 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox4]

theorem row4 (j : Fin 57) :
    Leaf004.rationalSystem.rows 4 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 21 j := by
  have hd : ∀ j : Fin 57, ([7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 7680000), (⟨30, by decide⟩, 1600), (⟨39, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 21).terms := by
    change ([(⟨0, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨30, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨39, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((-1600 : ℚ))), (⟨30, by decide⟩, -((-1600 : ℚ))), (⟨39, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs4 :
    Leaf004.rationalSystem.rhs 4 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 21 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row5 (j : Fin 57) :
    Leaf004.rationalSystem.rows 5 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 28 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨3, by decide⟩, -7680000), (⟨29, by decide⟩, -1600), (⟨38, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨3, by decide⟩, -7680000), (⟨29, by decide⟩, -1600), (⟨38, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 28).terms := by
    change ([(⟨3, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨29, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000), (⟨38, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨3, by decide⟩, -((1600 : ℚ))), (⟨29, by decide⟩, -((1600 : ℚ))), (⟨38, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs5 :
    Leaf004.rationalSystem.rhs 5 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 28 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row6 (j : Fin 57) :
    Leaf004.rationalSystem.rows 6 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 51 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨27, by decide⟩, 1600), (⟨36, by decide⟩, 1600), (⟨56, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨27, by decide⟩, 1600), (⟨36, by decide⟩, 1600), (⟨56, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 51).terms := by
    change ([(⟨27, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨36, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨56, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨27, by decide⟩, -((-1600 : ℚ))), (⟨36, by decide⟩, -((-1600 : ℚ))), (⟨56, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs6 :
    Leaf004.rationalSystem.rhs 6 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 51 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row7 (j : Fin 57) :
    Leaf004.rationalSystem.rows 7 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 63 j := by
  have hd : ∀ j : Fin 57, ([0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, 7680000), (⟨25, by decide⟩, 1600), (⟨34, by decide⟩, 1600), (⟨51, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, 7680000), (⟨25, by decide⟩, 1600), (⟨34, by decide⟩, 1600), (⟨51, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 63).terms := by
    change ([(⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨25, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨34, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨51, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((-1600 : ℚ))), (⟨25, by decide⟩, -((-1600 : ℚ))), (⟨34, by decide⟩, -((-1600 : ℚ))), (⟨51, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs7 :
    Leaf004.rationalSystem.rhs 7 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 63 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row8 (j : Fin 57) :
    Leaf004.rationalSystem.rows 8 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 74 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨43, by decide⟩, 1600), (⟨47, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨43, by decide⟩, 1600), (⟨47, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 74).terms := by
    change ([(⟨43, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨47, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨43, by decide⟩, -((-1600 : ℚ))), (⟨47, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs8 :
    Leaf004.rationalSystem.rhs 8 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 74 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row9 (j : Fin 57) :
    Leaf004.rationalSystem.rows 9 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 87 j := by
  have hd : ∀ j : Fin 57, ([0, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1600, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, 7680000), (⟨23, by decide⟩, 1600), (⟨32, by decide⟩, 1600), (⟨52, by decide⟩, 1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, 7680000), (⟨23, by decide⟩, 1600), (⟨32, by decide⟩, 1600), (⟨52, by decide⟩, 1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 87).terms := by
    change ([(⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨23, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨32, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000), (⟨52, by decide⟩, ((1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((-1600 : ℚ))), (⟨23, by decide⟩, -((-1600 : ℚ))), (⟨32, by decide⟩, -((-1600 : ℚ))), (⟨52, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs9 :
    Leaf004.rationalSystem.rhs 9 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 87 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row10 (j : Fin 57) :
    Leaf004.rationalSystem.rows 10 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 90 j := by
  have hd : ∀ j : Fin 57, ([-7680000, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, -7680000), (⟨2, by decide⟩, -7680000), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, -7680000), (⟨2, by decide⟩, -7680000), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 90).terms := by
    change ([(⟨0, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨50, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((1600 : ℚ))), (⟨2, by decide⟩, -((1600 : ℚ))), (⟨50, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs10 :
    Leaf004.rationalSystem.rhs 10 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 90 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox4]

theorem row11 (j : Fin 57) :
    Leaf004.rationalSystem.rows 11 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 94 j := by
  have hd : ∀ j : Fin 57, ([0, 0, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1600, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨2, by decide⟩, -7680000), (⟨22, by decide⟩, -1600), (⟨31, by decide⟩, -1600), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨2, by decide⟩, -7680000), (⟨22, by decide⟩, -1600), (⟨31, by decide⟩, -1600), (⟨50, by decide⟩, -1600)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 94).terms := by
    change ([(⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨22, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000), (⟨31, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000), (⟨50, by decide⟩, ((-1600 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨2, by decide⟩, -((1600 : ℚ))), (⟨22, by decide⟩, -((1600 : ℚ))), (⟨31, by decide⟩, -((1600 : ℚ))), (⟨50, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs11 :
    Leaf004.rationalSystem.rhs 11 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 94 := by
  change (36864000000 : ℚ) / 23040000 = (1600 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row12 (j : Fin 57) :
    Leaf004.rationalSystem.rows 12 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 95 j := by
  have hd : ∀ j : Fin 57, ([0, -7680000, 7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨1, by decide⟩, -7680000), (⟨2, by decide⟩, 7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨1, by decide⟩, -7680000), (⟨2, by decide⟩, 7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 95).terms := by
    change ([(⟨1, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨1, by decide⟩, -((1600 : ℚ))), (⟨2, by decide⟩, -((-1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs12 :
    Leaf004.rationalSystem.rhs 12 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 95 := by
  change (-152340480000 : ℚ) / 23040000 = (-6612 : ℚ) + 0
  norm_num [GeometryBindings.flatBox4]

theorem row13 (j : Fin 57) :
    Leaf004.rationalSystem.rows 13 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 103 j := by
  have hd : ∀ j : Fin 57, ([-15360000, 7680000, -7680000, 7680000, -7680000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, -15360000), (⟨1, by decide⟩, 7680000), (⟨2, by decide⟩, -7680000), (⟨3, by decide⟩, 7680000), (⟨4, by decide⟩, -7680000)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, -15360000), (⟨1, by decide⟩, 7680000), (⟨2, by decide⟩, -7680000), (⟨3, by decide⟩, 7680000), (⟨4, by decide⟩, -7680000)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 103).terms := by
    change ([(⟨0, by decide⟩, ((-15360000 : ℚ) * 4800) / 23040000), (⟨1, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨2, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000), (⟨3, by decide⟩, ((7680000 : ℚ) * 4800) / 23040000), (⟨4, by decide⟩, ((-7680000 : ℚ) * 4800) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, -((3200 : ℚ))), (⟨1, by decide⟩, -((-1600 : ℚ))), (⟨2, by decide⟩, -((1600 : ℚ))), (⟨3, by decide⟩, -((-1600 : ℚ))), (⟨4, by decide⟩, -((1600 : ℚ)))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs13 :
    Leaf004.rationalSystem.rhs 13 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 103 := by
  change (0 : ℚ) / 23040000 = (0 : ℚ)
  norm_num [GeometryBindings.flatBox4]

theorem row14 (j : Fin 57) :
    Leaf004.rationalSystem.rows 14 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 109 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9600, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨15, by decide⟩, 9600), (⟨21, by decide⟩, 0), (⟨22, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨15, by decide⟩, 9600), (⟨21, by decide⟩, 0), (⟨22, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 109).terms := by
    change ([(⟨15, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨21, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨22, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨15, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨21, by decide⟩)), (⟨21, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨15, by decide⟩)), (⟨22, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs14 :
    Leaf004.rationalSystem.rhs 14 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 109 := by
  change (0 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨15, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨21, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row15 (j : Fin 57) :
    Leaf004.rationalSystem.rows 15 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 137 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨13, by decide⟩, 9600), (⟨20, by decide⟩, 0), (⟨29, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨13, by decide⟩, 9600), (⟨20, by decide⟩, 0), (⟨29, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 137).terms := by
    change ([(⟨13, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨20, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨29, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨13, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨20, by decide⟩)), (⟨20, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨13, by decide⟩)), (⟨29, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs15 :
    Leaf004.rationalSystem.rhs 15 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 137 := by
  change (0 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨13, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨20, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row16 (j : Fin 57) :
    Leaf004.rationalSystem.rows 16 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 145 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, 0), (⟨18, by decide⟩, -4800), (⟨31, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, 0), (⟨18, by decide⟩, -4800), (⟨31, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 145).terms := by
    change ([(⟨12, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨31, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨18, by decide⟩)), (⟨18, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨12, by decide⟩)), (⟨31, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs16 :
    Leaf004.rationalSystem.rhs 16 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 145 := by
  change (0 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨12, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row17 (j : Fin 57) :
    Leaf004.rationalSystem.rows 17 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 146 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, -4800), (⟨17, by decide⟩, 0), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, -4800), (⟨17, by decide⟩, 0), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 146).terms := by
    change ([(⟨12, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨17, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨32, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, (GeometryBindings.flatBox4.lo ⟨17, by decide⟩)), (⟨17, by decide⟩, (GeometryBindings.flatBox4.lo ⟨12, by decide⟩)), (⟨32, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs17 :
    Leaf004.rationalSystem.rhs 17 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 146 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox4.lo ⟨12, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨17, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row18 (j : Fin 57) :
    Leaf004.rationalSystem.rows 18 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 147 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨12, by decide⟩, 4800), (⟨17, by decide⟩, 4800), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨12, by decide⟩, 4800), (⟨17, by decide⟩, 4800), (⟨32, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 147).terms := by
    change ([(⟨12, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨17, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨32, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨12, by decide⟩, (GeometryBindings.flatBox4.hi ⟨17, by decide⟩)), (⟨17, by decide⟩, (GeometryBindings.flatBox4.hi ⟨12, by decide⟩)), (⟨32, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs18 :
    Leaf004.rationalSystem.rhs 18 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 147 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨12, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨17, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row19 (j : Fin 57) :
    Leaf004.rationalSystem.rows 19 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 155 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨11, by decide⟩, 4800), (⟨18, by decide⟩, 4800), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨11, by decide⟩, 4800), (⟨18, by decide⟩, 4800), (⟨34, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 155).terms := by
    change ([(⟨11, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨18, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨34, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨11, by decide⟩, (GeometryBindings.flatBox4.hi ⟨18, by decide⟩)), (⟨18, by decide⟩, (GeometryBindings.flatBox4.hi ⟨11, by decide⟩)), (⟨34, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs19 :
    Leaf004.rationalSystem.rhs 19 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 155 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨11, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨18, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row20 (j : Fin 57) :
    Leaf004.rationalSystem.rows 20 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 162 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨11, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨36, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨11, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨36, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 162).terms := by
    change ([(⟨11, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨16, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨36, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨11, by decide⟩, (GeometryBindings.flatBox4.lo ⟨16, by decide⟩)), (⟨16, by decide⟩, (GeometryBindings.flatBox4.lo ⟨11, by decide⟩)), (⟨36, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs20 :
    Leaf004.rationalSystem.rhs 20 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 162 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox4.lo ⟨11, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨16, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row21 (j : Fin 57) :
    Leaf004.rationalSystem.rows 21 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 173 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨10, by decide⟩, 4800), (⟨17, by decide⟩, -4800), (⟨38, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨10, by decide⟩, 4800), (⟨17, by decide⟩, -4800), (⟨38, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 173).terms := by
    change ([(⟨10, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨17, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨38, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨10, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨17, by decide⟩)), (⟨17, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨10, by decide⟩)), (⟨38, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs21 :
    Leaf004.rationalSystem.rhs 21 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 173 := by
  change (23040000 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨10, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨17, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row22 (j : Fin 57) :
    Leaf004.rationalSystem.rows 22 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 174 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨10, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨39, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨10, by decide⟩, -4800), (⟨16, by decide⟩, 0), (⟨39, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 174).terms := by
    change ([(⟨10, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨16, by decide⟩, ((0 : ℚ) * 4800) / 23040000), (⟨39, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨10, by decide⟩, (GeometryBindings.flatBox4.lo ⟨16, by decide⟩)), (⟨16, by decide⟩, (GeometryBindings.flatBox4.lo ⟨10, by decide⟩)), (⟨39, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs22 :
    Leaf004.rationalSystem.rhs 22 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 174 := by
  change (0 : ℚ) / 23040000 = (GeometryBindings.flatBox4.lo ⟨10, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨16, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row23 (j : Fin 57) :
    Leaf004.rationalSystem.rows 23 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 191 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨8, by decide⟩, 4800), (⟨12, by decide⟩, 4800), (⟨43, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨8, by decide⟩, 4800), (⟨12, by decide⟩, 4800), (⟨43, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 191).terms := by
    change ([(⟨8, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨12, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨43, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨8, by decide⟩, (GeometryBindings.flatBox4.hi ⟨12, by decide⟩)), (⟨12, by decide⟩, (GeometryBindings.flatBox4.hi ⟨8, by decide⟩)), (⟨43, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs23 :
    Leaf004.rationalSystem.rhs 23 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 191 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨8, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨12, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row24 (j : Fin 57) :
    Leaf004.rationalSystem.rows 24 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 199 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, 4800, 0, 4800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨8, by decide⟩, 4800), (⟨10, by decide⟩, 4800), (⟨45, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨8, by decide⟩, 4800), (⟨10, by decide⟩, 4800), (⟨45, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 199).terms := by
    change ([(⟨8, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨10, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨45, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨8, by decide⟩, (GeometryBindings.flatBox4.hi ⟨10, by decide⟩)), (⟨10, by decide⟩, (GeometryBindings.flatBox4.hi ⟨8, by decide⟩)), (⟨45, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs24 :
    Leaf004.rationalSystem.rhs 24 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 199 := by
  change (23040000 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨8, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨10, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row25 (j : Fin 57) :
    Leaf004.rationalSystem.rows 25 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 204 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 0, -4800, -159, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨8, by decide⟩, -4800), (⟨9, by decide⟩, -159), (⟨46, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨8, by decide⟩, -4800), (⟨9, by decide⟩, -159), (⟨46, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 204).terms := by
    change ([(⟨8, by decide⟩, ((-4800 : ℚ) * 4800) / 23040000), (⟨9, by decide⟩, ((-159 : ℚ) * 4800) / 23040000), (⟨46, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨8, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨9, by decide⟩)), (⟨9, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨8, by decide⟩)), (⟨46, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs25 :
    Leaf004.rationalSystem.rhs 25 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 204 := by
  change (-763200 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.lo ⟨8, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨9, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row26 (j : Fin 57) :
    Leaf004.rationalSystem.rows 26 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 209 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, 0, 0, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨7, by decide⟩, 4800), (⟨15, by decide⟩, -9600), (⟨47, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨7, by decide⟩, 4800), (⟨15, by decide⟩, -9600), (⟨47, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 209).terms := by
    change ([(⟨7, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨15, by decide⟩, ((-9600 : ℚ) * 4800) / 23040000), (⟨47, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨7, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨15, by decide⟩)), (⟨15, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨7, by decide⟩)), (⟨47, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs26 :
    Leaf004.rationalSystem.rhs 26 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 209 := by
  change (46080000 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨7, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨15, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row27 (j : Fin 57) :
    Leaf004.rationalSystem.rows 27 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 217 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 0, 0, 0, 4800, 0, 0, 0, 0, 0, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨7, by decide⟩, 4800), (⟨13, by decide⟩, -9600), (⟨49, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨7, by decide⟩, 4800), (⟨13, by decide⟩, -9600), (⟨49, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 217).terms := by
    change ([(⟨7, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨13, by decide⟩, ((-9600 : ℚ) * 4800) / 23040000), (⟨49, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨7, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨13, by decide⟩)), (⟨13, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨7, by decide⟩)), (⟨49, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs27 :
    Leaf004.rationalSystem.rhs 27 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 217 := by
  change (46080000 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨7, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨13, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row28 (j : Fin 57) :
    Leaf004.rationalSystem.rows 28 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 220 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, -4482, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨4, by decide⟩, -4482), (⟨6, by decide⟩, 9600), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨4, by decide⟩, -4482), (⟨6, by decide⟩, 9600), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 220).terms := by
    change ([(⟨4, by decide⟩, ((-4482 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨50, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨4, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨6, by decide⟩)), (⟨6, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨4, by decide⟩)), (⟨50, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs28 :
    Leaf004.rationalSystem.rhs 28 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 220 := by
  change (43027200 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.lo ⟨4, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row29 (j : Fin 57) :
    Leaf004.rationalSystem.rows 29 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 221 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, -318, 0, 636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨4, by decide⟩, -318), (⟨6, by decide⟩, 636), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨4, by decide⟩, -318), (⟨6, by decide⟩, 636), (⟨50, by decide⟩, 1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 221).terms := by
    change ([(⟨4, by decide⟩, ((-318 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((636 : ℚ) * 4800) / 23040000), (⟨50, by decide⟩, ((1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨4, by decide⟩, -(GeometryBindings.flatBox4.lo ⟨6, by decide⟩)), (⟨6, by decide⟩, -(GeometryBindings.flatBox4.hi ⟨4, by decide⟩)), (⟨50, by decide⟩, (1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs29 :
    Leaf004.rationalSystem.rhs 29 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 221 := by
  change (202248 : ℚ) / 23040000 = -(GeometryBindings.flatBox4.hi ⟨4, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row30 (j : Fin 57) :
    Leaf004.rationalSystem.rows 30 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 223 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 0, 4800, -636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨4, by decide⟩, 4800), (⟨5, by decide⟩, -636), (⟨51, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨4, by decide⟩, 4800), (⟨5, by decide⟩, -636), (⟨51, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 223).terms := by
    change ([(⟨4, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨5, by decide⟩, ((-636 : ℚ) * 4800) / 23040000), (⟨51, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨4, by decide⟩, (GeometryBindings.flatBox4.hi ⟨5, by decide⟩)), (⟨5, by decide⟩, (GeometryBindings.flatBox4.hi ⟨4, by decide⟩)), (⟨51, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs30 :
    Leaf004.rationalSystem.rhs 30 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 223 := by
  change (-3052800 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨4, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨5, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row31 (j : Fin 57) :
    Leaf004.rationalSystem.rows 31 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 226 j := by
  have hd : ∀ j : Fin 57, ([0, 0, 0, 318, 0, 0, -9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨3, by decide⟩, 318), (⟨6, by decide⟩, -9600), (⟨52, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨3, by decide⟩, 318), (⟨6, by decide⟩, -9600), (⟨52, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 226).terms := by
    change ([(⟨3, by decide⟩, ((318 : ℚ) * 4800) / 23040000), (⟨6, by decide⟩, ((-9600 : ℚ) * 4800) / 23040000), (⟨52, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨3, by decide⟩, (GeometryBindings.flatBox4.lo ⟨6, by decide⟩)), (⟨6, by decide⟩, (GeometryBindings.flatBox4.lo ⟨3, by decide⟩)), (⟨52, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs31 :
    Leaf004.rationalSystem.rhs 31 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 226 := by
  change (-3052800 : ℚ) / 23040000 = (GeometryBindings.flatBox4.lo ⟨3, by decide⟩) * (GeometryBindings.flatBox4.lo ⟨6, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem row32 (j : Fin 57) :
    Leaf004.rationalSystem.rows 32 j =
      (Model.generatedSystem GeometryBindings.flatBox4).a 243 j := by
  have hd : ∀ j : Fin 57, ([4800, 0, 0, 0, 0, 9600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD j.val 0 =
      sparseIntCoeff ([(⟨0, by decide⟩, 4800), (⟨5, by decide⟩, 9600), (⟨56, by decide⟩, -1)] : List (Fin 57 × ℤ)) j := by decide
  have ht : ([(⟨0, by decide⟩, 4800), (⟨5, by decide⟩, 9600), (⟨56, by decide⟩, -1)] : List (Fin 57 × ℤ)).map
      (fun t => (t.1, (t.2 : ℚ) * Leaf004.coordinateScale t.1 / 23040000)) =
      (Model.generatedRow GeometryBindings.flatBox4 243).terms := by
    change ([(⟨0, by decide⟩, ((4800 : ℚ) * 4800) / 23040000), (⟨5, by decide⟩, ((9600 : ℚ) * 4800) / 23040000), (⟨56, by decide⟩, ((-1 : ℚ) * 23040000) / 23040000)] : List (Fin 57 × ℚ)) = [(⟨0, by decide⟩, (GeometryBindings.flatBox4.hi ⟨5, by decide⟩)), (⟨5, by decide⟩, (GeometryBindings.flatBox4.hi ⟨0, by decide⟩)), (⟨56, by decide⟩, (-1 : ℚ))]
    norm_num [GeometryBindings.flatBox4]
  exact scaled_dense_eq_sparse _ _ Leaf004.coordinateScale (23040000 : ℚ) _ hd ht j

theorem rhs32 :
    Leaf004.rationalSystem.rhs 32 =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs 243 := by
  change (46080000 : ℚ) / 23040000 = (GeometryBindings.flatBox4.hi ⟨0, by decide⟩) * (GeometryBindings.flatBox4.hi ⟨5, by decide⟩)
  norm_num [GeometryBindings.flatBox4]

theorem all_rows (i : Fin 33) (j : Fin 57) :
    Leaf004.rationalSystem.rows i j =
      (Model.generatedSystem GeometryBindings.flatBox4).a (selectedId i) j := by
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
  · exact row28 j
  · exact row29 j
  · exact row30 j
  · exact row31 j
  · exact row32 j

theorem all_rhs (i : Fin 33) :
    Leaf004.rationalSystem.rhs i =
      (Model.generatedSystem GeometryBindings.flatBox4).rhs (selectedId i) := by
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
  · exact rhs28
  · exact rhs29
  · exact rhs30
  · exact rhs31
  · exact rhs32

end Rho5.Shared.MainlineTreeCover.V31Batch.Rows004
