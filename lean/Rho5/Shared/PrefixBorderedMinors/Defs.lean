/-
D61 — the fixed ordered embeddings and the actual bordered `2 × 2` / `3 × 3` minors.

The card fixes two finite index families of the actual `5 × 5` matrix:

* `e2 i : Fin 2 → Fin 5` with index list `[0, 1 + i]`  (`i : Fin 4`) — 16 ordered
  `2 × 2` minors `m2 M i j`;
* `e3 i : Fin 3 → Fin 5` with index list `[0, 1, 2 + i]`  (`i : Fin 3`) — 9 ordered
  `3 × 3` minors `m3 M i j`.

Both are *signed* determinants of the ordered row/column submatrices, exactly as D52
fixed its four `4 × 4` bordered minors.  This is a fixed-order family, not a generic
embedding or submatrix framework.

The embeddings are defined by `Fin` pattern matching, so their values are `rfl`
lemmas — the same style D52 used for `embed`.
-/
import Rho5.Shared.MatrixNormalization
import Rho5.Certificate.B24Extraction.Extract
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Rho5.PrefixBorderedMinors

open Rho5
open Matrix
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t S4_apply S3_apply)

/-! ## 1. The two fixed ordered embeddings -/

/-- **Card-fixed ordered embedding `e2`**: `e2 i = [0, 1 + i]`, i.e. the leading index
together with one of the last four.  Only this finite family is defined. -/
def e2 (i : Fin 4) : Fin 2 → Fin 5
  | 0 => 0
  | 1 => i.succ

/-- **Card-fixed ordered embedding `e3`**: `e3 i = [0, 1, 2 + i]`, i.e. the two leading
indices together with one of the last three. -/
def e3 (i : Fin 3) : Fin 3 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => i.succ.succ

@[simp] theorem e2_zero (i : Fin 4) : e2 i 0 = 0 := rfl
@[simp] theorem e2_one (i : Fin 4) : e2 i 1 = i.succ := rfl
@[simp] theorem e3_zero (i : Fin 3) : e3 i 0 = 0 := rfl
@[simp] theorem e3_one (i : Fin 3) : e3 i 1 = 1 := rfl
@[simp] theorem e3_two (i : Fin 3) : e3 i 2 = i.succ.succ := rfl

/-! ## 2. The signed minors -/

/-- **The 16 ordered `2 × 2` minors.**  `m2 M i j` is the determinant of the submatrix
on rows `e2 i = [0, 1+i]` and columns `e2 j = [0, 1+j]`, read in that order (hence
*signed*). -/
noncomputable def m2 (M : Matrix5) (i j : Fin 4) : ℝ :=
  (M.submatrix (e2 i) (e2 j)).det

/-- **The 9 ordered `3 × 3` minors.**  `m3 M i j` is the determinant of the submatrix
on rows `e3 i = [0, 1, 2+i]` and columns `e3 j = [0, 1, 2+j]`, read in that order. -/
noncomputable def m3 (M : Matrix5) (i j : Fin 3) : ℝ :=
  (M.submatrix (e3 i) (e3 j)).det

/-- Entrywise reading of `m2`. -/
theorem m2_apply (M : Matrix5) (i j : Fin 4) (a b : Fin 2) :
    M.submatrix (e2 i) (e2 j) a b = M (e2 i a) (e2 j b) := rfl

/-- Entrywise reading of `m3`. -/
theorem m3_apply (M : Matrix5) (i j : Fin 3) (a b : Fin 3) :
    M.submatrix (e3 i) (e3 j) a b = M (e3 i a) (e3 j b) := rfl

/-- Corner entry of every `m2` submatrix is `M 0 0` (the embeddings preserve `0`). -/
theorem m2_submatrix_zero_zero (M : Matrix5) (i j : Fin 4) :
    M.submatrix (e2 i) (e2 j) 0 0 = M 0 0 := by simp

/-- Corner entry of every `m3` submatrix is `M 0 0`. -/
theorem m3_submatrix_zero_zero (M : Matrix5) (i j : Fin 3) :
    M.submatrix (e3 i) (e3 j) 0 0 = M 0 0 := by simp

end Rho5.PrefixBorderedMinors
