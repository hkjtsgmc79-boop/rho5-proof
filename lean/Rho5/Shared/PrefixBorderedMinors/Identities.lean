/-
D61 — the actual bordered `2 × 2` and `3 × 3` minor identities.

The two families of `PrefixBorderedMinors/Defs.lean` are identified with the frozen D37
Schur updates:

    m2 M i j = S4 M i j                     (needs only `M 0 0 = 1`)
    m3 M i j = p M * S3 M i j               (needs `M 0 0 = 1` and `p M ≠ 0`)

plus the corners `m2 M 0 0 = p M`, `m3 M 0 0 = p M * k M`, and the exact match between the
leading `m3` and D54's `B3` determinant.

Nonzero assumptions actually used, and nothing more:

* `m2_eq_S4` — `M 0 0 = 1` only (no `p`, no `k`);
* `m3_eq_p_mul_S3` — `M 0 0 = 1` and `p M ≠ 0` only (no `k ≠ 0`, no complete pivot, no
  balance, no rank, no sign premise);
* `m3_zero_zero_eq_det_B3` — none at all (it is an equality of two determinants of the
  same submatrix).

The signed Schur formulas reused are D37's `S4_apply` / `S3_apply`; no upstream proof is
replayed, and D52's four `4 × 4` bordered identities and D54's bound are not redone.
-/
import Rho5.Shared.PrefixBorderedMinors.Defs
import Rho5.Shared.MinorThreeBound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Rho5.PrefixBorderedMinors

open Rho5
open Matrix
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t S4_apply S3_apply)

/-! ## 1. The `2 × 2` family equals the first Schur update -/

/-- **The 16 ordered `2 × 2` minors are the entries of `S4 M`.**  The bordered minor on
rows `[0, 1+i]` and columns `[0, 1+j]` expands to
`M 0 0 * M (1+i) (1+j) - M 0 (1+j) * M (1+i) 0`, which is D37's `S4 M i j` exactly when
`M 0 0 = 1`. -/
theorem m2_eq_S4 (M : Matrix5) (h00 : M 0 0 = 1) (i j : Fin 4) :
    m2 M i j = S4 M i j := by
  rw [m2, Matrix.det_fin_two, S4_apply]
  simp only [Matrix.submatrix_apply, e2_zero, e2_one, h00, div_one]
  ring

/-! ## 2. The `3 × 3` family equals `p M` times the second Schur update -/

/-- The `Fin 4` index pair `[0, 1+i]` — the `S4`-side companion of `e3 i = [0, 1, 2+i]`:
`S4`'s index `k` is the original index `k + 1`, so the remaining rows `1` and `2+i` of the
bordered `3 × 3` block are `S4` indices `0` and `1+i`. -/
def f2 (i : Fin 3) : Fin 2 → Fin 4
  | 0 => 0
  | 1 => i.succ

@[simp] theorem f2_zero (i : Fin 3) : f2 i 0 = 0 := rfl
@[simp] theorem f2_one (i : Fin 3) : f2 i 1 = i.succ := rfl

/-- The top-left `2 × 2` block of `S4 M` picked out by `f2 i`, `f2 j`. -/
noncomputable def s4sub (M : Matrix5) (i j : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => S4 M (f2 i a) (f2 j b)

/-- The first Schur step of the bordered `3 × 3` submatrix is exactly `s4sub`. -/
theorem fixedSchur_m3 (M : Matrix5) (h00 : M 0 0 = 1) (i j : Fin 3) :
    Rho5.Pivot.fixedSchur (M.submatrix (e3 i) (e3 j)) = s4sub M i j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Rho5.Pivot.fixedSchur, s4sub, f2, e3, Matrix.submatrix_apply, S4_apply, h00]

/-- The `(0,0)` entry of `s4sub` is the first pivot. -/
theorem s4sub_zero_zero (M : Matrix5) (i j : Fin 3) : s4sub M i j 0 0 = p M := rfl

/-- The second Schur step of `s4sub` is the `1 × 1` matrix with entry `S3 M i j`. -/
theorem fixedSchur_s4sub (M : Matrix5) (i j : Fin 3) :
    Rho5.Pivot.fixedSchur (s4sub M i j) = fun _ _ : Fin 1 => S3 M i j := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Rho5.Pivot.fixedSchur, s4sub, f2, S3_apply]

/-- **The 9 ordered `3 × 3` minors are `p M * S3 M i j`.**  Both sides are the determinant
of the same bordered `3 × 3` block written through the two signed Schur steps: D27's
`det_eq_pivot_mul_det_fixedSchur` at the pivot `M 0 0 = 1`, then at the pivot `p M`.  Only
`p M ≠ 0` is assumed — `k M`, complete pivots, balance, rank and signs are all untouched. -/
theorem m3_eq_p_mul_S3 (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) (i j : Fin 3) :
    m3 M i j = p M * S3 M i j := by
  have hcorner : (M.submatrix (e3 i) (e3 j)) 0 0 = 1 := by
    simp [Matrix.submatrix_apply, h00]
  have hB00 : (M.submatrix (e3 i) (e3 j)) 0 0 ≠ 0 := by rw [hcorner]; norm_num
  have h1 := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur
    (M.submatrix (e3 i) (e3 j)) hB00
  rw [hcorner, one_mul, fixedSchur_m3 M h00 i j] at h1
  have hS00 : s4sub M i j 0 0 ≠ 0 := by rw [s4sub_zero_zero]; exact hp
  have h2 := Rho5.TraceDeterminant.det_eq_pivot_mul_det_fixedSchur (s4sub M i j) hS00
  rw [fixedSchur_s4sub, Matrix.det_fin_one] at h2
  show (M.submatrix (e3 i) (e3 j)).det = p M * S3 M i j
  rw [h1, h2, s4sub_zero_zero]

/-! ## 3. Corner identities -/

/-- **Corner `2 × 2`.**  The leading `2 × 2` minor is the first pivot. -/
theorem m2_zero_zero (M : Matrix5) (h00 : M 0 0 = 1) : m2 M 0 0 = p M := by
  rw [m2_eq_S4 M h00 0 0]
  rfl

/-- **Corner `3 × 3`.**  The leading `3 × 3` minor is `p M * k M`. -/
theorem m3_zero_zero (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) :
    m3 M 0 0 = p M * k M := by
  rw [m3_eq_p_mul_S3 M h00 hp 0 0]
  rfl

/-! ## 4. The leading `3 × 3` minor is D54's `B3` determinant -/

/-- The leading `m3` submatrix is exactly D54's actual leading `3 × 3` block. -/
theorem submatrix_e3_zero_zero (M : Matrix5) :
    M.submatrix (e3 0) (e3 0) = Rho5.MinorThreeBound.B3 M := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Rho5.MinorThreeBound.B3, e3, Matrix.submatrix_apply]

/-- **Exact match with D54.**  The leading `3 × 3` minor is the determinant of D54's `B3`,
so D54's identity `det (B3 M) = p M * k M` applies verbatim.  No hypothesis is needed for
this equality itself, and D54's bound is not reproved here. -/
theorem m3_zero_zero_eq_det_B3 (M : Matrix5) :
    m3 M 0 0 = (Rho5.MinorThreeBound.B3 M).det := by
  rw [m3, submatrix_e3_zero_zero]

end Rho5.PrefixBorderedMinors
