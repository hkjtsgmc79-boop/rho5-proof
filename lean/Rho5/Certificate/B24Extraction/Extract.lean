import Rho5.Certificate.B24Reconstruction
import Rho5.Certificate.B24Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# D37 / B24Extraction — reading the B24 coordinates back out of a normalized matrix

Forward direction (D28) builds `reconstruct z` from the same-source parameters.  This
file pays the **inverse interface** for one explicitly delimited class: a real
`5 × 5` matrix `A` that is already normalized (`A 0 0 = 1`), whose successive Schur
updates

`S4 A = pivotSchur A 0 0`, `S3 A = pivotSchur (S4 A) 0 0`, `T2 A = pivotSchur (S3 A) 0 0`

have the **balanced tail** `T2 A 1 1 = -r A` (the last `2 × 2` block is
`[[r, s], [t, -r]]`), and whose first three pivots are legal with `p, k, r ≠ 0`.

The coordinates are read off exactly as the card fixes them:

| coordinate | value |
| --- | --- |
| `k = z 0` | `S3 A 0 0` |
| `r = z 1` | `T2 A 0 0` |
| `s = z 2` | `T2 A 0 1` |
| `t = z 3` | `T2 A 1 0` |
| `A`-parameter `= z 4` | `S3 A 0 1` |
| `B`-parameter `= z 5` | `S3 A 0 2` |
| `c = z 6` | `S3 A 1 0 / k` |
| `d = z 7` | `S3 A 2 0 / k` |
| `p = z 8` | `S4 A 0 0` |
| `e = z 9` | `-A 0 1` |
| `beta = z 10` | `A 1 0` |
| `u_i = z (11+i)` | `A (i+2) 0` |
| `x_i = z (14+i)` | `S4 A (i+1) 0 / p` |
| `v_j = z (17+j)` | `A 0 (j+2)` |
| `q_j = z (20+j)` | `S4 A 0 (j+1)` |
| `F = z 23` | `r + s t / r` |

The class is **not** assumed to be all matrices: the normalization `A 0 0 = 1`, the
balance condition `T2 1 1 = -r` and the pivot qualifications are explicit hypotheses,
and nothing here claims that such a matrix exists or that every matrix can be brought
into this form.
-/

namespace Rho5.Certificate.B24Extraction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage HeadBand beta)

/-! ## The three successive Schur updates and the extracted scalars -/

/-- The real `4 × 4` matrix after the first complete-pivot step of `A`. -/
noncomputable def S4 (A : Matrix5) : Matrix (Fin 4) (Fin 4) ℝ :=
  Rho5.PivotReindex.pivotSchur A 0 0

/-- The real `3 × 3` matrix after the second step. -/
noncomputable def S3 (A : Matrix5) : Matrix (Fin 3) (Fin 3) ℝ :=
  Rho5.PivotReindex.pivotSchur (S4 A) 0 0

/-- The real `2 × 2` tail after the third step.  The card's balance condition is
`T2 A 1 1 = -r A`. -/
noncomputable def T2 (A : Matrix5) : Matrix (Fin 2) (Fin 2) ℝ :=
  Rho5.PivotReindex.pivotSchur (S3 A) 0 0

noncomputable def p (A : Matrix5) : ℝ := S4 A 0 0
noncomputable def k (A : Matrix5) : ℝ := S3 A 0 0
noncomputable def r (A : Matrix5) : ℝ := T2 A 0 0
noncomputable def s (A : Matrix5) : ℝ := T2 A 0 1
noncomputable def t (A : Matrix5) : ℝ := T2 A 1 0

/-- The height coordinate read off the tail: `F = r + s t / r`. -/
noncomputable def F (A : Matrix5) : ℝ := r A + s A * t A / r A

/-! ## Entrywise Schur formulas (frozen `pivotSchur` at the active corner) -/

theorem S4_apply (A : Matrix5) (i j : Fin 4) :
    S4 A i j = A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0 := by
  rw [S4, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  rfl

theorem S3_apply (A : Matrix5) (i j : Fin 3) :
    S3 A i j = S4 A i.succ j.succ - S4 A i.succ 0 * S4 A 0 j.succ / S4 A 0 0 := by
  rw [S3, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  rfl

theorem T2_apply (A : Matrix5) (i j : Fin 2) :
    T2 A i j = S3 A i.succ j.succ - S3 A i.succ 0 * S3 A 0 j.succ / S3 A 0 0 := by
  rw [T2, Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  rfl

/-- The `T2` denominator is `k` by definition. -/
theorem S3_zero_zero (A : Matrix5) : S3 A 0 0 = k A := rfl

/-! ## The extracted point -/

/-- **Item 1 (definition).**  The B24 coordinates read off `A`; see the module
documentation for the entry-by-entry table.  `A`'s own indices (`A 0 0`, `A 1 0`, …)
are not to be confused with the model's `A`-parameter (`z 4 = S3 A 0 1`). -/
noncomputable def extract (A : Matrix5) : Point :=
  ![k A, r A, s A, t A, S3 A 0 1, S3 A 0 2, S3 A 1 0 / k A, S3 A 2 0 / k A,
    p A, -A 0 1, A 1 0,
    A 2 0, A 3 0, A 4 0,
    S4 A 1 0 / p A, S4 A 2 0 / p A, S4 A 3 0 / p A,
    A 0 2, A 0 3, A 0 4,
    S4 A 0 1, S4 A 0 2, S4 A 0 3,
    F A]

/-! ## Tail identities: the third step's entries written back through `T2` -/

theorem S3_11 (A : Matrix5) : S3 A 1 1 = r A + S3 A 1 0 * S3 A 0 1 / k A := by
  have h : r A = S3 A 1 1 - S3 A 1 0 * S3 A 0 1 / k A := by
    rw [r]; exact T2_apply A 0 0
  rw [h]; ring

theorem S3_12 (A : Matrix5) : S3 A 1 2 = s A + S3 A 1 0 * S3 A 0 2 / k A := by
  have h : s A = S3 A 1 2 - S3 A 1 0 * S3 A 0 2 / k A := by
    rw [s]; exact T2_apply A 0 1
  rw [h]; ring

theorem S3_21 (A : Matrix5) : S3 A 2 1 = t A + S3 A 2 0 * S3 A 0 1 / k A := by
  have h : t A = S3 A 2 1 - S3 A 2 0 * S3 A 0 1 / k A := by
    rw [t]; exact T2_apply A 1 0
  rw [h]; ring

/-- The balance condition `T2 1 1 = -r` is exactly what makes the lower-right corner
of the extracted `3 × 3` core match `S3`. -/
theorem S3_22 (A : Matrix5) (htail : T2 A 1 1 = -r A) :
    S3 A 2 2 = -r A + S3 A 2 0 * S3 A 0 2 / k A := by
  have h : T2 A 1 1 = S3 A 2 2 - S3 A 2 0 * S3 A 0 2 / k A := T2_apply A 1 1
  rw [htail] at h
  rw [h]; ring

/-! ## The `3 × 3` core of the extraction is the second Schur update -/

/-- **Item 2 (`D` block).**  The frozen `B16.D` of the extracted coordinates is
exactly the second Schur update `S3 A` (this is where `k ≠ 0` and the balance
condition `T2 1 1 = -r` are used). -/
theorem D_extract (A : Matrix5) (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A) :
    D (extract A) = S3 A := by
  have hk' : S3 A 0 0 ≠ 0 := hk
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, extract, k, r, s, t, S3_11 A, S3_12 A, S3_21 A, S3_22 A htail] <;>
    field_simp [hk'] <;> ring

/-! ## The `(2+i, 2+j)` block identity that closes the reconstruction -/

/-- The lower `3 × 3` block of `A` written through the extracted blocks.  This is the
kernel of the inverse reconstruction: `S3` is the second update, so
`A (i+2) (j+2) = S3 i j + u_i v_j + x_i q_j`. -/
theorem A_block (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (i j : Fin 3) :
    A i.succ.succ j.succ.succ
      = S3 A i j + A i.succ.succ 0 * A 0 j.succ.succ
        + (S4 A i.succ 0 / p A) * S4 A 0 j.succ := by
  have hp4 : S4 A 0 0 = p A := rfl
  rw [S3_apply A i j, hp4, S4_apply A i.succ j.succ, S4_apply A i.succ 0,
    S4_apply A 0 j.succ, h00]
  field_simp [hp]
  ring

/-! ## Coordinate evaluation of the frozen accessors at the extracted point -/

theorem e_extract (A : Matrix5) :
    Rho5.Certificate.B24Reconstruction.e (extract A) = -A 0 1 := by
  simp [extract, Rho5.Certificate.B24Reconstruction.e]

theorem p_extract (A : Matrix5) :
    Rho5.Certificate.B24Reconstruction.p (extract A) = p A := by
  simp [extract, Rho5.Certificate.B24Reconstruction.p]

theorem beta_extract (A : Matrix5) : beta (extract A) = A 1 0 := by
  simp [extract, beta]

theorem u_extract (A : Matrix5) (i : Fin 3) : u (extract A) i = A i.succ.succ 0 := by
  fin_cases i <;> simp [extract, u]

theorem v_extract (A : Matrix5) (j : Fin 3) : v (extract A) j = A 0 j.succ.succ := by
  fin_cases j <;> simp [extract, v]

theorem xv_extract (A : Matrix5) (i : Fin 3) : xv (extract A) i = S4 A i.succ 0 / p A := by
  fin_cases i <;> simp [extract, xv]

theorem q_extract_coord (A : Matrix5) (j : Fin 3) : q (extract A) j = S4 A 0 j.succ := by
  fin_cases j <;> simp [extract, q]

theorem extract_eight (A : Matrix5) : extract A 8 = p A := by simp [extract]

theorem extract_nine (A : Matrix5) : extract A 9 = -A 0 1 := by simp [extract]

theorem extract_ten (A : Matrix5) : extract A 10 = A 1 0 := by simp [extract]

/-! ## Structural entry families of the reconstruction (any point) -/

theorem reconstruct_01 (z : Point) : reconstruct z 0 1 = -Rho5.Certificate.B24Reconstruction.e z := by
  simp [reconstruct]

theorem reconstruct_10 (z : Point) : reconstruct z 1 0 = beta z := by
  simp [reconstruct]

theorem reconstruct_11 (z : Point) :
    reconstruct z 1 1 = Rho5.Certificate.B24Reconstruction.p z
      - Rho5.Certificate.B24Reconstruction.e z * beta z := by
  simp [reconstruct]

theorem reconstruct_0v (z : Point) (j : Fin 3) :
    reconstruct z 0 j.succ.succ = v z j := by
  fin_cases j <;> simp [reconstruct]

theorem reconstruct_1P (z : Point) (j : Fin 3) :
    reconstruct z 1 j.succ.succ = P z j := by
  fin_cases j <;> simp [reconstruct, P]

theorem reconstruct_u (z : Point) (i : Fin 3) :
    reconstruct z i.succ.succ 0 = u z i := by
  fin_cases i <;> simp [reconstruct]

theorem reconstruct_L (z : Point) (i : Fin 3) :
    reconstruct z i.succ.succ 1 =
      Rho5.Certificate.B24Reconstruction.p z * xv z i
        - Rho5.Certificate.B24Reconstruction.e z * u z i := by
  fin_cases i <;> simp [reconstruct]

theorem reconstruct_O (z : Point) (i j : Fin 3) :
    reconstruct z i.succ.succ j.succ.succ = O z i j := by
  fin_cases i <;> fin_cases j <;> simp [reconstruct, O]

theorem firstStage_row0 (z : Point) (j : Fin 3) : firstStage z 0 j.succ = q z j := by
  fin_cases j <;> simp [firstStage]

theorem firstStage_block (z : Point) (i j : Fin 3) : firstStage z i.succ j.succ = S z i j := by
  fin_cases i <;> fin_cases j <;> simp [firstStage]

/-! ## Item 2 — the reconstruction is exact on this class -/

/-- **Item 2 (top-left `2 × 2`).**  `A 0 0 = 1` is what makes the reconstructed
`(0, 0)` entry match; the other three entries are definitional. -/
theorem rec_00 (A : Matrix5) (h00 : A 0 0 = 1) :
    reconstruct (extract A) 0 0 = A 0 0 := by
  rw [Rho5.Certificate.B24Reconstruction.reconstruct_zero_zero, h00]

theorem rec_01 (A : Matrix5) : reconstruct (extract A) 0 1 = A 0 1 := by
  rw [reconstruct_01, e_extract]; ring

theorem rec_0v (A : Matrix5) (j : Fin 3) :
    reconstruct (extract A) 0 j.succ.succ = A 0 j.succ.succ := by
  rw [reconstruct_0v, v_extract]

theorem rec_10 (A : Matrix5) : reconstruct (extract A) 1 0 = A 1 0 := by
  rw [reconstruct_10, beta_extract]

theorem rec_11 (A : Matrix5) (h00 : A 0 0 = 1) :
    reconstruct (extract A) 1 1 = A 1 1 := by
  rw [reconstruct_11, p_extract, e_extract, beta_extract, p, S4_apply A 0 0, h00]
  first
    | (norm_num; ring)
    | norm_num

theorem rec_1P (A : Matrix5) (h00 : A 0 0 = 1) (j : Fin 3) :
    reconstruct (extract A) 1 j.succ.succ = A 1 j.succ.succ := by
  rw [reconstruct_1P, P, extract_ten, v_extract, q_extract_coord,
    S4_apply A 0 j.succ, h00]
  first
    | (norm_num; ring)
    | norm_num

theorem rec_u (A : Matrix5) (i : Fin 3) :
    reconstruct (extract A) i.succ.succ 0 = A i.succ.succ 0 := by
  rw [reconstruct_u, u_extract]

theorem rec_L (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (i : Fin 3) :
    reconstruct (extract A) i.succ.succ 1 = A i.succ.succ 1 := by
  rw [reconstruct_L, p_extract, e_extract, xv_extract, u_extract,
    S4_apply A i.succ 0, h00]
  field_simp [hp]
  first
    | (norm_num; ring)
    | norm_num

theorem rec_O (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (hk : k A ≠ 0)
    (htail : T2 A 1 1 = -r A) (i j : Fin 3) :
    reconstruct (extract A) i.succ.succ j.succ.succ = A i.succ.succ j.succ.succ := by
  rw [reconstruct_O, O, D_extract A hk htail, u_extract, v_extract, xv_extract,
    q_extract_coord]
  rw [← A_block A h00 hp i j]

/-- **Item 2 (main identity).**  Under `A 0 0 = 1`, `p ≠ 0`, `k ≠ 0` and the balanced
tail `T2 1 1 = -r`, reading the coordinates off `A` and reconstructing gives `A` back.
The identity is *proved*, not assumed. -/
theorem reconstruct_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0)
    (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A) :
    reconstruct (extract A) = A := by
  funext i j
  fin_cases i <;> fin_cases j <;> first
    | exact rec_00 A h00
    | exact rec_01 A
    | exact rec_10 A
    | exact rec_11 A h00
    | exact rec_0v A 0 | exact rec_0v A 1 | exact rec_0v A 2
    | exact rec_1P A h00 0 | exact rec_1P A h00 1 | exact rec_1P A h00 2
    | exact rec_u A 0 | exact rec_u A 1 | exact rec_u A 2
    | exact rec_L A h00 hp 0 | exact rec_L A h00 hp 1 | exact rec_L A h00 hp 2
    | exact rec_O A h00 hp hk htail 0 0 | exact rec_O A h00 hp hk htail 0 1
    | exact rec_O A h00 hp hk htail 0 2
    | exact rec_O A h00 hp hk htail 1 0 | exact rec_O A h00 hp hk htail 1 1
    | exact rec_O A h00 hp hk htail 1 2
    | exact rec_O A h00 hp hk htail 2 0 | exact rec_O A h00 hp hk htail 2 1
    | exact rec_O A h00 hp hk htail 2 2

/-- **Item 2 (`D` block, entry form).** -/
theorem D_extract_apply (A : Matrix5) (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A)
    (i j : Fin 3) : D (extract A) i j = S3 A i j := by
  rw [D_extract A hk htail]

/-- **Item 2 (`S` block).**  The frozen `B16.S` of the extracted coordinates is the
lower `3 × 3` block of the first Schur update `S4 A`. -/
theorem S_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (hk : k A ≠ 0)
    (htail : T2 A 1 1 = -r A) (i j : Fin 3) :
    S (extract A) i j = S4 A i.succ j.succ := by
  have h4 : S4 A = firstStage (extract A) := by
    rw [← Rho5.Certificate.B24Reconstruction.pivotSchur_reconstruct_zero_zero (extract A),
      reconstruct_extract A h00 hp hk htail]
    rfl
  calc S (extract A) i j = firstStage (extract A) i.succ j.succ :=
        (firstStage_block (extract A) i j).symm
    _ = S4 A i.succ j.succ := by rw [h4]

/-- **Item 2 (`O` block).**  The frozen `B16.O` of the extracted coordinates is the
lower `3 × 3` block of `A`. -/
theorem O_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (hk : k A ≠ 0)
    (htail : T2 A 1 1 = -r A) (i j : Fin 3) :
    O (extract A) i j = A i.succ.succ j.succ.succ := by
  have h := congrFun (congrFun (reconstruct_extract A h00 hp hk htail) i.succ.succ)
    j.succ.succ
  rwa [reconstruct_O (extract A) i j] at h

/-- **Item 2 (`q` block).**  The frozen `B16.q` of the extracted coordinates is the
first row of `S4` (columns `1..3`). -/
theorem q_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (hk : k A ≠ 0)
    (htail : T2 A 1 1 = -r A) (j : Fin 3) :
    q (extract A) j = S4 A 0 j.succ := by
  have h4 : S4 A = firstStage (extract A) := by
    rw [← Rho5.Certificate.B24Reconstruction.pivotSchur_reconstruct_zero_zero (extract A),
      reconstruct_extract A h00 hp hk htail]
    rfl
  calc q (extract A) j = firstStage (extract A) 0 j.succ :=
        (firstStage_row0 (extract A) j).symm
    _ = S4 A 0 j.succ := by rw [h4]

/-- **Item 2 (`L` block).**  The frozen `B16.L` of the extracted coordinates is the
second column of `A` (rows `2..4`): `L_i = p x_i - e u_i = A (i+2) 1`, which is the
reference's `px - eu` entry of the reconstructed matrix. -/
theorem L_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0) (i : Fin 3) :
    L (extract A) i = A i.succ.succ 1 := by
  rw [L, extract_eight, extract_nine, xv_extract, u_extract, S4_apply A i.succ 0, h00]
  field_simp [hp]
  first
    | (norm_num; ring)
    | norm_num

/-- **Item 2 (`P` block).**  The frozen `B16.P` of the extracted coordinates is the
second row of `A` (columns `2..4`): `P_j = q_j + beta v_j = A 1 (j+2)`. -/
theorem P_extract (A : Matrix5) (h00 : A 0 0 = 1) (j : Fin 3) :
    P (extract A) j = A 1 j.succ.succ := by
  rw [P, extract_ten, v_extract, q_extract_coord, S4_apply A 0 j.succ, h00]
  first
    | (norm_num; ring)
    | norm_num

end Rho5.Certificate.B24Extraction
