import Rho5.Certificate.B16Model
import Rho5.Shared.PivotReindex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# D28 / B24Reconstruction — the same-source parameters as the real 5 × 5 matrix

Mathematical source (the only one): `MODEL_V37_V39_REFERENCE.md` §3 of the frozen
B16 delivery (`b16/input/B_STRUCTURE_16_DELIVERY/accepted_inputs`).  With the fixed
B24 coordinate reading

`k = z 0`, `r = z 1`, `s = z 2`, `t = z 3`, `A = z 4`, `B = z 5`, `c = z 6`,
`d = z 7`, `p = z 8`, `e = z 9`, `beta = z 10`, `u = z 11..13`, `x = z 14..16`,
`v = z 17..19`, `q = z 20..22`, `F = z 23`,

the reference reconstructs one single matrix from the same variables:

`M = [[1, -e, vᵀ], [β, p - eβ, (q + βv)ᵀ], [u, px - eu, D + xqᵀ + uvᵀ]]`

with the frozen `D` of `B16Model` (the coordinate reading is checked lemma by lemma
below, not assumed).  Everything here is stated with the *frozen* objects
`Rho5.Certificate.B16.{Point, D, O, S, L, P, u, xv, v, q, Physical}`; nothing in
`B16Model` is redefined or replaced, and no hypothesis is hidden in a new definition.

This file delivers the reconstruction and its coordinate correspondence table; the
first two elimination steps, the entry-max/pivot-legality statements and the explicit
head-band predicate are in `FirstPivot`, `SecondPivot` and `PivotLegal`.

Scope: the reference's further chain — the last two tail pivots, the five-step
`LegalTrace`, the arbitrary-matrix inverse normalization and the macro-class
coverage — is **not** proved here.
-/

namespace Rho5.Certificate.B24Reconstruction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)

/-! ## 1. The B24 coordinates the frozen model does not name -/

/-- The reference's `p` is the B24 coordinate `z 8`. -/
def p (z : Point) : ℝ := z 8

/-- The reference's `e` is the B24 coordinate `z 9`. -/
def e (z : Point) : ℝ := z 9

/-- The reference's `beta` is the B24 coordinate `z 10`. -/
def beta (z : Point) : ℝ := z 10

/-- The reference's height coordinate `F` is the B24 coordinate `z 23`. -/
def F (z : Point) : ℝ := z 23

/-- The reference's `x` (coordinates 14..16) is exactly the frozen `B16.xv`.
This is a name alias, not a new object: `x z` and `xv z` are the same function. -/
abbrev x (z : Point) : Fin 3 → ℝ := xv z

/-! ## 2. Coordinate correspondence, checked against the frozen definitions

The B24 reading of §3 of the reference.  Each row is a `rfl`-level or `ring`-level
identity against `Rho5.Certificate.B16Model`; nothing is taken on faith. -/

section Coordinates

variable (z : Point)

theorem p_coord : p z = z 8 := rfl

theorem e_coord : e z = z 9 := rfl

theorem beta_coord : beta z = z 10 := rfl

theorem F_coord : F z = z 23 := rfl

/-- `u` occupies the B24 coordinates 11, 12, 13. -/
theorem u_coord : u z 0 = z 11 ∧ u z 1 = z 12 ∧ u z 2 = z 13 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The reference's `x` occupies the B24 coordinates 14, 15, 16. -/
theorem x_coord : x z 0 = z 14 ∧ x z 1 = z 15 ∧ x z 2 = z 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- `v` occupies the B24 coordinates 17, 18, 19. -/
theorem v_coord : v z 0 = z 17 ∧ v z 1 = z 18 ∧ v z 2 = z 19 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- `q` occupies the B24 coordinates 20, 21, 22. -/
theorem q_coord : q z 0 = z 20 ∧ q z 1 = z 21 ∧ q z 2 = z 22 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- The alias `x` is the frozen `xv`, coordinate by coordinate. -/
theorem x_eq_xv (i : Fin 3) : x z i = xv z i := rfl

/-- The frozen `D` in B24 coordinates: `[[k, A, B], [ck, r + cA, s + cB],
[dk, t + dA, -r + dB]]` with `k = z 0`, `A = z 4`, `B = z 5`, `c = z 6`, `d = z 7`,
`r = z 1`, `s = z 2`, `t = z 3`. -/
theorem D_coord :
    D z 0 0 = z 0 ∧ D z 0 1 = z 4 ∧ D z 0 2 = z 5 ∧
      D z 1 0 = z 0 * z 6 ∧ D z 1 1 = z 1 + z 4 * z 6 ∧ D z 1 2 = z 2 + z 5 * z 6 ∧
      D z 2 0 = z 0 * z 7 ∧ D z 2 1 = z 3 + z 4 * z 7 ∧ D z 2 2 = -z 1 + z 5 * z 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## 3. The four derived quantities `L`, `P`, `S`, `O` in the reference's form -/

theorem L_doc (i : Fin 3) : L z i = p z * x z i - e z * u z i := rfl

theorem P_doc (j : Fin 3) : P z j = q z j + beta z * v z j := by
  simp only [P, beta]
  ring

theorem S_doc (i j : Fin 3) : S z i j = D z i j + x z i * q z j := rfl

theorem O_doc (i j : Fin 3) : O z i j = D z i j + x z i * q z j + u z i * v z j := by
  simp only [O]
  ring

end Coordinates

/-! ## 4. What `Physical` already supplies, read in the reference's coordinates

The reference's full condition list is
`|e|,|β|,|p-eβ|,|u_i|,|x_i|,|v_j|,|L_i|,|P_j|,|O_ij| ≤ 1`,
`|q_j|,|S_ij| ≤ p`, `|D_ij| ≤ k`, `p,k,r > 0`, `0 ≤ s,t ≤ r`.
The frozen `B16.Physical` supplies the `P`, `O`, `q`, `S`, `D`, `r > 0` and height
parts; the rest is *not* derivable from it and is carried explicitly (see
`HeadBand`).  The next lemmas are the exact field readings under the coordinate
names, so that later statements can cite them without restating the model. -/

section PhysicalReading

variable {z : Point}

theorem abs_q_le_p (hz : Physical z) (j : Fin 3) : |q z j| ≤ p z := hz.q_bound j

theorem abs_S_le_p (hz : Physical z) (i j : Fin 3) : |S z i j| ≤ p z := hz.s_bound i j

theorem abs_P_le_one (hz : Physical z) (j : Fin 3) : |P z j| ≤ 1 := hz.p_bound j

theorem abs_O_le_one (hz : Physical z) (i j : Fin 3) : |O z i j| ≤ 1 := hz.o_bound i j

theorem abs_D_le_k (hz : Physical z) (i j : Fin 3) : |D z i j| ≤ z 0 := hz.d_bound i j

/-- The reference's height law `F = r + st/r`, which is the frozen `height` field. -/
theorem F_eq_height (hz : Physical z) : F z = z 1 + z 2 * z 3 / z 1 := hz.height

theorem r_pos (hz : Physical z) : 0 < z 1 := hz.r_pos

theorem order_t (hz : Physical z) : z 3 ≤ z 1 := hz.order_t

end PhysicalReading

/-! ## 5. The head band that `Physical` does not supply

`|e|`, `|β|`, `|p - eβ|`, `|u_i|`, `|x_i|`, `|v_j|`, `|L_i| ≤ 1` are part of the
reference's actual condition list but are **not** fields of `B16.Physical`, and they
cannot be derived from it.  They are therefore carried as explicit fields here, one
field per condition, with no field asserting any *conclusion* of this lane: in
particular neither `IsCompletePivot` nor `matrixEntryMax = 1` appears below. -/

/-- The reference's head band beyond `B16.Physical`.  Every field is one of the
listed inequalities, in the reference's own shape; the remaining conditions
(`|P_j|, |O_ij| ≤ 1`, `|q_j|, |S_ij| ≤ p`, `|D_ij| ≤ k`, `r > 0`, height) come from
`Physical`, and `p > 0`, `k > 0`, `0 ≤ s, t ≤ r` are passed where they are used. -/
structure HeadBand (z : Point) : Prop where
  abs_e : |e z| ≤ 1
  abs_beta : |beta z| ≤ 1
  abs_u : ∀ i, |u z i| ≤ 1
  abs_x : ∀ i, |x z i| ≤ 1
  abs_v : ∀ j, |v z j| ≤ 1
  abs_p_sub_e_mul_beta : |p z - e z * beta z| ≤ 1
  abs_L : ∀ i, |p z * x z i - e z * u z i| ≤ 1

/-! ## 6. The reconstructed matrix and the first Schur stage -/

/-- **Item 1 (definition).** The real 5 × 5 matrix of §3 of the reference,
reconstructed from the same B24 coordinates:
`[[1, -e, vᵀ], [β, p - eβ, Pᵀ], [u, px - eu, O]]` with the frozen `P` and `O`
(the `P_doc`/`O_doc` lemmas above rewrite these to the reference's
`(q + βv)ᵀ` and `D + xqᵀ + uvᵀ`). -/
noncomputable def reconstruct (z : Point) : Rho5.Matrix5 :=
  Matrix.of
    ![![1, -e z, v z 0, v z 1, v z 2],
      ![beta z, p z - e z * beta z, P z 0, P z 1, P z 2],
      ![u z 0, p z * x z 0 - e z * u z 0, O z 0 0, O z 0 1, O z 0 2],
      ![u z 1, p z * x z 1 - e z * u z 1, O z 1 0, O z 1 1, O z 1 2],
      ![u z 2, p z * x z 2 - e z * u z 2, O z 2 0, O z 2 1, O z 2 2]]

/-- **Item 1 (definition).** The first Schur stage of the reference:
`[[p, qᵀ], [px, D + xqᵀ]]`, with the frozen `S = D + xqᵀ` in the 3 × 3 block. -/
noncomputable def firstStage (z : Point) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of
    ![![p z, q z 0, q z 1, q z 2],
      ![p z * x z 0, S z 0 0, S z 0 1, S z 0 2],
      ![p z * x z 1, S z 1 0, S z 1 1, S z 1 2],
      ![p z * x z 2, S z 2 0, S z 2 1, S z 2 2]]

/-- `firstStage` in the reference's own block notation: `[[p, qᵀ], [px, D + xqᵀ]]`.
Every entry is checked against the frozen `D`, `S`, `x`, `q`. -/
theorem firstStage_table (z : Point) :
    firstStage z 0 0 = p z ∧
      (∀ j : Fin 3, firstStage z 0 j.succ = q z j) ∧
      (∀ i : Fin 3, firstStage z i.succ 0 = p z * x z i) ∧
      (∀ i j : Fin 3, firstStage z i.succ j.succ = D z i j + xv z i * q z j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [firstStage]
  · intro j; fin_cases j <;> simp [firstStage]
  · intro i; fin_cases i <;> simp [firstStage]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [firstStage, S]

/-- **Item 1 (formula).** `reconstruct` in the reference's own block notation,
entry family by entry family.  This is the same-source reconstruction the card fixes:
`M 0 0 = 1`, `M 0 1 = -e`, `M 0 (j+2) = v_j`, `M 1 0 = β`, `M 1 1 = p - eβ`,
`M 1 (j+2) = q_j + βv_j`, `M (i+2) 0 = u_i`, `M (i+2) 1 = px_i - eu_i`,
`M (i+2) (j+2) = D_ij + x_i q_j + u_i v_j`. -/
theorem reconstruct_table (z : Point) :
    reconstruct z 0 0 = 1 ∧
      reconstruct z 0 1 = -e z ∧
      (∀ j : Fin 3, reconstruct z 0 j.succ.succ = v z j) ∧
      reconstruct z 1 0 = beta z ∧
      reconstruct z 1 1 = p z - e z * beta z ∧
      (∀ j : Fin 3, reconstruct z 1 j.succ.succ = q z j + beta z * v z j) ∧
      (∀ i : Fin 3, reconstruct z i.succ.succ 0 = u z i) ∧
      (∀ i : Fin 3, reconstruct z i.succ.succ 1 = p z * x z i - e z * u z i) ∧
      (∀ i j : Fin 3, reconstruct z i.succ.succ j.succ.succ
        = D z i j + xv z i * q z j + u z i * v z j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [reconstruct]
  · simp [reconstruct]
  · intro j; fin_cases j <;> simp [reconstruct]
  · simp [reconstruct]
  · simp [reconstruct]
  · intro j; fin_cases j <;> simp [reconstruct, P, beta] <;> ring
  · intro i; fin_cases i <;> simp [reconstruct]
  · intro i; fin_cases i <;> simp [reconstruct]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [reconstruct, O] <;> ring

theorem reconstruct_zero_zero (z : Point) : reconstruct z 0 0 = 1 := by
  simp [reconstruct]

theorem firstStage_zero_zero (z : Point) : firstStage z 0 0 = p z := by
  simp [firstStage]

end Rho5.Certificate.B24Reconstruction
