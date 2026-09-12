import Rho5.Certificate.B24Reconstruction.Basic
import Rho5.Certificate.B24Reconstruction.FirstPivot
import Rho5.Certificate.B24Reconstruction.SecondPivot

/-!
# D28 / B24Reconstruction — entry maximum and pivot legality of the first two steps

**Item 3 of the card.**

* `matrixEntryMax (reconstruct z) = 1` and `(0, 0)` is a complete pivot of the
  reconstructed matrix, from `B16.Physical` (which supplies the `P_j` and `O_ij`
  rows, `|q_j| ≤ p`, `|S_ij| ≤ p`, `|D_ij| ≤ k`, `r > 0` and the height law) together
  with the explicit head band `HeadBand` (which supplies the fields `Physical` does
  **not** have: `|e|`, `|β|`, `|p - eβ|`, `|u_i|`, `|x_i|`, `|v_j|`, `|L_i| ≤ 1`).
  The matrix entry `M 0 0 = 1` is what pins the maximum to exactly `1`, so the first
  pivot is legal in the strongest available sense (`PivotReady`: complete pivot *and*
  nonzero pivot entry).
* The second stage's `(0, 0)` is a complete pivot under exactly the four conditions
  the card lists — `p > 0`, `|x_i| ≤ 1`, `|q_j| ≤ p`, `|S_ij| ≤ p` — and then
  `PivotReady` again, with the nonzero pivot entry `firstStage 0 0 = p`.

No field of `HeadBand` states any of these conclusions, and no boundedness is
inferred from `Physical` that `Physical` does not contain.
-/

namespace Rho5.Certificate.B24Reconstruction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)

/-! ## The entry bound of the reconstructed matrix -/

/-- Every one of the 25 entries of `reconstruct z` is bounded by `1` in absolute
value: the `P_j` and `O_ij` rows come from `Physical`, the `e`, `β`, `p - eβ`, `u`,
`x`, `v`, `L` rows from the explicit head band. -/
theorem abs_entry_reconstruct_le_one (z : Point) (hz : Physical z) (h : HeadBand z) :
    ∀ i j : Fin 5, |reconstruct z i j| ≤ 1 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct] <;>
    first
      | exact le_of_eq abs_one
      | exact h.abs_e
      | exact h.abs_beta
      | exact h.abs_p_sub_e_mul_beta
      | exact h.abs_v 0 | exact h.abs_v 1 | exact h.abs_v 2
      | exact h.abs_u 0 | exact h.abs_u 1 | exact h.abs_u 2
      | exact h.abs_L 0 | exact h.abs_L 1 | exact h.abs_L 2
      | exact hz.p_bound 0 | exact hz.p_bound 1 | exact hz.p_bound 2
      | exact hz.o_bound 0 0 | exact hz.o_bound 0 1 | exact hz.o_bound 0 2
      | exact hz.o_bound 1 0 | exact hz.o_bound 1 1 | exact hz.o_bound 1 2
      | exact hz.o_bound 2 0 | exact hz.o_bound 2 1 | exact hz.o_bound 2 2

/-- **Item 3 (maximum).**  The entry maximum of the reconstructed matrix is exactly
`1`, because `M 0 0 = 1` and every entry is bounded by `1`. -/
theorem matrixEntryMax_reconstruct (z : Point) (hz : Physical z) (h : HeadBand z) :
    Rho5.matrixEntryMax (reconstruct z) = 1 := by
  have hle : ∀ i j : Fin 5, |reconstruct z i j| ≤ 1 :=
    abs_entry_reconstruct_le_one z hz h
  have hmax : Rho5.matrixEntryMax (reconstruct z) ≤ 1 := by
    unfold Rho5.matrixEntryMax
    refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => hle ij.1 ij.2)
  have hge : 1 ≤ Rho5.matrixEntryMax (reconstruct z) := by
    have h00 := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax (reconstruct z) 0 0
    rw [reconstruct_zero_zero] at h00
    simpa using h00
  exact le_antisymm hmax hge

/-! ## First pivot legality -/

/-- **Item 3 (first pivot).**  `(0, 0)` is a complete pivot of the reconstructed
matrix: every entry is bounded by the pivot entry `M 0 0 = 1`. -/
theorem isCompletePivot_reconstruct_zero_zero (z : Point) (hz : Physical z)
    (h : HeadBand z) : Rho5.Pivot.IsCompletePivot (reconstruct z) 0 0 := by
  intro i j
  rw [reconstruct_zero_zero, abs_one]
  exact abs_entry_reconstruct_le_one z hz h i j

/-- **Item 3 (first pivot, qualified).**  The first step is *ready*: `(0, 0)` is a
complete pivot and its entry is nonzero.  This is the frozen
`Rho5.PivotReindex.PivotReady`, so the next stage can be fed directly. -/
theorem pivotReady_reconstruct_zero_zero (z : Point) (hz : Physical z) (h : HeadBand z) :
    Rho5.PivotReindex.PivotReady (reconstruct z) 0 0 :=
  Rho5.PivotReindex.pivotReady_of_ne_zero
    (fun hzero => by
      have h1 : reconstruct z 0 0 = (1 : ℝ) := reconstruct_zero_zero z
      rw [hzero] at h1
      simp at h1)
    (isCompletePivot_reconstruct_zero_zero z hz h)

theorem reconstruct_ne_zero (z : Point) : reconstruct z ≠ 0 := by
  intro hzero
  have h1 : reconstruct z 0 0 = (1 : ℝ) := reconstruct_zero_zero z
  rw [hzero] at h1
  simp at h1

/-! ## Second pivot legality -/

/-- **Item 3 (second pivot).**  Under exactly `p > 0`, `|x_i| ≤ 1`, `|q_j| ≤ p` and
`|S_ij| ≤ p`, the active corner `(0, 0)` of the first stage is a complete pivot: the
pivot entry is `p`, the first row/column entries are `q_j` and `p x_i`, and the
`3 × 3` block is `S_ij = D_ij + x_i q_j`. -/
theorem isCompletePivot_firstStage_zero_zero (z : Point) (hp0 : 0 < p z)
    (hx : ∀ i, |x z i| ≤ 1) (hq : ∀ j, |q z j| ≤ p z) (hS : ∀ i j, |S z i j| ≤ p z) :
    Rho5.Pivot.IsCompletePivot (firstStage z) 0 0 := by
  have hpabs : |p z| = p z := abs_of_pos hp0
  have h00 : |p z| ≤ |p z| := le_rfl
  have hq' : ∀ j : Fin 3, |q z j| ≤ |p z| := fun j => by rw [hpabs]; exact hq j
  have hx' : ∀ i : Fin 3, |p z| * |x z i| ≤ |p z| := fun i =>
    mul_le_of_le_one_right (abs_nonneg _) (hx i)
  have hS' : ∀ i j : Fin 3, |S z i j| ≤ |p z| := fun i j => by rw [hpabs]; exact hS i j
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [firstStage] <;>
    first
      | exact h00
      | exact hq' _
      | exact hx' _
      | exact hS' _ _

/-- **Item 3 (second pivot, qualified).**  With `p > 0` the pivot entry
`firstStage 0 0 = p` is nonzero, so the second step is legal: the active corner is a
complete pivot *and* its entry does not vanish.  (The frozen `PivotReady` structure is
the `Matrix5` form and applies to the first stage; for the `4 × 4` second stage the
same two facts are stated directly, with no new structure invented.) -/
theorem firstStage_ready_zero_zero (z : Point) (hp0 : 0 < p z)
    (hx : ∀ i, |x z i| ≤ 1) (hq : ∀ j, |q z j| ≤ p z) (hS : ∀ i j, |S z i j| ≤ p z) :
    Rho5.Pivot.IsCompletePivot (firstStage z) 0 0 ∧ firstStage z 0 0 ≠ 0 :=
  ⟨isCompletePivot_firstStage_zero_zero z hp0 hx hq hS,
    fun h0 => (ne_of_gt hp0) (by simpa [firstStage_zero_zero z] using h0)⟩

/-! ## The same two legality statements read off `Physical` + `HeadBand` -/

/-- The second pivot is legal from `Physical` (which supplies `|q_j| ≤ p` and
`|S_ij| ≤ p`), the head band's `|x_i| ≤ 1`, and the explicit positivity `p > 0`
(which `Physical` does **not** contain). -/
theorem isCompletePivot_firstStage_of_physical (z : Point) (hz : Physical z)
    (h : HeadBand z) (hp0 : 0 < p z) :
    Rho5.Pivot.IsCompletePivot (firstStage z) 0 0 :=
  isCompletePivot_firstStage_zero_zero z hp0 h.abs_x (fun j => hz.q_bound j)
    (fun i j => hz.s_bound i j)

/-- Qualified form of the previous statement. -/
theorem firstStage_ready_of_physical (z : Point) (hz : Physical z) (h : HeadBand z)
    (hp0 : 0 < p z) :
    Rho5.Pivot.IsCompletePivot (firstStage z) 0 0 ∧ firstStage z 0 0 ≠ 0 :=
  firstStage_ready_zero_zero z hp0 h.abs_x (fun j => hz.q_bound j)
    (fun i j => hz.s_bound i j)

end Rho5.Certificate.B24Reconstruction
