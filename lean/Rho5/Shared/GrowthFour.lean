import Rho5.Shared.GrowthSupremum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# D44 — a real five-order growth witness: `H4 ⊕ [1]` gives `4 ≤ rho5Trace`

The concrete matrix of the card: the fourth-order Hadamard matrix in the top-left
`4 × 4` block, `1` in the bottom-right corner and `0` across the two off-diagonal
blocks:

`H = [[1,1,1,1,0], [1,-1,1,-1,0], [1,1,-1,-1,0], [1,-1,-1,1,0], [0,0,0,0,1]]`.

All 25 entries are given literally (there is no existence hypothesis and no
placeholder matrix): this is the actual real matrix of the card.

Eliminating with the **real** frozen `Rho5.PivotReindex.pivotSchur` at the active
corner `(0, 0)` at every stage gives the successive matrices

* `S1 = pivotSchur H 0 0 = [[-2,0,-2,0],[0,-2,-2,0],[-2,-2,0,0],[0,0,0,1]]`,
* `S2 = pivotSchur S1 0 0 = [[-2,-2,0],[-2,2,0],[0,0,1]]`,
* `S3 = pivotSchur S2 0 0 = [[4,0],[0,1]]`,
* `S4 = pivotSchur S3 0 0 = [[1]]`,
* `pivotSchur S4 0 0 = 0` (the `0 × 0` matrix),

with signed pivot values `1, -2, -2, 4, 1`.  The `LegalTrace` records the *absolute*
values, so the trace is `[1, 2, 2, 4, 1]` and its peak is `4` — the last pivot `1`
is **not** the peak.  Since `matrixEntryMax H = 1`, the actual growth ratio is
`4 / 1 = 4`, hence `4 ∈ GrowthValues` and `4 ≤ rho5Trace` through D18's bounded
supremum interface.

Every entry of every stage is checked by the real formulas and rational arithmetic;
the expected values are *not* assumed anywhere.

Scope: this is a **lower bound witness** only.  It does not claim that `4` is the
five-order sharp value, does not claim a fourth-order global upper bound, does not
claim `4 = alpha`, and does not modify or re-prove D18's earlier lower bound.
-/

namespace Rho5.GrowthFour

open Rho5

/-! ## The concrete matrix -/

/-- The fourth-order Hadamard block of the card. -/
noncomputable def hadamard4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![1, 1, 1, 1], ![1, -1, 1, -1], ![1, 1, -1, -1], ![1, -1, -1, 1]]

/-- **Item 1 (the actual matrix).**  `H4 ⊕ [1]`: the Hadamard block in the top-left
`4 × 4`, `1` at `(4, 4)`, and `0` in the two off-diagonal blocks.  All 25 entries are
literal. -/
noncomputable def H : Matrix5 :=
  Matrix.of ![![1, 1, 1, 1, 0], ![1, -1, 1, -1, 0], ![1, 1, -1, -1, 0],
    ![1, -1, -1, 1, 0], ![0, 0, 0, 0, 1]]

theorem H_zero_zero : H 0 0 = 1 := by simp [H]

theorem H_ne_zero : H ≠ 0 := by
  intro h0
  have h := H_zero_zero
  rw [h0] at h
  norm_num at h

/-- Every entry of `H` is bounded by `1` in absolute value (the entries are `±1` and
`0`). -/
theorem abs_H_entry_le_one (i j : Fin 5) : |H i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp [H] <;> norm_num

/-- **Item 1 (`matrixEntryMax`).**  The frozen entry maximum of `H` is exactly `1`,
because `H 0 0 = 1` and every entry is bounded by `1`. -/
theorem matrixEntryMax_H : matrixEntryMax H = 1 := by
  have hmax : matrixEntryMax H ≤ 1 := by
    unfold matrixEntryMax
    refine Finset.sup'_le Finset.univ_nonempty _ (fun ij _ => abs_H_entry_le_one ij.1 ij.2)
  have hge : 1 ≤ matrixEntryMax H := by
    have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax H 0 0
    rw [H_zero_zero] at h
    simpa using h
  exact le_antisymm hmax hge

/-! ## The successive Schur matrices -/

/-- The first update of `H`. -/
noncomputable def S1 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![-2, 0, -2, 0], ![0, -2, -2, 0], ![-2, -2, 0, 0], ![0, 0, 0, 1]]

/-- The second update. -/
noncomputable def S2 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of ![![-2, -2, 0], ![-2, 2, 0], ![0, 0, 1]]

/-- The third update. -/
noncomputable def S3 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of ![![4, 0], ![0, 1]]

/-- The fourth update: the single remaining entry. -/
noncomputable def S4 : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of ![![1]]

theorem S1_zero_zero : S1 0 0 = -2 := by simp [S1]

theorem S2_zero_zero : S2 0 0 = -2 := by simp [S2]

theorem S3_zero_zero : S3 0 0 = 4 := by simp [S3]

theorem S4_zero_zero : S4 0 0 = 1 := by simp [S4]

/-! ## Item 2 — the real elimination steps -/

/-- The frozen Schur update of `H` at the active corner is the explicit `S1`. -/
theorem pivotSchur_H : Rho5.PivotReindex.pivotSchur H 0 0 = S1 := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;> simp [H, S1] <;> norm_num

theorem pivotSchur_S1 : Rho5.PivotReindex.pivotSchur S1 0 0 = S2 := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;> simp [S1, S2] <;> norm_num

theorem pivotSchur_S2 : Rho5.PivotReindex.pivotSchur S2 0 0 = S3 := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;> simp [S2, S3] <;> norm_num

theorem pivotSchur_S3 : Rho5.PivotReindex.pivotSchur S3 0 0 = S4 := by
  funext i j
  rw [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq]
  simp only [Rho5.Pivot.fixedSchur]
  fin_cases i <;> fin_cases j <;> simp [S3, S4] <;> norm_num

/-- The fifth step reaches the `0 × 0` matrix: the trace ends without an extra `0`. -/
theorem pivotSchur_S4 : Rho5.PivotReindex.pivotSchur S4 0 0 = 0 := by
  funext i j
  exact Fin.elim0 i

/-! ## Item 2 — legality of every step -/

theorem completePivot_H : Rho5.Pivot.IsCompletePivot H 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [H] <;> norm_num

theorem completePivot_S1 : Rho5.Pivot.IsCompletePivot S1 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [S1] <;> norm_num

theorem completePivot_S2 : Rho5.Pivot.IsCompletePivot S2 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [S2] <;> norm_num

theorem completePivot_S3 : Rho5.Pivot.IsCompletePivot S3 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [S3] <;> norm_num

theorem completePivot_S4 : Rho5.Pivot.IsCompletePivot S4 0 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [S4] <;> norm_num

/-! ## Item 3 — the real legal trace and the growth ratio -/

/-- **Item 3 (legal trace).**  The actual `LegalTrace` of `H`: each step is a real
`Rho5.CompletePivotPath.LegalTrace.step` with the frozen complete-pivot predicate and a
non-zero pivot, and the recorded values are the absolute pivot values. -/
theorem legalTrace_H : Rho5.CompletePivotPath.LegalTrace H [1, 2, 2, 4, 1] := by
  have h : Rho5.CompletePivotPath.LegalTrace H
      [|H 0 0|, |S1 0 0|, |S2 0 0|, |S3 0 0|, |S4 0 0|] := by
    refine Rho5.CompletePivotPath.LegalTrace.step (0 : Fin 5) 0 completePivot_H ?_ ?_
    · rw [H_zero_zero]; norm_num
    · rw [pivotSchur_H]
      refine Rho5.CompletePivotPath.LegalTrace.step (0 : Fin 4) 0 completePivot_S1 ?_ ?_
      · rw [S1_zero_zero]; norm_num
      · rw [pivotSchur_S1]
        refine Rho5.CompletePivotPath.LegalTrace.step (0 : Fin 3) 0 completePivot_S2 ?_ ?_
        · rw [S2_zero_zero]; norm_num
        · rw [pivotSchur_S2]
          refine Rho5.CompletePivotPath.LegalTrace.step (0 : Fin 2) 0 completePivot_S3 ?_ ?_
          · rw [S3_zero_zero]; norm_num
          · rw [pivotSchur_S3]
            refine Rho5.CompletePivotPath.LegalTrace.step (0 : Fin 1) 0 completePivot_S4 ?_ ?_
            · rw [S4_zero_zero]; norm_num
            · rw [pivotSchur_S4]
              exact Rho5.CompletePivotPath.LegalTrace.empty
  simpa [H_zero_zero, S1_zero_zero, S2_zero_zero, S3_zero_zero, S4_zero_zero] using h

/-- **Item 3 (peak).**  The peak of the full trace is `4`; the final pivot `1` is not
the peak (`tracePeak` folds `max` over the whole list). -/
theorem tracePeak_five : Rho5.GrowthModel.tracePeak [1, 2, 2, 4, 1] = 4 := by
  refine le_antisymm ?_ ?_
  · refine Rho5.GrowthModel.tracePeak_le (by norm_num) ?_
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · exact Rho5.GrowthModel.le_tracePeak (by simp)

/-- **Item 3 (growth ratio).**  The actual growth ratio of `H` along its trace is
`4`. -/
theorem growthRatio_H : Rho5.GrowthModel.growthRatio H [1, 2, 2, 4, 1] = 4 := by
  rw [Rho5.GrowthModel.growthRatio_eq, matrixEntryMax_H, tracePeak_five]
  norm_num

/-! ## Item 4 — the new lower bound -/

/-- **Item 4 (`4 ∈ GrowthValues`).**  The witness is the concrete matrix `H` with its
real trace; the defining conditions (`H ≠ 0` and `LegalTrace H […]`) are *proved*
above, not assumed. -/
theorem four_mem_growthValues : (4 : ℝ) ∈ Rho5.GrowthModel.GrowthValues :=
  ⟨H, [1, 2, 2, 4, 1], H_ne_zero, legalTrace_H, growthRatio_H.symm⟩

/-- **Item 4 (`4 ≤ rho5Trace`).**  Through D18's bounded-supremum interface
(`le_rho5Trace`), the new witness improves the previous lower bound `2` to `4`. -/
theorem four_le_rho5Trace : (4 : ℝ) ≤ Rho5.GrowthSupremum.rho5Trace :=
  Rho5.GrowthSupremum.le_rho5Trace four_mem_growthValues

/-- The new lower bound together with D18's coarse upper bound. -/
theorem four_le_rho5Trace_le_sixteen :
    (4 : ℝ) ≤ Rho5.GrowthSupremum.rho5Trace ∧ Rho5.GrowthSupremum.rho5Trace ≤ 16 :=
  ⟨four_le_rho5Trace, Rho5.GrowthSupremum.rho5Trace_le_sixteen⟩

end Rho5.GrowthFour
