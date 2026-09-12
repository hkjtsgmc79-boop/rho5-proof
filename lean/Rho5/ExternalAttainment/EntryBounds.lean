import Rho5.ExternalAttainment.TailEquations
import Rho5.Shared.MatrixStage

noncomputable section
namespace Rho5.ExternalAttainment
variable {x y z g : ℝ}

/-- Exhaustive 25-entry bound, including exact pivot ties. -/
theorem matrixA_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 5) : |matrixA x y z i j| ≤ 1 := by
  have nb := numerics_of_candidateBox box
  fin_cases i <;> fin_cases j
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |((-z) / y)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a02_bound (by norm_num) (by norm_num)
  · change |(-z)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a03_bound (by norm_num) (by norm_num)
  · change |(topRight x y z)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a04_bound (by norm_num) (by norm_num)
  · change |x| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a10_bound (by norm_num) (by norm_num)
  · change |((x + z) + (1:ℝ))| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a11_bound (by norm_num) (by norm_num)
  · change |(reducedB23 x y z)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a12_bound (by norm_num) (by norm_num)
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |z| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a21_bound (by norm_num) (by norm_num)
  · change |(reducedB33 x y z)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a22_bound (by norm_num) (by norm_num)
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |y| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a30_bound (by norm_num) (by norm_num)
  · change |(reducedT x y z)| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a31_bound (by norm_num) (by norm_num)
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |z| ≤ 1
    exact Bounds.abs_le (u := 1) nb.a40_bound (by norm_num) (by norm_num)
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num
  · change |(-1:ℝ)| ≤ 1
    norm_num
  · change |(1:ℝ)| ≤ 1
    norm_num

/-- Exhaustive 16-entry bound, including exact pivot ties. -/
theorem matrixF_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 4) : |matrixF x y z i j| ≤ pivotTwo x y z := by
  have nb := numerics_of_candidateBox box
  have hb : (36:ℝ)/25 ≤ pivotTwo x y z := by linarith [nb.pivotTwo_bound.1]
  fin_cases i <;> fin_cases j
  · change |(pivotTwo x y z)| ≤ pivotTwo x y z
    rw [abs_of_pos (pivotTwo_pos box)]
  · change |(headEntry x y z)| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f01_bound (by norm_num) (by norm_num)).trans hb
  · change |((x * z) - (1:ℝ))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f02_bound (by norm_num) (by norm_num)).trans hb
  · change |((1:ℝ) - (x * (topRight x y z)))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f03_bound (by norm_num) (by norm_num)).trans hb
  · change |(pivotTwo x y z)| ≤ pivotTwo x y z
    rw [abs_of_pos (pivotTwo_pos box)]
  · change |((corePivot x y z) + (headEntry x y z))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f11_bound (by norm_num) (by norm_num)).trans hb
  · change |(-(pivotTwo x y z))| ≤ pivotTwo x y z
    rw [abs_neg, abs_of_pos (pivotTwo_pos box)]
  · change |((topRight x y z) - (1:ℝ))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f13_bound (by norm_num) (by norm_num)).trans hb
  · change |((pivotTwo x y z) * (ratioRD x y z))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f20_bound (by norm_num) (by norm_num)).trans hb
  · change |(pivotTwo x y z)| ≤ pivotTwo x y z
    rw [abs_of_pos (pivotTwo_pos box)]
  · change |((1:ℝ) + (y * z))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f22_bound (by norm_num) (by norm_num)).trans hb
  · change |((1:ℝ) - (y * (topRight x y z)))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f23_bound (by norm_num) (by norm_num)).trans hb
  · change |(-(pivotTwo x y z))| ≤ pivotTwo x y z
    rw [abs_neg, abs_of_pos (pivotTwo_pos box)]
  · change |((1:ℝ) + ((z ^ 2) / y))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f31_bound (by norm_num) (by norm_num)).trans hb
  · change |((z ^ 2) - (1:ℝ))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f32_bound (by norm_num) (by norm_num)).trans hb
  · change |((1:ℝ) - (z * (topRight x y z)))| ≤ pivotTwo x y z
    exact (Bounds.abs_le (u := ((36:ℝ)/25)) nb.f33_bound (by norm_num) (by norm_num)).trans hb

/-- Exhaustive 9-entry bound, including exact pivot ties. -/
theorem matrixG_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 3) : |matrixG x y z i j| ≤ corePivot x y z := by
  have nb := numerics_of_candidateBox box
  have hb : (2:ℝ) ≤ corePivot x y z := by linarith [nb.corePivot_bound.1]
  fin_cases i <;> fin_cases j
  · change |(corePivot x y z)| ≤ corePivot x y z
    rw [abs_of_pos (corePivot_pos box)]
  · change |(coreArm x y z)| ≤ corePivot x y z
    exact (Bounds.abs_le (u := (2:ℝ)) nb.g01_bound (by norm_num) (by norm_num)).trans hb
  · change |(-(corePivot x y z))| ≤ corePivot x y z
    rw [abs_neg, abs_of_pos (corePivot_pos box)]
  · change |(corePivot x y z)| ≤ corePivot x y z
    rw [abs_of_pos (corePivot_pos box)]
  · change |((halfHeight x y z) + (coreArm x y z))| ≤ corePivot x y z
    exact (Bounds.abs_le (u := (2:ℝ)) nb.g11_bound (by norm_num) (by norm_num)).trans hb
  · change |((halfHeight x y z) - (corePivot x y z))| ≤ corePivot x y z
    exact (Bounds.abs_le (u := (2:ℝ)) nb.g12_bound (by norm_num) (by norm_num)).trans hb
  · change |(coreBottom x y z)| ≤ corePivot x y z
    exact (Bounds.abs_le (u := (2:ℝ)) nb.g20_bound (by norm_num) (by norm_num)).trans hb
  · change |(-(corePivot x y z))| ≤ corePivot x y z
    rw [abs_neg, abs_of_pos (corePivot_pos box)]
  · change |(coreCorner x y z)| ≤ corePivot x y z
    exact (Bounds.abs_le (u := (2:ℝ)) nb.g22_bound (by norm_num) (by norm_num)).trans hb

theorem candidate_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 5) : |candidateMatrix x y z g i j| ≤ 1 := by
  rw [candidate_eq_matrixA box]
  exact matrixA_abs_le box i j

theorem stageF_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 4) : |stageF x y z g i j| ≤ 1+z := by
  rw [stageF_eq box]
  exact matrixF_abs_le box i j

theorem stageG_abs_le (box : Rho5.Algebraic.CandidateBox x y z g)
    (i j : Fin 3) : |stageG x y z g i j| ≤ p3 x y z g := by
  rw [stageG_eq box, p3_eq box]
  exact matrixG_abs_le box i j

theorem stageH_abs_le
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0)
    (i j : Fin 2) : |stageH x y z g i j| ≤ g/2 := by
  have hg : 0 < g/2 := by linarith [candidate_g_gt_four box]
  rw [stageH_eq_targetTail box h1 h2 h3]
  fin_cases i <;> fin_cases j <;> simp [targetTail, abs_of_pos hg]

theorem stageL_abs_le
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0)
    (i j : Fin 1) : |stageL x y z g i j| ≤ g := by
  have hg : 0 < g := by linarith [candidate_g_gt_four box]
  fin_cases i <;> fin_cases j
  show |stageL x y z g 0 0| ≤ g
  rw [stageL_00 box h1 h2 h3, abs_of_pos hg]

theorem candidate_entry_max (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.matrixEntryMax (candidateMatrix x y z g) = 1 := by
  apply le_antisymm
  · unfold Rho5.matrixEntryMax
    exact Finset.sup'_le Finset.univ_nonempty _
      (fun ij _ => candidate_abs_le box ij.1 ij.2)
  · have h := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax
      (candidateMatrix x y z g) 0 0
    simpa only [candidate_00, abs_one] using h

/-- The coarse displayed bounds are formally derived, not extra assumptions. -/
theorem pivot_bounds (box : Rho5.Algebraic.CandidateBox x y z g) :
    (1453:ℝ)/1000 < 1+z ∧ 1+z < (1454:ℝ)/1000 ∧
    (2074:ℝ)/1000 < p3 x y z g ∧ p3 x y z g < (2075:ℝ)/1000 ∧
    (4132:ℝ)/1000 < g ∧ g < (4133:ℝ)/1000 := by
  have nb := numerics_of_candidateBox box
  have ng := (narrowBox_of_candidateBox box).gb
  simp only [p3_eq box]
  change (1453:ℝ)/1000 < pivotTwo x y z ∧
    pivotTwo x y z < (1454:ℝ)/1000 ∧
    (2074:ℝ)/1000 < corePivot x y z ∧ corePivot x y z < (2075:ℝ)/1000 ∧
    (4132:ℝ)/1000 < g ∧ g < (4133:ℝ)/1000
  exact ⟨by linarith [nb.pivotTwo_bound.1], by linarith [nb.pivotTwo_bound.2],
    by linarith [nb.corePivot_bound.1], by linarith [nb.corePivot_bound.2],
    by linarith [ng.1], by linarith [ng.2]⟩

end Rho5.ExternalAttainment
