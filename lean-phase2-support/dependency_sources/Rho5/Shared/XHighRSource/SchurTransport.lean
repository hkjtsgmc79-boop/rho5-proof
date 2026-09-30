import Rho5.Shared.XHighRSource.Transpose
import Rho5.Certificate.B24Extraction.Extract
import Rho5.Shared.PivotReindex.Schur

/-!
# D145 stage B — Schur-level transport of the real transpose

`SatFrame` (D119) is carried to `transX M`: the Schur layers of `transX M` are signed transposes of
the layers of `M`, so `p, k, r, w` are preserved.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t S4_apply S3_apply T2_apply)
open Rho5.Shared.V43MatrixRoundTrip

/-- the four-index sign `J4 i = D (i+1)` = (-1,1,-1,-1). -/
def sgnZ4 (i : Fin 4) : ℝ := if (i : ℕ) = 1 then 1 else -1
/-- the three-index sign `J3 i = D (i+2)` = (1,-1,-1). -/
def sgnZ3 (i : Fin 3) : ℝ := if (i : ℕ) = 0 then 1 else -1
/-- the two-index sign `J2 i = D (i+3)` = (-1,-1). -/
def sgnZ2 (_ : Fin 2) : ℝ := -1

theorem abs_sgnD (i : Fin 5) : |sgnD i| = 1 := by
  fin_cases i <;> simp [sgnD, sgnQ, sgnJ]
theorem abs_sgnZ4 (i : Fin 4) : |sgnZ4 i| = 1 := by
  fin_cases i <;> simp [sgnZ4]
theorem abs_sgnZ3 (i : Fin 3) : |sgnZ3 i| = 1 := by
  fin_cases i <;> simp [sgnZ3]
theorem abs_sgnZ2 (i : Fin 2) : |sgnZ2 i| = 1 := by
  simp [sgnZ2]

/-- entrywise absolute values are preserved up to the index swap. -/
theorem abs_transX (M : M5) (i j : Fin 5) : |transX M i j| = |M j i| := by
  rw [transX, abs_mul, abs_mul, abs_sgnD, abs_sgnD]
  ring

/-- **`S4` conjugation**: `S4_new = J4 · (S4 M)^T · J4`. -/
theorem S4_transX (M : M5) (h : SatFrame M) (i j : Fin 4) :
    S4 (transX M) i j = sgnZ4 i * sgnZ4 j * S4 M j i := by
  rw [S4_apply, S4_apply]
  simp only [transX, h.h00]
  fin_cases i <;> fin_cases j <;> simp [sgnZ4, sgnD, sgnQ, sgnJ] <;> ring

/-- `p` is preserved. -/
theorem p_transX (M : M5) (h : SatFrame M) : p (transX M) = p M := by
  simp only [p]
  rw [S4_transX M h]
  norm_num [sgnZ4]

/-- **`S3` conjugation**: `S3_new = J3 · (S3 M)^T · J3`. -/
theorem S3_transX (M : M5) (h : SatFrame M) (i j : Fin 3) :
    S3 (transX M) i j = sgnZ3 i * sgnZ3 j * S3 M j i := by
  have hp : S4 M 0 0 ≠ 0 := ne_of_gt h.hp
  simp only [S3_apply, S4_transX M h]
  fin_cases i <;> fin_cases j <;> simp [sgnZ3, sgnZ4] <;> field_simp [hp] <;> ring

/-- **`T2` conjugation**: `T2_new = J2 · (T2 M)^T · J2`. -/
theorem T2_transX (M : M5) (h : SatFrame M) (i j : Fin 2) :
    T2 (transX M) i j = sgnZ2 i * sgnZ2 j * T2 M j i := by
  have hk : S3 M 0 0 ≠ 0 := ne_of_gt h.hk
  simp only [T2_apply, S3_transX M h]
  fin_cases i <;> fin_cases j <;> simp [sgnZ2, sgnZ3] <;> field_simp [hk] <;> ring

/-! ## The four extracted scalars, and the free tail entry -/

theorem k_transX (M : M5) (h : SatFrame M) : k (transX M) = k M := by
  simp only [k]
  rw [S3_transX M h]
  norm_num [sgnZ3]

theorem r_transX (M : M5) (h : SatFrame M) : r (transX M) = r M := by
  simp only [r]
  rw [T2_transX M h]
  norm_num [sgnZ2]

/-- The off-diagonal tail entries are exchanged, as in the plain transpose. -/
theorem s_transX (M : M5) (h : SatFrame M) : s (transX M) = t M := by
  simp only [s, t]
  rw [T2_transX M h]
  norm_num [sgnZ2]

theorem t_transX (M : M5) (h : SatFrame M) : t (transX M) = s M := by
  simp only [s, t]
  rw [T2_transX M h]
  norm_num [sgnZ2]

theorem kX_transX (M : M5) (h : SatFrame M) : kX (transX M) = kX M := k_transX M h
theorem rX_transX (M : M5) (h : SatFrame M) : rX (transX M) = rX M := r_transX M h

/-- The free tail entry `w = T2 1 1` is preserved. -/
theorem wX_transX (M : M5) (h : SatFrame M) : wX (transX M) = wX M := by
  simp only [wX]
  rw [T2_transX M h]
  norm_num [sgnZ2]

/-- Hence the frozen height `F = r - w` is preserved by the real transpose. -/
theorem height_transX (M : M5) (h : SatFrame M) :
    Rho5.LocalAnalysis.height (extractX (transX M)) = Rho5.LocalAnalysis.height (extractX M) := by
  rw [height_extractX_eq, height_extractX_eq, rX_transX M h, wX_transX M h]

/-! ## `matrixEntryMax` and the four complete-pivot qualifications -/

/-- The frozen entry maximum is invariant: the index swap `(i,j) ↦ (j,i)` permutes the entries. -/
theorem matrixEntryMax_transX (M : M5) : Rho5.matrixEntryMax (transX M) = Rho5.matrixEntryMax M := by
  apply le_antisymm
  · rw [Rho5.matrixEntryMax, Rho5.matrixEntryMax]
    refine Finset.sup'_le Finset.univ_nonempty (fun ij : Fin 5 × Fin 5 => |transX M ij.1 ij.2|)
      (fun ij _ => ?_)
    simp only []
    rw [abs_transX]
    exact Finset.le_sup' (f := fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|)
      (Finset.mem_univ (ij.2, ij.1))
  · rw [Rho5.matrixEntryMax, Rho5.matrixEntryMax]
    refine Finset.sup'_le Finset.univ_nonempty (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|)
      (fun ij _ => ?_)
    simp only []
    rw [← abs_transX M ij.2 ij.1]
    exact Finset.le_sup' (f := fun ij : Fin 5 × Fin 5 => |transX M ij.1 ij.2|)
      (Finset.mem_univ (ij.2, ij.1))

/-- `matrixEntryMax = 1` is transported. -/
theorem matrixEntryMax_transX_eq_one (M : M5) (h : SatFrame M) :
    Rho5.matrixEntryMax (transX M) = 1 := by
  rw [matrixEntryMax_transX, h.hmax]

/-- The base complete pivot is transported (the index swap is a bijection). -/
theorem cp1_transX (M : M5) (h : SatFrame M) :
    Rho5.Pivot.IsCompletePivot (transX M) 0 0 := by
  intro i j
  rw [abs_transX M i j, abs_transX M 0 0]
  exact h.cp1 j i

/-- Absolute values of the `S4` layer: the signs drop and the entries transpose. -/
theorem abs_S4_transX (M : M5) (h : SatFrame M) (i j : Fin 4) :
    |S4 (transX M) i j| = |S4 M j i| := by
  rw [S4_transX M h]
  simp only [abs_mul, abs_sgnZ4, one_mul]

theorem abs_S3_transX (M : M5) (h : SatFrame M) (i j : Fin 3) :
    |S3 (transX M) i j| = |S3 M j i| := by
  rw [S3_transX M h]
  simp only [abs_mul, abs_sgnZ3, one_mul]

theorem abs_T2_transX (M : M5) (h : SatFrame M) (i j : Fin 2) :
    |T2 (transX M) i j| = |T2 M j i| := by
  rw [T2_transX M h]
  simp only [abs_mul, abs_sgnZ2, one_mul]

theorem cp2_transX (M : M5) (h : SatFrame M) :
    Rho5.Pivot.IsCompletePivot (S4 (transX M)) 0 0 := by
  intro i j
  rw [abs_S4_transX M h i j, abs_S4_transX M h 0 0]
  exact h.cp2 j i

theorem cp3_transX (M : M5) (h : SatFrame M) :
    Rho5.Pivot.IsCompletePivot (S3 (transX M)) 0 0 := by
  intro i j
  rw [abs_S3_transX M h i j, abs_S3_transX M h 0 0]
  exact h.cp3 j i

theorem cp4_transX (M : M5) (h : SatFrame M) :
    Rho5.Pivot.IsCompletePivot (T2 (transX M)) 0 0 := by
  intro i j
  rw [abs_T2_transX M h i j, abs_T2_transX M h 0 0]
  exact h.cp4 j i

/-- **The `SatFrame` class is carried to the real transpose.**  All eleven fields are paid: the
normalisation, the entry maximum, the four complete-pivot qualifications, the three positive pivots
and the two tail-balance equalities. -/
theorem satFrame_transX (M : M5) (h : SatFrame M) : SatFrame (transX M) := by
  have h0 : sgnD (0 : Fin 5) = 1 := by norm_num [sgnD, sgnQ, sgnJ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [transX, h.h00, h0, mul_one]
  · exact matrixEntryMax_transX_eq_one M h
  · exact cp1_transX M h
  · exact cp2_transX M h
  · exact cp3_transX M h
  · exact cp4_transX M h
  · rw [p_transX M h]; exact h.hp
  · rw [k_transX M h]; exact h.hk
  · rw [r_transX M h]; exact h.hr
  · rw [s_transX M h, r_transX M h]; exact h.ht
  · rw [t_transX M h, r_transX M h]; exact h.hs

end

end Rho5.Shared.XHighRSource
