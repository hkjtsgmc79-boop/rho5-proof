import Rho5.ExternalAttainment.EntryBounds
import Rho5.Shared.CompletePivotPath.Basic

noncomputable section
namespace Rho5.ExternalAttainment

/-- The frozen general-pivot Schur update really is the fixed update at (0,0).
This explicitly discharges the remaining-index/reindexing interface. -/
theorem pivotSchur_leading {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Rho5.PivotReindex.pivotSchur A 0 0 = Rho5.Pivot.fixedSchur A := by
  rw [Rho5.PivotReindex.pivotSchur,
    Rho5.PivotReindex.movePivot_zero_zero_eq]

/-- A bridge to the *existing* LegalTrace constructor, allowing all ties. -/
theorem legalTrace_leading {n : ℕ}
    {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} {a : ℝ} {tail : List ℝ}
    (h00 : A 0 0 = a) (ha : 0 < a)
    (hbound : ∀ i j, |A i j| ≤ a)
    (htail : Rho5.CompletePivotPath.LegalTrace (Rho5.Pivot.fixedSchur A) tail) :
    Rho5.CompletePivotPath.LegalTrace A (a :: tail) := by
  have hp : Rho5.Pivot.IsCompletePivot A 0 0 := by
    intro i j
    rw [h00, abs_of_pos ha]
    exact hbound i j
  have hn : A 0 0 ≠ 0 := by rw [h00]; exact ne_of_gt ha
  have ht : Rho5.CompletePivotPath.LegalTrace
      (Rho5.PivotReindex.pivotSchur A 0 0) tail := by
    rw [pivotSchur_leading]
    exact htail
  have hs := Rho5.CompletePivotPath.LegalTrace.step 0 0 hp hn ht
  simpa only [h00, abs_of_pos ha] using hs

theorem candidate_legalTrace {x y z g : ℝ}
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    Rho5.CompletePivotPath.LegalTrace
      (candidateMatrix x y z g) (candidateValues x y z g) := by
  have hg : 0 < g := by linarith [candidate_g_gt_four box]
  have hg2 : 0 < g/2 := by linarith
  have hp : 0 < 1+z := pivotTwo_pos box
  have hk : 0 < p3 x y z g := by rw [p3_eq box]; exact corePivot_pos box
  have hlast : Rho5.Pivot.fixedSchur (stageL x y z g) =
      (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
    funext i j
    exact Fin.elim0 i
  have ht0 : Rho5.CompletePivotPath.LegalTrace
      (Rho5.Pivot.fixedSchur (stageL x y z g)) [] := by
    rw [hlast]
    exact Rho5.CompletePivotPath.LegalTrace.empty
  have ht1 : Rho5.CompletePivotPath.LegalTrace (stageL x y z g) [g] :=
    legalTrace_leading (stageL_00 box h1 h2 h3) hg
      (stageL_abs_le box h1 h2 h3) ht0
  have hh00 : stageH x y z g 0 0 = g/2 := by
    rw [stageH_eq_targetTail box h1 h2 h3]
    rfl
  have ht2 : Rho5.CompletePivotPath.LegalTrace (stageH x y z g) [g/2,g] :=
    legalTrace_leading hh00 hg2 (stageH_abs_le box h1 h2 h3) ht1
  have ht3 : Rho5.CompletePivotPath.LegalTrace
      (stageG x y z g) [p3 x y z g,g/2,g] :=
    legalTrace_leading (by rfl) hk (stageG_abs_le box) ht2
  have ht4 : Rho5.CompletePivotPath.LegalTrace
      (stageF x y z g) [1+z,p3 x y z g,g/2,g] :=
    legalTrace_leading (stageF_00 box) hp (stageF_abs_le box) ht3
  exact legalTrace_leading (candidate_00 x y z g) (by norm_num)
    (candidate_abs_le box) ht4

end Rho5.ExternalAttainment
