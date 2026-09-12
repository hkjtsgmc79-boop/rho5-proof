import Rho5.ExternalAttainment.LegalTrace
import Rho5.Shared.GrowthModel

noncomputable section
namespace Rho5.ExternalAttainment

variable {x y z g : ℝ}

/-- The *whole trace* has peak g, not merely a last entry equal to g. -/
theorem candidate_tracePeak (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.GrowthModel.tracePeak (candidateValues x y z g) = g := by
  have hg : 0 < g := by linarith [candidate_g_gt_four box]
  obtain ⟨_, hpU, _, hkU, hgL, _⟩ := pivot_bounds box
  apply le_antisymm
  · apply Rho5.GrowthModel.tracePeak_le (le_of_lt hg)
    intro v hv
    simp only [candidateValues, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
    · linarith
    · exact le_rfl
  · exact Rho5.GrowthModel.le_tracePeak (by simp [candidateValues])

theorem candidate_growthRatio (box : Rho5.Algebraic.CandidateBox x y z g) :
    Rho5.GrowthModel.growthRatio
      (candidateMatrix x y z g) (candidateValues x y z g) = g := by
  rw [Rho5.GrowthModel.growthRatio_eq, candidate_entry_max box,
    div_one, candidate_tracePeak box]

/-- Requested conditional attainment theorem.  Its only hypotheses are the
original CandidateBox and the original P1=P2=P3=0.  No CP, entry-bound,
root-existence, alpha-identity or attained-growth hypothesis is added. -/
theorem candidate_attainment
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    Rho5.matrixEntryMax (candidateMatrix x y z g) = 1 ∧
    Rho5.CompletePivotPath.LegalTrace
      (candidateMatrix x y z g) [1,1+z,p3 x y z g,g/2,g] ∧
    Rho5.GrowthModel.growthRatio
      (candidateMatrix x y z g) [1,1+z,p3 x y z g,g/2,g] = g ∧
    g ∈ Rho5.GrowthModel.GrowthValues ∧
    g ∈ Rho5.GrowthModel.NormalizedGrowthValues := by
  have hm := candidate_entry_max box
  have ht := candidate_legalTrace box h1 h2 h3
  have hr := candidate_growthRatio box
  have hg : g ∈ Rho5.GrowthModel.GrowthValues :=
    ⟨candidateMatrix x y z g, candidateValues x y z g,
      Rho5.GrowthModel.ne_zero_of_matrixEntryMax_eq_one hm, ht, hr.symm⟩
  have hn : g ∈ Rho5.GrowthModel.NormalizedGrowthValues :=
    ⟨candidateMatrix x y z g, candidateValues x y z g, hm, ht,
      (candidate_tracePeak box).symm⟩
  exact ⟨hm, ht, hr, hg, hn⟩

theorem candidate_mem_GrowthValues
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0) :
    g ∈ Rho5.GrowthModel.GrowthValues :=
  (candidate_attainment box h1 h2 h3).2.2.2.1

/-- G04-compatible wrapper; the Jacobian equation is not needed for attainment. -/
theorem candidate_mem_GrowthValues_of_critical
    (box : Rho5.Algebraic.CandidateBox x y z g)
    (h1 : Rho5.Algebraic.P1 x y z g = 0)
    (h2 : Rho5.Algebraic.P2 x y z g = 0)
    (h3 : Rho5.Algebraic.P3 x y z g = 0)
    (_hJ : Rho5.Algebraic.J x y z g = 0) :
    g ∈ Rho5.GrowthModel.GrowthValues :=
  candidate_mem_GrowthValues box h1 h2 h3

end Rho5.ExternalAttainment
