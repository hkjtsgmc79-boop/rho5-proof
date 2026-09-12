import Rho5.Shared.GlobalAttainedWitness.Range
import Rho5.Shared.GlobalXBMaximizer.Basic

/-! C02: one importable entry for the accepted actual attainment, global bounds and
actual global maximizer. D92 remains the owner of the range API. -/
noncomputable section
namespace Rho5.Integration.StagedAssembly

open Rho5

/-- The actual alpha witness and an actual global maximizer, with the original
matrix, legal paths, growth ratio and supremum semantics. No safety premise. -/
theorem baseline :
    GrowthSupremum.rho5Trace = sSup GrowthModel.GrowthValues ∧
    matrixEntryMax ExternalAttainment.actualAlphaMatrix = 1 ∧
    CompletePivotPath.LegalTrace ExternalAttainment.actualAlphaMatrix
      ExternalAttainment.actualAlphaValues ∧
    GrowthModel.growthRatio ExternalAttainment.actualAlphaMatrix
      ExternalAttainment.actualAlphaValues = Algebraic.AlphaRoot.alpha ∧
    Algebraic.AlphaRoot.alpha ≤ GrowthSupremum.rho5Trace ∧
    GrowthSupremum.rho5Trace ≤ (81 : ℝ) / 16 ∧
    ∃ (P : Matrix5) (values : List ℝ),
      BoundaryMaximizer.SortedBoundaryMaximizerFacts P values ∧
      ExternalTailSaturation.LeadingInput P ∧
      ExternalTailSaturation.height P = GrowthSupremum.rho5Trace ∧
      (4 : ℝ) < ExternalTailSaturation.height P ∧
      matrixEntryMax P = 1 ∧
      CompletePivotPath.LegalTrace P
        [1, Certificate.B24Extraction.p P, Certificate.B24Extraction.k P,
          |Certificate.B24Extraction.r P|, ExternalTailSaturation.height P] ∧
      GrowthModel.growthRatio P values = GrowthSupremum.rho5Trace ∧
      (∀ (M : Matrix5), M ≠ 0 → ∀ ws : List ℝ,
        CompletePivotPath.LegalTrace M ws →
        GrowthModel.growthRatio M ws ≤ GrowthModel.growthRatio P values) := by
  obtain ⟨hm, ht, hg, _, _⟩ := ExternalAttainment.actualAlpha_attainment
  obtain ⟨P, values, hf, hlin, hgt, h4, _, _, _, hem, hleg, hgr, _, hgm⟩ :=
    Shared.GlobalXBMaximizer.exists_global_ts_maximizer
  exact ⟨Shared.GlobalAttainedWitness.rho5Trace_semantics, hm, ht, hg,
    Shared.GlobalAttainedWitness.alpha_le_rho5Trace,
    Shared.GlobalAttainedWitness.rho5Trace_le_eighty_one_sixteenth,
    P, values, hf, hlin, hgt, h4, hem, hleg, hgr, hgm⟩

end Rho5.Integration.StagedAssembly
