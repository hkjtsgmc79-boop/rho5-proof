import Rho5.Integration.StagedAssembly.RootReduction
import Rho5.ExternalFourthPivot.FifthReduction
import Rho5.Shared.FinalEndpointAssembly.Endpoints

/-! Conditional final entry. Both global safety obligations are explicit parameters.
This module contains no certificate asserting either safety obligation. -/
noncomputable section
set_option autoImplicit false
namespace Rho5.Integration.StagedAssembly
open Rho5
open Rho5.Algebraic.AlphaRoot (alpha)
open Rho5.GrowthSupremum (rho5Trace)
open Rho5.Shared.BRootCapacityEndpoint (RootEndpointSafety)

/-- Complete real Physical X domain; no cube or finite sample restriction. Unpaid. -/
def XGlobalSafety : Prop :=
  ∀ x : LocalAnalysis.X, LocalAnalysis.V43.Physical x → LocalAnalysis.height x ≤ alpha

/-- Conditional sharp equality from exactly the two remaining safety obligations. -/
theorem rho5Trace_eq_alpha_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety) : rho5Trace = alpha := by
  apply le_antisymm _ ExternalAttainment.actualAlpha_le_rho5Trace
  by_contra hn
  have hα : alpha < rho5Trace := lt_of_not_ge hn
  rcases exists_X_or_root_endpoint hα with hxp | hbp
  · obtain ⟨x, hx, heq⟩ := hxp
    have hh := hX x hx
    rw [heq] at hh
    exact (not_lt_of_ge hh) hα
  · obtain ⟨z, hz, heq⟩ := hbp
    have hh := hB z hz
    rw [heq] at hh
    exact (not_lt_of_ge hh) hα

/-- Original arbitrary nonzero matrix and its original legal path, through the
already-paid supremum bridge. -/
theorem legal_growth_le_alpha_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    GrowthModel.growthRatio A values ≤ alpha := by
  have h := GrowthSupremum.le_rho5Trace
    (GrowthModel.mem_growthValues_iff.mpr ⟨A, values, hne, htrace, rfl⟩)
  rw [rho5Trace_eq_alpha_of_safety hX hB] at h
  exact h

/-- Bound the fifth readout of the very same original path; early stopping uses
the original default-zero readout. -/
theorem fifth_readout_le_alpha_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    values.getD 4 0 ≤ alpha * matrixEntryMax A := by
  have hg := legal_growth_le_alpha_of_safety hX hB A values hne htrace
  rw [GrowthModel.growthRatio_eq] at hg
  have hp := (div_le_iff₀ (MatrixNormalization.matrixEntryMax_pos A hne)).mp hg
  exact (ExternalFourthPivot.getD_le_tracePeak values 4).trans hp

/-- D124's actual fifth-readout assembly, with both global safety assumptions
visible and the fifth-readout bound supplied above. -/
theorem legal_growth_le_alpha_via_fifth_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values) :
    GrowthModel.growthRatio A values ≤ alpha :=
  ExternalFourthPivot.growth_le_of_fifth_readout_le A values hne htrace alpha
    (le_of_lt Algebraic.AlphaRoot.alpha_gt_four)
    (fifth_readout_le_alpha_of_safety hX hB A values hne htrace)

/-- At growth above four, D124 identifies the actual fifth readout; its cap is
conditional on the two safety obligations, with the same matrix and path. -/
theorem high_path_fifth_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety)
    (A : Matrix5) (values : List ℝ) (hne : A ≠ 0)
    (htrace : CompletePivotPath.LegalTrace A values)
    (hhigh : 4 < GrowthModel.growthRatio A values) :
    values.length = 5 ∧ values.getD 4 0 = GrowthModel.tracePeak values ∧
    4 * matrixEntryMax A < values.getD 4 0 ∧
    values.getD 4 0 ≤ alpha * matrixEntryMax A := by
  obtain ⟨hlen, hread, hgt⟩ :=
    ExternalFourthPivot.growth_above_four_is_fifth A values hne htrace hhigh
  exact ⟨hlen, hread, hgt, fifth_readout_le_alpha_of_safety hX hB A values hne htrace⟩

/-- Reuse D96's existing endpoint equivalence; no new determinant route. -/
theorem det_endpoint_of_safety
    (hX : XGlobalSafety) (hB : RootEndpointSafety) :
    ∀ M : Matrix5, M 0 0 = 1 → MinorCPDomain.PolyCP M →
      |M.det| ≤ alpha * MinorGrowthThreshold.C M :=
  Shared.FinalEndpointAssembly.rho5Trace_eq_alpha_iff_det_endpoint.mp
    (rho5Trace_eq_alpha_of_safety hX hB)

end Rho5.Integration.StagedAssembly
