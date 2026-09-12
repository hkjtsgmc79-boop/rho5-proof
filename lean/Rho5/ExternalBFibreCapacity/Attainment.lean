import Rho5.ExternalBFibreCapacity.Paths

namespace Rho5.ExternalBFibreCapacity
noncomputable section
open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct)

def canonicalPivots (f : Frame) : List ℝ :=
  [1, prefixP f, f.k, (canonicalTail f).r, capF f]

/-- The actual maximum matrix. The last pivot is not presumed to dominate p,k. -/
theorem actual_matrix_attainment (z₀ : Point) (h₀ : NormalizedB z₀) :
    Rho5.matrixEntryMax (reconstruct (canonicalPoint (frameOf z₀))) = 1 ∧
    Rho5.CompletePivotPath.LegalTrace (reconstruct (canonicalPoint (frameOf z₀)))
      (canonicalPivots (frameOf z₀)) ∧
    Rho5.MinorCPDomain.PolyCP (reconstruct (canonicalPoint (frameOf z₀))) ∧
    capF (frameOf z₀) ≤ Rho5.GrowthModel.growthRatio
      (reconstruct (canonicalPoint (frameOf z₀))) (canonicalPivots (frameOf z₀)) := by
  have hq := (canonical_normalized z₀ h₀).1
  exact ⟨Rho5.Certificate.B24Reconstruction.matrixEntryMax_reconstruct _ hq.physical hq.headBand,
    Rho5.Certificate.B24MinorBridge.legalTrace_reconstruct _ hq,
    Rho5.Certificate.B24MinorBridge.polyCP_reconstruct _ hq,
    Rho5.Certificate.B24MinorBridge.le_growthRatio_z23 _ hq⟩

theorem canonical_r_le_height (z₀ : Point) (h₀ : NormalizedB z₀) :
    (canonicalTail (frameOf z₀)).r ≤ capF (frameOf z₀) := by
  have ht := (tail_endpoint_admissible (admissible_decode z₀ h₀)).2.2
  have hn : 0 ≤ (canonicalTail (frameOf z₀)).s*(canonicalTail (frameOf z₀)).t /
      (canonicalTail (frameOf z₀)).r :=
    div_nonneg (mul_nonneg ht.s_nonneg ht.t_nonneg) (le_of_lt ht.r_pos)
  unfold capF tailHeight
  linarith

/-- Exact whole-trace growth only with the required dominance conditions.
Dominance over R is proved, not assumed. -/
theorem actual_growth_eq_capacity (z₀ : Point) (h₀ : NormalizedB z₀)
    (h1 : 1 ≤ capF (frameOf z₀))
    (hp : prefixP (frameOf z₀) ≤ capF (frameOf z₀))
    (hk : (frameOf z₀).k ≤ capF (frameOf z₀)) :
    Rho5.GrowthModel.growthRatio (reconstruct (canonicalPoint (frameOf z₀)))
      (canonicalPivots (frameOf z₀)) = capF (frameOf z₀) := by
  exact Rho5.Certificate.B24MinorBridge.growthRatio_eq_z23 _
    (canonical_normalized z₀ h₀).1 h1 hp hk (canonical_r_le_height z₀ h₀)

/-- The four leading determinant readings are inherited from the real matrix
bridge; no scalar proxy matrix is introduced. -/
theorem actual_minor_readings (z₀ : Point) (h₀ : NormalizedB z₀) :
    let M := reconstruct (canonicalPoint (frameOf z₀))
    Rho5.MinorGrowthThreshold.A M = prefixP (frameOf z₀) ∧
    Rho5.MinorGrowthThreshold.B M = prefixP (frameOf z₀)*(frameOf z₀).k ∧
    Rho5.MinorGrowthThreshold.C M = prefixP (frameOf z₀)*(frameOf z₀).k*
      (canonicalTail (frameOf z₀)).r ∧
    Rho5.MinorGrowthThreshold.D M = -prefixP (frameOf z₀)*(frameOf z₀).k*
      (canonicalTail (frameOf z₀)).r*capF (frameOf z₀) := by
  exact (Rho5.Certificate.B24MinorBridge.witness_bundle _ (canonical_normalized z₀ h₀).1).2.1

end
end Rho5.ExternalBFibreCapacity
