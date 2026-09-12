import Rho5.Integration.StagedAssembly.Baseline
import Rho5.Shared.GlobalXBMaximizer.StageB
import Rho5.Shared.ActualBRootEntry.Assembly
import Rho5.Shared.BRootCapacityEndpoint.Refutation

/-!
# Actual global maximizer to X or a B17 root capacity endpoint

This module only assembles accepted interfaces. The original sorted global maximizer `P`
and its actual tail representative `N` remain in the result. On the B branch, D141 supplies
a genuine sign representative `z` of `N`; D142 supplies a further sign representative `y`
and the canonical capacity endpoint of `y`'s frame. The capacity endpoint need not be a
sign transform of the original matrix.

The strict premise `alpha < rho5Trace` is explicit. No whole-X or whole-B safety is asserted.
-/

noncomputable section

namespace Rho5.Integration.StagedAssembly

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Extraction (p k r s t)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.ExternalTailSaturation (LeadingInput TailReduction height)
open Rho5.ExternalBFibreCapacity
  (NormalizedB frameOf canonicalPoint canonicalPivots capF)
open Rho5.Shared.PaperB17RootEntry (B17Root)
open Rho5.Shared.BRootCapacityEndpoint (IsRootCapacityEndpoint)
open Rho5.Algebraic.AlphaRoot (alpha)
open Rho5.GrowthSupremum (rho5Trace)

/-- The original D131 facts, with the same `P`, pivot values and actual representative `N`. -/
structure GlobalMaximizerReductionFacts (P : Matrix5) (values : List ℝ) (N : Matrix5) : Prop where
  sorted : Rho5.BoundaryMaximizer.SortedBoundaryMaximizerFacts P values
  input : LeadingInput P
  height_eq_rho : height P = rho5Trace
  four_lt_height : (4 : ℝ) < height P
  reduction : TailReduction P N
  p_eq : p N = p P
  k_eq : k N = k P
  r_pos : 0 < r N
  r_le : r N ≤ |r P|
  legal : Rho5.CompletePivotPath.LegalTrace N [1, p P, k P, r N, height P]
  entry_max : matrixEntryMax N = 1
  original_growth :
    Rho5.GrowthModel.growthRatio P [1, p P, k P, |r P|, height P] = height P

/-- The X branch is reconstructed to the actual tail representative, at the original height. -/
def ActualXBranch (P N : Matrix5) : Prop :=
  ∃ x : Rho5.LocalAnalysis.X,
    Rho5.LocalAnalysis.V43.Physical x ∧
    Rho5.Shared.ActualXBReduction.reconstruct x = N ∧
    Rho5.LocalAnalysis.height x = height P

/-- D141's rooted representative, retaining its actual sign relation to `N`. -/
structure ActualRootRepresentative (N : Matrix5) (z : Point) (sg : Fin 5 → ℝ) : Prop where
  signs : ∀ i : Fin 5, sg i = 1 ∨ sg i = -1
  matrix_eq : ∀ i j : Fin 5, reconstruct z i j = sg i * N i j * sg j
  normalized : NormalizedB z
  root : B17Root (frameOf z)
  height_eq : z 23 = height N
  p_eq : z 8 = p N
  k_eq : z 0 = k N
  r_eq : z 1 = r N
  s_eq : z 2 = s N
  t_eq : z 3 = t N
  e_pos : 0 < z 9
  beta_pos : 0 < z 10
  high : alpha < z 23

/-- D142's complete endpoint payload. Only `z → y` is a sign relation; `y → zStar`
is the canonical capacity construction at the same frame. -/
structure RootCapacityWitness (z y zStar : Point) (sg : Fin 5 → ℝ) : Prop where
  signs : ∀ i : Fin 5, sg i = 1 ∨ sg i = -1
  matrix_eq : ∀ i j : Fin 5,
    reconstruct y i j = sg i * reconstruct z i j * sg j
  representative_normalized : NormalizedB y
  representative_root : B17Root (frameOf y)
  height_preserved : y 23 = z 23
  p_preserved : y 8 = z 8
  k_preserved : y 0 = z 0
  r_preserved : y 1 = z 1
  s_preserved : y 2 = z 2
  t_preserved : y 3 = z 3
  e_preserved : y 9 = z 9
  beta_preserved : y 10 = z 10
  canonical : zStar = canonicalPoint (frameOf y)
  frame_eq : frameOf zStar = frameOf y
  root : B17Root (frameOf zStar)
  normalized : NormalizedB zStar
  capacity_eq_rho : capF (frameOf y) = rho5Trace
  height_eq_rho : zStar 23 = rho5Trace
  entry_max : matrixEntryMax (reconstruct zStar) = 1
  legal : Rho5.CompletePivotPath.LegalTrace
    (reconstruct zStar) (canonicalPivots (frameOf y))
  poly : Rho5.MinorCPDomain.PolyCP (reconstruct zStar)
  growth_eq_rho : Rho5.GrowthModel.growthRatio
    (reconstruct zStar) (canonicalPivots (frameOf y)) = rho5Trace
  dominates : ∀ w : Point, NormalizedB w → frameOf w = frameOf y → w 23 ≤ zStar 23
  endpoint : IsRootCapacityEndpoint zStar

/-- The B branch keeps both actual sign operations and the final same-frame capacity step. -/
def ActualBRootEndpointBranch (N : Matrix5) : Prop :=
  ∃ (z : Point) (sg : Fin 5 → ℝ), ActualRootRepresentative N z sg ∧
    ∃ (y zStar : Point) (sg₂ : Fin 5 → ℝ), RootCapacityWitness z y zStar sg₂

/-- At a putative global value above alpha, the original D131 maximizer has either its
actual X representative or a same-height canonical capacity endpoint in the complete B17 root.
`LeadingInput N` and the height transport are paid by the returned `TailReduction`. -/
theorem exists_global_max_X_or_root_endpoint (hα : alpha < rho5Trace) :
    ∃ (P : Matrix5) (values : List ℝ) (N : Matrix5),
      GlobalMaximizerReductionFacts P values N ∧
        (ActualXBranch P N ∨ ActualBRootEndpointBranch N) := by
  obtain ⟨P, values, N, hf, hlin, hgt, h4, hred,
      hp, hk, hrpos, hrle, hleg, hen, hgro, hbr⟩ :=
    Rho5.Shared.GlobalXBMaximizer.exists_global_max_X_or_properB
  refine ⟨P, values, N, ⟨hf, hlin, hgt, h4, hred, hp, hk, hrpos, hrle,
    hleg, hen, hgro⟩, ?_⟩
  rcases hbr with hX | hb
  · exact Or.inl hX
  · have hNρ : height N = rho5Trace := hred.height_eq.trans hgt
    have hNhigh : alpha < height N := by
      rw [hNρ]
      exact hα
    obtain ⟨z, sg, hsg, hmat, hnorm, hroot, h23,
        h8, h0, h1, h2, h3, he, hbpos, hhighz⟩ :=
      Rho5.Shared.ActualBRootEntry.actual_properB_high_has_root_representative
        N hred.input hb hNhigh
    have hzρ : z 23 = rho5Trace := h23.trans hNρ
    obtain ⟨y, zStar, sg₂, hsg₂, hmat₂, hy, hyroot,
        hy23, hy8, hy0, hy1, hy2, hy3, hy9, hy10,
        hstar, hframe, hrootStar, hnormStar, hcap,
        hheight, hentry, hlegal, hpoly, hgrowth, hdom⟩ :=
      Rho5.Shared.BRootCapacityEndpoint.root_capacity_endpoint z hnorm hzρ hα
    exact Or.inr ⟨z, sg,
      ⟨hsg, hmat, hnorm, hroot, h23, h8, h0, h1, h2, h3, he, hbpos, hhighz⟩,
      y, zStar, sg₂,
      ⟨hsg₂, hmat₂, hy, hyroot, hy23, hy8, hy0, hy1, hy2, hy3, hy9, hy10,
        hstar, hframe, hrootStar, hnormStar, hcap, hheight, hentry, hlegal, hpoly,
        hgrowth, hdom, ⟨y, hy, hyroot, hstar⟩⟩⟩

/-- The projection needed by the explicit whole-X and root-endpoint safety interfaces. -/
theorem exists_X_or_root_endpoint (hα : alpha < rho5Trace) :
    (∃ x : Rho5.LocalAnalysis.X,
      Rho5.LocalAnalysis.V43.Physical x ∧ Rho5.LocalAnalysis.height x = rho5Trace) ∨
    (∃ zStar : Point, IsRootCapacityEndpoint zStar ∧ zStar 23 = rho5Trace) := by
  obtain ⟨P, values, N, hf, hbr⟩ := exists_global_max_X_or_root_endpoint hα
  rcases hbr with hX | hB
  · obtain ⟨x, hx, _hxN, hxheight⟩ := hX
    exact Or.inl ⟨x, hx, hxheight.trans hf.height_eq_rho⟩
  · obtain ⟨z, sg, _hz, y, zStar, sg₂, hw⟩ := hB
    exact Or.inr ⟨zStar, hw.endpoint, hw.height_eq_rho⟩

end Rho5.Integration.StagedAssembly

end
