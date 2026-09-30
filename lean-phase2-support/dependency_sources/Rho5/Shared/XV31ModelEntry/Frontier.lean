import Rho5.Shared.XV31ModelEntry.Entry
import Rho5.Shared.MainlineTreeCover.V31Batch.FiveTree
import Rho5.Shared.MainlineTreeCover.V31Batch.FiveSource

/-!
# D148 stage C — the actual remaining frontier

Consumes the coordinator-verified M02_G01 five-leaf result (`FiveSource.actual_root_remaining_cover`)
on the **actual** point: the representative `N` of stage B lies in one of the seven genuinely
remaining original frontier boxes `FiveTree.remainingSeven`, and the five paid terminals are
impossible for it (`FiveSource.subtree_impossible`).

Nothing here re-compiles the five terminals, re-runs a checker or asserts leftover-sibling safety:
the seven retained frontiers (including D136's first `C`) stay with their own owners.
-/

noncomputable section
namespace Rho5.Shared.XV31ModelEntry

open Rho5
open Rho5.Shared.XSmallKBranch
open Rho5.Shared.V43MatrixRoundTrip
open Rho5.Shared.MainlineTreeCover
open Rho5.Shared.MainlineTreeCover.V31Batch
open Rho5.Shared.XSmallKSigns
open Rho5.Certificate.B24Extraction (k)

/-- **D148 main theorem (stage C).**  From the three original inputs alone there is a real
same-height representative `N` of `M` whose actual model point

* is a genuine `Model.SameSource` point (D136's 106 rows),
* lies in the **actual** M01 root, and
* lies in one of M02's seven genuinely remaining frontier boxes (the five paid terminals excluded).

The height identity `height M = r - w` is kept on the same point. -/
theorem matrixPoint_remaining_frontier {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ Rho5.ExternalTailSaturation.height M) (hk2 : k M ≤ 2) :
    ∃ (σ₁ σ₂ σ₃ : ℝ) (N : Matrix5) (b : Box 22),
      (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧ (σ₃ = 1 ∨ σ₃ = -1) ∧
        N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M)) ∧
          SatFrame N ∧ Rho5.ExternalTailSaturation.height N = Rho5.ExternalTailSaturation.height M ∧
            k N = k M ∧ b ∈ FiveTree.remainingSeven ∧
              matrixPoint N ∈ Model.source ∩ b.denote ∧
                Rho5.ExternalTailSaturation.height M = matrixPoint N 1 - matrixPoint N 2 := by
  obtain ⟨σ₁, σ₂, σ₃, N, hσ₁, hσ₂, hσ₃, hN, hS, hH, hK, hSame, hRoot, hF⟩ :=
    matrix_has_v31_source_representative h hq hk2
  obtain ⟨b, hb, hxbox⟩ := FiveSource.actual_root_remaining_cover (matrixPoint N) hSame hRoot
  exact ⟨σ₁, σ₂, σ₃, N, b, hσ₁, hσ₂, hσ₃, hN, hS, hH, hK, hb, hxbox, hF⟩

/-- **The five paid terminals are impossible for an actual same-source point** (M02_G01's
`subtree_impossible`, available directly at D148's actual entry). -/
theorem matrixPoint_not_subRoot {N : Matrix5} (hSame : Model.SameSource (matrixPoint N))
    (hsub : matrixPoint N ∈ FiveTree.subRoot.denote) : False :=
  FiveSource.subtree_impossible (matrixPoint N) hSame hsub

/-- The same impossibility on the representative produced by the entry: the actual point of the
high-value small-`k` branch never falls in the already-excluded subtree `0000001`. -/
theorem representative_not_subRoot {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ Rho5.ExternalTailSaturation.height M) (hk2 : k M ≤ 2) :
    ∃ (σ₁ σ₂ σ₃ : ℝ) (N : Matrix5),
      (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧ (σ₃ = 1 ∨ σ₃ = -1) ∧
        N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M)) ∧
          SatFrame N ∧ Rho5.ExternalTailSaturation.height N = Rho5.ExternalTailSaturation.height M ∧
            k N = k M ∧ Model.SameSource (matrixPoint N) ∧
              matrixPoint N ∈ V31Prefix.root.denote ∧
                matrixPoint N ∉ FiveTree.subRoot.denote := by
  obtain ⟨σ₁, σ₂, σ₃, N, hσ₁, hσ₂, hσ₃, hN, hS, hH, hK, hSame, hRoot, _hF⟩ :=
    matrix_has_v31_source_representative h hq hk2
  exact ⟨σ₁, σ₂, σ₃, N, hσ₁, hσ₂, hσ₃, hN, hS, hH, hK, hSame, hRoot,
    fun hsub => matrixPoint_not_subRoot hSame hsub⟩

end Rho5.Shared.XV31ModelEntry
