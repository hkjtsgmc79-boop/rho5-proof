import Rho5.Shared.XV31ModelEntry.Rows
import Rho5.Shared.XSmallKSigns.Bridge
import Rho5.Shared.MainlineTreeCover.V31Prefix

/-!
# D148 stage B — the actual V31 root entry, with the sign premises eliminated

The M01 root is written with the common denominator `4800`, D136's root box with reduced rationals;
`root_lo_eq_boxLo` / `root_hi_eq_boxHi` prove the 44 endpoints are the same rationals, so D136's
already-paid `BoxIn` gives membership in **M01's** `V31Prefix.root.denote` for the actual point.

`matrix_has_v31_source_representative` is the card's stable export.  Its only inputs are the three
original ones — `SatFrame M`, `q* ≤ height M`, `k M ≤ 2`.  D143's
`sign_representative_chartState` supplies the real same-height representative `N` together with the
D136 sign/physical/high-value/small-`k`/`u₀` interface, so *no* `SameSource`, sign, root-containment
or leaf-safety premise is assumed here.
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

/-! ## 1. The 44 root endpoints: `4800` normalisation vs D136's reduced rationals -/

theorem root_lo_eq_boxLo (j : Fin 22) : V31Prefix.root.lo j = boxLo j := by
  fin_cases j <;> norm_num [V31Prefix.root, boxLo]

theorem root_hi_eq_boxHi (j : Fin 22) : V31Prefix.root.hi j = boxHi j := by
  fin_cases j <;> norm_num [V31Prefix.root, boxHi]

/-- The two root descriptions are the same box. -/
theorem root_eq_boxLoHi : V31Prefix.root = ⟨boxLo, boxHi⟩ :=
  Box.ext _ _ root_lo_eq_boxLo root_hi_eq_boxHi

/-! ## 2. Actual root containment from D136's paid box -/

/-- D136's paid root box for the actual state is M01's actual V31 root at the actual point. -/
theorem matrixPoint_mem_root_of_boxIn {N : Matrix5} (hbox : BoxIn (chartState N)) :
    matrixPoint N ∈ V31Prefix.root.denote := by
  intro j
  have hb := hbox j
  rw [root_lo_eq_boxLo j, root_hi_eq_boxHi j]
  exact ⟨hb.1, hb.2⟩

/-! ## 3. The stable export: an actual matrix with a real V31 source representative -/

/-- **D148 main theorem (stage B).**  From the three original inputs alone — `SatFrame M`,
`q* ≤ height M`, `k M ≤ 2` — there is a real matrix `N` obtained from `M` by three legitimate
`±1` signed row/column operations, with

* `SatFrame N`, `height N = height M`, `k N = k M` (same real frame class, same height and `k`);
* M02's actual `Model.SameSource (matrixPoint N)` — paid by D136's 106 rows, not assumed;
* `matrixPoint N ∈ V31Prefix.root.denote` — the **actual** M01 root, from D136's paid root box;
* the model's `F` identity `height M = r - w` on the actual point. -/
theorem matrix_has_v31_source_representative {M : Matrix5} (h : SatFrame M)
    (hq : qstar ≤ Rho5.ExternalTailSaturation.height M) (hk2 : k M ≤ 2) :
    ∃ (σ₁ σ₂ σ₃ : ℝ) (N : Matrix5),
      (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧ (σ₃ = 1 ∨ σ₃ = -1) ∧
        N = flipLast3 σ₃ (flipSecond σ₂ (flipMid σ₁ M)) ∧
          SatFrame N ∧ Rho5.ExternalTailSaturation.height N = Rho5.ExternalTailSaturation.height M ∧
            k N = k M ∧ Model.SameSource (matrixPoint N) ∧
              matrixPoint N ∈ V31Prefix.root.denote ∧
                Rho5.ExternalTailSaturation.height M = matrixPoint N 1 - matrixPoint N 2 := by
  obtain ⟨σ₁, σ₂, σ₃, N, hσ₁, hσ₂, hσ₃, hN, hS, _hPhys, hNS, hPS, hHV, hSTP, _hR4, hu0, hH, hK⟩ :=
    Rho5.Shared.XSmallKSigns.sign_representative_chartState h hq hk2
  have hbox : BoxIn (chartState N) :=
    (sourceSystem_of_satFrame N hS hNS hPS hu0 hHV hSTP).boxIn
  refine ⟨σ₁, σ₂, σ₃, N, hσ₁, hσ₂, hσ₃, hN, hS, hH, hK,
    sameSource_of_satFrame N hS hNS hPS hu0 hHV hSTP, ?_, ?_⟩
  · exact matrixPoint_mem_root_of_boxIn hbox
  · rw [← hH, Rho5.Shared.XSmallKSigns.height_eq_rr_sub_ww (M := N) hS]
    simp [matrixPoint, rr, ww]

end Rho5.Shared.XV31ModelEntry
