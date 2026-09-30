import Rho5.Shared.XHighRPhysicalRows.Head

/-!
# D149 — D145's eight `CoreSlacks` from the real core block

D145 left `CoreSlacks M` (`t = r-k ≥ 0`, `c(-B) ≥ t`, `d(-A) ≥ t`, `c(-A) ≥ t`, `c(-A) ≤ J`,
`t ≤ J`, `d(-B) ≥ 0`, `c(-A) ≥ 0`, `J = 21/10`) as a hypothesis.  Every one of the eight is paid
here from the **actual core block** `S3 M`, whose three complete-pivot bounds are exactly the
archived `D`-rows of the real V43 chart (D119 `DX_le_kX` / `neg_kX_le_DX`, themselves instances of
`SatFrame.cp3` at the third pivot):

| slack | real origin |
|---|---|
| `t ≥ 0` | the strict domain `k < r` |
| `c(-B) ≥ t` | `D12+ : r + B c ≤ k` (`DX_le_kX 1 2`) |
| `d(-A) ≥ t` | `D21+ : r + A d ≤ k` (`DX_le_kX 2 1`) |
| `c(-A) ≥ t` | `D11+ : r + A c ≤ k` (`DX_le_kX 1 1`) |
| `c(-A) ≤ J` | `D01- : A ≥ -k`, `D10+ : k c ≤ k`, `k ≤ 21/10` |
| `t ≤ J` | the two previous slacks |
| `d(-B) ≥ 0`, `c(-A) ≥ 0` | the high core signs `B, A ≤ 0 ≤ c, d` |

Nothing here assumes any of the eight; each is traced to its own block bound.
-/

namespace Rho5.Shared.XHighRPhysicalRows

noncomputable section

open Rho5
open Rho5.Shared.V43MatrixRoundTrip
open Rho5.Shared.XHighRSource

/-! ## The real core-block entry readings -/

theorem DX_00 (M : M5) : DX M 0 0 = kX M := by simp [DX]
theorem DX_01 (M : M5) : DX M 0 1 = aX M := by simp [DX]
theorem DX_02 (M : M5) : DX M 0 2 = bX M := by simp [DX]
theorem DX_10 (M : M5) : DX M 1 0 = kX M * cX M := by simp [DX]
theorem DX_11 (M : M5) : DX M 1 1 = rX M + aX M * cX M := by simp [DX]
theorem DX_12 (M : M5) : DX M 1 2 = rX M + bX M * cX M := by simp [DX]
theorem DX_21 (M : M5) : DX M 2 1 = rX M + aX M * dX M := by simp [DX]
theorem DX_22 (M : M5) : DX M 2 2 = wX M + bX M * dX M := by simp [DX]

/-! ## The archived `D`-rows, as bounds at this lane's entry point -/

/-- `D01- : A ≥ -k`. -/
theorem neg_k_le_aX (M : M5) (h : SatFrame M) : -kX M ≤ aX M := by
  have := neg_kX_le_DX M h 0 1
  rwa [DX_01] at this

/-- `D02+ : B ≤ k`. -/
theorem bX_le_kX (M : M5) (h : SatFrame M) : bX M ≤ kX M := by
  have := DX_le_kX M h 0 2
  rwa [DX_02] at this

/-- `D10+ : k c ≤ k`. -/
theorem kX_mul_cX_le_kX (M : M5) (h : SatFrame M) : kX M * cX M ≤ kX M := by
  have := DX_le_kX M h 1 0
  rwa [DX_10] at this

/-- `D11+ : r + A c ≤ k`. -/
theorem r_add_ac_le_k (M : M5) (h : SatFrame M) : rX M + aX M * cX M ≤ kX M := by
  have := DX_le_kX M h 1 1
  rwa [DX_11] at this

/-- `D12+ : r + B c ≤ k`. -/
theorem r_add_bc_le_k (M : M5) (h : SatFrame M) : rX M + bX M * cX M ≤ kX M := by
  have := DX_le_kX M h 1 2
  rwa [DX_12] at this

/-- `D21+ : r + A d ≤ k`. -/
theorem r_add_ad_le_k (M : M5) (h : SatFrame M) : rX M + aX M * dX M ≤ kX M := by
  have := DX_le_kX M h 2 1
  rwa [DX_21] at this

/-- `D22- : k + w + B d ≥ 0`, i.e. `w ≥ -k - B d`. -/
theorem neg_k_sub_bd_le_wX (M : M5) (h : SatFrame M) : -kX M - bX M * dX M ≤ wX M := by
  have := neg_kX_le_DX M h 2 2
  rw [DX_22] at this
  linarith

/-- `D22+ : k - w - B d ≥ 0`, i.e. `w ≤ k - B d`. -/
theorem wX_le_k_sub_bd (M : M5) (h : SatFrame M) : wX M ≤ kX M - bX M * dX M := by
  have := DX_le_kX M h 2 2
  rw [DX_22] at this
  linarith

/-- `c ≤ 1`, from `D10+` and `k > 0`. -/
theorem cX_le_one (M : M5) (h : SatFrame M) : cX M ≤ 1 := by
  have h1 := kX_mul_cX_le_kX M h
  have hk : 0 < kX M := h.hk
  nlinarith

/-- `d ≤ 1`, from `D20+` and `k > 0`. -/
theorem dX_le_one (M : M5) (h : SatFrame M) : dX M ≤ 1 := by
  have h1 : kX M * dX M ≤ kX M := by
    have := DX_le_kX M h 2 0
    simpa [DX] using this
  have hk : 0 < kX M := h.hk
  nlinarith

/-- `a ≤ k`, i.e. the high-branch `-A ≤ k`. -/
theorem neg_aX_le_kX (M : M5) (h : SatFrame M) : -(aX M) ≤ kX M := by
  have h1 := neg_k_le_aX M h
  linarith

/-! ## The eight slacks -/

/-- **D145's `CoreSlacks M`, paid from the real core block, the high core signs and the strict
domain.** -/
theorem coreSlacks_of_source (M : M5) (hs : SourceQual M) : CoreSlacks M := by
  have h := hs.sat
  obtain ⟨hk2, hk21, hkr, _⟩ := SourceQual.domain M hs
  obtain ⟨ha, hb, hc, hd⟩ := SourceQual.signs M hs
  -- the real core-block bounds
  have hD12 : rX M + bX M * cX M ≤ kX M := r_add_bc_le_k M h
  have hD21 : rX M + aX M * dX M ≤ kX M := r_add_ad_le_k M h
  have hD11 : rX M + aX M * cX M ≤ kX M := r_add_ac_le_k M h
  have hDker : -(aX M) ≤ kX M := neg_aX_le_kX M h
  have hc1 : cX M ≤ 1 := cX_le_one M h
  have ha0 : 0 ≤ -(aX M) := by linarith
  have hb0 : 0 ≤ -(bX M) := by linarith
  -- `c(-A) ≥ t`
  have h4 : 0 ≤ cX M * (-(aX M)) - (rX M - kX M) := by nlinarith [hD11]
  -- `c(-A) ≤ k ≤ J`
  have hchi_k : cX M * (-(aX M)) ≤ kX M := by
    have h1 : cX M * (-(aX M)) ≤ 1 * (-(aX M)) := mul_le_mul_of_nonneg_right hc1 ha0
    have h2 : (1 : ℝ) * (-(aX M)) ≤ 1 * kX M := mul_le_mul_of_nonneg_left hDker zero_le_one
    linarith
  have hchi_J : cX M * (-(aX M)) ≤ Jhigh := by
    have hJ : Jhigh = 21 / 10 := rfl
    linarith
  refine ⟨?_, ?_, ?_, h4, ?_, ?_, ?_, ?_⟩
  · linarith
  · nlinarith [hD12]
  · nlinarith [hD21]
  · linarith
  · linarith
  · exact mul_nonneg hd hb0
  · exact mul_nonneg hc ha0

end

end Rho5.Shared.XHighRPhysicalRows
