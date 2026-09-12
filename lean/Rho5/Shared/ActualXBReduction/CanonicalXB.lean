/-
D126 — the TS-facing assembly: actual high-value X/B classification into the X22 `Physical` domain
=================================================================================================

**Status: PREPARED, not yet compiled.**  This module consumes the frozen external TS structures
(`Rho5.ExternalTailSaturation.{LeadingInput, CanonicalX, ProperB, TailReduction,
high_value_X_or_properB}`) and D125's `Rho5.Shared.TailSaturationBounds.input_early_bounds`.  Both
are gate-blocked in this lane (D123 `TAIL_CLASSIFICATION_READY` and D125 `TAIL_INPUT_BOUNDS_READY`
were not published when this file was written), so it is delivered as prepared source and is not
claimed as compiled evidence.  See `WAITING_DEPENDENCY.json`.

What it does, once the gates open:

* `delta_bridge` / `height_bridge` — the frozen `CanonicalTail.delta` and the TS `delta`/`height`
  are the same expressions (`T2 1 1 - t * s / r`), so the δ notation of the two chains is connected
  definitionally rather than by a new assumption;
* `satFrame_of_canonicalX` — a TS `CanonicalX` matrix that also satisfies `LeadingInput` **is** a
  D119 `SatFrame`: `head`/normalization, the four leading complete pivots, `p`/`k` positivity,
  `r` positivity and the saturated tail `s = t = r` all come from the existing TS fields; nothing
  is added;
* `x_branch` — the X-side conclusion: the *same* actual matrix `N` is realized by a genuine
  `V43.Physical` X22 point whose reconstruction is `N` and whose height is the TS height of the
  input matrix;
* `high_input_physical_X_or_properB` — the card's headline: from `LeadingInput M` and
  `4 < height M` alone, using `|r M| ≤ 4` paid internally by D125's `input_early_bounds`, produce an
  actual `N` with `TailReduction M N`, the card's readings (`p N = p M`, `k N = k M`, `0 < r N`,
  `r N ≤ |r M|`, the real `LegalTrace N [1, p M, k M, r N, height M]`, `matrixEntryMax N = 1`, and
  D125's growth reading `growthRatio M [1, p M, k M, |r M|, height M] = height M`), and the exit

  `(∃ x, V43.Physical x ∧ M x = N ∧ height x = height M) ∨ ProperB N`.

Scope: the X exit is the **whole physical domain** (any `V43.Physical` point), not a small cube, and
no claim is made that global maximizers lie in the class or that `ProperB` carries the B package's
`NormalizedB` readings (`p ≥ 1/e`, `β ≥ 0`) — those are deliberately absent here.
-/
import Rho5.Shared.ActualXBReduction.Basic
import Rho5.ExternalTailSaturation.Classification
import Rho5.Shared.TailSaturationBounds.HighGrowth

namespace Rho5.Shared.ActualXBReduction

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The δ / height bridge between the frozen notations -/

/-- The TS `delta` is the frozen `CanonicalTail.delta`: both are `T2 1 1 - t * s / r`. -/
theorem delta_bridge (N : Rho5.Matrix5) :
    Rho5.ExternalTailSaturation.delta N = Rho5.CanonicalTail.delta N := by
  simp only [Rho5.ExternalTailSaturation.delta, Rho5.ExternalTailSaturation.w,
    Rho5.CanonicalTail.delta]

/-- The TS `height` is the absolute value of the frozen δ. -/
theorem height_bridge (N : Rho5.Matrix5) :
    Rho5.ExternalTailSaturation.height N = |Rho5.CanonicalTail.delta N| := by
  rw [Rho5.ExternalTailSaturation.height, delta_bridge]

/-! ## 2. `CanonicalX` + `LeadingInput` is a D119 `SatFrame` -/

/-- **The boundary connection.**  The TS fields already supply every field of D119's `SatFrame`:
`head` gives `N 0 0 = 1`, `entryMax_eq_one` gives the unit entry maximum from `head` and `cp0`, the
four pivots are `cp0..cp3`, `p`/`k` positivity is `p_pos`/`k_pos`, `r` positivity is `CanonicalX.r_pos`
and the saturated tail is `CanonicalX.s_eq`/`t_eq`.  The general `w` is untouched. -/
theorem satFrame_of_canonicalX (N : Rho5.Matrix5)
    (h : Rho5.ExternalTailSaturation.LeadingInput N)
    (hx : Rho5.ExternalTailSaturation.CanonicalX N) :
    Rho5.Shared.V43MatrixRoundTrip.SatFrame N where
  h00 := h.head
  hmax := Rho5.ExternalTailSaturation.entryMax_eq_one N h.head h.cp0
  cp1 := h.cp0
  cp2 := h.cp1
  cp3 := h.cp2
  cp4 := h.cp3
  hp := h.p_pos
  hk := h.k_pos
  hr := hx.r_pos
  hs := hx.s_eq
  ht := hx.t_eq

/-! ## 3. The X exit -/

/-- **The X branch in matrix terms.**  The same actual matrix `N` is realized by a genuine
`V43.Physical` point (D119's reverse point), its reconstruction is `N`, and its height is the TS
height of the input matrix. -/
theorem x_branch (N : Rho5.Matrix5) (h : Rho5.ExternalTailSaturation.LeadingInput N)
    (hx : Rho5.ExternalTailSaturation.CanonicalX N) (H : ℝ)
    (hH : H = Rho5.ExternalTailSaturation.height N) :
    ∃ x : Rho5.LocalAnalysis.X, Rho5.LocalAnalysis.V43.Physical x ∧
      reconstruct x = N ∧ Rho5.LocalAnalysis.height x = H := by
  obtain ⟨x, hpx, hrx, hhx⟩ :=
    exists_physical_of_satFrame N (satFrame_of_canonicalX N h hx)
  refine ⟨x, hpx, hrx, ?_⟩
  rw [hhx, ← height_bridge]
  exact hH.symm

/-! ## 4. The headline assembly -/

/-- **`high_input_physical_X_or_properB`.**  From the TS input `LeadingInput M` and
`4 < height M` alone: the accepted D123 classification `high_value_X_or_properB` (with the extra
`|r M| ≤ 4` paid internally by D125's `input_early_bounds`) yields an actual `N` with
`TailReduction M N`; the X exit realizes `N` by a genuine `V43.Physical` point of the same height,
the B exit keeps the original `ProperB N` predicate unchanged.

The returned readings are the ones the card lists: `p N = p M`, `k N = k M` (from `TailReduction`),
`0 < r N` and `r N ≤ |r M|`, the real `LegalTrace N [1, p M, k M, r N, height M]`, the initial
normalization `matrixEntryMax N = 1`, and D125's high-value growth reading
`growthRatio M [1, p M, k M, |r M|, height M] = height M`. -/
theorem high_input_physical_X_or_properB (M : Rho5.Matrix5)
    (h : Rho5.ExternalTailSaturation.LeadingInput M)
    (hhigh : 4 < Rho5.ExternalTailSaturation.height M) :
    ∃ N : Rho5.Matrix5, Rho5.ExternalTailSaturation.TailReduction M N ∧
      p N = p M ∧ k N = k M ∧ 0 < r N ∧ r N ≤ |r M| ∧
      Rho5.CompletePivotPath.LegalTrace N [1, p M, k M, r N, Rho5.ExternalTailSaturation.height M] ∧
      Rho5.matrixEntryMax N = 1 ∧
      Rho5.GrowthModel.growthRatio M [1, p M, k M, |r M|, Rho5.ExternalTailSaturation.height M]
        = Rho5.ExternalTailSaturation.height M ∧
      ((∃ x : Rho5.LocalAnalysis.X, Rho5.LocalAnalysis.V43.Physical x ∧ reconstruct x = N ∧
          Rho5.LocalAnalysis.height x = Rho5.ExternalTailSaturation.height M) ∨
        Rho5.ExternalTailSaturation.ProperB N) := by
  obtain ⟨-, -, hr4⟩ := Rho5.Shared.TailSaturationBounds.input_early_bounds h
  obtain ⟨h1, h2, h3, h4, hgrowth, -, -, -, -, -, -, -, -⟩ :=
    Rho5.Shared.TailSaturationBounds.input_growth_eq_height_of_high h hhigh
  obtain ⟨N, hred, hx | hb⟩ :=
    Rho5.ExternalTailSaturation.high_value_X_or_properB h hr4 hhigh
  · refine ⟨N, hred, hred.p_eq, hred.k_eq, hred.r_pos, hred.r_le, hred.legalTrace, hred.entryMax,
      hgrowth, Or.inl ?_⟩
    obtain ⟨x, hpx, hrx, hhx⟩ :=
      x_branch N hred.input hx (Rho5.ExternalTailSaturation.height N) rfl
    exact ⟨x, hpx, hrx, by rw [hhx, hred.height_eq]⟩
  · exact ⟨N, hred, hred.p_eq, hred.k_eq, hred.r_pos, hred.r_le, hred.legalTrace, hred.entryMax,
      hgrowth, Or.inr hb⟩

end

end Rho5.Shared.ActualXBReduction
