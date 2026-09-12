import Rho5.ExternalBFibreCapacity.TailIntervals

namespace Rho5.ExternalBFibreCapacity
noncomputable section
open Rho5.Certificate.B16 (Point)

/-- Clearing denominators of the *actual* height; no LP relaxation is involved. -/
theorem height_difference_identity (a b : Tail) (ha : a.r ≠ 0) (hb : b.r ≠ 0) :
    b.r*a.r*(tailHeight b-tailHeight a) =
      (b.r-a.r)*(b.r*a.r-a.s*a.t) + a.r*a.t*(b.s-a.s) +
      a.r*b.s*(b.t-a.t) := by
  dsimp [tailHeight]
  field_simp [ha, hb]
  <;> ring

/-- Coordinatewise tail growth is valid on the positive CP-tail domain.
This lemma is used for arbitrary pairs of points on the third path. -/
theorem tailHeight_mono {a b : Tail}
    (har : 0 < a.r) (hbr : 0 < b.r)
    (has : 0 ≤ a.s) (hat : 0 ≤ a.t)
    (hasr : a.s ≤ a.r) (hatr : a.t ≤ a.r)
    (hr : a.r ≤ b.r) (hs : a.s ≤ b.s) (ht : a.t ≤ b.t) :
    tailHeight a ≤ tailHeight b := by
  have hst : a.s*a.t ≤ a.r*a.r :=
    mul_le_mul hasr hatr hat (le_of_lt har)
  have hrr : a.r*a.r ≤ b.r*a.r := mul_le_mul_of_nonneg_right hr (le_of_lt har)
  have hgap : 0 ≤ b.r*a.r-a.s*a.t := sub_nonneg.mpr (hst.trans hrr)
  have h₁ := mul_nonneg (sub_nonneg.mpr hr) hgap
  have h₂ := mul_nonneg (mul_nonneg (le_of_lt har) hat) (sub_nonneg.mpr hs)
  have h₃ := mul_nonneg (mul_nonneg (le_of_lt har) (has.trans hs)) (sub_nonneg.mpr ht)
  have hprod : 0 ≤ b.r*a.r*(tailHeight b-tailHeight a) := by
    rw [height_difference_identity a b (ne_of_gt har) (ne_of_gt hbr)]
    linarith
  by_contra hbad
  have hn := mul_neg_of_pos_of_neg (mul_pos hbr har) (sub_neg.mpr (lt_of_not_ge hbad))
  linarith

def canonicalTail (f : Frame) : Tail := maxTail (tailLimits f (prefixP f))
def capF (f : Frame) : ℝ := tailHeight (canonicalTail f)
def canonicalPoint (f : Frame) : Point :=
  encode f (betaBar f) (prefixP f) (prefixE f) (canonicalTail f)

/-- No assumed feasibility of the endpoint: it follows from the actual source. -/
theorem tail_endpoint_admissible {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) :
    Admissible f (betaBar f) (prefixP f) (prefixE f) (canonicalTail f) := by
  have hp := (prefix_maximum h).1
  rcases (tailBounds_iff _ _ _).mp hp.2.2 with ⟨hfix, hb⟩
  exact ⟨h.1, hp.2.1, (tailBounds_iff _ _ _).mpr
    ⟨hfix, maxTail_feasible (endpointChecks_of_feasible hb)⟩⟩

/-- The fixed-frame maximum is an attained maximum over the entire normalized
six-variable fibre, not just over the tail of the input source. -/
theorem admissible_height_le_capF {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) : tailHeight t ≤ capF f := by
  have hp := (prefix_maximum h).1
  have hb := ((tailBounds_iff _ _ _).mp hp.2.2).2
  have hd := maxTail_dominates hb
  have hm := tail_endpoint_admissible h
  exact tailHeight_mono h.2.2.r_pos hm.2.2.r_pos h.2.2.s_nonneg h.2.2.t_nonneg
    h.2.2.s_le_r h.2.2.t_le_r hd.1 hd.2.1 hd.2.2

/-- B4: linearly interpolate r,s,t, and let encode recompute F. -/
theorem tail_segment_admissible {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Admissible f (betaBar f) (prefixP f) (prefixE f)
      (tailMix t (canonicalTail f) lam) := by
  have hp := (prefix_maximum h).1
  have hm := tail_endpoint_admissible h
  rcases (tailBounds_iff _ _ _).mp hp.2.2 with ⟨hfix, hb⟩
  have hc := ((tailBounds_iff _ _ _).mp hm.2.2).2
  exact ⟨h.1, hp.2.1, (tailBounds_iff _ _ _).mpr
    ⟨hfix, tailBox_segment hb hc h0 h1⟩⟩

theorem tail_segment_height_mono {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) {lam μ : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hlamμ : lam ≤ μ) :
    tailHeight (tailMix t (canonicalTail f) lam) ≤
      tailHeight (tailMix t (canonicalTail f) μ) := by
  have ha := (tail_segment_admissible h hlam0 hlam1).2.2
  have hb := (tail_segment_admissible h hμ0 hμ1).2.2
  have hp := (prefix_maximum h).1
  have hd := maxTail_dominates (((tailBounds_iff _ _ _).mp hp.2.2).2)
  exact tailHeight_mono ha.r_pos hb.r_pos ha.s_nonneg ha.t_nonneg ha.s_le_r ha.t_le_r
    (mix_mono_parameter hd.1 hlamμ)
    (mix_mono_parameter hd.2.1 hlamμ)
    (mix_mono_parameter hd.2.2 hlamμ)

theorem canonical_normalized (z : Point) (h : NormalizedB z) :
    NormalizedB (canonicalPoint (frameOf z)) := by
  apply (admissible_iff_normalized _ _ _ _ _).mp
  exact tail_endpoint_admissible (admissible_decode z h)

@[simp] theorem canonical_frame (f : Frame) : frameOf (canonicalPoint f) = f :=
  frameOf_encode _ _ _ _ _

@[simp] theorem canonical_height (f : Frame) : canonicalPoint f 23 = capF f := rfl

/-- All six coordinates have the prescribed formulas. R,S,T are not witnesses
selected by an optimizer or by an unproved existence assumption. -/
theorem canonical_coordinates (f : Frame) :
    canonicalPoint f 10 = betaBar f ∧ canonicalPoint f 8 = prefixP f ∧
    canonicalPoint f 9 = prefixE f ∧
    canonicalPoint f 1 = (tailLimits f (prefixP f)).R ∧
    canonicalPoint f 2 = min (tailLimits f (prefixP f)).R (tailLimits f (prefixP f)).sUpper ∧
    canonicalPoint f 3 = min (tailLimits f (prefixP f)).R (tailLimits f (prefixP f)).tUpper ∧
    canonicalPoint f 23 = capF f := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem height_le_capF (z : Point) (h : NormalizedB z) : z 23 ≤ capF (frameOf z) := by
  have hm := admissible_height_le_capF (admissible_decode z h)
  have he : z 23 = tailHeight (tailOf z) := h.1.physical.height
  simpa only [he] using hm

/-- The main task interface. The only input is Qualified plus p>=1,e>=0,beta>=0.
The universal competitor is another complete source with the same actual frame. -/
theorem complete_fibre_argmax (z₀ : Point) (h₀ : NormalizedB z₀) :
    NormalizedB (canonicalPoint (frameOf z₀)) ∧
    frameOf (canonicalPoint (frameOf z₀)) = frameOf z₀ ∧
    canonicalPoint (frameOf z₀) 23 = capF (frameOf z₀) ∧
    (∀ z : Point, NormalizedB z → frameOf z = frameOf z₀ →
      z 23 ≤ canonicalPoint (frameOf z₀) 23) := by
  refine ⟨canonical_normalized z₀ h₀, canonical_frame _, rfl, ?_⟩
  intro z hz hf
  simpa only [canonical_height, hf] using height_le_capF z hz

/-- Existence wording for consumers that do not want to name the explicit map. -/
theorem exists_attained_fibre_maximum (z₀ : Point) (h₀ : NormalizedB z₀) :
    ∃ zStar : Point, NormalizedB zStar ∧ frameOf zStar = frameOf z₀ ∧
      zStar 23 = capF (frameOf z₀) ∧
      ∀ z : Point, NormalizedB z → frameOf z = frameOf z₀ → z 23 ≤ zStar 23 := by
  exact ⟨canonicalPoint (frameOf z₀), complete_fibre_argmax z₀ h₀⟩

/-- The optional 17D transfer, derived *after* the actual attained maximum. -/
theorem transfer_frame_upper_bound (D : Set Frame) (a : ℝ)
    (hcap : ∀ f ∈ D, (∃ z, NormalizedB z ∧ frameOf z = f) → capF f ≤ a) :
    ∀ z : Point, NormalizedB z → frameOf z ∈ D → z 23 ≤ a := by
  intro z hz hD
  exact (height_le_capF z hz).trans (hcap _ hD ⟨z,hz,rfl⟩)

end
end Rho5.ExternalBFibreCapacity
