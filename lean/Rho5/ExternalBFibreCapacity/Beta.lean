import Rho5.ExternalBFibreCapacity.Model

namespace Rho5.ExternalBFibreCapacity
noncomputable section

/-- Constant rows use harmless endpoints 0,1, and a separate zero-row check. -/
def betaLowerRow (v q : ℝ) : ℝ :=
  if 0 < v then (-1-q)/v else if v < 0 then (1-q)/v else 0

def betaUpperRow (v q : ℝ) : ℝ :=
  if 0 < v then (1-q)/v else if v < 0 then (-1-q)/v else 1

def betaLower (f : Frame) : ℝ := max 0 (max3 fun j => betaLowerRow (f.v j) (f.q j))
def betaBar (f : Frame) : ℝ := min 1 (min3 fun j => betaUpperRow (f.v j) (f.q j))
def betaZeroChecks (f : Frame) : Prop := ∀ j, f.v j = 0 → |f.q j| ≤ 1

def BetaFeasible (f : Frame) (b : ℝ) : Prop :=
  0 ≤ b ∧ b ≤ 1 ∧ ∀ j, |b * f.v j + f.q j| ≤ 1

/-- Both signs are treated before division. -/
theorem beta_nonzero_row_iff (v q b : ℝ) (hv : v ≠ 0) :
    |b*v+q| ≤ 1 ↔ betaLowerRow v q ≤ b ∧ b ≤ betaUpperRow v q := by
  rcases lt_or_gt_of_ne hv with hvn | hvp
  · have hnp : ¬0 < v := not_lt.mpr (le_of_lt hvn)
    simp only [betaLowerRow, betaUpperRow, if_neg hnp, if_pos hvn]
    have hL : ((1-q)/v)*v = 1-q := div_mul_cancel₀ _ hv
    have hU : ((-1-q)/v)*v = -1-q := div_mul_cancel₀ _ hv
    constructor
    · intro h
      rcases abs_le.mp h with ⟨hl, hu⟩
      constructor
      · by_contra hx
        have hx' : b < (1-q)/v := lt_of_not_ge hx
        have hp := mul_pos (sub_pos.mpr hx') (neg_pos.mpr hvn)
        nlinarith
      · by_contra hx
        have hx' : (-1-q)/v < b := lt_of_not_ge hx
        have hp := mul_pos (sub_pos.mpr hx') (neg_pos.mpr hvn)
        nlinarith
    · rintro ⟨hl, hu⟩
      have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (le_of_lt hvn)
      have h₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu) (le_of_lt hvn)
      apply abs_le.mpr
      constructor <;> nlinarith
  · simp only [betaLowerRow, betaUpperRow, if_pos hvp]
    rw [div_le_iff₀ hvp, le_div_iff₀ hvp, abs_le]
    constructor
    · rintro ⟨hl, hu⟩
      constructor <;> linarith
    · rintro ⟨hl, hu⟩
      constructor <;> linarith

/-- Exact closed-interval characterization, including incompatible constant rows. -/
theorem beta_feasible_iff (f : Frame) (b : ℝ) :
    BetaFeasible f b ↔ betaZeroChecks f ∧ betaLower f ≤ b ∧ b ≤ betaBar f := by
  constructor
  · rintro ⟨hb0, hb1, hr⟩
    have hlo : ∀ j, betaLowerRow (f.v j) (f.q j) ≤ b := by
      intro j
      by_cases h : f.v j = 0
      · simpa [betaLowerRow, h] using hb0
      · exact ((beta_nonzero_row_iff _ _ _ h).mp (hr j)).1
    have hup : ∀ j, b ≤ betaUpperRow (f.v j) (f.q j) := by
      intro j
      by_cases h : f.v j = 0
      · simpa [betaUpperRow, h] using hb1
      · exact ((beta_nonzero_row_iff _ _ _ h).mp (hr j)).2
    refine ⟨?_, max_le hb0 ((max3_le_iff _ _).mpr hlo),
      le_min hb1 ((le_min3_iff _ _).mpr hup)⟩
    intro j hj
    simpa [hj] using hr j
  · rintro ⟨hz, hl, hu⟩
    have hb0 : 0 ≤ b := (le_max_left _ _).trans hl
    have hb1 : b ≤ 1 := hu.trans (min_le_left _ _)
    refine ⟨hb0, hb1, ?_⟩
    intro j
    by_cases hj : f.v j = 0
    · simpa [hj] using hz j hj
    · apply (beta_nonzero_row_iff _ _ _ hj).mpr
      exact ⟨(le_max3 _ j).trans ((le_max_right _ _).trans hl),
        hu.trans ((min_le_right _ _).trans (min3_le _ j))⟩

theorem beta_interval_nonempty_iff (f : Frame) :
    (∃ b, BetaFeasible f b) ↔ betaZeroChecks f ∧ betaLower f ≤ betaBar f := by
  constructor
  · rintro ⟨b, hb⟩
    rcases (beta_feasible_iff f b).mp hb with ⟨hz, hl, hu⟩
    exact ⟨hz, hl.trans hu⟩
  · rintro ⟨hz, h⟩
    exact ⟨betaBar f, (beta_feasible_iff _ _).mpr ⟨hz, h, le_rfl⟩⟩

theorem betaBar_spec {f : Frame} {b : ℝ} (h : BetaFeasible f b) :
    BetaFeasible f (betaBar f) ∧ b ≤ betaBar f := by
  rcases (beta_feasible_iff f b).mp h with ⟨hz, hl, hu⟩
  exact ⟨(beta_feasible_iff _ _).mpr ⟨hz, hl.trans hu, le_rfl⟩, hu⟩

theorem betaBar_greatest {f : Frame} {b : ℝ} (h : BetaFeasible f b) :
    b ≤ betaBar f := (betaBar_spec h).2

/-- Monotone replacement by *any* feasible larger right-prefix value. -/
theorem prefix_raise_beta {f : Frame} {b b' p e : ℝ}
    (h : PrefixBounds f b p e) (hb : BetaFeasible f b') (hle : b ≤ b') :
    PrefixBounds f b' p e := by
  refine { h with
    beta_nonneg := hb.1, beta_le_one := hb.2.1, right := hb.2.2,
    head := ?_ }
  have heb := mul_mem_unit h.e_nonneg h.e_le_one hb.1 hb.2.1
  have hmono := mul_le_mul_of_nonneg_left hle h.e_nonneg
  have hh := (abs_le.mp h.head).2
  apply abs_le.mpr
  constructor <;> linarith [h.one_le_p]

/-- The whole beta segment is a feasible interval, not a point check. -/
theorem beta_segment_feasible {f : Frame} {b : ℝ} (h : BetaFeasible f b)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    BetaFeasible f (mix b (betaBar f) lam) := by
  have hs := betaBar_spec h
  refine ⟨mix_lower h.1 hs.1.1 h0 h1,
    mix_upper h.2.1 hs.1.2.1 h0 h1, ?_⟩
  intro j
  have hm := abs_mix_le (h.2.2 j) (hs.1.2.2 j) h0 h1
  have he : mix (b*f.v j+f.q j) (betaBar f*f.v j+f.q j) lam =
      mix b (betaBar f) lam*f.v j+f.q j := by dsimp [mix]; ring
  rwa [he] at hm

theorem beta_segment_admissible {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Admissible f (mix b (betaBar f) lam) p e t := by
  have hb : BetaFeasible f b := ⟨h.2.1.beta_nonneg, h.2.1.beta_le_one, h.2.1.right⟩
  exact ⟨h.1, prefix_raise_beta h.2.1 (beta_segment_feasible hb h0 h1)
    ((mix_between (betaBar_greatest hb) h0 h1).1), h.2.2⟩

theorem beta_endpoint_admissible {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) : Admissible f (betaBar f) p e t := by
  simpa using beta_segment_admissible h (lam := 1) (by norm_num) (by norm_num)

end
end Rho5.ExternalBFibreCapacity
