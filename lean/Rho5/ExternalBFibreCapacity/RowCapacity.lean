import Rho5.ExternalBFibreCapacity.FiniteBounds

/-!
The finite p/e polygon.  A zero-x row is padded by (0,0), never divided by.
The four-by-four storage is fixed-size; noneligible entries are the harmless cap 2.
The head cap is at most 2, so padding does not change the minimum.
-/
namespace Rho5.ExternalBFibreCapacity
noncomputable section

structure RowSystem where
  a : Fin 4 → ℝ
  b : Fin 4 → ℝ
  a_nonneg : ∀ i, 0 ≤ a i
  a_le_one : ∀ i, a i ≤ 1
  b_bound : ∀ i, |b i| ≤ 1
  zero_row : ∀ i, a i = 0 → b i = 0
  head_a : a 0 = 1
  head_positive : 0 < b 0

def RowFeasible (w : RowSystem) (p e : ℝ) : Prop :=
  1 ≤ p ∧ 0 ≤ e ∧ e ≤ 1 ∧ ∀ i, w.a i*p-w.b i*e ≤ 1

def pairDen (w : RowSystem) (i j : Fin 4) : ℝ := w.a j*w.b i-w.a i*w.b j

def unaryCap (w : RowSystem) (i : Fin 4) : ℝ :=
  if 0 < w.a i ∧ 0 ≤ w.b i then (1+w.b i)/w.a i else 2

def pairCap (w : RowSystem) (i j : Fin 4) : ℝ :=
  if 0 < w.b i ∧ w.b j < 0 then (w.b i-w.b j)/pairDen w i j else 2

def rowP (w : RowSystem) : ℝ :=
  min (min4 (unaryCap w)) (min4 fun i => min4 (pairCap w i))

def eLower (w : RowSystem) (i : Fin 4) : ℝ :=
  if 0 < w.b i then (w.a i*rowP w-1)/w.b i else 0

def rowE (w : RowSystem) : ℝ := max 0 (max4 (eLower w))

theorem a_pos_of_b_ne_zero (w : RowSystem) (i : Fin 4) (h : w.b i ≠ 0) :
    0 < w.a i := by
  have ha := w.a_nonneg i
  by_contra hn
  have ha0 : w.a i = 0 := le_antisymm (le_of_not_gt hn) ha
  exact h (w.zero_row i ha0)

theorem pairDen_pos (w : RowSystem) (i j : Fin 4)
    (hi : 0 < w.b i) (hj : w.b j < 0) : 0 < pairDen w i j := by
  have hai := a_pos_of_b_ne_zero w i (ne_of_gt hi)
  have haj := a_pos_of_b_ne_zero w j (ne_of_lt hj)
  have h₁ := mul_pos haj hi
  have h₂ := mul_neg_of_pos_of_neg hai hj
  dsimp [pairDen]
  linarith

theorem rowP_le_unary (w : RowSystem) (i : Fin 4) : rowP w ≤ unaryCap w i :=
  (min_le_left _ _).trans (min4_le _ i)

theorem rowP_le_pair (w : RowSystem) (i j : Fin 4) : rowP w ≤ pairCap w i j :=
  (min_le_right _ _).trans ((min4_le _ i).trans (min4_le _ j))

theorem unary_ge_one (w : RowSystem) (i : Fin 4) : 1 ≤ unaryCap w i := by
  by_cases h : 0 < w.a i ∧ 0 ≤ w.b i
  · simp only [unaryCap, if_pos h]
    apply (le_div_iff₀ h.1).mpr
    have := w.a_le_one i
    nlinarith [h.2]
  · simp [unaryCap, h]

theorem pair_ge_one (w : RowSystem) (i j : Fin 4) : 1 ≤ pairCap w i j := by
  by_cases h : 0 < w.b i ∧ w.b j < 0
  · simp only [pairCap, if_pos h]
    apply (le_div_iff₀ (pairDen_pos w i j h.1 h.2)).mpr
    have h₁ := mul_nonneg (sub_nonneg.mpr (w.a_le_one j)) (le_of_lt h.1)
    have h₂ := mul_nonneg (sub_nonneg.mpr (w.a_le_one i)) (neg_nonneg.mpr (le_of_lt h.2))
    dsimp [pairDen]
    nlinarith
  · simp [pairCap, h]

theorem rowP_bounds (w : RowSystem) : 1 ≤ rowP w ∧ rowP w ≤ 2 := by
  have hlow : 1 ≤ rowP w := by
    apply le_min
    · exact (le_min4_iff _ _).mpr (unary_ge_one w)
    · apply (le_min4_iff _ _).mpr
      intro i
      exact (le_min4_iff _ _).mpr (pair_ge_one w i)
  have hhead : unaryCap w 0 = 1+w.b 0 := by
    simp [unaryCap, w.head_a, le_of_lt w.head_positive]
  have hup := rowP_le_unary w 0
  rw [hhead] at hup
  exact ⟨hlow, by linarith [(abs_le.mp (w.b_bound 0)).2]⟩

theorem feasible_le_two {w : RowSystem} {p e : ℝ} (h : RowFeasible w p e) : p ≤ 2 := by
  have hr := h.2.2.2 0
  rw [w.head_a] at hr
  have hm := mul_le_mul (abs_le.mp (w.b_bound 0)).2 h.2.2.1
    h.2.1 (by norm_num : (0:ℝ) ≤ 1)
  nlinarith

theorem feasible_le_unary {w : RowSystem} {p e : ℝ}
    (h : RowFeasible w p e) (i : Fin 4) : p ≤ unaryCap w i := by
  by_cases hi : 0 < w.a i ∧ 0 ≤ w.b i
  · simp only [unaryCap, if_pos hi]
    apply (le_div_iff₀ hi.1).mpr
    have hm := mul_nonneg hi.2 (sub_nonneg.mpr h.2.2.1)
    nlinarith [h.2.2.2 i]
  · simpa [unaryCap, hi] using feasible_le_two h

theorem feasible_le_pair {w : RowSystem} {p e : ℝ}
    (h : RowFeasible w p e) (i j : Fin 4) : p ≤ pairCap w i j := by
  by_cases hh : 0 < w.b i ∧ w.b j < 0
  · simp only [pairCap, if_pos hh]
    apply (le_div_iff₀ (pairDen_pos w i j hh.1 hh.2)).mpr
    have h₁ := mul_nonneg (neg_nonneg.mpr (le_of_lt hh.2))
      (sub_nonneg.mpr (h.2.2.2 i))
    have h₂ := mul_nonneg (le_of_lt hh.1) (sub_nonneg.mpr (h.2.2.2 j))
    dsimp [pairDen]
    nlinarith
  · simpa [pairCap, hh] using feasible_le_two h

theorem feasible_le_rowP {w : RowSystem} {p e : ℝ}
    (h : RowFeasible w p e) : p ≤ rowP w := by
  apply le_min
  · exact (le_min4_iff _ _).mpr (feasible_le_unary h)
  · apply (le_min4_iff _ _).mpr
    intro i
    exact (le_min4_iff _ _).mpr (feasible_le_pair h i)

theorem eLower_le_one (w : RowSystem) (i : Fin 4) : eLower w i ≤ 1 := by
  by_cases hb : 0 < w.b i
  · have ha := a_pos_of_b_ne_zero w i (ne_of_gt hb)
    have hc := rowP_le_unary w i
    simp only [unaryCap, if_pos (show 0 < w.a i ∧ 0 ≤ w.b i from ⟨ha, le_of_lt hb⟩)] at hc
    have hmul := (le_div_iff₀ ha).mp hc
    simp only [eLower, if_pos hb]
    apply (div_le_iff₀ hb).mpr
    nlinarith
  · simp [eLower, hb]

theorem rowE_bounds (w : RowSystem) : 0 ≤ rowE w ∧ rowE w ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num)
    ((max4_le_iff _ _).mpr (eLower_le_one w))⟩

/-- The head row supplies the otherwise-missing nonnegative upper bound for a
negative-slope row.  The cap formula does not need an extra 1/a_j entry. -/
theorem negative_row_numerator_nonpos (w : RowSystem) (j : Fin 4)
    (hj : w.b j < 0) : w.a j*rowP w-1 ≤ 0 := by
  have haj := a_pos_of_b_ne_zero w j (ne_of_lt hj)
  have hD := pairDen_pos w 0 j w.head_positive hj
  have hc := rowP_le_pair w 0 j
  simp only [pairCap, if_pos (show 0 < w.b 0 ∧ w.b j < 0 from ⟨w.head_positive, hj⟩)] at hc
  have hcap := (le_div_iff₀ hD).mp hc
  have hmul := mul_le_mul_of_nonneg_left hcap (le_of_lt haj)
  have hcomp : w.a j*(w.b 0-w.b j) ≤ pairDen w 0 j := by
    have h := mul_nonneg (sub_nonneg.mpr (w.a_le_one j)) (neg_nonneg.mpr (le_of_lt hj))
    dsimp [pairDen]
    rw [w.head_a]
    nlinarith
  by_contra hbad
  have hp := mul_pos hD (lt_of_not_ge hbad)
  nlinarith

/-- Opposite-row compatibility, proved without requiring a sign for either
numerator. -/
theorem lower_le_upper {ai bi aj bj p : ℝ}
    (hi : 0 < bi) (hj : bj < 0)
    (hc : (aj*bi-ai*bj)*p ≤ bi-bj) :
    (ai*p-1)/bi ≤ (aj*p-1)/bj := by
  have hi0 : bi ≠ 0 := ne_of_gt hi
  have hj0 : bj ≠ 0 := ne_of_lt hj
  have he : ((aj*p-1)/bj-(ai*p-1)/bi)*(bi*(-bj)) =
      bi-bj-(aj*bi-ai*bj)*p := by
    field_simp [hi0, hj0]
    <;> ring
  have hn : 0 ≤ ((aj*p-1)/bj-(ai*p-1)/bi)*(bi*(-bj)) := by
    rw [he]
    linarith
  have hpos : 0 < bi*(-bj) := mul_pos hi (neg_pos.mpr hj)
  by_contra hbad
  have hdiff : (aj*p-1)/bj-(ai*p-1)/bi < 0 := by linarith
  have := mul_neg_of_neg_of_pos hdiff hpos
  linarith

theorem rowE_le_negative_upper (w : RowSystem) (j : Fin 4)
    (hj : w.b j < 0) : rowE w ≤ (w.a j*rowP w-1)/w.b j := by
  have hn := negative_row_numerator_nonpos w j hj
  have hu0 : 0 ≤ (w.a j*rowP w-1)/w.b j := by
    have h1 : (w.a j*rowP w-1)/w.b j = (1 - w.a j*rowP w)/(-w.b j) := by
      field_simp
      ring
    rw [h1]
    exact div_nonneg (by linarith only [hn]) (by linarith only [hj])
  apply max_le hu0
  apply (max4_le_iff _ _).mpr
  intro i
  by_cases hi : 0 < w.b i
  · simp only [eLower, if_pos hi]
    have hc := rowP_le_pair w i j
    simp only [pairCap, if_pos (show 0 < w.b i ∧ w.b j < 0 from ⟨hi, hj⟩)] at hc
    have hh := (le_div_iff₀ (pairDen_pos w i j hi hj)).mp hc
    have hh' : (w.a j*w.b i-w.a i*w.b j)*rowP w ≤ w.b i-w.b j := by
      rw [pairDen] at hh
      nlinarith only [hh]
    exact lower_le_upper hi hj hh'
  · simpa [eLower, hi] using hu0

/-- The common eStar really satisfies *every* row. -/
theorem row_endpoint_feasible (w : RowSystem) : RowFeasible w (rowP w) (rowE w) := by
  refine ⟨(rowP_bounds w).1, (rowE_bounds w).1, (rowE_bounds w).2, ?_⟩
  intro i
  rcases lt_trichotomy (w.b i) 0 with hi | hi | hi
  · have he := rowE_le_negative_upper w i hi
    have hm := mul_le_mul_of_nonpos_right he (le_of_lt hi)
    have hz : (w.a i*rowP w-1)/w.b i*w.b i = w.a i*rowP w-1 :=
      div_mul_cancel₀ _ (ne_of_lt hi)
    nlinarith
  · by_cases ha : 0 < w.a i
    · have hp := rowP_le_unary w i
      simp only [unaryCap, if_pos (show 0 < w.a i ∧ 0 ≤ w.b i from ⟨ha, le_of_eq hi.symm⟩)] at hp
      have hm := (le_div_iff₀ ha).mp hp
      rw [hi] at *
      nlinarith
    · have ha0 : w.a i = 0 := le_antisymm (le_of_not_gt ha) (w.a_nonneg i)
      simp [ha0, hi]
  · have hl : (w.a i*rowP w-1)/w.b i ≤ rowE w := by
      calc
        (w.a i*rowP w-1)/w.b i = eLower w i := by simp [eLower, hi]
        _ ≤ max4 (eLower w) := le_max4 _ i
        _ ≤ rowE w := le_max_right _ _
    have hm := (div_le_iff₀ hi).mp hl
    nlinarith

theorem rowE_le_of_feasible_at_max {w : RowSystem} {e : ℝ}
    (h : RowFeasible w (rowP w) e) : rowE w ≤ e := by
  apply max_le h.2.1
  apply (max4_le_iff _ _).mpr
  intro i
  by_cases hi : 0 < w.b i
  · simp only [eLower, if_pos hi]
    apply (div_le_iff₀ hi).mpr
    nlinarith [h.2.2.2 i]
  · simpa [eLower, hi] using h.2.1

/-- Convexity of the *joint* polygon, not separate completions for different rows. -/
theorem rows_segment {w : RowSystem} {p e P E lam : ℝ}
    (h : RowFeasible w p e) (h' : RowFeasible w P E)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    RowFeasible w (mix p P lam) (mix e E lam) := by
  refine ⟨mix_lower h.1 h'.1 h0 h1,
    mix_lower h.2.1 h'.2.1 h0 h1,
    mix_upper h.2.2.1 h'.2.2.1 h0 h1, ?_⟩
  intro i
  have hline := mix_upper (h.2.2.2 i) (h'.2.2.2 i) h0 h1
  have heq : mix (w.a i*p-w.b i*e) (w.a i*P-w.b i*E) lam =
      w.a i*mix p P lam-w.b i*mix e E lam := by dsimp [mix]; ring
  rwa [heq] at hline

end
end Rho5.ExternalBFibreCapacity
