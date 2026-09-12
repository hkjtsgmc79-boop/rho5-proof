import Rho5.ExternalBFibreCapacity.Prefix

namespace Rho5.ExternalBFibreCapacity
noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The actual valid capacity providers.  Padding entries are not counted. -/
def unaryProviders (w : RowSystem) : Finset (Fin 4) :=
  Finset.univ.filter fun i => 0 < w.a i ∧ 0 ≤ w.b i

def pairProviders (w : RowSystem) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun ij => 0 < w.b ij.1 ∧ w.b ij.2 < 0

def signTag (b : ℝ) : Fin 3 := if b < 0 then 2 else if 0 < b then 0 else 1

def signCount (s : Fin 4 → Fin 3) : ℕ :=
  (Finset.univ.filter fun i => s i ≠ 2).card +
  (Finset.univ.filter fun ij : Fin 4 × Fin 4 => s ij.1 = 0 ∧ s ij.2 = 2).card

/-- Only 27 sign assignments occur after the positive head is fixed.  `decide`
builds a kernel term for this finite arithmetic fact; it is not native execution. -/
theorem signCount_three (s₁ s₂ s₃ : Fin 3) :
    signCount ![0,s₁,s₂,s₃] ≤ 6 := by
  revert s₁ s₂ s₃
  decide

theorem signCount_le_six (s : Fin 4 → Fin 3) (h : s 0 = 0) : signCount s ≤ 6 := by
  have he : s = ![0,s 1,s 2,s 3] := by
    funext i
    fin_cases i <;> simp_all
  rw [he]
  exact signCount_three _ _ _

@[simp] theorem signTag_eq_zero (b : ℝ) : signTag b = 0 ↔ 0 < b := by
  by_cases hn : b < 0
  · have hp : ¬0 < b := not_lt.mpr (le_of_lt hn)
    simp [signTag, hn, hp]
  · by_cases hp : 0 < b <;> simp [signTag, hn, hp]

@[simp] theorem signTag_eq_two (b : ℝ) : signTag b = 2 ↔ b < 0 := by
  by_cases hn : b < 0
  · simp [signTag, hn]
  · by_cases hp : 0 < b <;> simp [signTag, hn, hp]

@[simp] theorem signTag_ne_two (b : ℝ) : signTag b ≠ 2 ↔ 0 ≤ b := by
  rw [ne_eq, signTag_eq_two, not_lt]

/-- A2: the finite nonempty family has at most six real capacity entries. -/
theorem capacity_provider_count (w : RowSystem) :
    1 ≤ (unaryProviders w).card ∧
      (unaryProviders w).card+(pairProviders w).card ≤ 6 := by
  have hhead : (0 : Fin 4) ∈ unaryProviders w := by
    simp [unaryProviders, w.head_a, le_of_lt w.head_positive]
  have hsub : unaryProviders w ⊆ Finset.univ.filter (fun i => 0 ≤ w.b i) := by
    intro i hi
    simp only [unaryProviders, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi.2]
  have hcard := Finset.card_le_card hsub
  have hs := signCount_le_six (fun i => signTag (w.b i))
    ((signTag_eq_zero _).mpr w.head_positive)
  have he : signCount (fun i => signTag (w.b i)) =
      (Finset.univ.filter fun i : Fin 4 => 0 ≤ w.b i).card+(pairProviders w).card := by
    simp [signCount, pairProviders]
  rw [he] at hs
  have hpos : 0 < (unaryProviders w).card := Finset.card_pos.mpr ⟨0,hhead⟩
  exact ⟨by omega, by omega⟩

theorem min4_attained (f : Fin 4 → ℝ) : ∃ i, min4 f = f i := by
  by_cases h0 : f 0 ≤ min (f 1) (min (f 2) (f 3))
  · exact ⟨0, min_eq_left h0⟩
  · have h0' : min (f 1) (min (f 2) (f 3)) ≤ f 0 := le_of_not_ge h0
    by_cases h1 : f 1 ≤ min (f 2) (f 3)
    · refine ⟨1, ?_⟩
      unfold min4
      rw [min_eq_right h0', min_eq_left h1]
    · have h1' : min (f 2) (f 3) ≤ f 1 := le_of_not_ge h1
      rcases le_total (f 2) (f 3) with h2 | h2
      · refine ⟨2, ?_⟩
        unfold min4
        rw [min_eq_right h0', min_eq_right h1', min_eq_left h2]
      · refine ⟨3, ?_⟩
        unfold min4
        rw [min_eq_right h0', min_eq_right h1', min_eq_right h2]

/-- The stored padding value 2 can never introduce a spurious smaller capacity:
if the minimum is 2, the head itself is a genuine attaining provider. -/
theorem rowP_has_provider (w : RowSystem) :
    (∃ i ∈ unaryProviders w, rowP w = unaryCap w i) ∨
    (∃ ij ∈ pairProviders w, rowP w = pairCap w ij.1 ij.2) := by
  have head_if_two (hp : rowP w = 2) :
      ∃ i ∈ unaryProviders w, rowP w = unaryCap w i := by
    refine ⟨0, ?_, ?_⟩
    · simp [unaryProviders, w.head_a, le_of_lt w.head_positive]
    · have hl := rowP_le_unary w 0
      have hu : unaryCap w 0 ≤ 2 := by
        have hc : 0 < w.a 0 ∧ 0 ≤ w.b 0 :=
          ⟨by rw [w.head_a]; norm_num, le_of_lt w.head_positive⟩
        unfold unaryCap
        rw [if_pos hc, w.head_a]
        linarith [(abs_le.mp (w.b_bound 0)).2]
      exact le_antisymm hl (by linarith)
  by_cases hm : min4 (unaryCap w) ≤ min4 (fun i => min4 (pairCap w i))
  · obtain ⟨i, hi⟩ := min4_attained (unaryCap w)
    have hp : rowP w = unaryCap w i := by
      unfold rowP
      rw [min_eq_left hm, hi]
    by_cases hv : 0 < w.a i ∧ 0 ≤ w.b i
    · exact Or.inl ⟨i, by simp [unaryProviders, hv], hp⟩
    · exact Or.inl (head_if_two (by simpa [unaryCap, hv] using hp))
  · have hm' : min4 (fun i => min4 (pairCap w i)) ≤ min4 (unaryCap w) := le_of_not_ge hm
    obtain ⟨i, hi⟩ := min4_attained (fun i => min4 (pairCap w i))
    obtain ⟨j, hj⟩ := min4_attained (pairCap w i)
    have hp : rowP w = pairCap w i j := by
      unfold rowP
      rw [min_eq_right hm', hi, hj]
    by_cases hv : 0 < w.b i ∧ w.b j < 0
    · exact Or.inr ⟨(i,j), by simp [pairProviders, hv], hp⟩
    · exact Or.inl (head_if_two (by simpa [pairCap, hv] using hp))

end
end Rho5.ExternalBFibreCapacity
