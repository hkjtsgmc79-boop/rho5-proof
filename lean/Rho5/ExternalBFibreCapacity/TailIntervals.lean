import Rho5.ExternalBFibreCapacity.Prefix

namespace Rho5.ExternalBFibreCapacity
noncomputable section

/-- Intersection of the three bands for *one and the same* core entry. -/
def entryLower (f : Frame) (p : ℝ) (i j : Fin 3) : ℝ :=
  max (-f.k) (max (-p-f.x i*f.q j) (-1-f.x i*f.q j-f.u i*f.v j))

def entryUpper (f : Frame) (p : ℝ) (i j : Fin 3) : ℝ :=
  min f.k (min (p-f.x i*f.q j) (1-f.x i*f.q j-f.u i*f.v j))

theorem joint_band_iff (k p xq uv a : ℝ) :
    (|a| ≤ k ∧ |a+xq| ≤ p ∧ |a+uv+xq| ≤ 1) ↔
      max (-k) (max (-p-xq) (-1-xq-uv)) ≤ a ∧
      a ≤ min k (min (p-xq) (1-xq-uv)) := by
  constructor
  · rintro ⟨hd, hs, ho⟩
    rcases abs_le.mp hd with ⟨hd0, hd1⟩
    rcases abs_le.mp hs with ⟨hs0, hs1⟩
    rcases abs_le.mp ho with ⟨ho0, ho1⟩
    exact ⟨max_le hd0 (max_le (by linarith) (by linarith)),
      le_min hd1 (le_min (by linarith) (by linarith))⟩
  · rintro ⟨hl, hu⟩
    have hd0 := (le_max_left _ _).trans hl
    have hs0 := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
    have ho0 := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
    have hd1 := hu.trans (min_le_left _ _)
    have hs1 := hu.trans ((min_le_right _ _).trans (min_le_left _ _))
    have ho1 := hu.trans ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨abs_le.mpr ⟨hd0, hd1⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

theorem entry_bands_iff (f : Frame) (p : ℝ) (t : Tail) (i j : Fin 3) :
    (|core f t i j| ≤ f.k ∧ |stage f t i j| ≤ p ∧ |original f t i j| ≤ 1) ↔
    entryLower f p i j ≤ core f t i j ∧ core f t i j ≤ entryUpper f p i j :=
  joint_band_iff _ _ _ _ _

def FixedChecks (f : Frame) (p : ℝ) : Prop :=
  ∀ i j : Fin 3, i = 0 ∨ j = 0 →
    entryLower f p i j ≤ core f ⟨0,0,0⟩ i j ∧
    core f ⟨0,0,0⟩ i j ≤ entryUpper f p i j

structure TailLimits where
  rLower : ℝ
  R : ℝ
  sLower : ℝ
  sUpper : ℝ
  tLower : ℝ
  tUpper : ℝ

def tailLimits (f : Frame) (p : ℝ) : TailLimits where
  rLower := max 0 (max (entryLower f p 1 1-f.A*f.c)
    (f.B*f.d-entryUpper f p 2 2))
  R := min (entryUpper f p 1 1-f.A*f.c) (f.B*f.d-entryLower f p 2 2)
  sLower := max 0 (entryLower f p 1 2-f.B*f.c)
  sUpper := entryUpper f p 1 2-f.B*f.c
  tLower := max 0 (entryLower f p 2 1-f.A*f.d)
  tUpper := entryUpper f p 2 1-f.A*f.d

structure InTailBox (l : TailLimits) (t : Tail) : Prop where
  r_pos : 0 < t.r
  r_lower : l.rLower ≤ t.r
  r_upper : t.r ≤ l.R
  s_lower : l.sLower ≤ t.s
  s_upper : t.s ≤ l.sUpper
  t_lower : l.tLower ≤ t.t
  t_upper : t.t ≤ l.tUpper
  s_le_r : t.s ≤ t.r
  t_le_r : t.t ≤ t.r

def maxTail (l : TailLimits) : Tail := ⟨l.R, min l.R l.sUpper, min l.R l.tUpper⟩

def EndpointChecks (l : TailLimits) : Prop :=
  0 < l.R ∧ l.rLower ≤ l.R ∧
    l.sLower ≤ min l.R l.sUpper ∧ l.tLower ≤ min l.R l.tUpper

/-- Each fixed head cell is invariant under the tail replacements. -/
theorem core_fixed (f : Frame) (a b : Tail) (i j : Fin 3)
    (h : i = 0 ∨ j = 0) : core f a i j = core f b i j := by
  rcases h with h | h
  · subst i; fin_cases j <;> rfl
  · subst j; fin_cases i <;> rfl

/-- B1: a complete nine-cell interval equivalence.  None of the five fixed
cells is dropped.  q-stage bounds stay in `PrefixBounds`. -/
theorem tailBounds_iff (f : Frame) (p : ℝ) (t : Tail) :
    TailBounds f p t ↔ FixedChecks f p ∧ InTailBox (tailLimits f p) t := by
  constructor
  · intro h
    have hi : ∀ i j, entryLower f p i j ≤ core f t i j ∧
        core f t i j ≤ entryUpper f p i j :=
      fun i j => (entry_bands_iff _ _ _ _ _).mp ⟨h.core i j, h.stage i j, h.original i j⟩
    have h11 := hi 1 1
    have h12 := hi 1 2
    have h21 := hi 2 1
    have h22 := hi 2 2
    change entryLower f p 1 1 ≤ t.r+f.A*f.c ∧ t.r+f.A*f.c ≤ entryUpper f p 1 1 at h11
    change entryLower f p 1 2 ≤ t.s+f.B*f.c ∧ t.s+f.B*f.c ≤ entryUpper f p 1 2 at h12
    change entryLower f p 2 1 ≤ t.t+f.A*f.d ∧ t.t+f.A*f.d ≤ entryUpper f p 2 1 at h21
    change entryLower f p 2 2 ≤ -t.r+f.B*f.d ∧ -t.r+f.B*f.d ≤ entryUpper f p 2 2 at h22
    refine ⟨?_, ⟨h.r_pos, ?_, ?_, ?_, ?_, ?_, ?_, h.s_le_r, h.t_le_r⟩⟩
    · intro i j hj
      simpa only [core_fixed f t ⟨0,0,0⟩ i j hj] using hi i j
    · exact max_le (le_of_lt h.r_pos) (max_le (by linarith [h11.1]) (by linarith [h22.2]))
    · exact le_min (by linarith [h11.2]) (by linarith [h22.1])
    · exact max_le h.s_nonneg (by linarith [h12.1])
    · change t.s ≤ entryUpper f p 1 2-f.B*f.c
      linarith [h12.2]
    · exact max_le h.t_nonneg (by linarith [h21.1])
    · change t.t ≤ entryUpper f p 2 1-f.A*f.d
      linarith [h21.2]
  · rintro ⟨hf, h⟩
    have hr11 : entryLower f p 1 1-f.A*f.c ≤ t.r :=
      (le_max_left _ _).trans ((le_max_right _ _).trans h.r_lower)
    have hr22 : f.B*f.d-entryUpper f p 2 2 ≤ t.r :=
      (le_max_right _ _).trans ((le_max_right _ _).trans h.r_lower)
    have hr11u : t.r ≤ entryUpper f p 1 1-f.A*f.c := h.r_upper.trans (min_le_left _ _)
    have hr22u : t.r ≤ f.B*f.d-entryLower f p 2 2 := h.r_upper.trans (min_le_right _ _)
    have hs12 : entryLower f p 1 2-f.B*f.c ≤ t.s := (le_max_right _ _).trans h.s_lower
    have ht21 : entryLower f p 2 1-f.A*f.d ≤ t.t := (le_max_right _ _).trans h.t_lower
    have hs12u : t.s ≤ entryUpper f p 1 2-f.B*f.c := h.s_upper
    have ht21u : t.t ≤ entryUpper f p 2 1-f.A*f.d := h.t_upper
    have hi : ∀ i j, entryLower f p i j ≤ core f t i j ∧
        core f t i j ≤ entryUpper f p i j := by
      intro i j
      by_cases hh : i = 0 ∨ j = 0
      · simpa only [core_fixed f t ⟨0,0,0⟩ i j hh] using hf i j hh
      · have hni : i ≠ 0 := fun he => hh (Or.inl he)
        have hnj : j ≠ 0 := fun he => hh (Or.inr he)
        fin_cases i <;> fin_cases j <;> try contradiction
        all_goals
          -- Port repair (the D104/D30 defect class): `linarith` treats the unreduced
          -- `![…] i j` indexing of `core` as an atom, and the projection `simp` lemmas do not
          -- fire on `Fin.mk` numerals in this revision, so the four non-zero `core` entries are
          -- exposed through definitional (`rfl`-level) reduction before `linarith` runs.
          first
            | change entryLower f p 1 1 ≤ t.r + f.A * f.c ∧ t.r + f.A * f.c ≤ entryUpper f p 1 1
            | change entryLower f p 1 2 ≤ t.s + f.B * f.c ∧ t.s + f.B * f.c ≤ entryUpper f p 1 2
            | change entryLower f p 2 1 ≤ t.t + f.A * f.d ∧ t.t + f.A * f.d ≤ entryUpper f p 2 1
            | change entryLower f p 2 2 ≤ -t.r + f.B * f.d ∧ -t.r + f.B * f.d ≤ entryUpper f p 2 2
          constructor <;> linarith
    refine ⟨h.r_pos, (le_max_left _ _).trans h.s_lower, h.s_le_r,
      (le_max_left _ _).trans h.t_lower, h.t_le_r, ?_, ?_, ?_⟩
    · exact fun i j => ((entry_bands_iff _ _ _ _ _).mpr (hi i j)).1
    · exact fun i j => ((entry_bands_iff _ _ _ _ _).mpr (hi i j)).2.1
    · exact fun i j => ((entry_bands_iff _ _ _ _ _).mpr (hi i j)).2.2

theorem maxTail_dominates {l : TailLimits} {t : Tail} (h : InTailBox l t) :
    t.r ≤ (maxTail l).r ∧ t.s ≤ (maxTail l).s ∧ t.t ≤ (maxTail l).t := by
  exact ⟨h.r_upper, le_min (h.s_le_r.trans h.r_upper) h.s_upper,
    le_min (h.t_le_r.trans h.r_upper) h.t_upper⟩

theorem endpointChecks_of_feasible {l : TailLimits} {t : Tail}
    (h : InTailBox l t) : EndpointChecks l := by
  have hm := maxTail_dominates h
  exact ⟨h.r_pos.trans_le h.r_upper, h.r_lower.trans h.r_upper,
    h.s_lower.trans hm.2.1, h.t_lower.trans hm.2.2⟩

theorem maxTail_feasible {l : TailLimits} (h : EndpointChecks l) : InTailBox l (maxTail l) := by
  exact ⟨h.1, h.2.1, le_rfl, h.2.2.1, min_le_right _ _,
    h.2.2.2, min_le_right _ _, min_le_left _ _, min_le_left _ _⟩

theorem positive_tail_nonempty_iff (l : TailLimits) :
    (∃ t, InTailBox l t) ↔ EndpointChecks l := by
  constructor
  · rintro ⟨t, ht⟩; exact endpointChecks_of_feasible ht
  · intro h; exact ⟨maxTail l, maxTail_feasible h⟩

theorem full_tail_nonempty_iff (f : Frame) (p : ℝ) :
    (∃ t, TailBounds f p t) ↔ FixedChecks f p ∧ EndpointChecks (tailLimits f p) := by
  constructor
  · rintro ⟨t, ht⟩
    rcases (tailBounds_iff _ _ _).mp ht with ⟨hf, hb⟩
    exact ⟨hf, endpointChecks_of_feasible hb⟩
  · rintro ⟨hf, hh⟩
    exact ⟨maxTail (tailLimits f p), (tailBounds_iff _ _ _).mpr ⟨hf, maxTail_feasible hh⟩⟩

/-- Closed endpoint conditions and positive r are preserved along the actual
three-coordinate line segment. -/
theorem tailBox_segment {l : TailLimits} {a b : Tail}
    (ha : InTailBox l a) (hb : InTailBox l b) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : InTailBox l (tailMix a b lam) := by
  have hr : 0 < mix a.r b.r lam := by
    have hlo : 0 < min a.r b.r := lt_min ha.r_pos hb.r_pos
    exact hlo.trans_le (mix_lower (min_le_left _ _) (min_le_right _ _) h0 h1)
  exact ⟨hr,
    mix_lower ha.r_lower hb.r_lower h0 h1,
    mix_upper ha.r_upper hb.r_upper h0 h1,
    mix_lower ha.s_lower hb.s_lower h0 h1,
    mix_upper ha.s_upper hb.s_upper h0 h1,
    mix_lower ha.t_lower hb.t_lower h0 h1,
    mix_upper ha.t_upper hb.t_upper h0 h1,
    mix_le_mix ha.s_le_r hb.s_le_r h0 h1,
    mix_le_mix ha.t_le_r hb.t_le_r h0 h1⟩

end
end Rho5.ExternalBFibreCapacity
