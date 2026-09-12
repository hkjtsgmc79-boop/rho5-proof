import Rho5.ExternalBFibreCapacity.Beta
import Rho5.ExternalBFibreCapacity.RowCapacity

namespace Rho5.ExternalBFibreCapacity
noncomputable section

/-- A zero-x row is represented by (0,0).  No sign is imposed on any receiver. -/
def signedRow (x u : ℝ) : ℝ := if x = 0 then 0 else if 0 < x then u else -u

def rowA (f : Frame) : Fin 4 → ℝ := ![1, |f.x 0|, |f.x 1|, |f.x 2|]
def rowB (f : Frame) (b : ℝ) : Fin 4 → ℝ :=
  ![b, signedRow (f.x 0) (f.u 0), signedRow (f.x 1) (f.u 1),
    signedRow (f.x 2) (f.u 2)]

theorem signedRow_bound {x u : ℝ} (h : |u| ≤ 1) : |signedRow x u| ≤ 1 := by
  unfold signedRow
  split_ifs <;> simp_all

theorem left_row_iff {x u p e : ℝ} (hu : |u| ≤ 1) (hp : 0 ≤ p)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |p*x-e*u| ≤ 1 ↔ |x| * p - signedRow x u * e ≤ 1 := by
  have hU : e*u ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hu).2 he0
    nlinarith
  have hL : -1 ≤ e*u := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 he0
    nlinarith
  by_cases hx : x = 0
  · simp only [hx, abs_zero, zero_mul, mul_zero, zero_sub, abs_neg,
      signedRow, if_pos rfl]
    constructor
    · intro _; norm_num
    · intro _; exact abs_le.mpr ⟨hL, hU⟩
  · rcases lt_or_gt_of_ne hx with hxn | hxp
    · have hn : ¬0 < x := not_lt.mpr (le_of_lt hxn)
      have hm := mul_nonpos_of_nonneg_of_nonpos hp (le_of_lt hxn)
      simp only [signedRow, if_neg hx, if_neg hn, abs_of_neg hxn, abs_le]
      constructor
      · rintro ⟨hl, hh⟩; nlinarith
      · intro h; constructor <;> nlinarith
    · have hm := mul_nonneg hp (le_of_lt hxp)
      simp only [signedRow, if_neg hx, if_pos hxp, abs_of_pos hxp, abs_le]
      constructor
      · rintro ⟨hl, hh⟩; nlinarith
      · intro h; constructor <;> nlinarith

/-- The original lower head band is automatic in the normalized p>=1 slice. -/
theorem head_row_iff {p e b : ℝ} (hp : 1 ≤ p)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |p-e*b| ≤ 1 ↔ p-b*e ≤ 1 := by
  have hh := mul_mem_unit he0 he1 hb0 hb1
  rw [abs_le]
  constructor
  · rintro ⟨hl, hu⟩; nlinarith
  · intro h; constructor <;> nlinarith

def rows (f : Frame) (hf : FrameBounds f) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    RowSystem where
  a := rowA f
  b := rowB f b
  a_nonneg := by intro i; fin_cases i <;> simp [rowA, abs_nonneg]
  a_le_one := by
    intro i
    fin_cases i
    · norm_num [rowA]
    · simpa [rowA] using hf.x_bound 0
    · simpa [rowA] using hf.x_bound 1
    · simpa [rowA] using hf.x_bound 2
  b_bound := by
    intro i
    fin_cases i
    · simpa [rowB, abs_of_pos hb] using hb1
    · simpa [rowB] using signedRow_bound (x := f.x 0) (hf.u_bound 0)
    · simpa [rowB] using signedRow_bound (x := f.x 1) (hf.u_bound 1)
    · simpa [rowB] using signedRow_bound (x := f.x 2) (hf.u_bound 2)
  zero_row := by
    intro i h
    fin_cases i
    · norm_num [rowA] at h
    · have hz : f.x 0 = 0 := abs_eq_zero.mp (by simpa [rowA] using h)
      simp [rowB, signedRow, hz]
    · have hz : f.x 1 = 0 := abs_eq_zero.mp (by simpa [rowA] using h)
      simp [rowB, signedRow, hz]
    · have hz : f.x 2 = 0 := abs_eq_zero.mp (by simpa [rowA] using h)
      simp [rowB, signedRow, hz]
  head_a := rfl
  head_positive := hb

/-- The row polygon is exactly the head and left-prefix part of the physical
system. The right prefix and q-stage checks are retained separately. -/
def LeftFeasible (f : Frame) (b p e : ℝ) : Prop :=
  1 ≤ p ∧ 0 ≤ e ∧ e ≤ 1 ∧ |p-e*b| ≤ 1 ∧
    ∀ i, |p*f.x i-e*f.u i| ≤ 1

theorem rows_iff_left (f : Frame) (hf : FrameBounds f) (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) (p e : ℝ) :
    RowFeasible (rows f hf b hb hb1) p e ↔ LeftFeasible f b p e := by
  constructor
  · rintro ⟨hp, he0, he1, hr⟩
    have hhead : p-b*e ≤ 1 := by simpa [rows, rowA, rowB] using hr 0
    refine ⟨hp, he0, he1,
      (head_row_iff hp he0 he1 (le_of_lt hb) hb1).mpr hhead, ?_⟩
    intro i
    apply (left_row_iff (hf.u_bound i) (by linarith) he0 he1).mpr
    fin_cases i
    · simpa [rows, rowA, rowB] using hr 1
    · simpa [rows, rowA, rowB] using hr 2
    · simpa [rows, rowA, rowB] using hr 3
  · rintro ⟨hp, he0, he1, hh, hl⟩
    refine ⟨hp, he0, he1, ?_⟩
    intro i
    fin_cases i
    · simpa [rows, rowA, rowB] using
        (head_row_iff hp he0 he1 (le_of_lt hb) hb1).mp hh
    · simpa [rows, rowA, rowB] using
        (left_row_iff (hf.u_bound 0) (by linarith) he0 he1).mp (hl 0)
    · simpa [rows, rowA, rowB] using
        (left_row_iff (hf.u_bound 1) (by linarith) he0 he1).mp (hl 1)
    · simpa [rows, rowA, rowB] using
        (left_row_iff (hf.u_bound 2) (by linarith) he0 he1).mp (hl 2)

/-- Raw finite expressions let the canonical map be a function of the frame,
not of a supplied feasibility witness. -/
def rawUnary (a b : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  if 0 < a i ∧ 0 ≤ b i then (1+b i)/a i else 2

def rawPair (a b : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if 0 < b i ∧ b j < 0 then (b i-b j)/(a j*b i-a i*b j) else 2

def rawP (a b : Fin 4 → ℝ) : ℝ :=
  min (min4 (rawUnary a b)) (min4 fun i => min4 (rawPair a b i))

def rawE (a b : Fin 4 → ℝ) : ℝ :=
  max 0 (max4 fun i => if 0 < b i then (a i*rawP a b-1)/b i else 0)

def prefixP (f : Frame) : ℝ :=
  if 0 < betaBar f then rawP (rowA f) (rowB f (betaBar f)) else 1

def prefixE (f : Frame) : ℝ :=
  if 0 < betaBar f then rawE (rowA f) (rowB f (betaBar f)) else 0

@[simp] theorem rawP_rows (f : Frame) (hf : FrameBounds f) (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    rowP (rows f hf b hb hb1) = rawP (rowA f) (rowB f b) := rfl
@[simp] theorem rawE_rows (f : Frame) (hf : FrameBounds f) (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    rowE (rows f hf b hb hb1) = rawE (rowA f) (rowB f b) := rfl

theorem prefix_zero_beta {f : Frame} {p e : ℝ}
    (h : PrefixBounds f 0 p e) : p = 1 := by
  have hh := (abs_le.mp h.head).2
  simp only [mul_zero, sub_zero] at hh
  exact le_antisymm hh h.one_le_p

/-- A1+A2+A3: one prefix common to every source of the same frame. -/
theorem prefix_maximum {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) :
    Admissible f (betaBar f) (prefixP f) (prefixE f) t ∧
    p ≤ prefixP f ∧ 1 ≤ prefixP f ∧ prefixP f ≤ 2 ∧
    0 ≤ prefixE f ∧ prefixE f ≤ 1 := by
  have hB := beta_endpoint_admissible h
  by_cases hb : 0 < betaBar f
  · let w := rows f h.1 (betaBar f) hb hB.2.1.beta_le_one
    have hrow : RowFeasible w p e :=
      (rows_iff_left f h.1 _ hb hB.2.1.beta_le_one p e).mpr
        ⟨hB.2.1.one_le_p, hB.2.1.e_nonneg, hB.2.1.e_le_one,
          hB.2.1.head, hB.2.1.left⟩
    have hP : prefixP f = rowP w := by simp [prefixP, hb, w]
    have hE : prefixE f = rowE w := by simp [prefixE, hb, w]
    have hpmax : p ≤ prefixP f := by rw [hP]; exact feasible_le_rowP hrow
    have hm := row_endpoint_feasible w
    have hl : LeftFeasible f (betaBar f) (prefixP f) (prefixE f) := by
      rw [hP, hE]
      exact (rows_iff_left f h.1 _ hb hB.2.1.beta_le_one _ _).mp hm
    have pp : PrefixBounds f (betaBar f) (prefixP f) (prefixE f) := {
      one_le_p := hl.1, e_nonneg := hl.2.1, e_le_one := hl.2.2.1,
      beta_nonneg := hB.2.1.beta_nonneg, beta_le_one := hB.2.1.beta_le_one,
      head := hl.2.2.2.1, left := hl.2.2.2.2,
      right := hB.2.1.right,
      q_stage := fun j => (hB.2.1.q_stage j).trans hpmax }
    refine ⟨⟨h.1, pp, tailBounds_mono_p h.2.2 hpmax⟩, hpmax,
      hl.1, ?_, hl.2.1, hl.2.2.1⟩
    rw [hP]; exact (rowP_bounds w).2
  · have hb0 : betaBar f = 0 :=
      le_antisymm (le_of_not_gt hb) hB.2.1.beta_nonneg
    have hp1 : p = 1 := prefix_zero_beta (by simpa [hb0] using hB.2.1)
    have hp' : prefixP f = 1 := by simp [prefixP, hb]
    have he' : prefixE f = 0 := by simp [prefixE, hb]
    have pp : PrefixBounds f (betaBar f) (prefixP f) (prefixE f) := by
      rw [hb0, hp', he']
      refine ⟨le_rfl, le_rfl, by norm_num, le_rfl, by norm_num,
        by norm_num, ?_, ?_, ?_⟩
      · intro i; simpa using h.1.x_bound i
      · simpa [hb0] using hB.2.1.right
      · simpa [hp1] using h.2.1.q_stage
    refine ⟨⟨h.1, pp, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hp', hp1] using h.2.2
    all_goals simp [hp', he', hp1]

/-- Least e at the maximal p, including the betaBar=0 face. -/
theorem prefixE_le_of_at_max {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t)
    {E : ℝ} (hE : LeftFeasible f (betaBar f) (prefixP f) E) : prefixE f ≤ E := by
  have hB := beta_endpoint_admissible h
  by_cases hb : 0 < betaBar f
  · let w := rows f h.1 (betaBar f) hb hB.2.1.beta_le_one
    have hm : RowFeasible w (rowP w) E := by
      apply (rows_iff_left f h.1 _ hb hB.2.1.beta_le_one _ _).mpr
      simpa [prefixP, hb, w] using hE
    simpa [prefixE, hb, w] using rowE_le_of_feasible_at_max hm
  · simpa [prefixE, hb] using hE.2.1

/-- All original left/head bands remain convex when p and e change together. -/
theorem prefix_segment {f : Frame} {b p e P E lam : ℝ}
    (h : PrefixBounds f b p e) (h' : PrefixBounds f b P E) (hp : p ≤ P)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    PrefixBounds f b (mix p P lam) (mix e E lam) := by
  refine ⟨mix_lower h.one_le_p h'.one_le_p h0 h1,
    mix_lower h.e_nonneg h'.e_nonneg h0 h1,
    mix_upper h.e_le_one h'.e_le_one h0 h1,
    h.beta_nonneg, h.beta_le_one, ?_, ?_, h.right, ?_⟩
  · have hm := abs_mix_le h.head h'.head h0 h1
    have heq : mix (p-e*b) (P-E*b) lam = mix p P lam-mix e E lam*b := by
      dsimp [mix]; ring
    rwa [heq] at hm
  · intro i
    have hm := abs_mix_le (h.left i) (h'.left i) h0 h1
    have heq : mix (p*f.x i-e*f.u i) (P*f.x i-E*f.u i) lam =
        mix p P lam*f.x i-mix e E lam*f.u i := by dsimp [mix]; ring
    rwa [heq] at hm
  · intro j
    exact (h.q_stage j).trans (mix_between hp h0 h1).1

/-- A4 in full actual-source semantics; e is not assumed monotone. -/
theorem pe_segment_admissible {f : Frame} {b p e : ℝ} {t : Tail}
    (h : Admissible f b p e t) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Admissible f (betaBar f) (mix p (prefixP f) lam) (mix e (prefixE f) lam) t := by
  have hB := beta_endpoint_admissible h
  have hm := prefix_maximum h
  exact ⟨h.1, prefix_segment hB.2.1 hm.1.2.1 hm.2.1 h0 h1,
    tailBounds_mono_p h.2.2 (mix_between hm.2.1 h0 h1).1⟩

end
end Rho5.ExternalBFibreCapacity
