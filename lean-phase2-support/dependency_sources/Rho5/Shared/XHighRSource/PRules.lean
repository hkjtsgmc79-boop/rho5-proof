import Rho5.Shared.XHighRSource.CoordTransport

/-!
# D145 stage B — the V34 `P0`–`P3` factor rules as Lean

The archived V34 high package closes leaves with four new rules (`fixed_source/source/
rankone_oracle.hpp`, `factor_oracle.hpp`, `factor_graph.hpp`, theory `BOUNDED_RANK_ONE_GRAPH.md`):

* `P0`–`P2` — **whole-factor incompatibility**: a complete bounded rank-one factor packet is
  infeasible (`packet_feasible = false` on the three actual packets `X` (stage), `Y` (orig) and
  `C` (core));
* `P3` — **direct intersection contradiction**: some contracted interval is empty (`empty_i`).

This module pays the *soundness* content of those rules over the reals, in the exact interval
arithmetic of the archived implementation:

1. `BI` and the operations `plus_i`/`minus_i`/`meet_i`/`times_i`, each sound for real points
   (`Mem`), and `Empty ⟹ no real point` — the `P3` rule;
2. the packet predicate `Realizes`, the three empty-factor rules, the single-factor zero
   reduction and the magnitude/sign lemmas — the `P0`/`P1` layer;
3. the `P2` **multiplicative cycle rule**: the archived difference-constraint graph, with potentials
   `pot anchor = 1`, `pot x_i = a_i`, `pot y_j = 1/b_j`, and the theorem that a closed chain of
   constraints forces the product of its edge weights to be at least one.  Hence a closed chain with
   product `< 1` rejects every strictly positive realization — exactly the certificate the archived
   solver records.

Explicitly **not** paid here (recorded, not assumed): the completeness direction of `P1` (the full
sign-mask enumeration over the forced factors) and of `P2` (the relaxation/shortest-path
construction of rational factors when no small cycle exists), and the model-specific packets of the
two diagrams (they are the `SourceRows`/`DiagramIntake` stage-B items).  The archived report itself
states the general result had no Lean formalization; nothing here is imported from it.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

/-! ## 1. Exact intervals and the `P3` contraction rules -/

/-- A closed interval with real endpoints (the archived `BI`). -/
structure BI where
  /-- lower endpoint -/
  lo : ℝ
  /-- upper endpoint -/
  hi : ℝ

namespace BI

/-- Membership of a real in the interval. -/
def Mem (I : BI) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- The archived `empty_i`: an interval with `hi < lo` carries no real point. -/
def Empty (I : BI) : Prop := I.hi < I.lo

/-- The archived `plus_i`. -/
def plus (I J : BI) : BI := ⟨I.lo + J.lo, I.hi + J.hi⟩
/-- The archived `minus_i`. -/
def minus (I J : BI) : BI := ⟨I.lo - J.hi, I.hi - J.lo⟩
/-- The archived `meet_i`. -/
def meet (I J : BI) : BI := ⟨max I.lo J.lo, min I.hi J.hi⟩
/-- The interval `[0,0]`. -/
def zero : BI := ⟨0, 0⟩
/-- The four-corner product interval of the archived `times_i`. -/
def times (I J : BI) : BI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- The archived `mag_interval` at sign `+1`. -/
def magPos (I : BI) : BI := ⟨max I.lo 0, I.hi⟩
/-- The archived `mag_interval` at sign `-1`. -/
def magNeg (I : BI) : BI := ⟨max (-I.hi) 0, -I.lo⟩

theorem not_mem_of_empty {I : BI} {x : ℝ} (h : I.Empty) : ¬ I.Mem x :=
  fun hx => (not_le.mpr h) (le_trans hx.1 hx.2)

/-- **The `P3` rule**: an empty interval refutes every real point that had to lie in it. -/
theorem empty_contradiction {I : BI} (h : I.Empty) : ¬ ∃ x : ℝ, I.Mem x :=
  fun ⟨_, hx⟩ => not_mem_of_empty h hx

theorem mem_plus {I J : BI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.plus J).Mem (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem mem_minus {I J : BI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.minus J).Mem (x - y) :=
  ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

theorem mem_meet {I J : BI} {x : ℝ} (hx : I.Mem x) (hy : J.Mem x) : (I.meet J).Mem x :=
  ⟨max_le hx.1 hy.1, le_min hx.2 hy.2⟩

theorem mem_zero {x : ℝ} (h : x = 0) : BI.zero.Mem x := by
  rw [h]; exact ⟨le_refl 0, le_refl 0⟩

/-- Magnitudes of a nonnegative member lie in `magPos`. -/
theorem mem_magPos {I : BI} {x : ℝ} (hx : I.Mem x) (h0 : 0 ≤ x) : (magPos I).Mem |x| := by
  have hx' : |x| = x := abs_of_nonneg h0
  exact ⟨by rw [hx']; exact max_le hx.1 h0, by rw [hx']; exact hx.2⟩

/-- Magnitudes of a nonpositive member lie in `magNeg`. -/
theorem mem_magNeg {I : BI} {x : ℝ} (hx : I.Mem x) (h0 : x ≤ 0) : (magNeg I).Mem |x| := by
  have hx' : |x| = -x := abs_of_nonpos h0
  refine ⟨?_, ?_⟩
  · rw [hx']; exact max_le (by linarith [hx.2]) (by linarith)
  · rw [hx']
    show -x ≤ -I.lo
    linarith [hx.1]

/-! ### The four-corner product is a sound product interval -/

private theorem min4_le_left {a b c d : ℝ} : min (min a b) (min c d) ≤ a :=
  (min_le_left _ _).trans (min_le_left _ _)
private theorem min4_le_right {a b c d : ℝ} : min (min a b) (min c d) ≤ b :=
  (min_le_left _ _).trans (min_le_right _ _)
private theorem min4_le_left' {a b c d : ℝ} : min (min a b) (min c d) ≤ c :=
  (min_le_right _ _).trans (min_le_left _ _)
private theorem min4_le_right' {a b c d : ℝ} : min (min a b) (min c d) ≤ d :=
  (min_le_right _ _).trans (min_le_right _ _)
private theorem le_max4_left {a b c d : ℝ} : a ≤ max (max a b) (max c d) :=
  (le_max_left _ _).trans (le_max_left _ _)
private theorem le_max4_right {a b c d : ℝ} : b ≤ max (max a b) (max c d) :=
  (le_max_right _ _).trans (le_max_left _ _)
private theorem le_max4_left' {a b c d : ℝ} : c ≤ max (max a b) (max c d) :=
  (le_max_left _ _).trans (le_max_right _ _)
private theorem le_max4_right' {a b c d : ℝ} : d ≤ max (max a b) (max c d) :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The lower corner bound of the product of two intervals. -/
private theorem min4_le_mul {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y)
    (hy2 : y ≤ d) : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rcases le_total 0 a with ha | ha
    · rcases le_total 0 c with hc | hc
      · exact min4_le_left.trans (mul_le_mul hx1 hy1 hc hx)
      · exact min4_le_left.trans
          (le_trans (mul_nonpos_of_nonneg_of_nonpos ha hc) (mul_nonneg hx hy))
    · exact min4_le_right.trans
        (le_trans (mul_le_mul_of_nonpos_left hy2 ha) (mul_le_mul_of_nonneg_right hx1 hy))
  · exact min4_le_left'.trans
      (le_trans (mul_le_mul_of_nonneg_left hy1 (le_trans hx hx2))
        (mul_le_mul_of_nonpos_right hx2 hy))
  · exact min4_le_right.trans
      (le_trans (mul_le_mul_of_nonneg_right hx1 (le_trans hy hy2))
        (mul_le_mul_of_nonpos_left hy2 hx))
  · rcases le_total 0 b with hb | hb
    · exact min4_le_left'.trans
        (le_trans (mul_nonpos_of_nonneg_of_nonpos hb (le_trans hy1 hy))
          (mul_nonneg_of_nonpos_of_nonpos hx hy))
    · rcases le_total 0 d with hd | hd
      · exact min4_le_right'.trans
          (le_trans (mul_nonpos_of_nonpos_of_nonneg hb hd) (mul_nonneg_of_nonpos_of_nonpos hx hy))
      · refine min4_le_right'.trans ?_
        have h1 : (-b) * (-d) ≤ (-x) * (-y) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
        have e1 : (-b) * (-d) = b * d := by ring
        have e2 : (-x) * (-y) = x * y := by ring
        rwa [e1, e2] at h1

/-- The upper corner bound, by the sign symmetry of the lower one. -/
private theorem mul_le_max4 {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y)
    (hy2 : y ≤ d) : x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h := min4_le_mul (a := a) (b := b) (c := -d) (d := -c) (x := x) (y := -y)
    hx1 hx2 (by linarith) (by linarith)
  have hneg : min (min (a * -d) (a * -c)) (min (b * -d) (b * -c))
      = -max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
    simp only [mul_neg, min_neg_neg, max_comm (a * c) (a * d), max_comm (b * c) (b * d)]
  rw [hneg] at h
  have hxy : x * -y = -(x * y) := mul_neg x y
  rw [hxy] at h
  linarith

/-- `times_i` is sound: every real product of two members lies in the product interval. -/
theorem mem_times {I J : BI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.times J).Mem (x * y) :=
  ⟨min4_le_mul hx.1 hx.2 hy.1 hy.2, mul_le_max4 hx.1 hx.2 hy.1 hy.2⟩

end BI

/-! ## 2. Packets, and the `P0`/`P1` layer -/

/-- A bounded rank-one factor packet: factor intervals `a`, `b` and product intervals `z`. -/
structure Packet (m n : ℕ) where
  /-- the left factor intervals -/
  a : Fin m → BI
  /-- the right factor intervals -/
  b : Fin n → BI
  /-- the product intervals -/
  z : Fin m → Fin n → BI

namespace Packet

/-- A real realization of a packet. -/
def Realizes (P : Packet m n) (A : Fin m → ℝ) (B : Fin n → ℝ) : Prop :=
  (∀ i, (P.a i).Mem (A i)) ∧ (∀ j, (P.b j).Mem (B j)) ∧
    (∀ i j, (P.z i j).Mem (A i * B j))

/-- `P0`: an empty factor interval refutes the packet. -/
theorem not_realizes_of_empty_a {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ} {i : Fin m}
    (h : (P.a i).Empty) : ¬ P.Realizes A B :=
  fun hr => (P.a i).not_mem_of_empty h (hr.1 i)

theorem not_realizes_of_empty_b {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ} {j : Fin n}
    (h : (P.b j).Empty) : ¬ P.Realizes A B :=
  fun hr => (P.b j).not_mem_of_empty h (hr.2.1 j)

theorem not_realizes_of_empty_z {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ} {i : Fin m}
    {j : Fin n} (h : (P.z i j).Empty) : ¬ P.Realizes A B :=
  fun hr => (P.z i j).not_mem_of_empty h (hr.2.2 i j)

/-- `P1` (zero reduction, left factor): a factor whose own interval and all incident product
intervals contain zero may be set to zero. -/
theorem realizes_update_zero_a {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ}
    (hreal : P.Realizes A B) {i : Fin m} (h0a : (P.a i).Mem 0)
    (h0z : ∀ j, (P.z i j).Mem 0) : P.Realizes (Function.update A i 0) B := by
  refine ⟨?_, hreal.2.1, ?_⟩
  · intro i'
    by_cases h : i' = i
    · subst h; rw [Function.update_self]; exact h0a
    · rw [Function.update_of_ne h]; exact hreal.1 i'
  · intro i' j
    by_cases h : i' = i
    · subst h; rw [Function.update_self, zero_mul]; exact h0z j
    · rw [Function.update_of_ne h]; exact hreal.2.2 i' j

/-- `P1` (zero reduction, right factor). -/
theorem realizes_update_zero_b {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ}
    (hreal : P.Realizes A B) {j : Fin n} (h0b : (P.b j).Mem 0)
    (h0z : ∀ i, (P.z i j).Mem 0) : P.Realizes A (Function.update B j 0) := by
  refine ⟨hreal.1, ?_, ?_⟩
  · intro j'
    by_cases h : j' = j
    · subst h; rw [Function.update_self]; exact h0b
    · rw [Function.update_of_ne h]; exact hreal.2.1 j'
  · intro i j'
    by_cases h : j' = j
    · subst h; rw [Function.update_self, mul_zero]; exact h0z i
    · rw [Function.update_of_ne h]; exact hreal.2.2 i j'

/-- `P1` (forced sign, left): an interval strictly above zero forces a nonzero factor. -/
theorem ne_zero_of_mem_a {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ}
    (hreal : P.Realizes A B) {i : Fin m} (h : 0 < (P.a i).lo) : A i ≠ 0 :=
  fun hz => (not_le.mpr h) (hz ▸ (hreal.1 i).1)

/-- `P1` (forced sign, right). -/
theorem ne_zero_of_mem_b {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ}
    (hreal : P.Realizes A B) {j : Fin n} (h : 0 < (P.b j).lo) : B j ≠ 0 :=
  fun hz => (not_le.mpr h) (hz ▸ (hreal.2.1 j).1)

end Packet

/-! ## 3. The `P2` multiplicative difference-constraint graph -/

/-- The vertices of the archived constraint graph: the anchor `t_0 = 0`, the left potentials
`x_i = log a_i` and the right potentials `y_j = -log b_j`. -/
inductive PVert (m n : ℕ) where
  | anchor : PVert m n
  | left : Fin m → PVert m n
  | right : Fin n → PVert m n

/-- The multiplicative potential: `pot anchor = 1`, `pot x_i = a_i`, `pot y_j = 1/b_j`. -/
def ppot {m n : ℕ} (A : Fin m → ℝ) (B : Fin n → ℝ) : PVert m n → ℝ
  | .anchor => 1
  | .left i => A i
  | .right j => (B j)⁻¹

/-- The six edge families of `factor_graph.hpp` §2, each read as `pot v ≤ pot u * w`:
`a_i ≤ u_i`, `l_i ≤ a_i`, `b_j ≤ v_j`, `m_j ≤ b_j`, `a_i b_j ≤ U_ij`, `L_ij ≤ a_i b_j`. -/
inductive PEdge {m n : ℕ} (P : Packet m n) : PVert m n → ℝ → PVert m n → Prop where
  | hiA (i : Fin m) : PEdge P .anchor ((P.a i).hi) (.left i)
  | loA (i : Fin m) (h : 0 < (P.a i).lo) : PEdge P (.left i) ((P.a i).lo)⁻¹ .anchor
  | hiB (j : Fin n) : PEdge P (.right j) ((P.b j).hi) .anchor
  | loB (j : Fin n) (h : 0 < (P.b j).lo) : PEdge P .anchor ((P.b j).lo)⁻¹ (.right j)
  | hiZ (i : Fin m) (j : Fin n) : PEdge P (.right j) ((P.z i j).hi) (.left i)
  | loZ (i : Fin m) (j : Fin n) (h : 0 < (P.z i j).lo) :
      PEdge P (.left i) ((P.z i j).lo)⁻¹ (.right j)

/-- A walk of weighted edges. -/
inductive Walk {V : Type*} (E : V → ℝ → V → Prop) : V → List (V × ℝ) → V → Prop where
  | nil (u : V) : Walk E u [] u
  | cons {u v x : V} {w : ℝ} {l : List (V × ℝ)} (he : E u w v) (htl : Walk E v l x) :
      Walk E u ((v, w) :: l) x

/-- **The telescoping core of the `P2` rule**: a walk of constraints multiplies out, and all edge
weights are positive. -/
theorem Walk.le_prod_and_pos {V : Type*} {E : V → ℝ → V → Prop} {pot : V → ℝ}
    (hpos : ∀ v, 0 < pot v) (hEpos : ∀ u w v, E u w v → 0 < w)
    (hE : ∀ u w v, E u w v → pot v ≤ pot u * w) {u₀ x₀ : V} {l₀ : List (V × ℝ)}
    (h : Walk E u₀ l₀ x₀) :
    pot x₀ ≤ pot u₀ * (l₀.map Prod.snd).prod ∧ 0 < (l₀.map Prod.snd).prod := by
  induction h with
  | nil u => exact ⟨by simp, by simp⟩
  | cons he htl ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hstep : pot _ ≤ pot _ * _ := hE _ _ _ he
      have hw : (0 : ℝ) < _ := hEpos _ _ _ he
      refine ⟨?_, ?_⟩
      · calc pot _ ≤ pot _ * (List.map Prod.snd _).prod := ih1
          _ ≤ (pot _ * _) * (List.map Prod.snd _).prod :=
              mul_le_mul_of_nonneg_right hstep ih2.le
          _ = pot _ * (List.map Prod.snd _).prod := by
              rw [List.map_cons, List.prod_cons]; ring
      · rw [List.map_cons, List.prod_cons]
        exact mul_pos hw ih2

/-- **The `P2` cycle rule**: a closed walk forces the product of its edge weights to be at least
one. -/
theorem Walk.one_le_prod {V : Type*} {E : V → ℝ → V → Prop} {pot : V → ℝ}
    (hpos : ∀ v, 0 < pot v) (hEpos : ∀ u w v, E u w v → 0 < w)
    (hE : ∀ u w v, E u w v → pot v ≤ pot u * w) {u : V} {l : List (V × ℝ)}
    (h : Walk E u l u) : 1 ≤ (l.map Prod.snd).prod := by
  obtain ⟨h1, _⟩ := Walk.le_prod_and_pos hpos hEpos hE h
  have h2 : pot u * 1 ≤ pot u * (l.map Prod.snd).prod := by simpa using h1
  exact le_of_mul_le_mul_left h2 (hpos u)

/-- Each archived edge is a true constraint for every strictly positive realization. -/
theorem PEdge.le_pot {m n : ℕ} {P : Packet m n} {A : Fin m → ℝ} {B : Fin n → ℝ}
    (hreal : P.Realizes A B) (hB : ∀ j, 0 < B j)
    {u : PVert m n} {w : ℝ} {v : PVert m n} (e : PEdge P u w v) :
    ppot A B v ≤ ppot A B u * w := by
  cases e with
  | hiA i =>
      have h1 : A i ≤ (P.a i).hi := (hreal.1 i).2
      simpa [ppot] using h1
  | loA i h =>
      have h1 : (1 : ℝ) ≤ A i / (P.a i).lo := by
        rw [le_div_iff₀ h]
        simpa using (hreal.1 i).1
      simpa [ppot, div_eq_mul_inv] using h1
  | hiB j =>
      have hb : 0 < B j := hB j
      have h1 : (1 : ℝ) ≤ (P.b j).hi / B j := by
        rw [le_div_iff₀ hb]
        simpa using (hreal.2.1 j).2
      have h2 : (P.b j).hi / B j = (B j)⁻¹ * (P.b j).hi := by
        rw [div_eq_inv_mul, mul_comm]
      show (1 : ℝ) ≤ (B j)⁻¹ * (P.b j).hi
      rw [← h2]
      exact h1
  | loB j h =>
      have h1 : (B j)⁻¹ ≤ ((P.b j).lo)⁻¹ := by
        rw [inv_le_inv₀ (hB j) h]
        exact (hreal.2.1 j).1
      simpa [ppot] using h1
  | hiZ i j =>
      have hb : 0 < B j := hB j
      have hz : A i * B j ≤ (P.z i j).hi := (hreal.2.2 i j).2
      have h1 : A i ≤ (P.z i j).hi / B j := (le_div_iff₀ hb).mpr hz
      have h2 : (P.z i j).hi / B j = (B j)⁻¹ * (P.z i j).hi := by
        rw [div_eq_inv_mul, mul_comm]
      show A i ≤ (B j)⁻¹ * (P.z i j).hi
      rw [← h2]
      exact h1
  | loZ i j h =>
      have hb : 0 < B j := hB j
      have hz : (P.z i j).lo ≤ A i * B j := (hreal.2.2 i j).1
      have h1 : (B j)⁻¹ * (P.z i j).lo ≤ A i := by
        have h2 : (P.z i j).lo * (B j)⁻¹ ≤ A i * B j * (B j)⁻¹ :=
          mul_le_mul_of_nonneg_right hz (inv_nonneg.mpr hb.le)
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one] at h2
        simpa [mul_comm] using h2
      have h3 : (B j)⁻¹ ≤ A i / (P.z i j).lo := (le_div_iff₀ h).mpr h1
      simpa [ppot, div_eq_mul_inv] using h3

/-- **The `P2` rejection rule for a packet**: a closed constraint chain whose weight product is
`< 1` refutes every strictly positive realization. -/
theorem not_realizes_of_cycle {m n : ℕ} {P : Packet m n} {u : PVert m n}
    {l : List (PVert m n × ℝ)} (hwpos : ∀ u w v, PEdge P u w v → 0 < w)
    (hwalk : Walk (PEdge P) u l u) (hsmall : (l.map Prod.snd).prod < 1) :
    ¬ ∃ A B, P.Realizes A B ∧ (∀ i, 0 < A i) ∧ (∀ j, 0 < B j) := by
  rintro ⟨A, B, hreal, hA, hB⟩
  have hpos : ∀ v : PVert m n, 0 < ppot A B v := by
    intro v
    cases v with
    | anchor => simp [ppot]
    | left i => simpa [ppot] using hA i
    | right j => simpa [ppot] using inv_pos.mpr (hB j)
  have hone := Walk.one_le_prod hpos hwpos (fun u w v he => PEdge.le_pot hreal hB he) hwalk
  linarith

end

end Rho5.Shared.XHighRSource
