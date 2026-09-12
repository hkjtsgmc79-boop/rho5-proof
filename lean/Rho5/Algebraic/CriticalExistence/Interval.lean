import Rho5.Algebraic.CriticalExistence.Expression
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Rho5.Algebraic.CriticalExistence
noncomputable section

structure QI where
  lo : ℚ
  hi : ℚ

def QI.Mem (I : QI) (v : ℝ) : Prop := (I.lo : ℝ) ≤ v ∧ v ≤ (I.hi : ℝ)
def QI.Subset (I J : QI) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

def QI.pt (q : ℚ) : QI := ⟨q,q⟩
def QI.plus (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩
def QI.minus (I : QI) : QI := ⟨-I.hi,-I.lo⟩
def QI.times (I J : QI) : QI :=
  ⟨min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi)),
   max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))⟩

def QBox := Fin 4 → QI
def MemBox (B : QBox) (v : Vec) : Prop := ∀ i, (B i).Mem (v i)

theorem QI.mem_subset {I J : QI} {v : ℝ} (h : I.Subset J) (hv : I.Mem v) : J.Mem v := by
  rcases h with ⟨hl,hu⟩
  have hl' : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hl
  have hu' : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hu
  exact ⟨hl'.trans hv.1, hv.2.trans hu'⟩

theorem QI.mem_plus {I J : QI} {v w : ℝ} (hv : I.Mem v) (hw : J.Mem w) :
    (I.plus J).Mem (v+w) := by
  simpa [QI.Mem, QI.plus] using And.intro (add_le_add hv.1 hw.1) (add_le_add hv.2 hw.2)

theorem QI.mem_minus {I : QI} {v : ℝ} (hv : I.Mem v) : (I.minus).Mem (-v) := by
  simpa [QI.Mem, QI.minus] using And.intro (neg_le_neg hv.2) (neg_le_neg hv.1)

/-- Four-corner product theorem. No endpoint sign or positive-width assumptions. -/
theorem mul_corner_bounds {al au bl bu x y l u : ℝ}
    (hx : al ≤ x ∧ x ≤ au) (hy : bl ≤ y ∧ y ≤ bu)
    (hl : l ≤ al*bl ∧ l ≤ al*bu ∧ l ≤ au*bl ∧ l ≤ au*bu)
    (hu : al*bl ≤ u ∧ al*bu ≤ u ∧ au*bl ≤ u ∧ au*bu ≤ u) :
    l ≤ x*y ∧ x*y ≤ u := by
  have low (a : ℝ) (h₁ : l ≤ a*bl) (h₂ : l ≤ a*bu) : l ≤ a*y := by
    by_cases h : 0 ≤ a
    · exact h₁.trans (mul_le_mul_of_nonneg_left hy.1 h)
    · exact h₂.trans (mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge h))
  have high (a : ℝ) (h₁ : a*bl ≤ u) (h₂ : a*bu ≤ u) : a*y ≤ u := by
    by_cases h : 0 ≤ a
    · exact (mul_le_mul_of_nonneg_left hy.2 h).trans h₂
    · exact (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge h)).trans h₁
  constructor
  · by_cases h : 0 ≤ y
    · exact (low al hl.1 hl.2.1).trans (mul_le_mul_of_nonneg_right hx.1 h)
    · exact (low au hl.2.2.1 hl.2.2.2).trans
        (mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge h))
  · by_cases h : 0 ≤ y
    · exact (mul_le_mul_of_nonneg_right hx.2 h).trans (high au hu.2.2.1 hu.2.2.2)
    · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge h)).trans (high al hu.1 hu.2.1)

theorem QI.mem_times {I J : QI} {v w : ℝ} (hv : I.Mem v) (hw : J.Mem w) :
    (I.times J).Mem (v*w) := by
  apply mul_corner_bounds hv hw
  · have h₁ : (I.times J).lo ≤ I.lo*J.lo := (min_le_left _ _).trans (min_le_left _ _)
    have h₂ : (I.times J).lo ≤ I.lo*J.hi := (min_le_left _ _).trans (min_le_right _ _)
    have h₃ : (I.times J).lo ≤ I.hi*J.lo := (min_le_right _ _).trans (min_le_left _ _)
    have h₄ : (I.times J).lo ≤ I.hi*J.hi := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂,
      by exact_mod_cast h₃, by exact_mod_cast h₄⟩
  · have h₁ : I.lo*J.lo ≤ (I.times J).hi := (le_max_left _ _).trans (le_max_left _ _)
    have h₂ : I.lo*J.hi ≤ (I.times J).hi := (le_max_right _ _).trans (le_max_left _ _)
    have h₃ : I.hi*J.lo ≤ (I.times J).hi := (le_max_left _ _).trans (le_max_right _ _)
    have h₄ : I.hi*J.hi ≤ (I.times J).hi := (le_max_right _ _).trans (le_max_right _ _)
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂,
      by exact_mod_cast h₃, by exact_mod_cast h₄⟩

theorem QI.abs_le_of_mem {I : QI} {v : ℝ} (h : I.Mem v) :
    |v| ≤ (max |I.lo| |I.hi| : ℚ) := by
  have hl : -(max |I.lo| |I.hi| : ℚ) ≤ I.lo := by
    have h₁ := neg_abs_le I.lo
    have h₂ := le_max_left |I.lo| |I.hi|
    linarith
  have hu : I.hi ≤ (max |I.lo| |I.hi| : ℚ) :=
    (le_abs_self _).trans (le_max_right _ _)
  have hlR : -((max |I.lo| |I.hi| : ℚ) : ℝ) ≤ (I.lo : ℝ) := by
    exact_mod_cast hl
  have huR : (I.hi : ℝ) ≤ ((max |I.lo| |I.hi| : ℚ) : ℝ) := by
    exact_mod_cast hu
  exact abs_le.mpr ⟨hlR.trans h.1,h.2.trans huR⟩


/-- Value bounds and all two-point single-coordinate secants. In particular this
bounds all genuine partial derivatives by putting the two endpoints equal. -/
structure JetSound (B : QBox) (e : Expr) (V : QI) (D : Fin 4 → QI) : Prop where
  value : ∀ x, MemBox B x → V.Mem (e.eval x)
  slope : ∀ i x y, MemBox B x → MemBox B y → (D i).Mem (e.secant i x y)

def ValueSound (B : QBox) (e : Expr) (V : QI) : Prop :=
  ∀ x, MemBox B x → V.Mem (e.eval x)

theorem rat_jet (B : QBox) (q : ℚ) :
    JetSound B (.rat q) (QI.pt q) (fun _ => QI.pt 0) := by
  constructor <;> intros <;> simp [QI.Mem, QI.pt, Expr.eval, Expr.secant]

theorem var_jet (B : QBox) (j : Fin 4) :
    JetSound B (.var j) (B j) (fun i => QI.pt (if j=i then 1 else 0)) := by
  constructor
  · intro x hx; exact hx j
  · intro i x y hx hy; by_cases h : j=i <;> simp [QI.Mem,QI.pt,Expr.secant,h]

theorem add_jet {B : QBox} {a b : Expr} {Va Vb V : QI} {Da Db D : Fin 4 → QI}
    (ha : JetSound B a Va Da) (hb : JetSound B b Vb Db)
    (hv : (Va.plus Vb).Subset V)
    (hd : ∀ i, ((Da i).plus (Db i)).Subset (D i)) : JetSound B (.add a b) V D := by
  constructor
  · intro x hx; exact QI.mem_subset hv (QI.mem_plus (ha.value x hx) (hb.value x hx))
  · intro i x y hx hy
    exact QI.mem_subset (hd i) (QI.mem_plus (ha.slope i x y hx hy) (hb.slope i x y hx hy))

theorem neg_jet {B : QBox} {a : Expr} {Va V : QI} {Da D : Fin 4 → QI}
    (ha : JetSound B a Va Da) (hv : Va.minus.Subset V)
    (hd : ∀ i, (Da i).minus.Subset (D i)) : JetSound B (.neg a) V D := by
  constructor
  · intro x hx; exact QI.mem_subset hv (QI.mem_minus (ha.value x hx))
  · intro i x y hx hy; exact QI.mem_subset (hd i) (QI.mem_minus (ha.slope i x y hx hy))

theorem mul_jet {B : QBox} {a b : Expr} {Va Vb V : QI} {Da Db D : Fin 4 → QI}
    (ha : JetSound B a Va Da) (hb : JetSound B b Vb Db)
    (hv : (Va.times Vb).Subset V)
    (hd : ∀ i, (((Da i).times Vb).plus (Va.times (Db i))).Subset (D i)) :
    JetSound B (.mul a b) V D := by
  constructor
  · intro x hx; exact QI.mem_subset hv (QI.mem_times (ha.value x hx) (hb.value x hx))
  · intro i x y hx hy
    exact QI.mem_subset (hd i) (QI.mem_plus
      (QI.mem_times (ha.slope i x y hx hy) (hb.value y hy))
      (QI.mem_times (ha.value x hx) (hb.slope i x y hx hy)))

theorem rat_value (B : QBox) (q : ℚ) : ValueSound B (.rat q) (QI.pt q) :=
  (rat_jet B q).value

theorem var_value (B : QBox) (j : Fin 4) : ValueSound B (.var j) (B j) :=
  (var_jet B j).value

theorem add_value {B : QBox} {a b : Expr} {A Bv V : QI}
    (ha : ValueSound B a A) (hb : ValueSound B b Bv) (h : (A.plus Bv).Subset V) :
    ValueSound B (.add a b) V := by
  intro x hx; exact QI.mem_subset h (QI.mem_plus (ha x hx) (hb x hx))

theorem neg_value {B : QBox} {a : Expr} {A V : QI}
    (ha : ValueSound B a A) (h : A.minus.Subset V) : ValueSound B (.neg a) V := by
  intro x hx; exact QI.mem_subset h (QI.mem_minus (ha x hx))

theorem mul_value {B : QBox} {a b : Expr} {A Bv V : QI}
    (ha : ValueSound B a A) (hb : ValueSound B b Bv) (h : (A.times Bv).Subset V) :
    ValueSound B (.mul a b) V := by
  intro x hx; exact QI.mem_subset h (QI.mem_times (ha x hx) (hb x hx))

end
end Rho5.Algebraic.CriticalExistence
