import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Order
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
Small, explicitly finite extrema and convex interpolation.  No compactness or
choice is needed for any of the constructions below.
-/
namespace Rho5.ExternalBFibreCapacity

noncomputable section

/-- Minimum of exactly three entries, with all ties retained. -/
def min3 (f : Fin 3 → ℝ) : ℝ := min (f 0) (min (f 1) (f 2))
def max3 (f : Fin 3 → ℝ) : ℝ := max (f 0) (max (f 1) (f 2))
def min4 (f : Fin 4 → ℝ) : ℝ := min (f 0) (min (f 1) (min (f 2) (f 3)))
def max4 (f : Fin 4 → ℝ) : ℝ := max (f 0) (max (f 1) (max (f 2) (f 3)))

theorem le_min3_iff (a : ℝ) (f : Fin 3 → ℝ) :
    a ≤ min3 f ↔ ∀ i, a ≤ f i := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [min3, le_min_iff]
  · intro h
    exact le_min (h 0) (le_min (h 1) (h 2))

theorem max3_le_iff (f : Fin 3 → ℝ) (a : ℝ) :
    max3 f ≤ a ↔ ∀ i, f i ≤ a := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [max3, max_le_iff]
  · intro h
    exact max_le (h 0) (max_le (h 1) (h 2))

theorem min3_le (f : Fin 3 → ℝ) (i : Fin 3) : min3 f ≤ f i :=
  (le_min3_iff _ _).mp le_rfl i

theorem le_max3 (f : Fin 3 → ℝ) (i : Fin 3) : f i ≤ max3 f :=
  (max3_le_iff _ _).mp le_rfl i

theorem le_min4_iff (a : ℝ) (f : Fin 4 → ℝ) :
    a ≤ min4 f ↔ ∀ i, a ≤ f i := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [min4, le_min_iff]
  · intro h
    exact le_min (h 0) (le_min (h 1) (le_min (h 2) (h 3)))

theorem max4_le_iff (f : Fin 4 → ℝ) (a : ℝ) :
    max4 f ≤ a ↔ ∀ i, f i ≤ a := by
  constructor
  · intro h i
    fin_cases i <;> simp_all [max4, max_le_iff]
  · intro h
    exact max_le (h 0) (max_le (h 1) (max_le (h 2) (h 3)))

theorem min4_le (f : Fin 4 → ℝ) (i : Fin 4) : min4 f ≤ f i :=
  (le_min4_iff _ _).mp le_rfl i

theorem le_max4 (f : Fin 4 → ℝ) (i : Fin 4) : f i ≤ max4 f :=
  (max4_le_iff _ _).mp le_rfl i

/-- The arithmetic interpolation used in all three *actual* paths. -/
def mix (a b t : ℝ) : ℝ := (1 - t) * a + t * b

@[simp] theorem mix_zero (a b : ℝ) : mix a b 0 = a := by simp [mix]
@[simp] theorem mix_one (a b : ℝ) : mix a b 1 = b := by simp [mix]
@[simp] theorem mix_self (a t : ℝ) : mix a a t = a := by dsimp [mix]; ring

theorem mix_lower {a b l t : ℝ} (ha : l ≤ a) (hb : l ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : l ≤ mix a b t := by
  have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg ht0 (sub_nonneg.mpr hb)
  dsimp [mix]
  nlinarith

theorem mix_upper {a b u t : ℝ} (ha : a ≤ u) (hb : b ≤ u)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : mix a b t ≤ u := by
  have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg ht0 (sub_nonneg.mpr hb)
  dsimp [mix]
  nlinarith

theorem mix_le_mix {a b c d t : ℝ} (hac : a ≤ c) (hbd : b ≤ d)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : mix a b t ≤ mix c d t := by
  have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hac)
  have h₂ := mul_nonneg ht0 (sub_nonneg.mpr hbd)
  dsimp [mix]
  nlinarith

theorem mix_between {a b t : ℝ} (hab : a ≤ b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : a ≤ mix a b t ∧ mix a b t ≤ b :=
  ⟨mix_lower le_rfl hab ht0 ht1, mix_upper hab le_rfl ht0 ht1⟩

theorem mix_mono_parameter {a b t u : ℝ} (hab : a ≤ b) (htu : t ≤ u) :
    mix a b t ≤ mix a b u := by
  have := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr htu)
  dsimp [mix]
  nlinarith

theorem abs_mix_le {a b c t : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ c)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |mix a b t| ≤ c := by
  rcases abs_le.mp ha with ⟨ha0, ha1⟩
  rcases abs_le.mp hb with ⟨hb0, hb1⟩
  exact abs_le.mpr ⟨mix_lower ha0 hb0 ht0 ht1,
    mix_upper ha1 hb1 ht0 ht1⟩

theorem mul_mem_unit {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ a * b ∧ a * b ≤ 1 := by
  refine ⟨mul_nonneg ha0 hb0, ?_⟩
  calc a * b ≤ 1 * 1 := mul_le_mul ha1 hb1 hb0 (by norm_num)
       _ = 1 := by ring

end
end Rho5.ExternalBFibreCapacity
