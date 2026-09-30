import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact rational coordinate certificates, interpreted at arbitrary real points.
No property of a JSON parser or of the source-row generator is assumed implicitly. -/
namespace Rho5.Shared.CertificateContraction
open scoped BigOperators

structure Box (n : ℕ) where
  lo : Fin n → ℚ
  hi : Fin n → ℚ

def Box.Contains {n : ℕ} (b : Box n) (z : Fin n → ℝ) : Prop :=
  ∀ i, (b.lo i : ℝ) ≤ z i ∧ z i ≤ (b.hi i : ℝ)

structure Rows (n m : ℕ) where
  a : Fin m → Fin n → ℚ
  rhs : Fin m → ℚ

def Rows.Holds {n m : ℕ} (rows : Rows n m) (z : Fin n → ℝ) : Prop :=
  ∀ j, ∑ h, (rows.a j h : ℝ) * z h ≤ (rows.rhs j : ℝ)

inductive Direction where
  | upper
  | lower
  deriving DecidableEq, Repr

def Direction.sign : Direction → ℚ
  | .upper => 1
  | .lower => -1

/-- A generic mathematical record: zero weights encode absent rows. The stricter
runtime adapter also checks nonempty, unique, positive sparse support. -/
structure BoundRecord (n m : ℕ) where
  coordinate : Fin n
  direction : Direction
  multiplier : ℕ
  multiplier_pos : 0 < multiplier
  weight : Fin m → ℕ

def residual {n m : ℕ} (rows : Rows n m) (r : BoundRecord n m) (h : Fin n) : ℚ :=
  (∑ j, (r.weight j : ℚ) * rows.a j h) -
    if h = r.coordinate then (r.multiplier : ℚ) * r.direction.sign else 0

def weightedRhs {n m : ℕ} (rows : Rows n m) (r : BoundRecord n m) : ℚ :=
  ∑ j, (r.weight j : ℚ) * rows.rhs j

def residualLower {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) : ℚ :=
  ∑ h, min (residual rows r h * b.lo h) (residual rows r h * b.hi h)

def boundValue {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) : ℚ :=
  (weightedRhs rows r - residualLower rows b r) / r.multiplier

theorem min_endpoint_le {c l u x : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    min (c * l) (c * u) ≤ c * x := by
  by_cases hc : 0 ≤ c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hu (le_of_not_ge hc))

theorem residualLower_le {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) (z : Fin n → ℝ) (hb : b.Contains z) :
    (residualLower rows b r : ℝ) ≤ ∑ h, (residual rows r h : ℝ) * z h := by
  unfold residualLower
  push_cast
  exact Finset.sum_le_sum fun i _ => min_endpoint_le (hb i).1 (hb i).2

theorem residual_identity {n m : ℕ} (rows : Rows n m)
    (r : BoundRecord n m) (z : Fin n → ℝ) :
    (∑ h, (residual rows r h : ℝ) * z h) =
      (∑ j, (r.weight j : ℝ) * ∑ h, (rows.a j h : ℝ) * z h) -
        (r.multiplier : ℝ) * (r.direction.sign : ℝ) * z r.coordinate := by
  unfold residual
  push_cast
  simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum, mul_assoc, apply_ite, ite_mul]

/-- The primary theorem: all residual coefficients remain exact, and the witness
is an arbitrary real vector, not a rational vector. -/
theorem coordinate_bound_real {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) (z : Fin n → ℝ)
    (hr : rows.Holds z) (hb : b.Contains z) :
    (r.direction.sign : ℝ) * z r.coordinate ≤ (boundValue rows b r : ℝ) := by
  have hw : (∑ j, (r.weight j : ℝ) * ∑ h, (rows.a j h : ℝ) * z h) ≤
      (weightedRhs rows r : ℝ) := by
    unfold weightedRhs
    push_cast
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr j) (by positivity)
  have hlow := residualLower_le rows b r z hb
  rw [residual_identity] at hlow
  have ht : (0 : ℝ) < r.multiplier := by exact_mod_cast r.multiplier_pos
  unfold boundValue
  push_cast
  apply (le_div_iff₀ ht).2
  nlinarith only [hw, hlow]

theorem upper_bound_real {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) (z : Fin n → ℝ) (hr : rows.Holds z) (hb : b.Contains z)
    (hd : r.direction = .upper) : z r.coordinate ≤ (boundValue rows b r : ℝ) := by
  simpa [hd, Direction.sign] using coordinate_bound_real rows b r z hr hb

theorem lower_bound_real {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) (z : Fin n → ℝ) (hr : rows.Holds z) (hb : b.Contains z)
    (hd : r.direction = .lower) : -(boundValue rows b r : ℝ) ≤ z r.coordinate := by
  have h := coordinate_bound_real rows b r z hr hb
  simp [hd, Direction.sign] at h
  linarith

/-- The dense sign-selection expression used by the independent runtime cross-check. -/
def denseResidualLower {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) : ℚ :=
  ∑ h, residual rows r h * (if 0 ≤ residual rows r h then b.lo h else b.hi h)

theorem denseResidualLower_eq {n m : ℕ} (rows : Rows n m) (b : Box n)
    (r : BoundRecord n m) (hb : ∀ i, b.lo i ≤ b.hi i) :
    denseResidualLower rows b r = residualLower rows b r := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp
  split_ifs with hc
  · rw [min_eq_left (mul_le_mul_of_nonneg_left (hb i) hc)]
  · rw [min_eq_right (mul_le_mul_of_nonpos_left (hb i) (le_of_not_ge hc))]

end Rho5.Shared.CertificateContraction
