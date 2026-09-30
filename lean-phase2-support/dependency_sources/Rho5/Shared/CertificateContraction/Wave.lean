import Rho5.Shared.CertificateContraction.Runtime
import Mathlib.Data.Rat.Floor

namespace Rho5.Shared.CertificateContraction

/-- A precise inclusion contract also permits another exact outward format. -/
structure Outward where
  down : ℚ → ℚ
  up : ℚ → ℚ
  down_le : ∀ q, down q ≤ q
  le_up : ∀ q, q ≤ up q

def exactOutward : Outward := ⟨id, id, fun _ => le_rfl, fun _ => le_rfl⟩

def floorGrid (g : ℕ) (q : ℚ) : ℚ := (⌊q * g⌋ : ℤ) / (g : ℚ)
def ceilGrid (g : ℕ) (q : ℚ) : ℚ := -floorGrid g (-q)

theorem floorGrid_le (g : ℕ) (hg : 0 < g) (q : ℚ) : floorGrid g q ≤ q := by
  unfold floorGrid
  exact (div_le_iff₀ (by exact_mod_cast hg : (0 : ℚ) < g)).2 (Int.floor_le _)

theorem le_ceilGrid (g : ℕ) (hg : 0 < g) (q : ℚ) : q ≤ ceilGrid g q := by
  have h := floorGrid_le g hg (-q)
  dsimp [ceilGrid]
  linarith

/-- Matches Fraction((q*GRID).numerator // (q*GRID).denominator, GRID).
Int division here is Euclidean division, including negative numerators. -/
theorem floorGrid_num_den (g : ℕ) (q : ℚ) :
    floorGrid g q = (((q * g).num / (q * g).den : ℤ) : ℚ) / g := by
  simp only [floorGrid, Rat.floor_def']

def gridOutward (g : ℕ) (hg : 0 < g) : Outward :=
  ⟨floorGrid g, ceilGrid g, floorGrid_le g hg, le_ceilGrid g hg⟩

/-- Frozen graph_contract.py uses GRID = 2**36. -/
def runtimeOutward : Outward := gridOutward (2 ^ 36) (by norm_num)

def meetBound {n m : ℕ} (round : Outward) (b : Box n)
    (r : BoundRecord n m) (v : ℚ) : Box n where
  lo := fun i => if i = r.coordinate ∧ r.direction = .lower then
    max (b.lo i) (round.down (-v)) else b.lo i
  hi := fun i => if i = r.coordinate ∧ r.direction = .upper then
    min (b.hi i) (round.up v) else b.hi i

theorem meetBound_preserves {n m : ℕ} (round : Outward) (b : Box n)
    (r : BoundRecord n m) (v : ℚ) (z : Fin n → ℝ) (hb : b.Contains z)
    (hv : (r.direction.sign : ℝ) * z r.coordinate ≤ (v : ℝ)) :
    (meetBound round b r v).Contains z := by
  intro i
  constructor
  · dsimp [meetBound]
    split_ifs with h
    · obtain ⟨rfl, hd⟩ := h
      have hv' : -(v : ℝ) ≤ z r.coordinate := by
        simp [hd, Direction.sign] at hv
        linarith
      have hdown : (round.down (-v) : ℝ) ≤ -(v : ℝ) := by
        exact_mod_cast round.down_le (-v)
      push_cast
      exact max_le (hb _).1 (hdown.trans hv')
    · exact (hb i).1
  · dsimp [meetBound]
    split_ifs with h
    · obtain ⟨rfl, hd⟩ := h
      have hv' : z r.coordinate ≤ (v : ℝ) := by
        simpa [hd, Direction.sign] using hv
      have hup : (v : ℝ) ≤ (round.up v : ℝ) := by exact_mod_cast round.le_up v
      push_cast
      exact le_min (hb _).2 (hv'.trans hup)
    · exact (hb i).2

theorem meetBound_subset {n m : ℕ} (round : Outward) (b : Box n)
    (r : BoundRecord n m) (v : ℚ) (z : Fin n → ℝ)
    (hz : (meetBound round b r v).Contains z) : b.Contains z := by
  intro i
  have h := hz i
  dsimp [meetBound] at h
  constructor
  · split_ifs at h with hl hu hu <;> push_cast at h <;>
      first | exact h.1 | exact (le_max_left _ _).trans h.1
  · split_ifs at h with hl hu hu <;> push_cast at h <;>
      first | exact h.2 | exact h.2.trans (min_le_left _ _)

/-- The frozen input `old` stays fixed while `current` accumulates intersections.
In particular, no value is computed on a partially updated box. -/
def intersectFrozen {n m : ℕ} (round : Outward) (rows : Rows n m) (old : Box n) :
    List (BoundRecord n m) → Box n → Box n
  | [], current => current
  | r :: rs, current =>
      intersectFrozen round rows old rs (meetBound round current r (boundValue rows old r))

def frozenWave {n m : ℕ} (round : Outward) (rows : Rows n m) (old : Box n)
    (wave : List (BoundRecord n m)) : Box n := intersectFrozen round rows old wave old

theorem intersectFrozen_preserves {n m : ℕ} (round : Outward) (rows : Rows n m)
    (old : Box n) (wave : List (BoundRecord n m)) (current : Box n)
    (z : Fin n → ℝ) (hr : rows.Holds z) (ho : old.Contains z) (hc : current.Contains z) :
    (intersectFrozen round rows old wave current).Contains z := by
  induction wave generalizing current with
  | nil => exact hc
  | cons r rs ih =>
    exact ih _ (meetBound_preserves round current r _ z hc
      (coordinate_bound_real rows old r z hr ho))

theorem frozenWave_preserves {n m : ℕ} (round : Outward) (rows : Rows n m)
    (old : Box n) (wave : List (BoundRecord n m)) (z : Fin n → ℝ)
    (hr : rows.Holds z) (ho : old.Contains z) :
    (frozenWave round rows old wave).Contains z :=
  intersectFrozen_preserves round rows old wave old z hr ho ho

theorem box_inconsistent_empty {n : ℕ} (b : Box n)
    (hi : ∃ i, b.hi i < b.lo i) : ¬ ∃ z : Fin n → ℝ, b.Contains z := by
  rintro ⟨z, hz⟩
  obtain ⟨i, hi⟩ := hi
  have hir : (b.hi i : ℝ) < (b.lo i : ℝ) := by exact_mod_cast hi
  exact (not_lt_of_ge ((hz i).1.trans (hz i).2)) hir

theorem frozenWave_inconsistent_empty {n m : ℕ} (round : Outward) (rows : Rows n m)
    (old : Box n) (wave : List (BoundRecord n m))
    (hi : ∃ i, (frozenWave round rows old wave).hi i <
      (frozenWave round rows old wave).lo i) :
    ¬ ∃ z : Fin n → ℝ, rows.Holds z ∧ old.Contains z := by
  rintro ⟨z, hr, ho⟩
  exact box_inconsistent_empty _ hi ⟨z, frozenWave_preserves round rows old wave z hr ho⟩

/-- This is exactly the simultaneous intersection for unrounded bounds. -/
def SatisfiesBound {n m : ℕ} (rows : Rows n m) (old : Box n)
    (r : BoundRecord n m) (z : Fin n → ℝ) : Prop :=
  (r.direction.sign : ℝ) * z r.coordinate ≤ (boundValue rows old r : ℝ)

theorem meetBound_exact_iff {n m : ℕ} (b : Box n) (r : BoundRecord n m)
    (v : ℚ) (z : Fin n → ℝ) :
    (meetBound exactOutward b r v).Contains z ↔
      b.Contains z ∧ (r.direction.sign : ℝ) * z r.coordinate ≤ (v : ℝ) := by
  constructor
  · intro h
    refine ⟨meetBound_subset _ _ _ _ _ h, ?_⟩
    have hi := h r.coordinate
    cases hd : r.direction <;>
      simp [meetBound, hd, Direction.sign, exactOutward] at hi ⊢ <;> linarith [hi.1, hi.2]
  · rintro ⟨hb, hv⟩
    exact meetBound_preserves _ _ _ _ _ hb hv

theorem intersectFrozen_exact_iff {n m : ℕ} (rows : Rows n m) (old : Box n)
    (wave : List (BoundRecord n m)) (current : Box n) (z : Fin n → ℝ) :
    (intersectFrozen exactOutward rows old wave current).Contains z ↔
      current.Contains z ∧ ∀ r ∈ wave, SatisfiesBound rows old r z := by
  induction wave generalizing current with
  | nil => simp [intersectFrozen]
  | cons r rs ih =>
    simp only [intersectFrozen, ih, meetBound_exact_iff, List.mem_cons, forall_eq_or_imp]
    simp only [SatisfiesBound]
    tauto

theorem frozenWave_exact_iff {n m : ℕ} (rows : Rows n m) (old : Box n)
    (wave : List (BoundRecord n m)) (z : Fin n → ℝ) :
    (frozenWave exactOutward rows old wave).Contains z ↔
      old.Contains z ∧ ∀ r ∈ wave, SatisfiesBound rows old r z :=
  intersectFrozen_exact_iff rows old wave old z

end Rho5.Shared.CertificateContraction
