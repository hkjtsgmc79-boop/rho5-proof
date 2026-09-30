import Rho5.Shared.CertificateContraction.Coordinate

namespace Rho5.Shared.CertificateContraction

/-- Already structurally decoded integers. JSON keys, array shape, exact number
decoding, and Python's rejection of booleans are serialization obligations. -/
structure RawRecord where
  coordinate : ℤ
  direction : ℤ
  objectiveWeight : ℤ
  weights : List (ℤ × ℤ)
  deriving DecidableEq, Repr

def RawRecord.Valid (n m : ℕ) (r : RawRecord) : Prop :=
  (0 ≤ r.coordinate ∧ r.coordinate < n ∧ r.coordinate < 24) ∧
  (r.direction = 1 ∨ r.direction = -1) ∧
  0 < r.objectiveWeight ∧
  r.weights ≠ [] ∧
  (r.weights.map Prod.fst).Nodup ∧
  ∀ p ∈ r.weights, 0 ≤ p.1 ∧ p.1 < m ∧ 0 < p.2

instance (n m : ℕ) (r : RawRecord) : Decidable (r.Valid n m) := by
  unfold RawRecord.Valid
  infer_instance

def RawRecord.check (n m : ℕ) (r : RawRecord) : Bool := decide (r.Valid n m)

theorem RawRecord.check_iff (n m : ℕ) (r : RawRecord) :
    r.check n m = true ↔ r.Valid n m := by simp [RawRecord.check]

/-- Exact sparse-to-dense aggregation. No tolerance, floating point, or removal
of residual coefficients occurs. Under Valid, each selected row occurs once. -/
def RawRecord.denseWeight (r : RawRecord) (j : ℕ) : ℕ :=
  ((r.weights.filter fun p => p.1 = (j : ℤ)).map fun p => p.2.toNat).sum

def RawRecord.toBound {n m : ℕ} (r : RawRecord) (h : r.Valid n m) : BoundRecord n m where
  coordinate := ⟨r.coordinate.toNat, by have := h.1; omega⟩
  direction := if r.direction = 1 then .upper else .lower
  multiplier := r.objectiveWeight.toNat
  multiplier_pos := by have := h.2.2.1; omega
  weight := fun j => r.denseWeight j.val

theorem RawRecord.toBound_original {n m : ℕ} (r : RawRecord) (h : r.Valid n m) :
    (r.toBound h).coordinate.val < 24 := by
  have := h.1
  change r.coordinate.toNat < 24
  omega

theorem RawRecord.toBound_sign {n m : ℕ} (r : RawRecord) (h : r.Valid n m) :
    (r.toBound h).direction.sign = (r.direction : ℚ) := by
  rcases h.2.1 with hd | hd <;> simp [RawRecord.toBound, hd, Direction.sign]

theorem RawRecord.toBound_multiplier {n m : ℕ} (r : RawRecord) (h : r.Valid n m) :
    ((r.toBound h).multiplier : ℤ) = r.objectiveWeight := by
  have := h.2.2.1
  change (r.objectiveWeight.toNat : ℤ) = r.objectiveWeight
  omega

def RawRecord.decode (n m : ℕ) (r : RawRecord) : Option (BoundRecord n m) :=
  if h : r.Valid n m then some (r.toBound h) else none

theorem RawRecord.decode_spec {n m : ℕ} (raw : RawRecord) (r : BoundRecord n m)
    (hd : raw.decode n m = some r) : ∃ h : raw.Valid n m, r = raw.toBound h := by
  unfold RawRecord.decode at hd
  split at hd
  · rename_i h
    exact ⟨h, (Option.some.inj hd).symm⟩
  · contradiction

theorem RawRecord.decode_none_iff (n m : ℕ) (r : RawRecord) :
    r.decode n m = none ↔ ¬ r.Valid n m := by
  unfold RawRecord.decode
  split <;> simp_all

theorem RawRecord.decode_sound {n m : ℕ} (raw : RawRecord) (r : BoundRecord n m)
    (hd : raw.decode n m = some r) :
    raw.Valid n m ∧ r.coordinate.val < 24 ∧ r.direction.sign = (raw.direction : ℚ) := by
  unfold RawRecord.decode at hd
  split at hd
  · rename_i h
    cases Option.some.inj hd
    exact ⟨h, raw.toBound_original h, raw.toBound_sign h⟩
  · contradiction

theorem decoded_bound_real {n m : ℕ} (rows : Rows n m) (b : Box n)
    (raw : RawRecord) (r : BoundRecord n m) (hd : raw.decode n m = some r)
    (z : Fin n → ℝ) (hr : rows.Holds z) (hb : b.Contains z) :
    r.coordinate.val < 24 ∧
      (raw.direction : ℝ) * z r.coordinate ≤ (boundValue rows b r : ℝ) := by
  obtain ⟨_, hi, hs⟩ := raw.decode_sound r hd
  refine ⟨hi, ?_⟩
  have hc := coordinate_bound_real rows b r z hr hb
  rw [hs] at hc
  simpa using hc

def checkWave (n m : ℕ) (wave : List RawRecord) : Bool :=
  decide (1 ≤ wave.length ∧ wave.length ≤ 48) && wave.all (RawRecord.check n m)

theorem checkWave_iff (n m : ℕ) (wave : List RawRecord) :
    checkWave n m wave = true ↔
      1 ≤ wave.length ∧ wave.length ≤ 48 ∧ ∀ r ∈ wave, r.Valid n m := by
  simp [checkWave, RawRecord.check, and_assoc]

end Rho5.Shared.CertificateContraction
