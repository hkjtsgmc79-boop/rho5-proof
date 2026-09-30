import Rho5.Shared.CertificateContraction.Wave

namespace Rho5.Shared.CertificateContraction

def Enclosure (n : ℕ) := Option (Box n)

def Enclosure.Contains {n : ℕ} (e : Enclosure n) (z : Fin n → ℝ) : Prop :=
  match e with
  | none => False
  | some b => b.Contains z

def Box.consistent {n : ℕ} (b : Box n) : Bool := decide (∀ i, b.lo i ≤ b.hi i)

theorem Box.consistent_of_contains {n : ℕ} (b : Box n) (z : Fin n → ℝ)
    (h : b.Contains z) : b.consistent = true := by
  simp only [Box.consistent, decide_eq_true_eq]
  intro i
  have hi := (h i).1.trans (h i).2
  exact_mod_cast hi

/-- `none` represents EMPTY. All record values are evaluated using the same old
rows/box. Propagation and rebuilding after this intersection are separate. -/
def checkedFrozenWave {n m : ℕ} (round : Outward) (rows : Rows n m)
    (old : Box n) (wave : List (BoundRecord n m)) : Enclosure n :=
  let b := frozenWave round rows old wave
  if b.consistent then some b else none

theorem checkedFrozenWave_preserves {n m : ℕ} (round : Outward) (rows : Rows n m)
    (old : Box n) (wave : List (BoundRecord n m)) (z : Fin n → ℝ)
    (hr : rows.Holds z) (ho : old.Contains z) :
    (checkedFrozenWave round rows old wave).Contains z := by
  have h := frozenWave_preserves round rows old wave z hr ho
  have hc := Box.consistent_of_contains _ z h
  simpa [checkedFrozenWave, hc, Enclosure.Contains] using h

/-- The explicit soundness input required from common_contract or any other
postprocessor. A single source point z is retained, even if the result is EMPTY. -/
def PreservesOn {n : ℕ} (P : (Fin n → ℝ) → Prop)
    (f : Box n → Enclosure n) : Prop :=
  ∀ z, P z → ∀ b, b.Contains z → (f b).Contains z

/-- A row generator may depend on the newly contracted box. Its correctness for
the SAME real source point must be supplied separately for every input box. -/
def SourceRowsOn {n m : ℕ} (P : (Fin n → ℝ) → Prop)
    (makeRows : Box n → Rows n m) : Prop :=
  ∀ z, P z → ∀ b, b.Contains z → (makeRows b).Holds z

def Enclosure.andThen {n : ℕ} (e : Enclosure n) (f : Box n → Enclosure n) : Enclosure n :=
  match e with
  | none => none
  | some b => f b

theorem Enclosure.andThen_preserves {n : ℕ} (P : (Fin n → ℝ) → Prop)
    (f : Box n → Enclosure n) (hf : PreservesOn P f)
    (e : Enclosure n) (z : Fin n → ℝ) (hp : P z) (he : e.Contains z) :
    (e.andThen f).Contains z := by
  cases e with
  | none => exact False.elim he
  | some b => exact hf z hp b he

/-- Scope of apply_wave: the dual intersection is proved here; the row generator
and common_contract have explicit point-preservation premises. -/
def applyWave {n m : ℕ} (round : Outward) (makeRows : Box n → Rows n m)
    (records : Box n → List (BoundRecord n m)) (post : Box n → Enclosure n)
    (old : Box n) : Enclosure n :=
  (checkedFrozenWave round (makeRows old) old (records old)).andThen post

theorem applyWave_preserves {n m : ℕ} (P : (Fin n → ℝ) → Prop)
    (round : Outward) (makeRows : Box n → Rows n m)
    (records : Box n → List (BoundRecord n m)) (post : Box n → Enclosure n)
    (hrows : SourceRowsOn P makeRows) (hpost : PreservesOn P post) :
    PreservesOn P (applyWave round makeRows records post) := by
  intro z hp old ho
  exact Enclosure.andThen_preserves P post hpost _ z hp
    (checkedFrozenWave_preserves round (makeRows old) old (records old) z
      (hrows z hp old ho) ho)

def runSteps {n : ℕ} : List (Box n → Enclosure n) → Enclosure n → Enclosure n
  | [], e => e
  | f :: fs, e => runSteps fs (e.andThen f)

/-- Arbitrarily many finite waves; also allows different row counts in different
steps. The witness z is unchanged throughout the proof. -/
theorem finite_composition_preserves {n : ℕ} (P : (Fin n → ℝ) → Prop)
    (steps : List (Box n → Enclosure n))
    (hs : ∀ f ∈ steps, PreservesOn P f)
    (e : Enclosure n) (z : Fin n → ℝ) (hp : P z) (he : e.Contains z) :
    (runSteps steps e).Contains z := by
  induction steps generalizing e with
  | nil => exact he
  | cons f fs ih =>
    apply ih (fun g hg => hs g (by simp [hg]))
    exact Enclosure.andThen_preserves P f (hs f (by simp)) e z hp he

theorem finite_composition_empty {n : ℕ} (P : (Fin n → ℝ) → Prop)
    (steps : List (Box n → Enclosure n))
    (hs : ∀ f ∈ steps, PreservesOn P f) (e : Enclosure n)
    (hempty : runSteps steps e = none) :
    ¬ ∃ z : Fin n → ℝ, P z ∧ e.Contains z := by
  rintro ⟨z, hp, he⟩
  have h := finite_composition_preserves P steps hs e z hp he
  simp [hempty, Enclosure.Contains] at h

end Rho5.Shared.CertificateContraction
