import Rho5.Shared.BottomRightVariation.Basic
import Mathlib.Tactic.Tauto

/-!
# D55 — feasibility interval of the corner shift, from the actual whole-matrix data

This file answers the card's second and third items for the actual matrix of the B24
lane, with no generic perturbation framework:

* given the normalization `matrixEntryMax M = 1`, `M 0 0 = 1`, the four actual leading
  complete-pivot qualifications and `p, k, r > 0`, the varied matrix `shift M h`
  retains normalization **and all four leading complete pivots** exactly when the four
  actual entry constraints hold (`shift_qualifications_iff`);
* with the explicit nested `max`/`min` conventions `L` and `U`, those four constraints
  are exactly `L M ≤ h ≤ U M` (`feasible_iff_interval`);
* the original qualifications give `L M ≤ 0 ≤ U M` (`L_le_zero_le_U`), so `h = L M` is
  feasible (`feasible_L`);
* at `h = L M` the boundary is a genuine four-way disjunction: *some* one of the four
  lower bounds is attained (`boundary_at_L`) — not only the tail one.

Every hypothesis is an explicit whole-matrix datum: the varied matrix is not treated as
an isolated tail, and nothing is assumed about rank, balance or existence.
-/

namespace Rho5.BottomRightVariation

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.MatrixNormalization (abs_entry_le_matrixEntryMax)
open Rho5.Pivot (IsCompletePivot)

/-! ## 1. The four actual entry constraints and the interval `[L, U]` -/

/-- **The card's four entry constraints**, read on the actual D37 quantities. -/
def Feasible (M : Matrix5) (h : ℝ) : Prop :=
  |M 4 4 + h| ≤ 1 ∧ |S4 M 3 3 + h| ≤ p M ∧ |S3 M 2 2 + h| ≤ k M ∧ |d M + h| ≤ r M

/-- **Lower endpoint**, with the explicit nested-max convention: the maximum of the four
lower bounds `-1 - M 4 4`, `-p M - S4 M 3 3`, `-k M - S3 M 2 2`, `-r M - d M`. -/
noncomputable def L (M : Matrix5) : ℝ :=
  max (max (max (-1 - M 4 4) (-p M - S4 M 3 3)) (-k M - S3 M 2 2)) (-r M - d M)

/-- **Upper endpoint**, with the explicit nested-min convention: the minimum of the four
upper bounds `1 - M 4 4`, `p M - S4 M 3 3`, `k M - S3 M 2 2`, `r M - d M`. -/
noncomputable def U (M : Matrix5) : ℝ :=
  min (min (min (1 - M 4 4) (p M - S4 M 3 3)) (k M - S3 M 2 2)) (r M - d M)

theorem L_eq (M : Matrix5) :
    L M = max (max (max (-1 - M 4 4) (-p M - S4 M 3 3)) (-k M - S3 M 2 2)) (-r M - d M) :=
  rfl

theorem U_eq (M : Matrix5) :
    U M = min (min (min (1 - M 4 4) (p M - S4 M 3 3)) (k M - S3 M 2 2)) (r M - d M) :=
  rfl

/-- **Item 3 (interval form).**  The four actual entry constraints hold exactly on
`[L M, U M]`. -/
theorem feasible_iff_interval (M : Matrix5) (h : ℝ) :
    Feasible M h ↔ L M ≤ h ∧ h ≤ U M := by
  have e1 : (|M 4 4 + h| ≤ 1) ↔ (-1 - M 4 4 ≤ h ∧ h ≤ 1 - M 4 4) := by
    rw [abs_le]
    constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
  have e2 : (|S4 M 3 3 + h| ≤ p M) ↔ (-p M - S4 M 3 3 ≤ h ∧ h ≤ p M - S4 M 3 3) := by
    rw [abs_le]
    constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
  have e3 : (|S3 M 2 2 + h| ≤ k M) ↔ (-k M - S3 M 2 2 ≤ h ∧ h ≤ k M - S3 M 2 2) := by
    rw [abs_le]
    constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
  have e4 : (|d M + h| ≤ r M) ↔ (-r M - d M ≤ h ∧ h ≤ r M - d M) := by
    rw [abs_le]
    constructor <;> intro ⟨a, b⟩ <;> constructor <;> linarith
  rw [Feasible, e1, e2, e3, e4, L, U]
  simp only [max_le_iff, le_min_iff]
  tauto

/-! ## 2. Normalization and the four leading complete pivots after the shift -/

/-- **Item 2 (normalization).**  The varied matrix is normalized exactly when the moved
entry stays in the unit box. -/
theorem matrixEntryMax_shift_iff (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) :
    matrixEntryMax (shift M h) = 1 ↔ |M 4 4 + h| ≤ 1 := by
  constructor
  · intro h1
    have hle := abs_entry_le_matrixEntryMax (shift M h) 4 4
    rw [h1, shift_self] at hle
    exact hle
  · intro h1
    refine le_antisymm ?_ ?_
    · rw [matrixEntryMax]
      refine Finset.sup'_le (s := Finset.univ) Finset.univ_nonempty
        (fun ij : Fin 5 × Fin 5 => |shift M h ij.1 ij.2|) ?_
      rintro ⟨i, j⟩ -
      show |shift M h i j| ≤ 1
      by_cases hij : i = 4 ∧ j = 4
      · rw [hij.1, hij.2, shift_self]
        exact h1
      · rw [shift_of_ne M h hij]
        have hb := abs_entry_le_matrixEntryMax M i j
        rw [hmax] at hb
        exact hb
    · have h00' : shift M h 0 0 = 1 := by
        rw [shift_of_ne_left M h (by decide : (0 : Fin 5) ≠ 4), h00]
      have hle : (1 : ℝ) ≤ |shift M h 0 0| := by rw [h00']; simp
      exact hle.trans (abs_entry_le_matrixEntryMax (shift M h) 0 0)

/-- **Item 2 (first pivot).** -/
theorem isCompletePivot_shift_iff (M : Matrix5) (h : ℝ) (_hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) :
    IsCompletePivot (shift M h) 0 0 ↔ |M 4 4 + h| ≤ 1 := by
  have h00' : shift M h 0 0 = 1 := by
    rw [shift_of_ne_left M h (by decide : (0 : Fin 5) ≠ 4), h00]
  constructor
  · intro h'
    have hpivot := h' 4 4
    rw [shift_self, h00', abs_one] at hpivot
    exact hpivot
  · intro h1 i j
    rw [h00', abs_one]
    by_cases hij : i = 4 ∧ j = 4
    · rw [hij.1, hij.2, shift_self]
      exact h1
    · rw [shift_of_ne M h hij]
      have hb := hcp i j
      rw [h00, abs_one] at hb
      exact hb

/-- **Item 2 (second pivot).** -/
theorem isCompletePivot_S4_shift_iff (M : Matrix5) (h : ℝ)
    (hS4 : IsCompletePivot (S4 M) 0 0) (hp : 0 < p M) :
    IsCompletePivot (S4 (shift M h)) 0 0 ↔ |S4 M 3 3 + h| ≤ p M := by
  have hpiv : S4 (shift M h) 0 0 = p M := by
    rw [S4_shift_00]
    rfl
  have hbase : |p M| = p M := abs_of_pos hp
  constructor
  · intro h'
    have hpivot := h' 3 3
    rw [S4_shift_apply, if_pos ⟨rfl, rfl⟩, hpiv, hbase] at hpivot
    exact hpivot
  · intro h1 i j
    rw [hpiv, hbase, S4_shift_apply]
    by_cases hij : i = 3 ∧ j = 3
    · rw [if_pos hij]
      simpa [hij.1, hij.2] using h1
    · rw [if_neg hij]
      have hb := hS4 i j
      have h00S : S4 M 0 0 = p M := rfl
      rw [h00S, hbase] at hb
      exact hb

/-- **Item 2 (third pivot).** -/
theorem isCompletePivot_S3_shift_iff (M : Matrix5) (h : ℝ)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hk : 0 < k M) :
    IsCompletePivot (S3 (shift M h)) 0 0 ↔ |S3 M 2 2 + h| ≤ k M := by
  have hpiv : S3 (shift M h) 0 0 = k M := by
    rw [S3_shift_00]
    rfl
  have hbase : |k M| = k M := abs_of_pos hk
  constructor
  · intro h'
    have hpivot := h' 2 2
    rw [S3_shift_apply, if_pos ⟨rfl, rfl⟩, hpiv, hbase] at hpivot
    exact hpivot
  · intro h1 i j
    rw [hpiv, hbase, S3_shift_apply]
    by_cases hij : i = 2 ∧ j = 2
    · rw [if_pos hij]
      simpa [hij.1, hij.2] using h1
    · rw [if_neg hij]
      have hb := hS3 i j
      have h00S : S3 M 0 0 = k M := rfl
      rw [h00S, hbase] at hb
      exact hb

/-- **Item 2 (tail pivot).** -/
theorem isCompletePivot_T2_shift_iff (M : Matrix5) (h : ℝ)
    (hT2 : IsCompletePivot (T2 M) 0 0) (hr : 0 < r M) :
    IsCompletePivot (T2 (shift M h)) 0 0 ↔ |d M + h| ≤ r M := by
  have hpiv : T2 (shift M h) 0 0 = r M := by
    rw [T2_shift_00]
    rfl
  have hbase : |r M| = r M := abs_of_pos hr
  constructor
  · intro h'
    have hpivot := h' 1 1
    rw [T2_shift_apply, if_pos ⟨rfl, rfl⟩, hpiv, hbase] at hpivot
    simpa [d] using hpivot
  · intro h1 i j
    rw [hpiv, hbase, T2_shift_apply]
    by_cases hij : i = 1 ∧ j = 1
    · rw [if_pos hij]
      simpa [d, hij.1, hij.2] using h1
    · rw [if_neg hij]
      have hb := hT2 i j
      have h00T : T2 M 0 0 = r M := rfl
      rw [h00T, hbase] at hb
      exact hb

/-- **Item 2 (all four together).**  The varied matrix retains normalization and the four
actual leading complete pivots exactly when the four actual entry constraints hold.
Other entries are unchanged, so their whole-matrix bounds are reused, not re-assumed. -/
theorem shift_qualifications_iff (M : Matrix5) (h : ℝ) (hmax : matrixEntryMax M = 1)
    (h00 : M 0 0 = 1) (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    (matrixEntryMax (shift M h) = 1 ∧ IsCompletePivot (shift M h) 0 0 ∧
        IsCompletePivot (S4 (shift M h)) 0 0 ∧ IsCompletePivot (S3 (shift M h)) 0 0 ∧
        IsCompletePivot (T2 (shift M h)) 0 0) ↔
      Feasible M h := by
  rw [Feasible]
  constructor
  · rintro ⟨h1, _h2, h3, h4, h5⟩
    exact ⟨(matrixEntryMax_shift_iff M h hmax h00).mp h1,
      (isCompletePivot_S4_shift_iff M h hS4 hp).mp h3,
      (isCompletePivot_S3_shift_iff M h hS3 hk).mp h4,
      (isCompletePivot_T2_shift_iff M h hT2 hr).mp h5⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(matrixEntryMax_shift_iff M h hmax h00).mpr h1,
      (isCompletePivot_shift_iff M h hmax h00 hcp).mpr h1,
      (isCompletePivot_S4_shift_iff M h hS4 hp).mpr h2,
      (isCompletePivot_S3_shift_iff M h hS3 hk).mpr h3,
      (isCompletePivot_T2_shift_iff M h hT2 hr).mpr h4⟩

/-! ## 3. The original qualifications put `0` in the interval -/

/-- **Item 3 (the original matrix is feasible at `h = 0`).**  This is where the actual
whole-matrix qualifications are consumed: normalization bounds the corner, and each
leading complete pivot bounds its own last diagonal entry. -/
theorem feasible_zero (M : Matrix5) (hmax : matrixEntryMax M = 1) (_h00 : M 0 0 = 1)
    (_hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) : Feasible M 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := abs_entry_le_matrixEntryMax M 4 4
    rw [hmax] at hb
    simpa using hb
  · have hb := hS4 3 3
    have h00S : S4 M 0 0 = p M := rfl
    rw [h00S, abs_of_pos hp] at hb
    simpa using hb
  · have hb := hS3 2 2
    have h00S : S3 M 0 0 = k M := rfl
    rw [h00S, abs_of_pos hk] at hb
    simpa using hb
  · have hb := hT2 1 1
    have h00T : T2 M 0 0 = r M := rfl
    rw [h00T, abs_of_pos hr] at hb
    simpa [d] using hb

/-- **Item 3 (`L ≤ 0 ≤ U`).** -/
theorem L_le_zero_le_U (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) : L M ≤ 0 ∧ 0 ≤ U M :=
  (feasible_iff_interval M 0).mp (feasible_zero M hmax h00 hcp hS4 hS3 hT2 hp hk hr)

/-- **Item 3 (`h = L` is feasible).**  The left endpoint of the feasible interval is
attained by the actual matrix, with the four actual entry constraints re-derived from
`L ≤ h ≤ U` (not assumed). -/
theorem feasible_L (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) : Feasible M (L M) := by
  obtain ⟨hL0, h0U⟩ := L_le_zero_le_U M hmax h00 hcp hS4 hS3 hT2 hp hk hr
  exact (feasible_iff_interval M (L M)).mpr ⟨le_refl _, le_trans hL0 h0U⟩

/-- The four actual entry constraints at `h = L M`, in expanded form. -/
theorem constraints_at_L (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    |M 4 4 + L M| ≤ 1 ∧ |S4 M 3 3 + L M| ≤ p M ∧ |S3 M 2 2 + L M| ≤ k M ∧
      |d M + L M| ≤ r M :=
  feasible_L M hmax h00 hcp hS4 hS3 hT2 hp hk hr

/-! ## 4. The boundary at `L` is a genuine four-way disjunction -/

/-- Two-element maximum choice, kept here so the boundary proof does not depend on a
particular library lemma name. -/
theorem max_eq_left_or_right (a b : ℝ) : max a b = a ∨ max a b = b := by
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

/-- **Item 3 (boundary disjunction at `L`).**  At the left endpoint at least one of the
four *actual* lower bounds is attained: the shifted `(4,4)` hits `-1`, or the shifted
`S4 3 3` hits `-p`, or the shifted `S3 2 2` hits `-k`, **or** the shifted `d` hits `-r`.
The last alternative is not privileged. -/
theorem boundary_at_L (M : Matrix5) (hmax : matrixEntryMax M = 1) (h00 : M 0 0 = 1)
    (hcp : IsCompletePivot M 0 0) (hS4 : IsCompletePivot (S4 M) 0 0)
    (hS3 : IsCompletePivot (S3 M) 0 0) (hT2 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hr : 0 < r M) :
    M 4 4 + L M = -1 ∨ S4 M 3 3 + L M = -p M ∨ S3 M 2 2 + L M = -k M ∨
      d M + L M = -r M := by
  obtain ⟨c1, c2, c3, c4⟩ := constraints_at_L M hmax h00 hcp hS4 hS3 hT2 hp hk hr
  rw [abs_le] at c1 c2 c3 c4
  have l1 : -1 - M 4 4 ≤ L M := by linarith [c1.1]
  have l2 : -p M - S4 M 3 3 ≤ L M := by linarith [c2.1]
  have l3 : -k M - S3 M 2 2 ≤ L M := by linarith [c3.1]
  have l4 : -r M - d M ≤ L M := by linarith [c4.1]
  by_contra hcon
  have n1 : M 4 4 + L M ≠ -1 := fun he => hcon (Or.inl he)
  have n2 : S4 M 3 3 + L M ≠ -p M := fun he => hcon (Or.inr (Or.inl he))
  have n3 : S3 M 2 2 + L M ≠ -k M := fun he => hcon (Or.inr (Or.inr (Or.inl he)))
  have n4 : d M + L M ≠ -r M := fun he => hcon (Or.inr (Or.inr (Or.inr he)))
  have s1 : -1 - M 4 4 < L M := lt_of_le_of_ne l1 (by intro he; exact n1 (by linarith))
  have s2 : -p M - S4 M 3 3 < L M := lt_of_le_of_ne l2 (by intro he; exact n2 (by linarith))
  have s3 : -k M - S3 M 2 2 < L M := lt_of_le_of_ne l3 (by intro he; exact n3 (by linarith))
  have s4 : -r M - d M < L M := lt_of_le_of_ne l4 (by intro he; exact n4 (by linarith))
  have hs : max (max (max (-1 - M 4 4) (-p M - S4 M 3 3)) (-k M - S3 M 2 2)) (-r M - d M)
      < L M :=
    max_lt (max_lt (max_lt s1 s2) s3) s4
  rw [← L_eq] at hs
  exact absurd hs (lt_irrefl (L M))

end Rho5.BottomRightVariation
