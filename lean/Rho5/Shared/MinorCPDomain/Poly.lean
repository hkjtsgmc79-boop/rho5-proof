import Rho5.Shared.MinorCPDomain.Tail
import Rho5.Shared.PrefixBorderedMinors
import Rho5.Shared.MatrixNormalization

/-!
# D62 stage B — the division-free polynomial CP domain `PolyCP`

Using the actual minors of the two accepted deliveries and nothing else:

* `m2 M i j = det (M.submatrix (e2 i) (e2 j))`, `i j : Fin 4` — 16 ordered `2 × 2`
  minors keeping rows/columns `{0, 1 + i}` (D61 `Rho5.PrefixBorderedMinors`);
* `m3 M i j = det (M.submatrix (e3 i) (e3 j))`, `i j : Fin 3` — 9 ordered `3 × 3`
  minors keeping rows/columns `{0, 1, 2 + i}` (D61);
* `m4 M i j = det (D52.borderedMinor M i j)`, `i j : Fin 2` — the 4 bordered `4 × 4`
  minors deleting row `4 - i` and column `4 - j` (stage A of this lane).

With `A = m2 0 0`, `B = m3 0 0`, `C = m4 0 0` the card's `PolyCP` is the finite
inequality system

`A > 0 ∧ B > 0 ∧ C > 0 ∧ (all 25 |M i j| ≤ 1) ∧ (all 16 |m2 i j| ≤ A) ∧
 (all 9 |m3 i j| ≤ B) ∧ (all 4 |m4 i j| ≤ C)`,

written **only** from the original matrix entries and those determinant expressions: no
`S4`/`S3`/`T2`, no Schur update and no quotient coordinate occurs in the definition.

The main theorem `polyCP_iff_frame` proves, under `M 0 0 = 1`, that `PolyCP M` is
*equivalent* to the actual frame (`matrixEntryMax M = 1`, the four leading complete
pivots on `M`/`S4`/`S3`/`T2`, and `p, k, r > 0`).  In the forward direction the
positivity is *derived*, in the card's order: `p > 0` from `A = p`, then `k > 0` from
`B = p * k`, then `r > 0` from `C = p * k * r`; each cancellation uses that established
positive factor (`le_of_mul_le_mul_left` / `pos_of_mul_pos_right`), never a division and
never an assumed conclusion.
-/

namespace Rho5.MinorCPDomain

open Rho5 (Matrix5 matrixEntryMax)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)
open Rho5.MatrixNormalization (abs_entry_le_matrixEntryMax)
open Rho5.Pivot (IsCompletePivot)

/-! ## 1. The three leading minors `A`, `B`, `C` -/

/-- `A = m2 0 0`, the leading `2 × 2` minor of D61. -/
noncomputable def A (M : Matrix5) : ℝ := Rho5.PrefixBorderedMinors.m2 M 0 0

/-- `B = m3 0 0`, the leading `3 × 3` minor of D61. -/
noncomputable def B (M : Matrix5) : ℝ := Rho5.PrefixBorderedMinors.m3 M 0 0

/-- `C = m4 0 0`, the leading bordered `4 × 4` minor of D52 (stage A). -/
noncomputable def C (M : Matrix5) : ℝ := m4 M 0 0

/-- `A` is the second pivot reading. -/
theorem A_eq (M : Matrix5) (h00 : M 0 0 = 1) : A M = p M :=
  Rho5.PrefixBorderedMinors.m2_zero_zero M h00

/-- `B` is `p * k` (D61's identity; needs the *nonzero* `p`). -/
theorem B_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : p M ≠ 0) : B M = p M * k M :=
  Rho5.PrefixBorderedMinors.m3_zero_zero M h00 hp

/-- `C` is `p * k * r` (stage A's identity). -/
theorem C_eq (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    C M = p M * k M * r M :=
  m4_00_eq M h00 hp hk

/-! ## 2. The polynomial domain -/

/-- **The card's `PolyCP`.**  A pure finite inequality system on the original entries and
the three determinant families `m2` (16), `m3` (9), `m4` (4); no Schur update, no
`S4`/`S3`/`T2`, no quotient coordinate. -/
def PolyCP (M : Matrix5) : Prop :=
  0 < A M ∧ 0 < B M ∧ 0 < C M ∧
    (∀ i j : Fin 5, |M i j| ≤ 1) ∧
    (∀ i j : Fin 4, |Rho5.PrefixBorderedMinors.m2 M i j| ≤ A M) ∧
    (∀ i j : Fin 3, |Rho5.PrefixBorderedMinors.m3 M i j| ≤ B M) ∧
    (∀ i j : Fin 2, |m4 M i j| ≤ C M)

/-- The definition read back as the card's seven-clause list (definitional, no printing
of any large term). -/
theorem polyCP_iff_list (M : Matrix5) :
    PolyCP M ↔
      0 < A M ∧ 0 < B M ∧ 0 < C M ∧
        (∀ i j : Fin 5, |M i j| ≤ 1) ∧
        (∀ i j : Fin 4, |Rho5.PrefixBorderedMinors.m2 M i j| ≤ A M) ∧
        (∀ i j : Fin 3, |Rho5.PrefixBorderedMinors.m3 M i j| ≤ B M) ∧
        (∀ i j : Fin 2, |m4 M i j| ≤ C M) :=
  Iff.rfl

/-! ## 3. Each family of finite inequalities is exactly one actual qualification -/

/-- The 25 entry bounds are exactly the original normalization. -/
theorem matrixEntryMax_eq_one_iff_entries (M : Matrix5) (h00 : M 0 0 = 1) :
    matrixEntryMax M = 1 ↔ ∀ i j : Fin 5, |M i j| ≤ 1 := by
  constructor
  · intro hmax i j
    have h := abs_entry_le_matrixEntryMax M i j
    rwa [hmax] at h
  · intro h
    refine le_antisymm ?_ ?_
    · rw [matrixEntryMax]
      refine Finset.sup'_le (s := Finset.univ) Finset.univ_nonempty
        (fun ij : Fin 5 × Fin 5 => |M ij.1 ij.2|) ?_
      rintro ⟨i, j⟩ -
      exact h i j
    · have h1 : (1 : ℝ) ≤ |M 0 0| := by rw [h00]; simp
      exact h1.trans (abs_entry_le_matrixEntryMax M 0 0)

/-- The 25 entry bounds are also exactly the first leading complete pivot. -/
theorem isCompletePivot_M_iff_entries (M : Matrix5) (h00 : M 0 0 = 1) :
    IsCompletePivot M 0 0 ↔ ∀ i j : Fin 5, |M i j| ≤ 1 := by
  constructor
  · intro hcp i j
    have h := hcp i j
    rwa [h00, abs_one] at h
  · intro h i j
    rw [h00, abs_one]
    exact h i j

/-- The 16 `m2` bounds are exactly the second leading complete pivot (D61: `m2 = S4`
pointwise). -/
theorem isCompletePivot_iff_m2 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) :
    IsCompletePivot (S4 M) 0 0 ↔
      ∀ i j : Fin 4, |Rho5.PrefixBorderedMinors.m2 M i j| ≤ A M := by
  have hA : A M = S4 M 0 0 := by rw [A_eq M h00]; rfl
  have hApos : 0 < A M := by rw [A_eq M h00]; exact hp
  have hbase : |S4 M 0 0| = A M := by rw [← hA]; exact abs_of_pos hApos
  constructor
  · intro hcp i j
    have h := hcp i j
    rw [hbase] at h
    rwa [Rho5.PrefixBorderedMinors.m2_eq_S4 M h00 i j]
  · intro h i j
    have h' := h i j
    rw [Rho5.PrefixBorderedMinors.m2_eq_S4 M h00 i j] at h'
    rw [hbase]
    exact h'

/-- The 9 `m3` bounds are exactly the third leading complete pivot (D61:
`m3 = p * S3` pointwise), the factor `p > 0` being the established one. -/
theorem isCompletePivot_iff_m3 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) :
    IsCompletePivot (S3 M) 0 0 ↔
      ∀ i j : Fin 3, |Rho5.PrefixBorderedMinors.m3 M i j| ≤ B M := by
  have hpne : p M ≠ 0 := ne_of_gt hp
  have hkabs : |S3 M 0 0| = k M := by rw [k]; exact abs_of_pos hk
  have hbase : B M = p M * |S3 M 0 0| := by rw [B_eq M h00 hpne, hkabs]
  constructor
  · intro hcp i j
    have h := hcp i j
    rw [hbase, Rho5.PrefixBorderedMinors.m3_eq_p_mul_S3 M h00 hpne i j, abs_mul,
      abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left h hp.le
  · intro h i j
    have h' := h i j
    rw [hbase, Rho5.PrefixBorderedMinors.m3_eq_p_mul_S3 M h00 hpne i j, abs_mul,
      abs_of_pos hp] at h'
    exact le_of_mul_le_mul_left h' hp

/-- The 4 `m4` bounds are exactly the tail leading complete pivot (stage A). -/
theorem isCompletePivot_iff_m4 (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) (hr : 0 < r M) :
    IsCompletePivot (T2 M) 0 0 ↔ ∀ i j : Fin 2, |m4 M i j| ≤ C M :=
  tail_cp_iff_minors M h00 hp hk hr

/-! ## 4. Positivity derived, in the card's order -/

/-- `p > 0` from `A > 0`. -/
theorem p_pos_of_A (M : Matrix5) (h00 : M 0 0 = 1) (hA : 0 < A M) : 0 < p M := by
  rwa [A_eq M h00] at hA

/-- `k > 0` from `B = p * k > 0` and the established `p > 0`. -/
theorem k_pos_of_B (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hB : 0 < B M) :
    0 < k M := by
  have hB' : 0 < p M * k M := by rwa [B_eq M h00 (ne_of_gt hp)] at hB
  exact pos_of_mul_pos_right hB' hp.le

/-- `r > 0` from `C = p * k * r > 0` and the established `p, k > 0`. -/
theorem r_pos_of_C (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M)
    (hC : 0 < C M) : 0 < r M := by
  have hC' : 0 < p M * k M * r M := by rwa [C_eq M h00 hp hk] at hC
  exact pos_of_mul_pos_right hC' (le_of_lt (mul_pos hp hk))

/-! ## 5. The exact equivalence with the actual frame -/

/-- **Stage B main theorem.**  Under `M 0 0 = 1`, the division-free polynomial domain is
equivalent to the actual frame: the original normalization, the four leading complete
pivots on `M`/`S4`/`S3`/`T2`, and `p, k, r > 0`.

Forward direction: `p > 0` from `A`, then `k > 0` from `B = p * k`, then `r > 0` from
`C = p * k * r`; every cancellation uses the established positivity.  Reverse direction:
the three positivity facts and the four pivots give the seven finite clause families. -/
theorem polyCP_iff_frame (M : Matrix5) (h00 : M 0 0 = 1) :
    PolyCP M ↔
      (matrixEntryMax M = 1 ∧ IsCompletePivot M 0 0 ∧ IsCompletePivot (S4 M) 0 0 ∧
        IsCompletePivot (S3 M) 0 0 ∧ IsCompletePivot (T2 M) 0 0 ∧
        0 < p M ∧ 0 < k M ∧ 0 < r M) := by
  constructor
  · rintro ⟨hA, hB, hC, h25, h16, h9, h4⟩
    have hp : 0 < p M := p_pos_of_A M h00 hA
    have hk : 0 < k M := k_pos_of_B M h00 hp hB
    have hr : 0 < r M := r_pos_of_C M h00 hp hk hC
    exact ⟨(matrixEntryMax_eq_one_iff_entries M h00).mpr h25,
      (isCompletePivot_M_iff_entries M h00).mpr h25,
      (isCompletePivot_iff_m2 M h00 hp).mpr h16,
      (isCompletePivot_iff_m3 M h00 hp hk).mpr h9,
      (isCompletePivot_iff_m4 M h00 hp hk hr).mpr h4,
      hp, hk, hr⟩
  · rintro ⟨hmax, hcp, hS4, hS3, hT2, hp, hk, hr⟩
    exact ⟨by rw [A_eq M h00]; exact hp,
      by rw [B_eq M h00 (ne_of_gt hp)]; exact mul_pos hp hk,
      by rw [C_eq M h00 hp hk]; exact mul_pos (mul_pos hp hk) hr,
      (matrixEntryMax_eq_one_iff_entries M h00).mp hmax,
      (isCompletePivot_iff_m2 M h00 hp).mp hS4,
      (isCompletePivot_iff_m3 M h00 hp hk).mp hS3,
      (isCompletePivot_iff_m4 M h00 hp hk hr).mp hT2⟩

end Rho5.MinorCPDomain
