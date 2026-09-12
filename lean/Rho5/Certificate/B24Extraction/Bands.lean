import Rho5.Certificate.B24Extraction.Extract

/-!
# D37 / B24Extraction — the head band and the physical layer of the extracted point

**Item 3 of the card.**  For a normalized matrix of the extracted class
(`A 0 0 = 1`, balanced tail `T2 1 1 = -r`, legal first three pivots), the extracted
B24 point satisfies the *frozen* D28 predicates:

* `HeadBand (extract A)` — the fields `Physical` does not supply
  (`|e|, |β|, |p - eβ|, |u_i|, |x_i|, |v_j|, |L_i| ≤ 1`) all come from the pivot
  bounds of `A` and `S4`;
* `Physical (extract A)` — `d_bound` from `S3`, `o_bound` from `A`, `s_bound`/`q_bound`
  from `S4`, `l_bound`/`p_bound` from `A` again, `r_pos` from the hypothesis,
  `height` from the definition of `F`, and `order_t` from the last pivot bound
  `|T2 1 0| ≤ r`.

The normalized corner `A 0 0 = 1` and the completeness of the first pivot are what
make every `A`-entry bound available, so neither `Physical` nor `HeadBand` is
assumed: both are *proved* for the extracted point.  Every hypothesis is explicit.
-/

namespace Rho5.Certificate.B24Extraction

open Rho5.Certificate.B16 (Point D O S L P u xv v q Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct firstStage HeadBand beta)

/-! ## Coordinate readings of the extracted point -/

theorem extract_zero (A : Matrix5) : extract A 0 = k A := by simp [extract]

theorem extract_one (A : Matrix5) : extract A 1 = r A := by simp [extract]

theorem extract_two (A : Matrix5) : extract A 2 = s A := by simp [extract]

theorem extract_three (A : Matrix5) : extract A 3 = t A := by simp [extract]

theorem x_extract (A : Matrix5) (i : Fin 3) :
    Rho5.Certificate.B24Reconstruction.x (extract A) i = S4 A i.succ 0 / p A := by
  rw [show Rho5.Certificate.B24Reconstruction.x (extract A) i = xv (extract A) i from rfl,
    xv_extract]

theorem extract_twentythree (A : Matrix5) : extract A 23 = F A := by simp [extract]

theorem extract_height_coord (A : Matrix5) :
    extract A 23 = extract A 1 + extract A 2 * extract A 3 / extract A 1 := by
  simp [extract, F]

/-! ## Entry bound of the normalized matrix -/

/-- The normalized corner `A 0 0 = 1` plus completeness of `(0, 0)` bound every entry
of `A` by `1`. -/
theorem abs_entry_A_le_one (A : Matrix5) (h00 : A 0 0 = 1)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0) (i j : Fin 5) : |A i j| ≤ 1 := by
  have h := hpiv i j
  rwa [h00, abs_one] at h

/-! ## Item 3 — the head band -/

/-- **Item 3 (`HeadBand`).**  The head-band fields `Physical` lacks, proved from the
first-pivot completeness of `A` and `S4` (with `p > 0` for the `x_i` field). -/
theorem headBand_extract (A : Matrix5) (h00 : A 0 0 = 1)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (hS4 : Rho5.Pivot.IsCompletePivot (S4 A) 0 0) (hp : 0 < p A) :
    HeadBand (extract A) := by
  have h1 := abs_entry_A_le_one A h00 hpiv
  have hpabs : |p A| = p A := abs_of_pos hp
  have hS4abs : |S4 A 0 0| = S4 A 0 0 := hpabs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e_extract]; simpa using h1 0 1
  · rw [beta_extract]; exact h1 1 0
  · intro i; rw [u_extract]; exact h1 _ _
  · intro i
    rw [x_extract, abs_div, hpabs]
    refine (div_le_one hp).mpr ?_
    have h := hS4 i.succ 0
    rw [hS4abs] at h
    exact h
  · intro j; rw [v_extract]; exact h1 _ _
  · rw [p_extract, e_extract, beta_extract]
    have h : p A - -A 0 1 * A 1 0 = A 1 1 := by
      rw [p, S4_apply A 0 0, h00]
      first
        | (norm_num; ring)
        | norm_num
    rw [h]; exact h1 1 1
  · intro i
    rw [p_extract, e_extract, x_extract, u_extract]
    have h : p A * (S4 A i.succ 0 / p A) - -A 0 1 * A i.succ.succ 0
        = A i.succ.succ 1 := by
      rw [S4_apply A i.succ 0, h00]
      field_simp [hp]
      first
        | (norm_num; ring)
        | norm_num
    rw [h]; exact h1 _ _

/-! ## Item 3 — the physical layer -/

/-- **Item 3 (`Physical`).**  The frozen physical layer of the extracted point,
proved from the three Schur updates' complete pivots, the normalization `A 0 0 = 1`,
the balance condition and the three positivity hypotheses.  In particular `d_bound`
comes from `S3` (via `D_extract`), `o_bound` from `A`, and `s_bound`/`q_bound` from
`S4`. -/
theorem physical_extract (A : Matrix5) (h00 : A 0 0 = 1) (hp : p A ≠ 0)
    (hk : k A ≠ 0) (htail : T2 A 1 1 = -r A)
    (hpiv : Rho5.Pivot.IsCompletePivot A 0 0)
    (hS4 : Rho5.Pivot.IsCompletePivot (S4 A) 0 0)
    (hS3 : Rho5.Pivot.IsCompletePivot (S3 A) 0 0)
    (hT2 : Rho5.Pivot.IsCompletePivot (T2 A) 0 0)
    (hppos : 0 < p A) (hkpos : 0 < k A) (hrpos : 0 < r A) :
    Physical (extract A) := by
  have h1 := abs_entry_A_le_one A h00 hpiv
  have hkabs : |k A| = k A := abs_of_pos hkpos
  have hpabs : |p A| = p A := abs_of_pos hppos
  have hrabs : |r A| = r A := abs_of_pos hrpos
  have hS3abs : |S3 A 0 0| = S3 A 0 0 := hkabs
  have hS4abs : |S4 A 0 0| = S4 A 0 0 := hpabs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have h := hS3 i j
    have hD : D (extract A) i j = S3 A i j := by rw [D_extract A hk htail]
    rw [hD, extract_zero]
    rw [hS3abs] at h
    exact h
  · intro i j
    rw [O_extract A h00 hp hk htail]
    exact h1 _ _
  · intro i j
    have h := hS4 i.succ j.succ
    have hS : S (extract A) i j = S4 A i.succ j.succ :=
      S_extract A h00 hp hk htail i j
    rw [hS, extract_eight]
    rw [hS4abs] at h
    exact h
  · intro j
    rw [L_extract A h00 (ne_of_gt hppos)]
    exact h1 _ _
  · intro j
    rw [P_extract A h00]
    exact h1 _ _
  · intro j
    have h := hS4 0 j.succ
    have hq : q (extract A) j = S4 A 0 j.succ := q_extract A h00 hp hk htail j
    rw [hq, extract_eight]
    rw [hS4abs] at h
    exact h
  · rw [extract_one]; exact hrpos
  · rw [extract_height_coord]
  · have h := hT2 1 0
    have hrabs' : |T2 A 0 0| = T2 A 0 0 := hrabs
    rw [hrabs'] at h
    rw [extract_three, extract_one]
    exact (le_abs_self (t A)).trans (by simpa [t, r] using h)

end Rho5.Certificate.B24Extraction
