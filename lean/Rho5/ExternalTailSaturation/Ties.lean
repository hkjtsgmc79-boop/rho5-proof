import Rho5.ExternalTailSaturation.Signs
import Rho5.Shared.TracePermutation.Schur

/-!
T3: swaps of tied fourth-stage pivots, lifted to the last two rows/columns of M.
The early pivot indices stay fixed.  No non-maximal fourth-stage entry is swapped in.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.TracePermutation (permuteEntries)

def endPerm5 : Bool → Equiv.Perm (Fin 5)
  | false => Equiv.refl _
  | true => Equiv.swap 3 4
def endPerm4 : Bool → Equiv.Perm (Fin 4)
  | false => Equiv.refl _
  | true => Equiv.swap 2 3
def endPerm3 : Bool → Equiv.Perm (Fin 3)
  | false => Equiv.refl _
  | true => Equiv.swap 1 2
def endPerm2 : Bool → Equiv.Perm (Fin 2)
  | false => Equiv.refl _
  | true => Equiv.swap 0 1

@[simp] theorem endPerm5_zero (b : Bool) : endPerm5 b 0 = 0 := by cases b <;> decide
@[simp] theorem endPerm4_zero (b : Bool) : endPerm4 b 0 = 0 := by cases b <;> decide
@[simp] theorem endPerm3_zero (b : Bool) : endPerm3 b 0 = 0 := by cases b <;> decide

theorem endPerm5_succ (b : Bool) (i : Fin 4) : endPerm5 b i.succ = (endPerm4 b i).succ := by
  cases b <;> fin_cases i <;> decide

theorem endPerm4_succ (b : Bool) (i : Fin 3) : endPerm4 b i.succ = (endPerm3 b i).succ := by
  cases b <;> fin_cases i <;> decide

theorem endPerm3_succ (b : Bool) (i : Fin 2) : endPerm3 b i.succ = (endPerm2 b i).succ := by
  cases b <;> fin_cases i <;> decide

/-- The existing actual permutation operator, restricted to the last two indices. -/
def tailPermute (M : Matrix5) (rows cols : Bool) : Matrix5 :=
  permuteEntries M (endPerm5 rows) (endPerm5 cols)

theorem schur_head_permute {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a b : Equiv.Perm (Fin (n + 1))) (a' b' : Equiv.Perm (Fin n))
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (has : ∀ i, a i.succ = (a' i).succ) (hbs : ∀ j, b j.succ = (b' j).succ) :
    Rho5.PivotReindex.pivotSchur (permuteEntries A a b) 0 0 =
      permuteEntries (Rho5.PivotReindex.pivotSchur A 0 0) a' b' := by
  funext i j
  simp only [Rho5.PivotReindex.pivotSchur, Rho5.PivotReindex.movePivot_zero_zero_eq,
    Rho5.Pivot.fixedSchur, permuteEntries, ha0, hb0, has, hbs]

theorem S4_tailPermute (M : Matrix5) (a b : Bool) :
    S4 (tailPermute M a b) = permuteEntries (S4 M) (endPerm4 a) (endPerm4 b) := by
  exact schur_head_permute M _ _ _ _ (endPerm5_zero a) (endPerm5_zero b)
    (endPerm5_succ a) (endPerm5_succ b)

theorem S3_tailPermute (M : Matrix5) (a b : Bool) :
    S3 (tailPermute M a b) = permuteEntries (S3 M) (endPerm3 a) (endPerm3 b) := by
  unfold S3
  rw [S4_tailPermute]
  exact schur_head_permute (S4 M) _ _ _ _ (endPerm4_zero a) (endPerm4_zero b)
    (endPerm4_succ a) (endPerm4_succ b)

theorem T2_tailPermute (M : Matrix5) (a b : Bool) :
    T2 (tailPermute M a b) = permuteEntries (T2 M) (endPerm2 a) (endPerm2 b) := by
  unfold T2
  rw [S3_tailPermute]
  exact schur_head_permute (S3 M) _ _ _ _ (endPerm3_zero a) (endPerm3_zero b)
    (endPerm3_succ a) (endPerm3_succ b)

@[simp] theorem tailPermute_head (M : Matrix5) (a b : Bool) :
    tailPermute M a b 0 0 = M 0 0 := by simp [tailPermute, permuteEntries]
@[simp] theorem p_tailPermute (M : Matrix5) (a b : Bool) : p (tailPermute M a b) = p M := by
  simp [p, S4_tailPermute, permuteEntries]
@[simp] theorem k_tailPermute (M : Matrix5) (a b : Bool) : k (tailPermute M a b) = k M := by
  simp [k, S3_tailPermute, permuteEntries]

/-- Early CP preservation, separate from the fourth-stage tied-pivot qualification. -/
theorem tailPermute_early_cp {M : Matrix5} (h : LeadingInput M) (a b : Bool) :
    IsCompletePivot (tailPermute M a b) 0 0 ∧
    IsCompletePivot (S4 (tailPermute M a b)) 0 0 ∧
    IsCompletePivot (S3 (tailPermute M a b)) 0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tailPermute, Rho5.TracePermutation.isCompletePivot_permuteEntries_iff]
    simpa only [endPerm5_zero] using h.cp0
  · rw [S4_tailPermute, Rho5.TracePermutation.isCompletePivot_permuteEntries_iff]
    simpa only [endPerm4_zero] using h.cp1
  · rw [S3_tailPermute, Rho5.TracePermutation.isCompletePivot_permuteEntries_iff]
    simpa only [endPerm3_zero] using h.cp2

def swapColumns (M : Matrix5) : Matrix5 := tailPermute M false true
def swapRows (M : Matrix5) : Matrix5 := tailPermute M true false

@[simp] theorem r_swapColumns (M : Matrix5) : r (swapColumns M) = s M := by
  simp [swapColumns, r, s, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem s_swapColumns (M : Matrix5) : s (swapColumns M) = r M := by
  simp [swapColumns, r, s, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem t_swapColumns (M : Matrix5) : t (swapColumns M) = w M := by
  simp [swapColumns, t, w, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem w_swapColumns (M : Matrix5) : w (swapColumns M) = t M := by
  simp [swapColumns, t, w, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem r_swapRows (M : Matrix5) : r (swapRows M) = t M := by
  simp [swapRows, r, t, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem s_swapRows (M : Matrix5) : s (swapRows M) = w M := by
  simp [swapRows, s, w, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem t_swapRows (M : Matrix5) : t (swapRows M) = r M := by
  simp [swapRows, r, t, T2_tailPermute, permuteEntries, endPerm2]
@[simp] theorem w_swapRows (M : Matrix5) : w (swapRows M) = s M := by
  simp [swapRows, s, w, T2_tailPermute, permuteEntries, endPerm2]

/-- The swapped-in column pivot really is a tied largest entry. -/
theorem column_tie_legal {M : Matrix5} (h : LeadingInput M) (hs : s M = r M) :
    IsCompletePivot (T2 M) 0 1 := by
  apply Rho5.Pivot.tied_pivot (T2 M) 0 0 0 1 h.cp3
  change |s M| = |r M|
  rw [hs]

theorem row_tie_legal {M : Matrix5} (h : LeadingInput M) (ht : t M = r M) :
    IsCompletePivot (T2 M) 1 0 := by
  apply Rho5.Pivot.tied_pivot (T2 M) 0 1 0 0 h.cp3
  change |t M| = |r M|
  rw [ht]

theorem delta_swapColumns {M : Matrix5} (h : LeadingInput M) (hs : s M = r M) :
    delta (swapColumns M) = -delta M := by
  unfold delta
  rw [w_swapColumns, t_swapColumns, s_swapColumns, r_swapColumns, hs]
  field_simp [r_ne_zero h] <;> ring

theorem delta_swapRows {M : Matrix5} (h : LeadingInput M) (ht : t M = r M) :
    delta (swapRows M) = -delta M := by
  unfold delta
  rw [w_swapRows, t_swapRows, s_swapRows, r_swapRows, ht]
  field_simp [r_ne_zero h] <;> ring

theorem swapColumns_input {M : Matrix5} (h : LeadingInput M) (hs : s M = r M) :
    LeadingInput (swapColumns M) := by
  have he := tailPermute_early_cp h false true
  refine ⟨by simpa [swapColumns] using h.head, he.1, he.2.1, he.2.2, ?_,
    by simpa [swapColumns] using h.p_pos,
    by simpa [swapColumns] using h.k_pos, ?_⟩
  · rw [swapColumns, T2_tailPermute, Rho5.TracePermutation.isCompletePivot_permuteEntries_iff]
    simpa [endPerm2] using column_tie_legal h hs
  · rw [delta_swapColumns h hs]
    exact neg_ne_zero.mpr h.delta_ne

theorem swapRows_input {M : Matrix5} (h : LeadingInput M) (ht : t M = r M) :
    LeadingInput (swapRows M) := by
  have he := tailPermute_early_cp h true false
  refine ⟨by simpa [swapRows] using h.head, he.1, he.2.1, he.2.2, ?_,
    by simpa [swapRows] using h.p_pos,
    by simpa [swapRows] using h.k_pos, ?_⟩
  · rw [swapRows, T2_tailPermute, Rho5.TracePermutation.isCompletePivot_permuteEntries_iff]
    simpa [endPerm2] using row_tie_legal h ht
  · rw [delta_swapRows h ht]
    exact neg_ne_zero.mpr h.delta_ne

/-- Swap actual last two columns, then flip actual last row. -/
def columnTie (M : Matrix5) : Matrix5 := tailScale (swapColumns M) 1 (-1) 1 1
/-- Swap actual last two rows, then flip actual last column. -/
def rowTie (M : Matrix5) : Matrix5 := tailScale (swapRows M) 1 1 1 (-1)

@[simp] theorem p_columnTie (M : Matrix5) : p (columnTie M) = p M := by simp [columnTie, swapColumns]
@[simp] theorem k_columnTie (M : Matrix5) : k (columnTie M) = k M := by simp [columnTie, swapColumns]
@[simp] theorem r_columnTie (M : Matrix5) : r (columnTie M) = s M := by simp [columnTie]
@[simp] theorem s_columnTie (M : Matrix5) : s (columnTie M) = r M := by simp [columnTie]
@[simp] theorem t_columnTie (M : Matrix5) : t (columnTie M) = -w M := by simp [columnTie]
@[simp] theorem w_columnTie (M : Matrix5) : w (columnTie M) = -t M := by simp [columnTie]
@[simp] theorem p_rowTie (M : Matrix5) : p (rowTie M) = p M := by simp [rowTie, swapRows]
@[simp] theorem k_rowTie (M : Matrix5) : k (rowTie M) = k M := by simp [rowTie, swapRows]
@[simp] theorem r_rowTie (M : Matrix5) : r (rowTie M) = t M := by simp [rowTie]
@[simp] theorem s_rowTie (M : Matrix5) : s (rowTie M) = -w M := by simp [rowTie]
@[simp] theorem t_rowTie (M : Matrix5) : t (rowTie M) = r M := by simp [rowTie]
@[simp] theorem w_rowTie (M : Matrix5) : w (rowTie M) = -s M := by simp [rowTie]

theorem columnTie_input {M : Matrix5} (h : LeadingInput M) (hs : s M = r M) :
    LeadingInput (columnTie M) :=
  tailScale_sign_input (swapColumns_input h hs) _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem rowTie_input {M : Matrix5} (h : LeadingInput M) (ht : t M = r M) :
    LeadingInput (rowTie M) :=
  tailScale_sign_input (swapRows_input h ht) _ _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem delta_columnTie {M : Matrix5} (h : LeadingInput M) (hs : s M = r M) :
    delta (columnTie M) = delta M := by
  rw [columnTie, delta_tailScale _ 1 (-1) 1 1 (by norm_num) (by norm_num)
    (r_ne_zero (swapColumns_input h hs)), delta_swapColumns h hs]
  ring

theorem delta_rowTie {M : Matrix5} (h : LeadingInput M) (ht : t M = r M) :
    delta (rowTie M) = delta M := by
  rw [rowTie, delta_tailScale _ 1 1 1 (-1) (by norm_num) (by norm_num)
    (r_ne_zero (swapRows_input h ht)), delta_swapRows h ht]
  ring

theorem columnTie_X {M : Matrix5} (d : CanonicalD M) (hw : w M = -r M)
    (hs : s M = r M) : CanonicalX (columnTie M) := by
  apply canonicalX_of_entries
  · rw [r_columnTie, hs]; exact d.r_pos
  · rw [s_columnTie, r_columnTie, hs]
  · rw [t_columnTie, r_columnTie, hw, hs]; ring
  · rw [w_columnTie, r_columnTie, hs, abs_neg, abs_of_nonneg d.t_nonneg]
    exact d.t_le

theorem rowTie_X {M : Matrix5} (d : CanonicalD M) (hw : w M = -r M)
    (ht : t M = r M) : CanonicalX (rowTie M) := by
  apply canonicalX_of_entries
  · rw [r_rowTie, ht]; exact d.r_pos
  · rw [s_rowTie, r_rowTie, hw, ht]; ring
  · rw [t_rowTie, r_rowTie, ht]
  · rw [w_rowTie, r_rowTie, ht, abs_neg, abs_of_nonneg d.s_nonneg]
    exact d.s_le

end Rho5.ExternalTailSaturation
