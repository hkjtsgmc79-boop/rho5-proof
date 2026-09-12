import Rho5.ExternalTailSaturation.Saturation
import Rho5.Shared.TraceSigns.Trace

/-! T3 sign normalization is a full-matrix operation, including zero-arm sign choices. -/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.TraceSigns (signedEntries IsSign)

/-- At zero choose +1, never zero. -/
def signOne (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem signOne_cases (x : ℝ) : signOne x = 1 ∨ signOne x = -1 := by
  unfold signOne
  split_ifs <;> simp
@[simp] theorem signOne_abs (x : ℝ) : |signOne x| = 1 := by
  rcases signOne_cases x with h | h <;> simp [h]
@[simp] theorem signOne_sq (x : ℝ) : signOne x * signOne x = 1 := by
  rcases signOne_cases x with h | h <;> simp [h]
@[simp] theorem signOne_mul (x : ℝ) : signOne x * x = |x| := by
  unfold signOne
  split_ifs with hx
  · simp [abs_of_nonneg hx]
  · simp [abs_of_neg (lt_of_not_ge hx)]

theorem nonzero_of_abs_one {x : ℝ} (hx : |x| = 1) : x ≠ 0 := by
  intro hz
  simp [hz] at hx

private theorem factors5_sign {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1) :
    IsSign (factors5 a b) := by
  apply (Rho5.TraceSigns.isSign_iff_abs_eq_one _).mpr
  intro i
  fin_cases i <;> simp [factors5, ha, hb]
private theorem factors4_sign {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1) :
    IsSign (factors4 a b) := by
  apply (Rho5.TraceSigns.isSign_iff_abs_eq_one _).mpr
  intro i
  fin_cases i <;> simp [factors4, ha, hb]
private theorem factors3_sign {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1) :
    IsSign (factors3 a b) := by
  apply (Rho5.TraceSigns.isSign_iff_abs_eq_one _).mpr
  intro i
  fin_cases i <;> simp [factors3, ha, hb]
private theorem factors2_sign {a b : ℝ} (ha : |a| = 1) (hb : |b| = 1) :
    IsSign (factors2 a b) := by
  apply (Rho5.TraceSigns.isSign_iff_abs_eq_one _).mpr
  intro i
  fin_cases i <;> simp [factors2, ha, hb]

/-- The existing whole-trace sign API, specialized to our full last-two action. -/
theorem tailScale_sign_trace_iff (M : Matrix5) (a b c d : ℝ)
    (ha : |a| = 1) (hb : |b| = 1) (hc : |c| = 1) (hd : |d| = 1) (vs : List ℝ) :
    Rho5.CompletePivotPath.LegalTrace (tailScale M a b c d) vs ↔
      Rho5.CompletePivotPath.LegalTrace M vs :=
  Rho5.TraceSigns.legalTrace_signed_iff' M (factors5_sign ha hb) (factors5_sign hc hd) vs

/-- Fixed leading CP is also preserved, separately from arbitrary-path invariance. -/
theorem tailScale_sign_input {M : Matrix5} (h : LeadingInput M) (a b c d : ℝ)
    (ha : |a| = 1) (hb : |b| = 1) (hc : |c| = 1) (hd : |d| = 1) :
    LeadingInput (tailScale M a b c d) := by
  refine ⟨by simpa only [tailScale_head] using h.head, ?_, ?_, ?_, ?_,
    by simpa only [p_tailScale] using h.p_pos,
    by simpa only [k_tailScale] using h.k_pos, ?_⟩
  · exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff M
      (factors5_sign ha hb) (factors5_sign hc hd) 0 0).mpr h.cp0
  · rw [S4_tailScale]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S4 M)
      (factors4_sign ha hb) (factors4_sign hc hd) 0 0).mpr h.cp1
  · rw [S3_tailScale]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (S3 M)
      (factors3_sign ha hb) (factors3_sign hc hd) 0 0).mpr h.cp2
  · rw [T2_tailScale]
    exact (Rho5.TraceSigns.isCompletePivot_signedEntries_iff (T2 M)
      (factors2_sign ha hb) (factors2_sign hc hd) 0 0).mpr h.cp3
  · rw [delta_tailScale M a b c d (nonzero_of_abs_one ha) (nonzero_of_abs_one hc) (r_ne_zero h)]
    exact mul_ne_zero (mul_ne_zero (nonzero_of_abs_one hb) (nonzero_of_abs_one hd)) h.delta_ne

theorem tailScale_sign_height {M : Matrix5} (h : LeadingInput M) (a b c d : ℝ)
    (ha : |a| = 1) (hb : |b| = 1) (hc : |c| = 1) (hd : |d| = 1) :
    height (tailScale M a b c d) = height M := by
  unfold height
  rw [delta_tailScale M a b c d (nonzero_of_abs_one ha) (nonzero_of_abs_one hc) (r_ne_zero h)]
  simp only [abs_mul, hb, hd, one_mul]

/-- Both X and D use the same actual full-matrix normalization. -/
def canonical (M : Matrix5) : Matrix5 :=
  tailScale M (signOne (r M)) (signOne (t M)) 1 (signOne (r M) * signOne (s M))

@[simp] theorem canonical_head (M : Matrix5) : canonical M 0 0 = M 0 0 := by simp [canonical]
@[simp] theorem p_canonical (M : Matrix5) : p (canonical M) = p M := by simp [canonical]
@[simp] theorem k_canonical (M : Matrix5) : k (canonical M) = k M := by simp [canonical]
@[simp] theorem r_canonical (M : Matrix5) : r (canonical M) = |r M| := by simp [canonical]
@[simp] theorem t_canonical (M : Matrix5) : t (canonical M) = |t M| := by simp [canonical]
@[simp] theorem s_canonical (M : Matrix5) : s (canonical M) = |s M| := by
  rw [canonical, s_tailScale]
  calc signOne (r M) * s M * (signOne (r M) * signOne (s M)) =
      (signOne (r M) * signOne (r M)) * (signOne (s M) * s M) := by ring
    _ = |s M| := by rw [signOne_sq, signOne_mul, one_mul]
@[simp] theorem w_canonical_abs (M : Matrix5) : |w (canonical M)| = |w M| := by
  simp [canonical, abs_mul]

theorem canonical_input {M : Matrix5} (h : LeadingInput M) : LeadingInput (canonical M) :=
  tailScale_sign_input h _ _ _ _ (signOne_abs _) (signOne_abs _) (by norm_num)
    (by simp only [abs_mul, signOne_abs, one_mul])

theorem canonical_height {M : Matrix5} (h : LeadingInput M) : height (canonical M) = height M :=
  tailScale_sign_height h _ _ _ _ (signOne_abs _) (signOne_abs _) (by norm_num)
    (by simp only [abs_mul, signOne_abs, one_mul])

/-- Canonical X is the actual [[r,r],[r,w]] tail, together with its height identity. -/
structure CanonicalX (M : Matrix5) : Prop where
  r_pos : 0 < r M
  s_eq : s M = r M
  t_eq : t M = r M
  w_bound : |w M| ≤ r M
  height_eq : height M = r M - w M

/-- Canonical D carries all signs and both zero arms; no positivity strengthening. -/
structure CanonicalD (M : Matrix5) : Prop where
  r_pos : 0 < r M
  s_nonneg : 0 ≤ s M
  s_le : s M ≤ r M
  t_nonneg : 0 ≤ t M
  t_le : t M ≤ r M
  diagonal : w M = r M ∨ w M = -r M

structure ProperB (M : Matrix5) : Prop where
  r_pos : 0 < r M
  s_pos : 0 < s M
  s_lt : s M < r M
  t_pos : 0 < t M
  t_lt : t M < r M
  w_eq : w M = -r M
  height_eq : height M = r M + s M * t M / r M

theorem canonicalX_of_entries (M : Matrix5) (hr : 0 < r M)
    (hs : s M = r M) (ht : t M = r M) (hw : |w M| ≤ r M) : CanonicalX M := by
  refine ⟨hr, hs, ht, hw, ?_⟩
  have hdelta : delta M = w M - r M := by
    unfold delta
    rw [hs, ht]
    field_simp [ne_of_gt hr] <;> ring
  have hwle : w M ≤ r M := (le_abs_self _).trans hw
  rw [height, hdelta, abs_of_nonpos (sub_nonpos.mpr hwle)]
  ring

theorem canonical_X {M : Matrix5} (h : LeadingInput M) (hx : XFace M) :
    CanonicalX (canonical M) := by
  apply canonicalX_of_entries
  · rw [r_canonical]
    exact abs_pos.mpr (r_ne_zero h)
  · simpa only [s_canonical, r_canonical] using hx.1
  · simpa only [t_canonical, r_canonical] using hx.2
  · simpa only [w_canonical_abs, r_canonical] using (tail_bounds h).2.2

theorem canonical_D {M : Matrix5} (h : LeadingInput M) (hd : DFace M) :
    CanonicalD (canonical M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r_canonical]
    exact abs_pos.mpr (r_ne_zero h)
  · rw [s_canonical]; exact abs_nonneg _
  · simpa only [s_canonical, r_canonical] using (tail_bounds h).1
  · rw [t_canonical]; exact abs_nonneg _
  · simpa only [t_canonical, r_canonical] using (tail_bounds h).2.1
  · have heq : |w (canonical M)| = r (canonical M) := by
      simpa only [w_canonical_abs, r_canonical] using hd
    rcases le_total 0 (w (canonical M)) with hw | hw
    · exact Or.inl (by rwa [abs_of_nonneg hw] at heq)
    · exact Or.inr (by rw [abs_of_nonpos hw] at heq; linarith)

/-- Equivalent chi formulation of the actual D diagonal. -/
theorem CanonicalD.chi {M : Matrix5} (h : CanonicalD M) :
    ∃ χ : ℝ, (χ = -1 ∨ χ = 1) ∧ w M = χ * r M := by
  rcases h.diagonal with hp | hn
  · exact ⟨1, Or.inr rfl, by simpa only [one_mul] using hp⟩
  · exact ⟨-1, Or.inl rfl, by simpa only [neg_one_mul] using hn⟩

end Rho5.ExternalTailSaturation
