import Rho5.ExternalTailSaturation.Ties

/-!
T3 completion: X or proper B or F <= the current fourth pivot.  Only an explicit
separate input |r(original)| <= 4 removes the third exit when F > 4.
-/
noncomputable section
namespace Rho5.ExternalTailSaturation

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Pivot (IsCompletePivot)
open Rho5.CompletePivotPath (LegalTrace)

private theorem D_product_quotient_bounds {M : Matrix5} (d : CanonicalD M) :
    0 ≤ t M * s M / r M ∧ t M * s M / r M ≤ r M := by
  have hprod : t M * s M ≤ r M * r M :=
    mul_le_mul d.t_le d.s_le d.s_nonneg (le_of_lt d.r_pos)
  have hcancel : (t M * s M / r M) * r M = t M * s M :=
    div_mul_cancel₀ _ (ne_of_gt d.r_pos)
  refine ⟨div_nonneg (mul_nonneg d.t_nonneg d.s_nonneg) (le_of_lt d.r_pos), ?_⟩
  -- D123 API 修复（普通适配）：本 mathlib 的 `mul_le_mul_right` 是 MulLeftMono 版
  -- （`b ≤ c → ∀ a, a * b ≤ a * c`），没有 iff 形式；右因子消去用
  -- `le_of_mul_le_mul_right (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c`。数学内容不变。
  exact le_of_mul_le_mul_right (by rw [hcancel]; exact hprod) d.r_pos

/-- Positive diagonal or a zero arm has last height at most the current fourth pivot. -/
theorem D_small_last {M : Matrix5} (d : CanonicalD M)
    (hsmall : w M = r M ∨ s M = 0 ∨ t M = 0) : height M ≤ r M := by
  rcases hsmall with hw | hs | ht
  · have hq := D_product_quotient_bounds d
    rw [height, delta, hw, abs_of_nonneg (sub_nonneg.mpr hq.2)]
    linarith [hq.1]
  · rcases d.diagonal with hw | hw <;>
      simp [height, delta, hs, hw, abs_of_pos d.r_pos]
  · rcases d.diagonal with hw | hw <;>
      simp [height, delta, ht, hw, abs_of_pos d.r_pos]

/-- Negative D with no zero arm and no tied arm is exactly proper B. -/
theorem D_proper_of_not_boundary {M : Matrix5} (d : CanonicalD M)
    (hw : w M = -r M) (hs0 : s M ≠ 0) (ht0 : t M ≠ 0)
    (hsr : s M ≠ r M) (htr : t M ≠ r M) : ProperB M := by
  have hspos : 0 < s M := by
    by_contra hn
    exact hs0 (le_antisymm (le_of_not_gt hn) d.s_nonneg)
  have htpos : 0 < t M := by
    by_contra hn
    exact ht0 (le_antisymm (le_of_not_gt hn) d.t_nonneg)
  have hslt : s M < r M := by
    rcases lt_or_eq_of_le d.s_le with hh | hh
    · exact hh
    · exact False.elim (hsr hh)
  have htlt : t M < r M := by
    rcases lt_or_eq_of_le d.t_le with hh | hh
    · exact hh
    · exact False.elim (htr hh)
  refine ⟨d.r_pos, hspos, hslt, htpos, htlt, hw, ?_⟩
  have hq : 0 ≤ t M * s M / r M := (D_product_quotient_bounds d).1
  have hneg : -r M - t M * s M / r M ≤ 0 := by linarith [d.r_pos]
  rw [height, delta, hw, abs_of_nonpos hneg]
  ring

/-- Result of the D classification.  Its operation field names the actual matrices. -/
structure DClassification (M N : Matrix5) : Prop where
  input : LeadingInput N
  p_eq : p N = p M
  k_eq : k N = k M
  height_eq : height N = height M
  r_eq : r N = r M
  form : CanonicalX N ∨ ProperB N ∨ height M ≤ r N
  operation : N = M ∨ N = columnTie M ∨ N = rowTie M

theorem classify_D {M : Matrix5} (h : LeadingInput M) (d : CanonicalD M) :
    ∃ N : Matrix5, DClassification M N := by
  by_cases hsmall : w M = r M ∨ s M = 0 ∨ t M = 0
  · exact ⟨M, h, rfl, rfl, rfl, rfl, Or.inr (Or.inr (D_small_last d hsmall)), Or.inl rfl⟩
  have hwnot : w M ≠ r M := fun hh => hsmall (Or.inl hh)
  have hs0 : s M ≠ 0 := fun hh => hsmall (Or.inr (Or.inl hh))
  have ht0 : t M ≠ 0 := fun hh => hsmall (Or.inr (Or.inr hh))
  have hw : w M = -r M := d.diagonal.resolve_left hwnot
  by_cases hs : s M = r M
  · refine ⟨columnTie M, columnTie_input h hs, p_columnTie M, k_columnTie M,
      ?_, ?_, Or.inl (columnTie_X d hw hs), Or.inr (Or.inl rfl)⟩
    · unfold height
      rw [delta_columnTie h hs]
    · rw [r_columnTie, hs]
  by_cases ht : t M = r M
  · refine ⟨rowTie M, rowTie_input h ht, p_rowTie M, k_rowTie M,
      ?_, ?_, Or.inl (rowTie_X d hw ht), Or.inr (Or.inr rfl)⟩
    · unfold height
      rw [delta_rowTie h ht]
    · rw [r_rowTie, ht]
  exact ⟨M, h, rfl, rfl, rfl, rfl,
    Or.inr (Or.inl (D_proper_of_not_boundary d hw hs0 ht0 hs ht)), Or.inl rfl⟩

/-- A named concrete starting point for all three T3 exits. -/
def formBase (M : Matrix5) : Matrix5 := canonical (representative M)

/-- Every field is an output paid by the public reduction theorem, not a premise. -/
structure TailReduction (M N : Matrix5) : Prop where
  construction : N = formBase M ∨ N = columnTie (formBase M) ∨ N = rowTie (formBase M)
  input : LeadingInput N
  p_eq : p N = p M
  k_eq : k N = k M
  height_eq : height N = height M
  r_pos : 0 < r N
  r_le : r N ≤ |r M|

theorem base_reduction {M : Matrix5} (h : LeadingInput M) : TailReduction M (formBase M) := by
  have hr := contract_leadingInput h (chosen_factor_certificate h)
  have hrep : LeadingInput (representative M) := hr
  refine ⟨Or.inl rfl, canonical_input hrep, ?_, ?_, ?_, ?_, ?_⟩
  · simp [formBase, representative]
  · simp [formBase, representative]
  · exact (canonical_height hrep).trans (contract_height h (chosen_factor_certificate h))
  · change 0 < r (canonical (representative M))
    rw [r_canonical]
    exact abs_pos.mpr (r_ne_zero hrep)
  · change r (canonical (representative M)) ≤ |r M|
    rw [r_canonical]
    exact contract_fourth_le (chosen_factor_certificate h)

/-- Complete, unconditional trichotomy; F<=r is intentionally retained. -/
theorem exists_canonical_trichotomy {M : Matrix5} (h : LeadingInput M) :
    ∃ N : Matrix5, TailReduction M N ∧
      (CanonicalX N ∨ ProperB N ∨ height M ≤ r N) := by
  have hbase := base_reduction h
  have hrep : LeadingInput (representative M) := contract_leadingInput h (chosen_factor_certificate h)
  have hsat : DFace (representative M) ∨ XFace (representative M) :=
    contract_saturated h (chosen_factor_certificate h)
  rcases hsat with hd | hx
  · have d : CanonicalD (formBase M) := canonical_D hrep hd
    obtain ⟨N, c⟩ := classify_D hbase.input d
    have hred : TailReduction M N := by
      refine ⟨c.operation, c.input, c.p_eq.trans hbase.p_eq, c.k_eq.trans hbase.k_eq,
        c.height_eq.trans hbase.height_eq, ?_, ?_⟩
      · rw [c.r_eq]; exact hbase.r_pos
      · rw [c.r_eq]; exact hbase.r_le
    refine ⟨N, hred, ?_⟩
    rcases c.form with hx | hb | hsmall
    · exact Or.inl hx
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (by rwa [hbase.height_eq] at hsmall))
  · exact ⟨formBase M, hbase, Or.inl (canonical_X hrep hx)⟩

/-- The reduction also has the requested real normalized five-step trace. -/
theorem TailReduction.legalTrace {M N : Matrix5} (h : TailReduction M N) :
    LegalTrace N [1, p M, k M, r N, height M] := by
  simpa only [h.p_eq, h.k_eq, h.height_eq, abs_of_pos h.r_pos] using leading_legalTrace h.input

theorem TailReduction.entryMax {M N : Matrix5} (h : TailReduction M N) : matrixEntryMax N = 1 :=
  entryMax_eq_one N h.input.head h.input.cp0

/-- Full explicit T3 theorem type: actual matrix, explicit operations, CP, and actual trace. -/
theorem exists_same_fifth_trichotomy (M : Matrix5) (h00 : M 0 0 = 1)
    (h0 : IsCompletePivot M 0 0) (h1 : IsCompletePivot (S4 M) 0 0)
    (h2 : IsCompletePivot (S3 M) 0 0) (h3 : IsCompletePivot (T2 M) 0 0)
    (hp : 0 < p M) (hk : 0 < k M) (hd : delta M ≠ 0) :
    ∃ N : Matrix5,
      (N = formBase M ∨ N = columnTie (formBase M) ∨ N = rowTie (formBase M)) ∧
      LeadingInput N ∧ p N = p M ∧ k N = k M ∧ height N = height M ∧
      0 < r N ∧ r N ≤ |r M| ∧ matrixEntryMax N = 1 ∧
      LegalTrace N [1, p M, k M, r N, height M] ∧
      (CanonicalX N ∨ ProperB N ∨ height M ≤ r N) := by
  obtain ⟨N, hred, hform⟩ := exists_canonical_trichotomy
    (show LeadingInput M from ⟨h00, h0, h1, h2, h3, hp, hk, hd⟩)
  exact ⟨N, hred.construction, hred.input, hred.p_eq, hred.k_eq, hred.height_eq,
    hred.r_pos, hred.r_le, hred.entryMax, hred.legalTrace, hform⟩

/-- The <=4 bound is ONLY a supplied premise; no global fourth-pivot bound is proved here. -/
theorem high_value_X_or_properB {M : Matrix5} (h : LeadingInput M)
    (hfour : |r M| ≤ 4) (hhigh : 4 < height M) :
    ∃ N : Matrix5, TailReduction M N ∧ (CanonicalX N ∨ ProperB N) := by
  obtain ⟨N, hred, hform⟩ := exists_canonical_trichotomy h
  refine ⟨N, hred, ?_⟩
  rcases hform with hx | hb | hs
  · exact Or.inl hx
  · exact Or.inr hb
  · have hn : r N ≤ 4 := hred.r_le.trans hfour
    exfalso
    linarith

end Rho5.ExternalTailSaturation
