import Rho5.Algebraic.AlphaRoot.TransformData
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniqueness on all of (4,5)

The coefficient sign change proves strict increase of Q(t)/t^8 on t>0.
It does not assert that Q itself is increasing. All fractional identities have
explicit nonzero or positive denominator hypotheses.
-/

noncomputable section
namespace Rho5.Algebraic.AlphaRoot

set_option maxRecDepth 32768

/-- Reversal of the nine negative coefficients, with denominators cleared. -/
theorem negative_reversal_identity (t : ℝ) (ht : t ≠ 0) :
    evalInts Data.negativeCoefficients t =
      t^8 * evalInts Data.reversedNegativeCoefficients (1/t) := by
  norm_num [Data.negativeCoefficients, Data.reversedNegativeCoefficients, evalInts]
  field_simp [ht]
  <;> ring

theorem transformed_eq_scaled (t : ℝ) (ht : t ≠ 0) :
    transformedPolynomial t = t^8 * scaledTransform t := by
  unfold transformedPolynomial scaledTransform
  rw [negative_reversal_identity t ht]
  ring

theorem scaledTransform_strict {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    scaledTransform s < scaledTransform t := by
  have ht : 0 < t := lt_trans hs hst
  have hpos : 0 < evalInts Data.positiveCoefficients s :=
    positive_horner_pos (le_of_lt hs)
  have hmono : evalInts Data.positiveCoefficients s ≤
      evalInts Data.positiveCoefficients t :=
    evalInts_mono Data.positiveCoefficients positive_coefficients_nonneg
      (le_of_lt hs) (le_of_lt hst)
  have hfirst : s * evalInts Data.positiveCoefficients s <
      t * evalInts Data.positiveCoefficients t :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right hst hpos)
      (mul_le_mul_of_nonneg_left hmono (le_of_lt ht))
  have hinv : 1/t ≤ 1/s := one_div_le_one_div_of_le hs (le_of_lt hst)
  have hsecond : evalInts Data.reversedNegativeCoefficients (1/t) ≤
      evalInts Data.reversedNegativeCoefficients (1/s) :=
    evalInts_mono Data.reversedNegativeCoefficients
      reversed_negative_coefficients_nonneg
      (le_of_lt (one_div_pos.mpr ht)) hinv
  unfold scaledTransform
  linarith only [hfirst, hsecond]

theorem scaledTransform_zero_of_root (t : ℝ) (ht : 0 < t)
    (hroot : transformedPolynomial t = 0) : scaledTransform t = 0 := by
  have hprod : t^8 * scaledTransform t = 0 := by
    rw [← transformed_eq_scaled t (ne_of_gt ht), hroot]
  exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 8 (ne_of_gt ht))

theorem transformed_positive_root_unique (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hqs : transformedPolynomial s = 0) (hqt : transformedPolynomial t = 0) : s = t := by
  have hss := scaledTransform_zero_of_root s hs hqs
  have hst := scaledTransform_zero_of_root t ht hqt
  rcases lt_trichotomy s t with h | h | h
  · have hbad := scaledTransform_strict hs h
    rw [hss, hst] at hbad
    exact False.elim ((lt_irrefl (0 : ℝ)) hbad)
  · exact h
  · have hbad := scaledTransform_strict ht h
    rw [hst, hss] at hbad
    exact False.elim ((lt_irrefl (0 : ℝ)) hbad)

/-- Polynomial transformation with its actual denominator qualification. -/
theorem mobius_identity (g t : ℝ) (ht : 0 < t)
    (hgt : g * (1+t) = 4+5*t) :
    transformedPolynomial t = (1+t)^61 * rootPolynomial g := by
  have hhom := homogenized_eval Data.pTail0 g (4+5*t) (1+t) hgt
  rw [pTail_length_0, mobius_homogenized_identity] at hhom
  have heq : (1+t) * transformedPolynomial t =
      (1+t) * ((1+t)^61 * rootPolynomial g) := by
    calc
      (1+t) * transformedPolynomial t = (1+t)^62 * evalInts Data.pTail0 g := hhom
      _ = (1+t) * ((1+t)^61 * rootPolynomial g) := by
        unfold rootPolynomial
        ring
  have hv : (1+t : ℝ) ≠ 0 := ne_of_gt (by linarith)
  exact mul_left_cancel₀ hv heq

/-- The task's explicitly stated fractional version. -/
theorem mobius_fraction_identity (t : ℝ) (ht : 0 < t) :
    transformedPolynomial t = (1+t)^61 * rootPolynomial ((4+5*t)/(1+t)) := by
  apply mobius_identity _ t ht
  have hv : (1+t : ℝ) ≠ 0 := ne_of_gt (by linarith)
  exact div_mul_cancel₀ _ hv

def mobiusParameter (g : ℝ) : ℝ := (g-4)/(5-g)

theorem mobiusParameter_pos (g : ℝ) (hl : 4 < g) (hu : g < 5) :
    0 < mobiusParameter g := by
  exact div_pos (sub_pos.mpr hl) (sub_pos.mpr hu)

theorem mobiusParameter_relation (g : ℝ) (hu : g < 5) :
    g * (1+mobiusParameter g) = 4+5*mobiusParameter g := by
  have hd : (5-g : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  unfold mobiusParameter
  field_simp [hd]
  <;> ring

theorem transformed_root_of_root (g : ℝ) (hl : 4 < g) (hu : g < 5)
    (hg : rootPolynomial g = 0) : transformedPolynomial (mobiusParameter g) = 0 := by
  rw [mobius_identity g (mobiusParameter g) (mobiusParameter_pos g hl hu)
    (mobiusParameter_relation g hu), hg, mul_zero]

/-- At most one root in the full published interval, not only the tiny bracket. -/
theorem roots_eq_on_four_five (g h : ℝ)
    (hgl : 4 < g) (hgu : g < 5) (hhl : 4 < h) (hhu : h < 5)
    (hgp : rootPolynomial g = 0) (hhp : rootPolynomial h = 0) : g = h := by
  have ht := transformed_positive_root_unique (mobiusParameter g) (mobiusParameter h)
    (mobiusParameter_pos g hgl hgu) (mobiusParameter_pos h hhl hhu)
    (transformed_root_of_root g hgl hgu hgp)
    (transformed_root_of_root h hhl hhu hhp)
  have hgd : (5-g : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hgu)
  have hhd : (5-h : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hhu)
  change (g-4)/(5-g) = (h-4)/(5-h) at ht
  have hcross : (g-4)*(5-h) = (h-4)*(5-g) := (div_eq_div_iff hgd hhd).mp ht
  nlinarith only [hcross]

end Rho5.Algebraic.AlphaRoot
