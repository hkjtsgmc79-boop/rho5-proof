import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# D85 — the pure scalar double-envelope closure to `4`

For the two-piece envelope `phi(t) = if t ≤ 1 then 2*t else t*(3-t)` (written out
explicitly here, no new named definition), the card's scalar fact is

`∀ p t : ℝ, 0 ≤ p → p ≤ 2 → 0 ≤ t → t ≤ 2 → p*t ≤ phi(p) → p*phi(t) ≤ 4`,

with `p = 0` and `t = 0` included.  The proof follows the card's short route, in explicit
branches:

* `p ≤ 3/2`: `phi(t) ≤ 9/4` on `[0,2]`, so `p*phi(t) ≤ (3/2)*(9/4) = 27/8 ≤ 4`;
* `p > 3/2`: `phi(p) = p*(3-p)`, so `p*t ≤ p*(3-p)` gives `t ≤ 3-p < 3/2`; on `[0,3/2]` the
  map `q ↦ q*(3-q)` is increasing, so `phi(t) ≤ t*(3-t) ≤ (3-p)*(3-(3-p)) = p*(3-p)`, and
  finally `p * (p*(3-p)) ≤ 4` because `4 - p²(3-p) = (2-p)²(p+1) ≥ 0`.

This is a **pure scalar** statement: it says nothing about the actual fourth pivot of any
matrix (`r ≤ 4` is not claimed here).  The receipt records that explicitly.
-/

namespace Rho5.DoubleThreePivotEnvelope

/-- The envelope is nonnegative on `[0, 2]`. -/
theorem phi_nonneg {t : ℝ} (h0 : 0 ≤ t) (_h2 : t ≤ 2) :
    0 ≤ (if t ≤ 1 then 2 * t else t * (3 - t)) := by
  split_ifs with h1
  · linarith
  · exact mul_nonneg h0 (by linarith)

/-- The envelope never exceeds `9/4` on `[0, 2]` (its maximum is at `t = 3/2`). -/
theorem phi_le_nine_quarters {t : ℝ} (_h2 : t ≤ 2) :
    (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ 9 / 4 := by
  split_ifs with h1
  · linarith
  · nlinarith [sq_nonneg (t - 3 / 2)]

/-- Below the kink the envelope is dominated by the concave piece. -/
theorem phi_le_concave {t : ℝ} (_h0 : 0 ≤ t) :
    (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ t * (3 - t) := by
  split_ifs with h1
  · nlinarith
  · exact le_rfl

/-- `q ↦ q*(3-q)` is increasing on `[0, 3/2]`. -/
theorem concave_mono {t s : ℝ} (_h0 : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 3 / 2) :
    t * (3 - t) ≤ s * (3 - s) := by
  have h1 : 0 ≤ s - t := sub_nonneg.mpr hts
  have h2 : 0 ≤ 3 - s - t := by linarith
  nlinarith [mul_nonneg h1 h2]

/-- The cubic profile is bounded by `4` on `[0, 2]`, with the explicit difference
`4 - p*(p*(3-p)) = (2-p)^2 * (p+1)`. -/
theorem self_mul_three_sub_le_four {p : ℝ} (h0 : 0 ≤ p) (_h2 : p ≤ 2) :
    p * (p * (3 - p)) ≤ 4 := by
  nlinarith [sq_nonneg (2 - p), h0]

/-- **The card's theorem.**  Under `0 ≤ p ≤ 2`, `0 ≤ t ≤ 2` and the single coupling
hypothesis `p*t ≤ phi(p)`, the product `p*phi(t)` is at most `4`; `p = 0` and `t = 0` are
included, and the bound is attained at `p = 2`, `t = 1`. -/
theorem double_envelope_le_four (p t : ℝ) (hp0 : 0 ≤ p) (_hp2 : p ≤ 2) (ht0 : 0 ≤ t)
    (ht2 : t ≤ 2) (h : p * t ≤ (if p ≤ 1 then 2 * p else p * (3 - p))) :
    p * (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ 4 := by
  by_cases hp : p ≤ 3 / 2
  · have hphi : (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ 9 / 4 := phi_le_nine_quarters ht2
    have hnon : 0 ≤ (if t ≤ 1 then 2 * t else t * (3 - t)) := phi_nonneg ht0 ht2
    have h1 : p * (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ (3 / 2) * (9 / 4) :=
      mul_le_mul hp hphi hnon (by norm_num)
    linarith
  · have hp32 : 3 / 2 < p := not_le.mp hp
    have hp1 : ¬ p ≤ 1 := by linarith
    rw [if_neg hp1] at h
    have ht : t ≤ 3 - p := by nlinarith [h, hp32]
    have hs : 3 - p ≤ 3 / 2 := by linarith
    have hstep : (if t ≤ 1 then 2 * t else t * (3 - t)) ≤ (3 - p) * (3 - (3 - p)) :=
      (phi_le_concave ht0).trans (concave_mono ht0 ht hs)
    have hmul : p * (if t ≤ 1 then 2 * t else t * (3 - t)) ≤
        p * ((3 - p) * (3 - (3 - p))) :=
      mul_le_mul_of_nonneg_left hstep hp0
    have hfin : p * ((3 - p) * (3 - (3 - p))) ≤ 4 := by
      nlinarith [sq_nonneg (2 - p), hp0]
    linarith

end Rho5.DoubleThreePivotEnvelope
