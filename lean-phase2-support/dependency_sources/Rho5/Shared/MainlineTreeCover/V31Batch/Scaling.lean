import Rho5.Shared.MainlineTreeCover.V31Batch.TerminalBridge

/-!
M02 scaling adapter for the actual V31 integer lattice. Original coordinates
use U*x and shared-product coordinates use U^2*x_i*x_j. The positive diagonal
factors therefore cannot be replaced by a single scalar. This module only
transports feasibility; it neither generates source rows nor proves a new
terminal-checker rule. Those responsibilities remain C03 and D135.
-/
namespace Rho5.Shared.MainlineTreeCover.V31Batch

open Rho5.Shared.CertificateRules
open scoped BigOperators

namespace TerminalData

def scaledSystem (d : TerminalData) (ho : d.Ordered)
    (s : Fin d.lo.length → ℚ) (hs : ∀ j, 0 < s j) (b : ℚ) :
    Rational.RatSystem (Fin d.weights.length) (Fin d.lo.length) where
  lo := fun j => ((d.system ho).lo j : ℚ) / s j
  hi := fun j => ((d.system ho).hi j : ℚ) / s j
  lo_le_hi := fun j => div_le_div_of_nonneg_right
    (by exact_mod_cast (d.system ho).lo_le_hi j) (le_of_lt (hs j))
  rows := fun i j => (((d.system ho).rows i j : ℚ) * s j) / b
  rhs := fun i => ((d.system ho).rhs i : ℚ) / b

theorem feasible_scaledSystem (d : TerminalData) (ho : d.Ordered)
    (s : Fin d.lo.length → ℚ) (hs : ∀ j, 0 < s j) (b : ℚ) (hb : 0 < b)
    (z : Fin d.lo.length → ℝ)
    (hz : Rational.FeasibleR (d.scaledSystem ho s hs b) z) :
    FeasibleR (d.system ho) (fun j => (s j : ℝ) * z j) := by
  obtain ⟨hbox, hrows⟩ := hz
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  refine ⟨fun j => ?_, fun i => ?_⟩
  · have hsR : (0 : ℝ) < (s j : ℝ) := by exact_mod_cast hs j
    have hsne : (s j : ℝ) ≠ 0 := ne_of_gt hsR
    obtain ⟨hl, hu⟩ := hbox j
    simp only [scaledSystem] at hl hu
    have hlo : (s j : ℝ) * ((((d.system ho).lo j : ℚ) / s j : ℚ) : ℝ)
        = ((d.system ho).lo j : ℝ) := by
      rw [Rat.cast_div]
      push_cast
      field_simp [hsne]
    have hhi : (s j : ℝ) * ((((d.system ho).hi j : ℚ) / s j : ℚ) : ℝ)
        = ((d.system ho).hi j : ℝ) := by
      rw [Rat.cast_div]
      push_cast
      field_simp [hsne]
    constructor
    · have h := mul_le_mul_of_nonneg_left hl (le_of_lt hsR)
      rwa [hlo] at h
    · have h := mul_le_mul_of_nonneg_left hu (le_of_lt hsR)
      rwa [hhi] at h
  · have hh := mul_le_mul_of_nonneg_left (hrows i) (le_of_lt hbR)
    simp only [scaledSystem] at hh
    rw [Finset.mul_sum] at hh
    have hrhs : (b : ℝ) * ((((d.system ho).rhs i : ℚ) / b : ℚ) : ℝ)
        = ((d.system ho).rhs i : ℝ) := by
      rw [Rat.cast_div]
      push_cast
      field_simp [hbne]
    have hsum :
        (∑ j, (b : ℝ) * (((((d.system ho).rows i j : ℚ) * s j) / b : ℚ) : ℝ) * z j)
        = ∑ j, ((d.system ho).rows i j : ℝ) * ((s j : ℝ) * z j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Rat.cast_div, Rat.cast_mul]
      push_cast
      field_simp [hbne]
      <;> ring
    rw [hrhs] at hh
    have hsum' :
        (∑ j, (b : ℝ) * ((((((d.system ho).rows i j : ℚ) * s j) / b : ℚ) : ℝ) * z j))
        = ∑ j, ((d.system ho).rows i j : ℝ) * ((s j : ℝ) * z j) := by
      simpa only [mul_assoc] using hsum
    rwa [hsum'] at hh

theorem scaled_empty_real (d : TerminalData) (hshape : d.Shape) (ho : d.Ordered)
    (hw : d.Nonnegative) (hc : d.check = true)
    (s : Fin d.lo.length → ℚ) (hs : ∀ j, 0 < s j) (b : ℚ) (hb : 0 < b) :
    ∀ z : Fin d.lo.length → ℝ, ¬ Rational.FeasibleR (d.scaledSystem ho s hs b) z := by
  intro z hz
  exact d.empty_real hshape ho hw hc _ (d.feasible_scaledSystem ho s hs b hb z hz)

end TerminalData
end Rho5.Shared.MainlineTreeCover.V31Batch
