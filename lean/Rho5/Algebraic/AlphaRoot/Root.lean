import Rho5.Algebraic.AlphaRoot.EndpointSigns
import Rho5.Algebraic.AlphaRoot.Uniqueness
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual RHO5 algebraic constant

The definition of alpha is chosen from a proved exact-interval existence
statement. There is no external root-existence, uniqueness, or RootSpec
parameter in this module.
-/

noncomputable section
namespace Rho5.Algebraic.AlphaRoot

theorem exists_root_in_exact_interval :
    ∃ a : ℝ, alphaLower < a ∧ a < alphaUpper ∧ rootPolynomial a = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Ioo (rootPolynomial alphaLower) (rootPolynomial alphaUpper) :=
    ⟨rootPolynomial_lower_neg, rootPolynomial_upper_pos⟩
  obtain ⟨a, ha, hroot⟩ :=
    intermediate_value_Ioo (le_of_lt alphaLower_lt_alphaUpper)
      rootPolynomial_continuous.continuousOn hzero
  exact ⟨a, ha.1, ha.2, hroot⟩

noncomputable def alpha : ℝ := Classical.choose exists_root_in_exact_interval

theorem alpha_properties :
    alphaLower < alpha ∧ alpha < alphaUpper ∧ rootPolynomial alpha = 0 :=
  Classical.choose_spec exists_root_in_exact_interval

theorem alpha_in_exact_interval : alphaLower < alpha ∧ alpha < alphaUpper :=
  ⟨alpha_properties.1, alpha_properties.2.1⟩

theorem alpha_is_root : rootPolynomial alpha = 0 := alpha_properties.2.2

theorem alpha_gt_four : (4 : ℝ) < alpha :=
  lt_trans four_lt_alphaLower alpha_in_exact_interval.1

theorem alpha_lt_five : alpha < (5 : ℝ) :=
  lt_trans alpha_in_exact_interval.2 alphaUpper_lt_five

theorem root_unique (t : ℝ) (hl : 4 < t) (hu : t < 5)
    (hroot : rootPolynomial t = 0) : t = alpha :=
  roots_eq_on_four_five t alpha hl hu alpha_gt_four alpha_lt_five hroot alpha_is_root

theorem exists_unique_root :
    ∃! a : ℝ, 4 < a ∧ a < 5 ∧ rootPolynomial a = 0 := by
  refine ⟨alpha, ⟨alpha_gt_four, alpha_lt_five, alpha_is_root⟩, ?_⟩
  intro a ha
  exact root_unique a ha.1 ha.2.1 ha.2.2

end Rho5.Algebraic.AlphaRoot
