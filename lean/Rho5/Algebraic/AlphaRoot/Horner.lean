import Mathlib.Data.Real.Basic
-- D09 API fix (2026-09-11): the frozen pilot's selective mathlib cache has no
-- `Mathlib.Topology.Instances.Real.Lemmas` (that directory holds only
-- `Lemmas.lean`, whose transitive closure needs 19 modules absent from the
-- cache: CharP/ZMod/Complex/...).  `Mathlib.Topology.Algebra.Ring.Real` is
-- present and supplies the same topological-field structure on ℝ that the
-- continuity arguments below use; this is an import narrowing only, no
-- statement or proof change.
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Ring.Basic
-- D09 API fix (2026-09-11): `Mathlib.Data.List.Basic` publicly imports
-- `Mathlib.Tactic.Common`, which publicly imports `Mathlib.Tactic.FunProp`,
-- which imports `Mathlib.Analysis.Complex.Trigonometric`; that subtree (9
-- modules) is absent from the frozen cache.  `Mathlib.Data.List.Defs` is
-- present and supplies the list API used here (core/Batteries lemmas).
import Mathlib.Data.List.Defs
import Mathlib.Tactic.Ring

/-!
# Small real semantics for concrete integer coefficient lists

Coefficients are stored in ascending order. `homogenized` deliberately has
homogeneous degree `cs.length`, one higher than the usual degree: this makes
its recursion and its identity with Horner evaluation valid also for `[]`.
No polynomial identity or sign certificate is assumed by this module.
-/

noncomputable section
namespace Rho5.Algebraic.AlphaRoot

def evalInts : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evalInts cs x

def homogenized : List ℤ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, u, v => (c : ℝ) * v ^ (cs.length + 1) + u * homogenized cs u v

theorem evalInts_continuous (cs : List ℤ) : Continuous (evalInts cs) := by
  induction cs with
  | nil =>
      change Continuous (fun _ : ℝ => (0 : ℝ))
      exact continuous_const
  | cons c cs ih =>
      change Continuous (fun x : ℝ => (c : ℝ) + x * evalInts cs x)
      exact continuous_const.add (continuous_id.mul ih)

theorem evalInts_nonneg (cs : List ℤ) :
    (∀ c ∈ cs, (0 : ℝ) ≤ (c : ℝ)) →
      ∀ {x : ℝ}, 0 ≤ x → 0 ≤ evalInts cs x := by
  induction cs with
  | nil =>
      intro _ x _
      exact le_rfl
  | cons c cs ih =>
      intro hc x hx
      have hhead : (0 : ℝ) ≤ (c : ℝ) := hc c (by simp)
      have htail : ∀ k ∈ cs, (0 : ℝ) ≤ (k : ℝ) := by
        intro k hk
        exact hc k (List.mem_cons_of_mem c hk)
      change 0 ≤ (c : ℝ) + x * evalInts cs x
      exact add_nonneg hhead (mul_nonneg hx (ih htail hx))

theorem evalInts_mono (cs : List ℤ) :
    (∀ c ∈ cs, (0 : ℝ) ≤ (c : ℝ)) →
      ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → evalInts cs s ≤ evalInts cs t := by
  induction cs with
  | nil =>
      intro _ s t _ _
      exact le_rfl
  | cons c cs ih =>
      intro hc s t hs hst
      have htail : ∀ k ∈ cs, (0 : ℝ) ≤ (k : ℝ) := by
        intro k hk
        exact hc k (List.mem_cons_of_mem c hk)
      have hsval : 0 ≤ evalInts cs s := evalInts_nonneg cs htail hs
      have ht : 0 ≤ t := le_trans hs hst
      change (c : ℝ) + s * evalInts cs s ≤ (c : ℝ) + t * evalInts cs t
      -- D09 API fix: in the frozen environment `add_le_add_left h a : b + a ≤ c + a`
      -- and `add_le_add_right h a : a + b ≤ a + c` (constant added on the right/left
      -- of the expression respectively); the constant here is added on the left.
      exact add_le_add_right (mul_le_mul hst (ih htail hs hst) hsval ht) _

theorem evalInts_pos_of_head (c : ℤ) (cs : List ℤ)
    (hc : (0 : ℝ) < (c : ℝ))
    (htail : ∀ k ∈ cs, (0 : ℝ) ≤ (k : ℝ))
    {x : ℝ} (hx : 0 ≤ x) : 0 < evalInts (c :: cs) x := by
  change 0 < (c : ℝ) + x * evalInts cs x
  exact add_pos_of_pos_of_nonneg hc (mul_nonneg hx (evalInts_nonneg cs htail hx))

theorem horner_upper_step (c : ℤ) (cs : List ℤ) (x b B : ℝ)
    (hx : 0 ≤ x) (hb : evalInts cs x ≤ b)
    (hround : (c : ℝ) + x * b ≤ B) : evalInts (c :: cs) x ≤ B := by
  change (c : ℝ) + x * evalInts cs x ≤ B
  exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_left hb hx) _) hround

theorem horner_lower_step (c : ℤ) (cs : List ℤ) (x b B : ℝ)
    (hx : 0 ≤ x) (hb : b ≤ evalInts cs x)
    (hround : B ≤ (c : ℝ) + x * b) : B ≤ evalInts (c :: cs) x := by
  change B ≤ (c : ℝ) + x * evalInts cs x
  exact le_trans hround (add_le_add_right (mul_le_mul_of_nonneg_left hb hx) _)

/-- Exact algebraic identity, including the zero-denominator case as a polynomial relation. -/
theorem homogenized_eval (cs : List ℤ) (g u v : ℝ) (hgv : g * v = u) :
    homogenized cs u v = v ^ cs.length * evalInts cs g := by
  induction cs with
  | nil =>
      simp only [homogenized, evalInts, List.length_nil, pow_zero, mul_zero]
  | cons c cs ih =>
      simp only [homogenized, evalInts, List.length_cons]
      rw [ih, ← hgv]
      simp only [pow_succ]
      ring

end Rho5.Algebraic.AlphaRoot
