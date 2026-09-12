import Rho5.Shared.BNormalizationInterface.HeadBound
import Rho5.Shared.SchurFourPivotBound.Bound
import Rho5.Shared.BHeadSign
import Rho5.Shared.PaperB17RootEntry.Entry

/-!
# D141 — the actual `ProperB` high source and the bridges it needs

This lane assembles the accepted conditional layers into one *actual-matrix* statement: from
`LeadingInput M`, `ProperB M` and `alpha < TS.height M` it reaches a real, same-height B17 root
representative of `M` itself.  Nothing is left conditional: the old `ResidualGap`, the
`F ≤ 4p` bound, `p > 1`, `e β > 0` and `NormalizedB` are all *paid* here, not assumed.

The layers it consumes (read-only, already compiled and audited):

| step | provider |
|---|---|
| `Qualified (extract M)` | D130 `Rho5.Shared.BNormalizationInterface.qualified_extract_of_properB` |
| `height M ≤ 4 * p M` | D138 `Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p` |
| `1 < p M` | D130 `one_lt_p_of_four_lt_F`, using D138 and `alpha_gt_four` |
| `0 < e β` | D130 `e_mul_beta_pos_of_four_lt_F` |
| head normalization | D137 `Rho5.Shared.BHeadSign.qualified_high_head_has_normalized_representative` |
| complete 17-dim root | D134 `Rho5.Shared.PaperB17RootEntry.high_normalizedB_has_canonical_root_representative` |
| `reconstruct (extract M) = M` | the frozen extraction bridge `Rho5.Certificate.B24Extraction.reconstruct_extract` |

This file contains the paid scalar readings and the honest sign-composition lemma; `Assembly`
performs the assembly and states the exported theorem.
-/

namespace Rho5.Shared.ActualBRootEntry

open Rho5 (Matrix5)
open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Extraction (extract F p k r s t)
open Rho5.ExternalTailSaturation (LeadingInput ProperB height)

noncomputable section

/-! ## 1. The extraction bridge and the height readings -/

/-- **`reconstruct (extract M) = M` for a proper-B source.**  The frozen extraction bridge
`B24Extraction.reconstruct_extract` needs exactly the data `LeadingInput`/`ProperB` supply:
`M 0 0 = 1` (the head normalization), `p M ≠ 0`, `k M ≠ 0`, and the balanced tail
`T2 M 1 1 = -r M` (which is `ProperB.w_eq`, definitionally).  This is what makes every later
sign statement a statement about the *original* `M`, not about an arbitrary reconstruction. -/
theorem reconstruct_extract_eq (M : Matrix5) (h : LeadingInput M) (hb : ProperB M) :
    Rho5.Certificate.B24Reconstruction.reconstruct (extract M) = M :=
  Rho5.Certificate.B24Extraction.reconstruct_extract M h.head (ne_of_gt h.p_pos) (ne_of_gt h.k_pos)
    hb.w_eq

/-- **`F M = height M` on the proper-B branch.**  The tail reading `F = r + s t / r` is the
balanced `ProperB.height_eq`; outside proper-B it is genuinely different from `|w - t s / r|`,
which is why this is a paid lemma and not a definitional rewrite. -/
theorem F_eq_height_of_properB (M : Matrix5) (hb : ProperB M) : F M = height M := by
  show Rho5.Certificate.B24Extraction.r M + Rho5.Certificate.B24Extraction.s M
      * Rho5.Certificate.B24Extraction.t M / Rho5.Certificate.B24Extraction.r M = height M
  exact hb.height_eq.symm

/-- **`4 < F M` from the actual isolation bound.**  `alpha_gt_four` is the paper's isolated
endpoint interval (`alphaLower < alpha < alphaUpper` with `4 < alphaLower`), reused here as the
card requires — no decimal approximation and no new root hypothesis. -/
theorem four_lt_F_of_high (M : Matrix5) (hb : ProperB M)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < height M) : (4 : ℝ) < F M := by
  rw [F_eq_height_of_properB M hb]
  exact lt_trans Rho5.Algebraic.AlphaRoot.alpha_gt_four hhigh

/-- **`F M ≤ 4 p M`, paid by D138** from `LeadingInput M` alone (the fourth-pivot Schur bound). -/
theorem F_le_four_mul_p_of_leadingInput (M : Matrix5) (h : LeadingInput M) (hb : ProperB M) :
    F M ≤ 4 * p M := by
  rw [F_eq_height_of_properB M hb]
  exact Rho5.Shared.SchurFourPivotBound.height_le_four_mul_p M h

/-- **`1 < p M`** on the high-value branch: the paper's `F ≤ 4p` route, with both inputs paid
above.  This is the `1 < z 8` premise D137 needs, no longer an assumption. -/
theorem one_lt_p_of_properB_high (M : Matrix5) (h : LeadingInput M) (hb : ProperB M)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < height M) : 1 < p M :=
  Rho5.Shared.BNormalizationInterface.one_lt_p_of_four_lt_F (four_lt_F_of_high M hb hhigh)
    (F_le_four_mul_p_of_leadingInput M h hb)

/-- **`0 < e · β`**, i.e. the two extracted corner signs agree: D130's head-band reading
`p - 1 ≤ e β` with the `1 < p` just paid.  This is the `0 < z 9 * z 10` premise D137 needs. -/
theorem e_mul_beta_pos_of_properB_high (M : Matrix5) (h : LeadingInput M) (hb : ProperB M)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < height M) :
    0 < Rho5.Certificate.B24Reconstruction.e (extract M)
      * Rho5.Certificate.B24Reconstruction.beta (extract M) :=
  Rho5.Shared.BNormalizationInterface.e_mul_beta_pos_of_four_lt_F h hb (four_lt_F_of_high M hb hhigh)
    (F_le_four_mul_p_of_leadingInput M h hb)

/-! ## 2. The real sign composition -/

/-- The composed sign vector of two real diagonal sign operations, entry by entry. -/
def sgMul (sg₁ sg₂ : Fin 5 → ℝ) : Fin 5 → ℝ := fun i => sg₁ i * sg₂ i

/-- A product of two `±1` sign vectors is again a `±1` sign vector. -/
theorem sgMul_eq_one_or_neg_one {sg₁ sg₂ : Fin 5 → ℝ}
    (h₁ : ∀ i, sg₁ i = 1 ∨ sg₁ i = -1) (h₂ : ∀ i, sg₂ i = 1 ∨ sg₂ i = -1) (i : Fin 5) :
    sgMul sg₁ sg₂ i = 1 ∨ sgMul sg₁ sg₂ i = -1 := by
  rcases h₁ i with h | h <;> rcases h₂ i with h' | h' <;> simp [sgMul, h, h']

/-- **The actual sign composition, entry by entry.**  If `z₀` reconstructs to the original `M`
and `z₁`, `z₂` are its successive legal diagonal sign conjugations, then `z₂` is the diagonal
sign conjugation of `M` by the composed sign vector.  The original matrix stays in the
statement: this is not a relation between two abstract reconstructions. -/
theorem reconstruct_conj_comp {M : Matrix5} {z₀ z₁ z₂ : Point} {sg₁ sg₂ : Fin 5 → ℝ}
    (hM : Rho5.Certificate.B24Reconstruction.reconstruct z₀ = M)
    (h₁ : ∀ i j, Rho5.Certificate.B24Reconstruction.reconstruct z₁ i j
      = sg₁ i * Rho5.Certificate.B24Reconstruction.reconstruct z₀ i j * sg₁ j)
    (h₂ : ∀ i j, Rho5.Certificate.B24Reconstruction.reconstruct z₂ i j
      = sg₂ i * Rho5.Certificate.B24Reconstruction.reconstruct z₁ i j * sg₂ j) :
    ∀ i j, Rho5.Certificate.B24Reconstruction.reconstruct z₂ i j
      = sgMul sg₁ sg₂ i * M i j * sgMul sg₁ sg₂ j := by
  intro i j
  have hMij : Rho5.Certificate.B24Reconstruction.reconstruct z₀ i j = M i j :=
    congrFun (congrFun hM i) j
  rw [h₂ i j, h₁ i j, hMij, sgMul, sgMul]
  ring

end

end Rho5.Shared.ActualBRootEntry
