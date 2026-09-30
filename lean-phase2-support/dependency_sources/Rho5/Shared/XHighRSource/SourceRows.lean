import Rho5.Shared.XHighRSource.PRules

/-!
# D145 stage B — the two high diagrams' actual source rows

`I200_210_high` (type I) and `II200_210_high` (type II) are the two actual roots of the archived
V34 high package.  This module carries their **exact source rows**, as read from
`fixed_source/models/{I200_210_high,II200_210_high}/model.json` (23 variables: the 22 X22
coordinates `k,r,w,A,B,c,d,p,e,be,u0..2,x0..2,v0..2,q0..2` plus the head product `G`), and pays the
parts of them that are Lean-level statements:

* the **head dictionary**: type I binds `G = e * beta` (`G_def+`/`G_def-` with `G_factor_1 = be`),
  type II binds `G = e * u0` (`factor_oracle.hpp` `HEAD_TYPE`), and the real transpose maps the two
  into each other: `G_I` is transpose-invariant while `G_II` becomes `beta * v0`;
* the seven `high_*` rows (`high_r_outer`, `high_rBc`, `high_rAc`, `high_rAd`, `high_gap_B`,
  `high_rank_product`, `high_rank_symmetric`) and the three inherited rational `r` tangents
  (`r_tangent_1..3`), stated on the actual coordinates with their exact polynomials;
* the archived **nonnegative decompositions** of the two rank-product rows, re-expanded and proved
  by `ring` (`NEW_MODEL_SCOPES.md`), plus the nonnegativity corollaries from explicit core slacks.

The row *certificates themselves* (why an actual high source satisfies `high_*`) come from the
supplied handoff Appendix A §§5,8; they are carried here as explicit hypotheses (`HighSourceRows`,
`CoreSlacks`) and never assumed globally.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.Shared.V43MatrixRoundTrip

/-- The archived high-branch `J = 21/10` (`model.json` `J`). -/
def Jhigh : ℝ := 21 / 10

/-- The two actual high roots' head types (`model.json` `type`). -/
inductive HeadType where
  | I
  | II
  deriving DecidableEq, Repr

/-! ## 1. The 23-variable model dictionary -/

/-- The head product `G` of each head type: `G = e * beta` (type I), `G = e * u0` (type II). -/
def Gmodel (M : M5) : HeadType → ℝ
  | .I => eX M * betaX M
  | .II => eX M * uX M 0

/-- **The actual 23-variable source dictionary** of the two models, in the archived variable
order. -/
def modelVec (M : M5) (ht : HeadType) : Fin 23 → ℝ
  | 0 => kX M
  | 1 => rX M
  | 2 => wX M
  | 3 => aX M
  | 4 => bX M
  | 5 => cX M
  | 6 => dX M
  | 7 => pX M
  | 8 => eX M
  | 9 => betaX M
  | 10 => uX M 0
  | 11 => uX M 1
  | 12 => uX M 2
  | 13 => xX M 0
  | 14 => xX M 1
  | 15 => xX M 2
  | 16 => vX M 0
  | 17 => vX M 1
  | 18 => vX M 2
  | 19 => qX M 0
  | 20 => qX M 1
  | 21 => qX M 2
  | 22 => Gmodel M ht
  | _ => 0

/-- The type-II head product is the module's `Ghead`. -/
theorem Gmodel_II_eq (M : M5) : Gmodel M .II = Ghead M := rfl

/-- The type-I head product `e * beta`. -/
theorem Gmodel_I_eq (M : M5) : Gmodel M .I = eX M * betaX M := rfl

/-- **Type I's head product is transpose-invariant**: the real transpose exchanges `e` and `beta`. -/
theorem Gmodel_I_transX (M : M5) : Gmodel (transX M) .I = Gmodel M .I := by
  simp only [Gmodel, eX_transX, betaX_transX]
  ring

/-- **Type II's head product becomes `beta * v0`** under the real transpose, exactly as the
archived report records (`G = e_new * u0_new = beta_old * v0_old`). -/
theorem Gmodel_II_transX (M : M5) : Gmodel (transX M) .II = GheadTranspose M := by
  simp only [Gmodel, GheadTranspose, eX_transX, uX_transX]
  simp [sgnZ]

/-! ## 2. The actual `high_*` source rows -/

/-- The seven added high-branch rows of `NEW_MODEL_SCOPES.md` / `model.json`, on the actual
coordinates: `r ≥ k`, `k - B - r ≥ 0`, `k(1+c) - r ≥ 0`, `k(1+d) - r ≥ 0`,
`2k - r + w - B ≥ 0`, `-J d B - (r-k)^2 ≥ 0`, `-J c A - (r-k)^2 ≥ 0`. -/
def HighSourceRows (M : M5) : Prop :=
  0 ≤ rX M - kX M ∧
  0 ≤ kX M - bX M - rX M ∧
  0 ≤ kX M * (1 + cX M) - rX M ∧
  0 ≤ kX M * (1 + dX M) - rX M ∧
  0 ≤ 2 * kX M - rX M + wX M - bX M ∧
  0 ≤ -(Jhigh * bX M * dX M) - (rX M - kX M) ^ 2 ∧
  0 ≤ -(Jhigh * aX M * cX M) - (rX M - kX M) ^ 2

/-- The closed outer box (`high_r_outer` plus the roots' `K = 2`): the archived models use
`k ≥ 2`, `r ≥ k`, and `A,B ≤ 0 ≤ c,d`. -/
def ClosedOuterBox (M : M5) : Prop :=
  2 ≤ kX M ∧ kX M ≤ 21 / 10 ∧ kX M ≤ rX M

/-- The actual strict high-`r` source lies in the models' closed outer box. -/
theorem highDomain_closedOuter (M : M5) (h : HighRDomain (extractX M)) : ClosedOuterBox M :=
  ⟨h.1.le, h.2.1, h.2.2.1.le⟩

/-- `high_r_outer` (`r ≥ k`) is exactly the closed-outer-box tail. -/
theorem high_r_outer_of_closed (M : M5) (h : ClosedOuterBox M) : 0 ≤ rX M - kX M := by
  linarith [h.2.2]

/-- The three inherited rational tangents on `r` (`r_tangent_1..3`), as upper bounds. -/
def RTangents (M : M5) : Prop :=
  rX M ≤ 6075 / 1024 - 15 / 16 * kX M ∧
  rX M ≤ 972 / 125 - 9 / 5 * kX M ∧
  rX M ≤ 1225 / 128 - 21 / 8 * kX M

/-! ## 3. The archived nonnegative decompositions of the rank-product rows -/

/-- `J d b - t^2 = (J - chi) d b + (c b - t) d a + t (d a - t)`, with `a = -A`, `b = -B`,
`t = r - k`, `chi = c a`, in the exact shape of the archived row `high_rank_product`. -/
theorem rank_product_decomp_dB (M : M5) :
    -(Jhigh * bX M * dX M) - (rX M - kX M) ^ 2
      = (Jhigh - cX M * (-(aX M))) * dX M * (-(bX M))
        + (cX M * (-(bX M)) - (rX M - kX M)) * dX M * (-(aX M))
        + (rX M - kX M) * (dX M * (-(aX M)) - (rX M - kX M)) := by
  ring

/-- `J chi - t^2 = (J - t) chi + t (chi - t)`, the symmetric rank-product row
`high_rank_symmetric`. -/
theorem rank_product_decomp_symmetric (M : M5) :
    -(Jhigh * aX M * cX M) - (rX M - kX M) ^ 2
      = (Jhigh - (rX M - kX M)) * (cX M * (-(aX M)))
        + (rX M - kX M) * (cX M * (-(aX M)) - (rX M - kX M)) := by
  ring

/-- The core-band slacks the archived decomposition feeds on: `t = r - k ≥ 0`,
`c b ≥ t`, `d a ≥ t`, `c a ≥ t`, `c a ≤ J`, `t ≤ J`, `d b ≥ 0`, `c a ≥ 0`
(`NEW_MODEL_SCOPES.md`: "the rank-product rows have explicit nonnegative decompositions"; each
factor's nonnegativity comes from the actual high-branch core band). -/
def CoreSlacks (M : M5) : Prop :=
  0 ≤ rX M - kX M ∧
  0 ≤ cX M * (-(bX M)) - (rX M - kX M) ∧
  0 ≤ dX M * (-(aX M)) - (rX M - kX M) ∧
  0 ≤ cX M * (-(aX M)) - (rX M - kX M) ∧
  0 ≤ Jhigh - cX M * (-(aX M)) ∧
  0 ≤ Jhigh - (rX M - kX M) ∧
  0 ≤ dX M * (-(bX M)) ∧
  0 ≤ cX M * (-(aX M))

/-- **`high_rank_product` from the archived nonnegative decomposition**: every summand of the
decomposition is nonnegative on the core band, so the row holds. -/
theorem high_rank_product_of_slacks (M : M5) (h : CoreSlacks M) :
    0 ≤ -(Jhigh * bX M * dX M) - (rX M - kX M) ^ 2 := by
  obtain ⟨ht, hcb, hda, hca, hchi_J, ht_J, hdb, hchi⟩ := h
  have h1' : 0 ≤ (Jhigh - cX M * (-(aX M))) * dX M * (-(bX M)) := by
    have hh : 0 ≤ (Jhigh - cX M * (-(aX M))) * (dX M * (-(bX M))) := mul_nonneg hchi_J hdb
    calc (0 : ℝ) ≤ (Jhigh - cX M * (-(aX M))) * (dX M * (-(bX M))) := hh
      _ = (Jhigh - cX M * (-(aX M))) * dX M * (-(bX M)) := by ring
  have h2' : 0 ≤ (cX M * (-(bX M)) - (rX M - kX M)) * dX M * (-(aX M)) := by
    have hda0 : 0 ≤ dX M * (-(aX M)) := by linarith
    have hh : 0 ≤ (cX M * (-(bX M)) - (rX M - kX M)) * (dX M * (-(aX M))) := mul_nonneg hcb hda0
    calc (0 : ℝ) ≤ (cX M * (-(bX M)) - (rX M - kX M)) * (dX M * (-(aX M))) := hh
      _ = (cX M * (-(bX M)) - (rX M - kX M)) * dX M * (-(aX M)) := by ring
  have h3' : 0 ≤ (rX M - kX M) * (dX M * (-(aX M)) - (rX M - kX M)) := mul_nonneg ht hda
  rw [rank_product_decomp_dB]
  linarith [h1', h2', h3']

/-- **`high_rank_symmetric` from the archived nonnegative decomposition**. -/
theorem high_rank_symmetric_of_slacks (M : M5) (h : CoreSlacks M) :
    0 ≤ -(Jhigh * aX M * cX M) - (rX M - kX M) ^ 2 := by
  obtain ⟨ht, hcb, hda, hca, hchi_J, ht_J, hdb, hchi⟩ := h
  have h2' : 0 ≤ (Jhigh - (rX M - kX M)) * (cX M * (-(aX M))) := mul_nonneg ht_J hchi
  have h3' : 0 ≤ (rX M - kX M) * (cX M * (-(aX M)) - (rX M - kX M)) := mul_nonneg ht hca
  rw [rank_product_decomp_symmetric]
  linarith [h2', h3']

end

end Rho5.Shared.XHighRSource
