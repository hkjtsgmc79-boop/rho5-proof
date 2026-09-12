/-
D134 — stage A: every B17 root bound from the real reconstruction
================================================================

For an arbitrary `NormalizedB z` the seventeen closed-root bounds are paid from the accepted
reconstruction `Rho5.Certificate.B24Reconstruction.reconstruct z` and the already compiled
theorems — no new premise, no re-proof of the three-pivot envelope:

* `k ≤ 9/4` — `Rho5.LastThreePivotEnvelope.k_le_nine_quarters` at the reconstruction
  (`PolyCP` from D71's `polyCP_reconstruct`), read back with `k_reconstruct : Rho5.Certificate.B24Extraction.k (reconstruct z) = z 0`;
* `4γ/9 ≤ k` — `Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k` (D87) together with
  `delta_reconstruct : δ (reconstruct z) = -z 23` and the high-value premise `alpha < z 23`, using
  `gamma_lt_alpha`; the constant stays the exact rational;
* `A`, `B` — the actual core block `D z = ![[z 0, z 4, z 5], …]` bounded by `Physical.d_bound`
  (`|D z i j| ≤ z 0 = k`), so both inherit `k ≤ 9/4`; `A ≤ 0` is the explicit sign input of stage A
  (it is discharged by D133's representative in stage B);
* `c`, `d` — `D z 1 0 = k·c`, `D z 2 0 = k·d` with `|D z i j| ≤ k` and `k > 0`;
* `u`, `x`, `v` — D28's head band (`HeadBand.abs_u/abs_x/abs_v`); `x0 ≥ 0` is the second explicit
  sign input of stage A;
* `q` — `Physical.q_bound : |q z j| ≤ z 8 = p` together with the prefix bound `p ≤ 2` from D120's
  `prefixPoint_spec`.

Nothing here uses `k ≤ 2`, drops a case, or claims `rho = alpha`.
-/
import Rho5.Shared.PaperB17RootEntry.Defs
import Rho5.Shared.LastThreePivotEnvelope.GlobalBound
import Rho5.Shared.LastThreePivotEnvelope.StageA
import Rho5.Certificate.B24MinorBridge.Witness
import Rho5.ExternalBFibreCapacity.PrefixPaths

namespace Rho5.Shared.PaperB17RootEntry

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B16 (Point D q u xv v Physical)
open Rho5.Certificate.B24Reconstruction (reconstruct reconstruct_zero_zero)
open Rho5.Certificate.B24MinorBridge (Qualified polyCP_reconstruct k_reconstruct delta_reconstruct)
open Rho5.ExternalBFibreCapacity (NormalizedB Frame frameOf frameVector frameOfVector)

/-! ## 1. The two reading lemmas -/

/-- The third B24 coordinate is positive on a normalized source. -/
theorem k_pos_of_normalizedB {z : Point} (h : NormalizedB z) : 0 < z 0 := h.1.k_pos

/-- `p z ≠ 0` on a normalized source (`1 ≤ z 8 = p z`). -/
theorem p_ne_zero_of_normalizedB {z : Point} (h : NormalizedB z) :
    Rho5.Certificate.B24Reconstruction.p z ≠ 0 := by
  have hp : (1 : ℝ) ≤ Rho5.Certificate.B24Reconstruction.p z := by
    simpa only [Rho5.Certificate.B24Reconstruction.p_coord] using h.2.1
  exact ne_of_gt (lt_of_lt_of_le one_pos hp)

/-- **The height reading**: on a normalized source the frozen `δ` of the reconstruction is
`-z 23`, hence `|δ| = z 23` as soon as the source is high-valued. -/
theorem abs_delta_reconstruct {z : Point} (h : NormalizedB z)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < z 23) :
    |Rho5.CanonicalTail.delta (reconstruct z)| = z 23 := by
  have hp := p_ne_zero_of_normalizedB h
  have hk : z 0 ≠ 0 := ne_of_gt h.1.k_pos
  have hd := delta_reconstruct z h.1.physical hp hk
  have hpos : 0 < z 23 := lt_trans (lt_trans (by norm_num : (0 : ℝ) < 4)
    Rho5.Algebraic.AlphaRoot.alpha_gt_four) hhigh
  rw [hd, abs_neg, abs_of_pos hpos]

/-! ## 2. The seventeen bounds -/

/-- **`k ≤ 9/4`**: D87's second-pivot bound at the reconstruction. -/
theorem k_le_nine_quarters_of_normalizedB {z : Point} (h : NormalizedB z) : z 0 ≤ 9 / 4 := by
  have hp := p_ne_zero_of_normalizedB h
  have hCP : Rho5.MinorCPDomain.PolyCP (reconstruct z) := polyCP_reconstruct z h.1
  have hk := Rho5.LastThreePivotEnvelope.k_le_nine_quarters (reconstruct z)
    (reconstruct_zero_zero z) hCP
  rwa [k_reconstruct z hp] at hk

/-- **`4γ/9 ≤ k`**: `|δ| ≤ (9/4)·k` (D87) with `|δ| = z 23 > alpha > gamma`. -/
theorem four_gamma_div_nine_le_k {z : Point} (h : NormalizedB z)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < z 23) : 4 * gamma / 9 ≤ z 0 := by
  have hp := p_ne_zero_of_normalizedB h
  have hCP : Rho5.MinorCPDomain.PolyCP (reconstruct z) := polyCP_reconstruct z h.1
  have hdelta := Rho5.LastThreePivotEnvelope.delta_abs_le_nine_quarters_mul_k (reconstruct z)
    (reconstruct_zero_zero z) hCP
  rw [k_reconstruct z hp, abs_delta_reconstruct h hhigh] at hdelta
  have hgamma : gamma < z 23 := lt_trans gamma_lt_alpha hhigh
  linarith

/-- **`-9/4 ≤ A`**: the actual core entry `D z 0 1 = z 4` obeys `|D| ≤ z 0 = k ≤ 9/4`. -/
theorem neg_nine_quarters_le_A {z : Point} (h : NormalizedB z) : -(9 / 4) ≤ z 4 := by
  have hD : |z 4| ≤ z 0 := by simpa only using h.1.physical.d_bound 0 1
  have hk := k_le_nine_quarters_of_normalizedB h
  have h1 := (abs_le.mp hD).1
  linarith

/-- **`|B| ≤ 9/4`**: the actual core entry `D z 0 2 = z 5`. -/
theorem abs_B_le_nine_quarters {z : Point} (h : NormalizedB z) : |z 5| ≤ 9 / 4 := by
  have hD : |z 5| ≤ z 0 := by simpa only using h.1.physical.d_bound 0 2
  have hk := k_le_nine_quarters_of_normalizedB h
  linarith

/-- **`|c| ≤ 1`**: `D z 1 0 = k·c` with `|D| ≤ k` and `k > 0`. -/
theorem abs_c_le_one {z : Point} (h : NormalizedB z) : |z 6| ≤ 1 := by
  have hD : |z 0 * z 6| ≤ z 0 := by simpa only using h.1.physical.d_bound 1 0
  have hk := k_pos_of_normalizedB h
  rw [abs_mul, abs_of_pos hk] at hD
  have h' : z 0 * |z 6| ≤ z 0 * 1 := by rwa [mul_one]
  exact le_of_mul_le_mul_left h' hk

/-- **`|d| ≤ 1`**: `D z 2 0 = k·d`. -/
theorem abs_d_le_one {z : Point} (h : NormalizedB z) : |z 7| ≤ 1 := by
  have hD : |z 0 * z 7| ≤ z 0 := by simpa only using h.1.physical.d_bound 2 0
  have hk := k_pos_of_normalizedB h
  rw [abs_mul, abs_of_pos hk] at hD
  have h' : z 0 * |z 7| ≤ z 0 * 1 := by rwa [mul_one]
  exact le_of_mul_le_mul_left h' hk

/-- **`|u_i| ≤ 1`** from D28's head band. -/
theorem abs_u_le_one {z : Point} (h : NormalizedB z) (i : Fin 3) : |u z i| ≤ 1 :=
  h.1.headBand.abs_u i

/-- **`|x_i| ≤ 1`** from D28's head band. -/
theorem abs_x_le_one {z : Point} (h : NormalizedB z) (i : Fin 3) : |xv z i| ≤ 1 :=
  h.1.headBand.abs_x i

/-- **`|v_i| ≤ 1`** from D28's head band. -/
theorem abs_v_le_one {z : Point} (h : NormalizedB z) (i : Fin 3) : |v z i| ≤ 1 :=
  h.1.headBand.abs_v i

/-- **`p ≤ 2`** from D120's prefix maximum (`z 8 ≤ prefixPoint z 8 ≤ 2`). -/
theorem p_le_two {z : Point} (h : NormalizedB z) : z 8 ≤ 2 := by
  have hspec := Rho5.ExternalBFibreCapacity.prefixPoint_spec z h
  linarith [hspec.2.2.2.1, hspec.2.2.2.2.2]

/-- **`|q_j| ≤ 2`**: `|q z j| ≤ z 8 = p ≤ 2`. -/
theorem abs_q_le_two {z : Point} (h : NormalizedB z) (j : Fin 3) : |q z j| ≤ 2 := by
  have hq := h.1.physical.q_bound j
  have hp := p_le_two h
  linarith

/-! ## 3. Stage A: the closed root -/

/-- **`root_of_normalizedB_high` (stage A).**  For an arbitrary `NormalizedB z` with the two
explicit sign conditions `0 ≤ z 14` (i.e. `x0 ≥ 0`) and `z 4 ≤ 0` (i.e. `A ≤ 0`) and the high-value
premise `alpha < z 23`, the full 17-dimensional closed root holds at `frameOf z`.  The two sign
conditions are *not* derived here — D133's same-height real sign representative supplies them in
stage B — and the general `w`/tail data is untouched. -/
theorem root_of_normalizedB_high (z : Point) (h : NormalizedB z)
    (hx0 : 0 ≤ z 14) (hA : z 4 ≤ 0) (hhigh : Rho5.Algebraic.AlphaRoot.alpha < z 23) :
    B17Root (frameOf z) := by
  have hk_lo := four_gamma_div_nine_le_k h hhigh
  have hk_hi := k_le_nine_quarters_of_normalizedB h
  have hA_lo := neg_nine_quarters_le_A h
  have hB := abs_B_le_nine_quarters h
  have hc := abs_c_le_one h
  have hd := abs_d_le_one h
  have hu0 := abs_u_le_one h 0
  have hu1 := abs_u_le_one h 1
  have hu2 := abs_u_le_one h 2
  have hx0_hi := abs_x_le_one h 0
  have hx1 := abs_x_le_one h 1
  have hx2 := abs_x_le_one h 2
  have hv0 := abs_v_le_one h 0
  have hv1 := abs_v_le_one h 1
  have hv2 := abs_v_le_one h 2
  have hq0 := abs_q_le_two h 0
  have hq1 := abs_q_le_two h 1
  have hq2 := abs_q_le_two h 2
  simp only [B17Root, B17RootVector, frameVector, frameOf]
  refine ⟨⟨hk_lo, hk_hi⟩, ⟨hA_lo, hA⟩, hB, ⟨hc, hd⟩, ⟨hu0, hu1, hu2⟩,
    ⟨hx0, ?_⟩, ⟨hx1, hx2⟩, ⟨hv0, hv1, hv2⟩, ⟨hq0, hq1, hq2⟩⟩
  exact (abs_le.mp hx0_hi).2

end

end Rho5.Shared.PaperB17RootEntry
