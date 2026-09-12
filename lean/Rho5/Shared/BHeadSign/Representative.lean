import Rho5.Shared.BHeadSign.Matrix

/-!
# D137 — the head normalization of a qualified high-value B point

This file pays the head normalization itself.  From `Qualified z`, `1 < z 8` and
`0 < z 9 * z 10` (the paper's route: `F > 4` with `F ≤ 4p` gives `p > 1`, and the head band
gives `e β ≥ p - 1 > 0`) it produces the flipped point `headPoint z` together with the sign
vector `sgOf (headSigma z) = diag(1,σ,1,1,1)`, and proves

* the actual matrix relation `reconstruct z' i j = sg i * reconstruct z i j * sg j`;
* `NormalizedB z'` — the predicate this card is paying for, obtained field by field from
  `Qualified z` (`Physical`, `HeadBand`, `p > 0`, `k > 0`, `0 ≤ s ≤ r`, `0 ≤ t`) plus the two
  positive head readings, *not* assumed in advance;
* the same height `z' 23 = z 23` and the preserved coordinates `k, r, s, t, p, A, B, c, d`;
* the flipped head readings `z' 9 = σ z 9`, `z' 10 = σ z 10` and both of them strictly positive.

The exported high-value theorem is `qualified_high_head_has_normalized_representative`; the
strict hypothesis `1 < z 8` is used only for `1 ≤ z' 8`, so the strictly weaker-premise version
`qualified_head_has_normalized_representative` (with `1 ≤ z 8`) is proved first and the card's
theorem is its immediate corollary.
-/

namespace Rho5.Shared.BHeadSign

open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (NormalizedB encode frameOf tailOf)
open Rho5.Certificate.B24MinorBridge (Qualified)
open Rho5.Certificate.B24Reconstruction (reconstruct p e beta)

noncomputable section

/-! ## 1. The head readings of the flipped point -/

@[simp] theorem p_headPointOf (z : Point) (sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.p (headPointOf z sigma)
      = Rho5.Certificate.B24Reconstruction.p z := by
  simp [Rho5.Certificate.B24Reconstruction.p]

@[simp] theorem e_headPointOf (z : Point) (sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.e (headPointOf z sigma)
      = sigma * Rho5.Certificate.B24Reconstruction.e z := by
  simp [Rho5.Certificate.B24Reconstruction.e]

@[simp] theorem beta_headPointOf (z : Point) (sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.beta (headPointOf z sigma)
      = sigma * Rho5.Certificate.B24Reconstruction.beta z := by
  simp [Rho5.Certificate.B24Reconstruction.beta]

/-! ## 2. `Qualified` is preserved -/

/-- **The actual qualification layer is preserved by the second row/column flip**, field by
field: `Physical`'s `D/O/S/L/P/q` bands, `r > 0`, the height equation and `t ≤ r`, the seven
`HeadBand` fields, `p > 0`, `k > 0`, `0 ≤ s ≤ r` and `0 ≤ t`. -/
theorem qualified_headPointOf (z : Point) (sigma : ℝ) (hσ : sigma = 1 ∨ sigma = -1)
    (hq : Qualified z) : Qualified (headPointOf z sigma) := by
  have hσabs : |sigma| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [D_headPointOf z hq sigma i j]
    simpa using hq.physical.d_bound i j
  · intro i j
    rw [O_headPointOf z hq sigma hσ i j]
    exact hq.physical.o_bound i j
  · intro i j
    rw [S_headPointOf z hq sigma hσ i j]
    simpa using hq.physical.s_bound i j
  · intro i
    rw [L_headPointOf z hq sigma i, abs_mul, hσabs, one_mul]
    exact hq.physical.l_bound i
  · intro i
    rw [P_headPointOf z hq sigma i, abs_mul, hσabs, one_mul]
    exact hq.physical.p_bound i
  · intro i
    rw [q_headPointOf z sigma i, abs_mul, hσabs, one_mul]
    simpa using hq.physical.q_bound i
  · simpa using hq.physical.r_pos
  · show headPointOf z sigma 23
      = headPointOf z sigma 1 + headPointOf z sigma 2 * headPointOf z sigma 3
        / headPointOf z sigma 1
    rw [headPointOf_twentythree, headPointOf_one, headPointOf_two, headPointOf_three]
  · simpa using hq.physical.order_t
  · rw [e_headPointOf z sigma, abs_mul, hσabs, one_mul]
    exact hq.headBand.abs_e
  · rw [beta_headPointOf z sigma, abs_mul, hσabs, one_mul]
    exact hq.headBand.abs_beta
  · intro i
    rw [u_headPointOf z sigma i]
    exact hq.headBand.abs_u i
  · intro i
    show |Rho5.Certificate.B16.xv (headPointOf z sigma) i| ≤ 1
    rw [xv_headPointOf z sigma i, abs_mul, hσabs, one_mul]
    exact hq.headBand.abs_x i
  · intro i
    rw [v_headPointOf z sigma i]
    exact hq.headBand.abs_v i
  · rw [p_headPointOf z sigma, e_headPointOf z sigma, beta_headPointOf z sigma]
    rcases hσ with rfl | rfl
    · simpa using hq.headBand.abs_p_sub_e_mul_beta
    · have h2 : Rho5.Certificate.B24Reconstruction.p z
          - (-1 * Rho5.Certificate.B24Reconstruction.e z)
            * (-1 * Rho5.Certificate.B24Reconstruction.beta z)
          = Rho5.Certificate.B24Reconstruction.p z
            - Rho5.Certificate.B24Reconstruction.e z
              * Rho5.Certificate.B24Reconstruction.beta z := by
        ring
      rw [h2]
      exact hq.headBand.abs_p_sub_e_mul_beta
  · intro i
    show |Rho5.Certificate.B24Reconstruction.p (headPointOf z sigma)
            * Rho5.Certificate.B16.xv (headPointOf z sigma) i
          - Rho5.Certificate.B24Reconstruction.e (headPointOf z sigma)
            * Rho5.Certificate.B16.u (headPointOf z sigma) i| ≤ 1
    rw [p_headPointOf z sigma, e_headPointOf z sigma, xv_headPointOf z sigma i,
      u_headPointOf z sigma i]
    have h2 : Rho5.Certificate.B24Reconstruction.p z * (sigma * Rho5.Certificate.B16.xv z i)
        - (sigma * Rho5.Certificate.B24Reconstruction.e z) * Rho5.Certificate.B16.u z i
        = sigma * (Rho5.Certificate.B24Reconstruction.p z * Rho5.Certificate.B16.xv z i
            - Rho5.Certificate.B24Reconstruction.e z * Rho5.Certificate.B16.u z i) := by
      ring
    rw [h2, abs_mul, hσabs, one_mul]
    exact hq.headBand.abs_L i
  · simpa using hq.p_pos
  · simpa using hq.k_pos
  · simpa using hq.s_nonneg
  · simpa using hq.s_le_r
  · simpa using hq.t_nonneg

/-- `NormalizedB` is reached: `Qualified`, `1 ≤ p` and the two nonnegative head readings. -/
theorem normalizedB_headPointOf (z : Point) (sigma : ℝ) (hσ : sigma = 1 ∨ sigma = -1)
    (hq : Qualified z) (hp : 1 ≤ z 8) (he : 0 < sigma * z 9) (hb : 0 < sigma * z 10) :
    NormalizedB (headPointOf z sigma) := by
  refine ⟨qualified_headPointOf z sigma hσ hq, ?_, ?_, ?_⟩
  · simpa [headPointOf_eight] using hp
  · exact le_of_lt (by simpa [headPointOf_nine] using he)
  · exact le_of_lt (by simpa [headPointOf_ten] using hb)

/-! ## 3. The exported theorems -/

/-- **The head normalization with the weak premise `1 ≤ p`.**  Both head signs flip together in
one real row/column operation, so `0 < e β` alone makes them positive; the point keeps its
height, `k, r, s, t, p` and `A, B, c, d`, and `NormalizedB` holds. -/
theorem qualified_head_has_normalized_representative
    (z : Point) (hq : Qualified z) (hp : 1 ≤ z 8) (heb : 0 < z 9 * z 10) :
    ∃ (z' : Point) (sg : Fin 5 → ℝ),
      (∀ i, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j, reconstruct z' i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB z' ∧ z' 23 = z 23 ∧
      z' 0 = z 0 ∧ z' 1 = z 1 ∧ z' 2 = z 2 ∧ z' 3 = z 3 ∧ z' 4 = z 4 ∧ z' 5 = z 5 ∧
      z' 6 = z 6 ∧ z' 7 = z 7 ∧ z' 8 = z 8 ∧
      z' 9 = headSigma z * z 9 ∧ z' 10 = headSigma z * z 10 ∧
      0 < z' 9 ∧ 0 < z' 10 := by
  refine ⟨headPoint z, sgOf (headSigma z), ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i
    exact sgOf_eq_one_or_neg_one (headSigma z) (headSigma_eq_one_or_neg_one z) i
  · intro i j
    exact reconstruct_headPointOf z hq (headSigma z) (headSigma_eq_one_or_neg_one z) i j
  · exact normalizedB_headPointOf z (headSigma z) (headSigma_eq_one_or_neg_one z) hq hp
      (headSigma_mul_pos_left z heb) (headSigma_mul_pos_right z heb)
  · show headPoint z 23 = z 23
    rw [hq.physical.height]
    rfl
  · show 0 < headSigma z * z 9
    exact headSigma_mul_pos_left z heb
  · show 0 < headSigma z * z 10
    exact headSigma_mul_pos_right z heb

/-- **The card's main theorem: the real head normalization of a qualified high-value B point.**
From `Qualified z`, `1 < z 8` and `0 < z 9 * z 10` it builds a same-height point `z'` reached by
one genuine row/column sign operation `diag(1,σ,1,1,1)` on the one real reconstructed matrix,
with `NormalizedB z'`, `k, r, s, t, p, A, B, c, d` preserved, the head readings multiplied by
`σ`, and both head coordinates strictly positive. -/
theorem qualified_high_head_has_normalized_representative
    (z : Point) (hq : Qualified z) (hp : 1 < z 8) (heb : 0 < z 9 * z 10) :
    ∃ (z' : Point) (sg : Fin 5 → ℝ),
      (∀ i, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j, reconstruct z' i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB z' ∧ z' 23 = z 23 ∧
      z' 0 = z 0 ∧ z' 1 = z 1 ∧ z' 2 = z 2 ∧ z' 3 = z 3 ∧ z' 4 = z 4 ∧ z' 5 = z 5 ∧
      z' 6 = z 6 ∧ z' 7 = z 7 ∧ z' 8 = z 8 ∧
      z' 9 = headSigma z * z 9 ∧ z' 10 = headSigma z * z 10 ∧
      0 < z' 9 ∧ 0 < z' 10 :=
  qualified_head_has_normalized_representative z hq (le_of_lt hp) heb

end

end Rho5.Shared.BHeadSign
