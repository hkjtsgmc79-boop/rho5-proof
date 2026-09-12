import Rho5.Shared.BHeadSign.Signs

/-!
# D137 — the real blocks under the second row/column flip

Flipping row `1` and column `1` of the real reconstruction `M = reconstruct z`, i.e. conjugating
by `diag(1,σ,1,1,1)`, acts on the B24 blocks exactly as follows:

* `core` (`D`), `stage` (`S = D + x qᵀ`) and `original` (`O = D + x qᵀ + u vᵀ`) are *invariant*
  (`u, v` are untouched and the `σ` of `x` cancels the `σ` of `q`);
* `L_i = p x_i - e u_i ↦ σ · L_i` and `P_j = β v_j + q_j ↦ σ · P_j`.

The frame-level lemmas are the generic statements; the point-level ones (`D_headPointOf`,
`S_headPointOf`, `O_headPointOf`, `L_headPointOf`, `P_headPointOf`, and the `u/xv/v/q` readings)
are what `Representative` transports `Physical`/`HeadBand`/`Qualified` with.  The point-level
statements need `Qualified z` only to rewrite `z` as the frozen encoding of its own frame via
D120's `encode_decode`; no feasibility conclusion is assumed.
-/

namespace Rho5.Shared.BHeadSign

open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail encode frameOf tailOf core stage original
  encode_decode)
open Rho5.Certificate.B24MinorBridge (Qualified)

noncomputable section

/-! ## 1. Frame-level equivariance -/

/-- The `3 × 3` core block is literally invariant: `diag(1,σ,1,1,1)` only touches `x` and `q`,
and neither occurs in `D`. -/
theorem core_headFrame (f : Frame) (t : Tail) (sigma : ℝ) (i j : Fin 3) :
    core (headFrame f sigma) t i j = core f t i j := by
  fin_cases i <;> fin_cases j <;> simp [core, headFrame]

/-- The stage block `S = D + x qᵀ` is invariant. -/
theorem stage_headFrame (f : Frame) (t : Tail) (sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) (i j : Fin 3) :
    stage (headFrame f sigma) t i j = stage f t i j := by
  rcases hσ with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [stage, core, headFrame]

/-- The original block `O = D + x qᵀ + u vᵀ` is invariant. -/
theorem original_headFrame (f : Frame) (t : Tail) (sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) (i j : Fin 3) :
    original (headFrame f sigma) t i j = original f t i j := by
  rcases hσ with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [original, core, headFrame]

/-- The left head band `L_i = p x_i - e u_i` picks up `σ` (the `e` of the encoded point also
carries `σ`). -/
theorem left_headFrame (f : Frame) (sigma p e : ℝ) (i : Fin 3) :
    p * (headFrame f sigma).x i - (sigma * e) * (headFrame f sigma).u i
      = sigma * (p * f.x i - e * f.u i) := by
  have hx : (headFrame f sigma).x i = sigma * f.x i := rfl
  have hu : (headFrame f sigma).u i = f.u i := rfl
  rw [hx, hu]
  ring

/-- The right head band `P_j = β v_j + q_j` picks up `σ` (the `β` of the encoded point also
carries `σ`). -/
theorem right_headFrame (f : Frame) (sigma b : ℝ) (j : Fin 3) :
    (sigma * b) * (headFrame f sigma).v j + (headFrame f sigma).q j
      = sigma * (b * f.v j + f.q j) := by
  have hv : (headFrame f sigma).v j = f.v j := rfl
  have hq : (headFrame f sigma).q j = sigma * f.q j := rfl
  rw [hv, hq]
  ring

/-! ## 2. Coordinate readings of the flipped point -/

theorem u_headPointOf (z : Point) (sigma : ℝ) (i : Fin 3) :
    Rho5.Certificate.B16.u (headPointOf z sigma) i = Rho5.Certificate.B16.u z i := by
  fin_cases i <;> simp [Rho5.Certificate.B16.u]

theorem xv_headPointOf (z : Point) (sigma : ℝ) (i : Fin 3) :
    Rho5.Certificate.B16.xv (headPointOf z sigma) i = sigma * Rho5.Certificate.B16.xv z i := by
  fin_cases i <;> simp [Rho5.Certificate.B16.xv]

theorem v_headPointOf (z : Point) (sigma : ℝ) (i : Fin 3) :
    Rho5.Certificate.B16.v (headPointOf z sigma) i = Rho5.Certificate.B16.v z i := by
  fin_cases i <;> simp [Rho5.Certificate.B16.v]

theorem q_headPointOf (z : Point) (sigma : ℝ) (i : Fin 3) :
    Rho5.Certificate.B16.q (headPointOf z sigma) i = sigma * Rho5.Certificate.B16.q z i := by
  fin_cases i <;> simp [Rho5.Certificate.B16.q]

/-! ## 3. The point-level bands -/

theorem D_headPointOf (z : Point) (hq : Qualified z) (sigma : ℝ) (i j : Fin 3) :
    Rho5.Certificate.B16.D (headPointOf z sigma) i j = Rho5.Certificate.B16.D z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hL : Rho5.Certificate.B16.D (headPointOf z sigma) i j
      = core (headFrame (frameOf z) sigma) (tailOf z) i j :=
    Rho5.ExternalBFibreCapacity.D_encode (headFrame (frameOf z) sigma) (sigma * z 10) (z 8)
      (sigma * z 9) (tailOf z) i j
  have hR : Rho5.Certificate.B16.D z i j = core (frameOf z) (tailOf z) i j := by
    conv_lhs => rw [← hdec]
    exact Rho5.ExternalBFibreCapacity.D_encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) i j
  rw [hL, hR, core_headFrame]

theorem S_headPointOf (z : Point) (hq : Qualified z) (sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) (i j : Fin 3) :
    Rho5.Certificate.B16.S (headPointOf z sigma) i j = Rho5.Certificate.B16.S z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hL : Rho5.Certificate.B16.S (headPointOf z sigma) i j
      = stage (headFrame (frameOf z) sigma) (tailOf z) i j :=
    Rho5.ExternalBFibreCapacity.S_encode (headFrame (frameOf z) sigma) (sigma * z 10) (z 8)
      (sigma * z 9) (tailOf z) i j
  have hR : Rho5.Certificate.B16.S z i j = stage (frameOf z) (tailOf z) i j := by
    conv_lhs => rw [← hdec]
    exact Rho5.ExternalBFibreCapacity.S_encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) i j
  rw [hL, hR, stage_headFrame _ _ _ hσ]

theorem O_headPointOf (z : Point) (hq : Qualified z) (sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) (i j : Fin 3) :
    Rho5.Certificate.B16.O (headPointOf z sigma) i j = Rho5.Certificate.B16.O z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hL : Rho5.Certificate.B16.O (headPointOf z sigma) i j
      = original (headFrame (frameOf z) sigma) (tailOf z) i j :=
    Rho5.ExternalBFibreCapacity.O_encode (headFrame (frameOf z) sigma) (sigma * z 10) (z 8)
      (sigma * z 9) (tailOf z) i j
  have hR : Rho5.Certificate.B16.O z i j = original (frameOf z) (tailOf z) i j := by
    conv_lhs => rw [← hdec]
    exact Rho5.ExternalBFibreCapacity.O_encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) i j
  rw [hL, hR, original_headFrame _ _ _ hσ]

theorem L_headPointOf (z : Point) (hq : Qualified z) (sigma : ℝ) (i : Fin 3) :
    Rho5.Certificate.B16.L (headPointOf z sigma) i = sigma * Rho5.Certificate.B16.L z i := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hL : Rho5.Certificate.B16.L (headPointOf z sigma) i
      = z 8 * (headFrame (frameOf z) sigma).x i
        - (sigma * z 9) * (headFrame (frameOf z) sigma).u i :=
    Rho5.ExternalBFibreCapacity.L_encode (headFrame (frameOf z) sigma) (sigma * z 10) (z 8)
      (sigma * z 9) (tailOf z) i
  have hR : Rho5.Certificate.B16.L z i
      = z 8 * (frameOf z).x i - z 9 * (frameOf z).u i := by
    conv_lhs => rw [← hdec]
    exact Rho5.ExternalBFibreCapacity.L_encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) i
  rw [hL, hR, left_headFrame]

theorem P_headPointOf (z : Point) (hq : Qualified z) (sigma : ℝ) (j : Fin 3) :
    Rho5.Certificate.B16.P (headPointOf z sigma) j = sigma * Rho5.Certificate.B16.P z j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hL : Rho5.Certificate.B16.P (headPointOf z sigma) j
      = (sigma * z 10) * (headFrame (frameOf z) sigma).v j
        + (headFrame (frameOf z) sigma).q j :=
    Rho5.ExternalBFibreCapacity.P_encode (headFrame (frameOf z) sigma) (sigma * z 10) (z 8)
      (sigma * z 9) (tailOf z) j
  have hR : Rho5.Certificate.B16.P z j = z 10 * (frameOf z).v j + (frameOf z).q j := by
    conv_lhs => rw [← hdec]
    exact Rho5.ExternalBFibreCapacity.P_encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) j
  rw [hL, hR, right_headFrame]

end

end Rho5.Shared.BHeadSign
