import Rho5.Shared.PaperB17Signs.Signs

/-!
# D133 — equivariance of the real blocks under the sign flips

The reconstructed matrix is `M = [[1, -e, vᵀ], [β, p - eβ, (q + βv)ᵀ], [u, px - eu, O]]` with
`O = D + x qᵀ + u vᵀ` and `S = D + x qᵀ` (D28/D120's frozen reconstruction).  Conjugating by
`diag(1,1,ε,εη,εη)` acts on the B24 coordinates exactly as the paper's §7 description says,
and every block is the corresponding signed conjugate:

* `core (the 3 × 3 block D)` ↦ `tau_i tau_j · core`,
* `stage (S = D + x qᵀ)` ↦ `tau_i tau_j · stage`,
* `original (O = D + x qᵀ + u vᵀ)` ↦ `tau_i tau_j · original`,
* the head bands `L_i = p x_i - e u_i` and `P_j = β v_j + q_j` ↦ `tau_i · L_i`, `tau_j · P_j`.

These are the *complete* actual matrix relations behind the normalization: the coupling bands
`|D| ≤ k`, `|S| ≤ p`, `|O| ≤ 1`, `|L| ≤ 1`, `|P| ≤ 1` are therefore preserved exactly, and
`Representative.admissible_signedFrame` transports them.
-/

namespace Rho5.Shared.PaperB17Signs

open Rho5.ExternalBFibreCapacity (Frame Tail core stage original)

noncomputable section

/-- **The real `3 × 3` core block is the signed conjugate.** `diag(1,1,ε,εη,εη)` conjugation
sends `D` to `tau_i tau_j D_ij`: the diagonal `k, r, s, t` and the entries `A, B, c, d` are
exactly the ones given by `signedFrame`. -/
theorem core_signedFrame (f : Frame) (t : Tail) (eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (i j : Fin 3) :
    core (signedFrame f eps eta) t i j = tau eps eta i * tau eps eta j * core f t i j := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [core, signedFrame, tau] <;> ring

/-- **The stage block `S = D + x qᵀ` is the signed conjugate.** -/
theorem stage_signedFrame (f : Frame) (t : Tail) (eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (i j : Fin 3) :
    stage (signedFrame f eps eta) t i j = tau eps eta i * tau eps eta j * stage f t i j := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [stage, core, signedFrame, tau] <;> ring

/-- **The original block `O = D + x qᵀ + u vᵀ` is the signed conjugate.** -/
theorem original_signedFrame (f : Frame) (t : Tail) (eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (i j : Fin 3) :
    original (signedFrame f eps eta) t i j
      = tau eps eta i * tau eps eta j * original f t i j := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [original, core, signedFrame, tau] <;> ring

/-- **The left head band `L_i = p x_i - e u_i` is the signed conjugate.**  This is the only
coupling in which `p` and `e` (which the flips leave untouched) meet the triples. -/
theorem left_signedFrame (f : Frame) (eps eta p e : ℝ) (i : Fin 3) :
    p * (signedFrame f eps eta).x i - e * (signedFrame f eps eta).u i
      = tau eps eta i * (p * f.x i - e * f.u i) := by
  have hx : (signedFrame f eps eta).x i = tau eps eta i * f.x i := rfl
  have hu : (signedFrame f eps eta).u i = tau eps eta i * f.u i := rfl
  rw [hx, hu]
  ring

/-- **The right head band `P_j = β v_j + q_j` is the signed conjugate.** -/
theorem right_signedFrame (f : Frame) (eps eta b : ℝ) (j : Fin 3) :
    b * (signedFrame f eps eta).v j + (signedFrame f eps eta).q j
      = tau eps eta j * (b * f.v j + f.q j) := by
  have hv : (signedFrame f eps eta).v j = tau eps eta j * f.v j := rfl
  have hq : (signedFrame f eps eta).q j = tau eps eta j * f.q j := rfl
  rw [hv, hq]
  ring

end

end Rho5.Shared.PaperB17Signs
