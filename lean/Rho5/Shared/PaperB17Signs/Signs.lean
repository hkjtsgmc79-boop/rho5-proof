import Rho5.ExternalBFibreCapacity.Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# D133 — the two real sign normalizations of a normalized B point

This lane formalizes the sign-normalization step of the paper's §7 fibre argument: from an
arbitrary `NormalizedB z` (D120's accurate domain: `Qualified z`, `1 ≤ z 8`, `0 ≤ z 9`,
`0 ≤ z 10`) it builds the *same height* point `z'` obtained from `z` by a genuine legal
row/column sign operation on the one real reconstructed `5 × 5` matrix, with `x0 = z' 14 ≥ 0`
and `A = z' 4 ≤ 0`.

The paper performs this in two steps, and both are simultaneous sign flips of rows **and**
the same columns (`M ↦ S M S` with `S = diag(sg)`, `sg i = ±1`):

1. flip the last three rows and columns, `S = diag(1,1,ε,ε,ε)`, `ε = ±1`.  In the B24
   coordinates `u, x, v, q` are all multiplied by `ε`, while `k, A, B, c, d` and the tail
   `r, s, t` (hence the height) are unchanged.  Choose `ε` so that `x0 ≥ 0`.
2. flip the last two rows and columns, `S = diag(1,1,1,η,η)`, `η = ±1`.  In the B24
   coordinates `A, B, c, d` are multiplied by `η`, `u, x, v, q` get `η` on components `1, 2`
   only (component `0` is untouched), and the tail `r, s, t` together with `x0` is unchanged.
   Choose `η` so that `A ≤ 0`.

Composing the two flips is again a single diagonal sign conjugation with
`sg = diag(1,1,ε,εη,εη)`; that composite is what `sigma`/`signedFrame` below encode, and
`reconstruct_signedFrame` proves the *complete* entrywise matrix identity
`reconstruct z' i j = sg i * reconstruct z i j * sg j`.  The single first flip is kept as
the separate stage-A objects `flipFrame`/`flipPoint`/`flipVector`.

This file fixes the vocabulary: the sign vectors `tau`/`sigma` and the signed frame.  The
block equivariance is in `Action`, the matrix identity in `Matrix`, and the predicate
transfer plus the exported theorem in `Representative`.
-/

namespace Rho5.Shared.PaperB17Signs

open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail)

noncomputable section

/-- The three-block sign vector of the two §7 flips: `diag(ε, εη, εη)`.  It is the sign
applied to each component of the B24 triples `u, x, v, q`. -/
def tau (eps eta : ℝ) : Fin 3 → ℝ := ![eps, eps * eta, eps * eta]

/-- The full `5 × 5` sign vector `diag(1,1,ε,εη,εη)`: rows/columns `2,3,4` are the `u, x, v, q`
block and rows/columns `0,1` are the head, which the paper's two flips never touch. -/
def sigma (eps eta : ℝ) : Fin 5 → ℝ := ![1, 1, eps, eps * eta, eps * eta]

/-- **The signed frame.**  The real B24 coordinate frame of `diag(1,1,ε,εη,εη) M diag(1,1,ε,εη,εη)`:
`A, B, c, d` pick up `η` and each of `u, x, v, q` picks up `tau ε η` componentwise.  The
first B24 coordinate `k` and the whole tail are untouched. -/
def signedFrame (f : Frame) (eps eta : ℝ) : Frame where
  k := f.k
  A := eta * f.A
  B := eta * f.B
  c := eta * f.c
  d := eta * f.d
  u := fun i => tau eps eta i * f.u i
  x := fun i => tau eps eta i * f.x i
  v := fun i => tau eps eta i * f.v i
  q := fun i => tau eps eta i * f.q i

/-- Every entry of `tau` is `±1` once both flips are `±1`. -/
theorem tau_eq_one_or_neg_one (eps eta : ℝ) (hε : eps = 1 ∨ eps = -1)
    (hη : eta = 1 ∨ eta = -1) (i : Fin 3) : tau eps eta i = 1 ∨ tau eps eta i = -1 := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> simp [tau]

/-- Every entry of `sigma` is `±1` once both flips are `±1`. -/
theorem sigma_eq_one_or_neg_one (eps eta : ℝ) (hε : eps = 1 ∨ eps = -1)
    (hη : eta = 1 ∨ eta = -1) (i : Fin 5) : sigma eps eta i = 1 ∨ sigma eps eta i = -1 := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> simp [sigma]

/-- The sign vector is unimodular: `|tau ε η i| = 1`. -/
theorem abs_tau (eps eta : ℝ) (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1)
    (i : Fin 3) : |tau eps eta i| = 1 := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> simp [tau]

end

end Rho5.Shared.PaperB17Signs
