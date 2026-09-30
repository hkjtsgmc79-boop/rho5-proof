import Rho5.Shared.XHighRSource.Height

/-!
# D145 — the real transpose interface, at the actual-entry level

All statements use the actual entries of `transX M = Q J0 M^T J0 Q` (closed form
`(transX M) i j = D i * M j i * D j`).  They are the native transformations of
`TRANSPOSE_INTERFACE.md` that involve **raw matrix entries only**:

* `e_new = beta`, `beta_new = e`;
* `u_new = Z v`, `v_new = Z u`;
* the real head product `G_new = e_new * u0_new = beta * v0`.

**Explicitly NOT paid here** (they need the Schur layers, not raw entries; listed for Stage B):
`p, k, r, w` preservation, the `S`/`D`/`O` block conjugations (`O`'s raw-entry reading needs
`SatFrame (transX M)`), the `x`/`q` transforms (they divide by `p`), the `A,B,c,d` transforms,
and the high-sign restoration.  Nothing about them is assumed anywhere in this module.
-/

namespace Rho5.Shared.XHighRSource

noncomputable section

open Rho5
open Rho5.Shared.V43MatrixRoundTrip

/-- `e_new = beta` (raw entry `-M 0 1`). -/
theorem eX_transX (M : M5) : eX (transX M) = betaX M := by
  simp only [eX, betaX, transX]
  simp [sgnD, sgnQ, sgnJ, mul_assoc]

/-- `beta_new = e` (raw entry `M 1 0`). -/
theorem betaX_transX (M : M5) : betaX (transX M) = eX M := by
  simp only [eX, betaX, transX]
  simp [sgnD, sgnQ, sgnJ, mul_assoc]

/-- `u_new = Z v` (raw entries `M (i+2) 0` / `M 0 (i+2)`). -/
theorem uX_transX (M : M5) (i : Fin 3) : uX (transX M) i = sgnZ i * vX M i := by
  fin_cases i <;> simp [uX, vX, transX, sgnD, sgnQ, sgnJ, sgnZ]

/-- `v_new = Z u`. -/
theorem vX_transX (M : M5) (i : Fin 3) : vX (transX M) i = sgnZ i * uX M i := by
  fin_cases i <;> simp [uX, vX, transX, sgnD, sgnQ, sgnJ, sgnZ]

/- `O_new = Z O^T Z` is **not** stated here: D119's raw-entry reading of `O` is
`OX_eq_entry (h : SatFrame M)`, so the block conjugation needs `SatFrame (transX M)` — i.e. the
Schur-level rounding of the transpose, which is Stage B.  No version of it is assumed. -/

/-- **The real shared product**: the transposed source's head product is `beta * v0`. -/
theorem Ghead_transX (M : M5) : Ghead (transX M) = GheadTranspose M := by
  simp only [Ghead, GheadTranspose, eX_transX, uX_transX]
  simp [sgnZ]

/-- The transform is an involution on the sign datum: `D * D = 1` entrywise. -/
theorem sgnD_mul_self (i : Fin 5) : sgnD i * sgnD i = 1 := by
  fin_cases i <;> simp [sgnD, sgnQ, sgnJ]

/-- `transX` is an involution (the transform is its own inverse). -/
theorem transX_transX (M : M5) : transX (transX M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transX, sgnD, sgnQ, sgnJ]

end

end Rho5.Shared.XHighRSource
