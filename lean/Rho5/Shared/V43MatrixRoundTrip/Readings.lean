/-
D119 — stage A (2/2): the Schur-layer readings of the extracted coordinates, and the round trip
==============================================================================================

With `M 0 0 = 1` the two frozen Schur formulas (D37 `S4_apply`, `S3_apply`, `T2_apply`) become

* `S4 M i j = M i⁺ j⁺ - M i⁺ 0 · M 0 j⁺`,
* `S3 M i j = S4 M i⁺ j⁺ - S4 M i⁺ 0 · S4 M 0 j⁺ / S4 M 0 0`,
* `T2 M i j = S3 M i⁺ j⁺ - S3 M i⁺ 0 · S3 M 0 j⁺ / S3 M 0 0`

(`i⁺` is `Fin.succ`).  This file reads those layers in the reverse coordinates of `Defs.lean`:

* `S4_row0  : S4 M 0 j⁺ = q_j`,  `S4_col0 : S4 M i⁺ 0 = p · x_i`,
  `S4_block : S4 M i⁺ j⁺ = M i⁺⁺ j⁺⁺ - u_i v_j`;
* `S3_block : S3 M i j = M i⁺⁺ j⁺⁺ - u_i v_j - x_i q_j`;
* `Dcore_extractX : Dcore (extractX M) = S3 M` — the core `D` block of the reconstruction is the
  actual second Schur layer, which is exactly where the saturated tail hypothesis `s = t = r` is
  spent (`D 1 2` needs `T2 0 1 = r`, `D 2 1` needs `T2 1 0 = r`; `D 2 2` needs neither);
* `reconstruct_extractX : M (extractX M) = M` — the general-`w` round trip.

Nothing here uses `d = -r`, `HeadBand`, `B24.Physical` or `V43.Physical`; the only hypotheses are the
`SatFrame` fields.
-/
import Rho5.Shared.V43MatrixRoundTrip.Defs

namespace Rho5.Shared.V43MatrixRoundTrip

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The normalized `S4` formula -/

/-- **Normalized first layer.**  With `M 0 0 = 1` the frozen `S4_apply` loses its division. -/
theorem S4_apply_of (M : Matrix5) (h00 : M 0 0 = 1) (i j : Fin 4) :
    S4 M i j = M i.succ j.succ - M i.succ 0 * M 0 j.succ := by
  rw [Rho5.Certificate.B24Extraction.S4_apply, h00, div_one]

/-! ## 2. The three readings of `S4` -/

/-- **`q` row**: `S4 M 0 j⁺` is the reverse coordinate `q_j = M 1 j⁺⁺ - β v_j`. -/
theorem S4_row0 (M : Matrix5) (h00 : M 0 0 = 1) (j : Fin 3) :
    S4 M 0 j.succ = qX M j := by
  rw [S4_apply_of M h00]
  simp [qX, vX, betaX]

/-- **`p x` column**: `S4 M i⁺ 0 = p · x_i`. -/
theorem S4_col0 (M : Matrix5) (h00 : M 0 0 = 1) (hp : pX M ≠ 0) (i : Fin 3) :
    S4 M i.succ 0 = pX M * xX M i := by
  rw [S4_apply_of M h00, xX, uX, eX]
  try field_simp
  try simp
  try ring

/-- **block**: `S4 M i⁺ j⁺ = M i⁺⁺ j⁺⁺ - u_i v_j`. -/
theorem S4_block (M : Matrix5) (h00 : M 0 0 = 1) (i j : Fin 3) :
    S4 M i.succ j.succ = M i.succ.succ j.succ.succ - uX M i * vX M j := by
  rw [S4_apply_of M h00]
  simp [uX, vX]

/-- The pivot itself: `S4 M 0 0 = pX M`. -/
theorem S4_zero_zero (M : Matrix5) : S4 M 0 0 = pX M := rfl

/-! ## 3. The reading of `S3` -/

/-- **Second layer.**  `S3 M i j` is the actual `(i⁺⁺, j⁺⁺)` entry of `M` minus the rank-one
correction `u_i v_j + x_i q_j`. -/
theorem S3_block (M : Matrix5) (h00 : M 0 0 = 1) (hp : pX M ≠ 0) (i j : Fin 3) :
    S3 M i j = M i.succ.succ j.succ.succ - uX M i * vX M j - xX M i * qX M j := by
  rw [Rho5.Certificate.B24Extraction.S3_apply, S4_block M h00, S4_col0 M h00 hp,
    S4_row0 M h00, S4_zero_zero]
  try field_simp
  try simp
  try ring

/-! ## 4. The core `D` block of the reconstruction is the actual `S3` -/

/-- **`Dcore (extractX M) = S3 M`.**  The single place where the saturated tail `s = t = r` is
spent: the `(1,2)` and `(2,1)` entries of the core block are read from `T2 M 0 1` and `T2 M 1 0`,
while `(2,2)` is read from the free `T2 M 1 1 = w`. -/
theorem Dcore_extractX (M : Matrix5) (h : SatFrame M) :
    Rho5.Shared.V43ActualMatrix.Dcore (extractX M) = S3 M := by
  have hk : S3 M 0 0 ≠ 0 := kX_ne_zero M h
  have h11 : T2 M 0 0 = S3 M 1 1 - S3 M 1 0 * S3 M 0 1 / S3 M 0 0 :=
    Rho5.Certificate.B24Extraction.T2_apply M 0 0
  have h12 : T2 M 0 1 = S3 M 1 2 - S3 M 1 0 * S3 M 0 2 / S3 M 0 0 :=
    Rho5.Certificate.B24Extraction.T2_apply M 0 1
  have h21 : T2 M 1 0 = S3 M 2 1 - S3 M 2 0 * S3 M 0 1 / S3 M 0 0 :=
    Rho5.Certificate.B24Extraction.T2_apply M 1 0
  have h22 : T2 M 1 1 = S3 M 2 2 - S3 M 2 0 * S3 M 0 2 / S3 M 0 0 :=
    Rho5.Certificate.B24Extraction.T2_apply M 1 1
  -- the tail hypothesis, in the unfolded coordinates linarith needs
  have hs : T2 M 0 1 = T2 M 0 0 := h.hs
  have ht : T2 M 1 0 = T2 M 0 0 := h.ht
  have h11' : S3 M 1 1 = T2 M 0 0 + S3 M 1 0 * S3 M 0 1 / S3 M 0 0 := by linarith
  have h12' : S3 M 1 2 = T2 M 0 0 + S3 M 1 0 * S3 M 0 2 / S3 M 0 0 := by linarith
  have h21' : S3 M 2 1 = T2 M 0 0 + S3 M 2 0 * S3 M 0 1 / S3 M 0 0 := by linarith
  have h22' : S3 M 2 2 = T2 M 1 1 + S3 M 2 0 * S3 M 0 2 / S3 M 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · show S3 M 0 0 * (S3 M 1 0 / S3 M 0 0) = S3 M 1 0
    try field_simp [hk]
    try ring
  · show T2 M 0 0 + S3 M 0 1 * (S3 M 1 0 / S3 M 0 0) = S3 M 1 1
    rw [h11']
    try field_simp [hk]
    try ring
  · show T2 M 0 0 + S3 M 0 2 * (S3 M 1 0 / S3 M 0 0) = S3 M 1 2
    rw [h12']
    try field_simp [hk]
    try ring
  · show S3 M 0 0 * (S3 M 2 0 / S3 M 0 0) = S3 M 2 0
    try field_simp [hk]
    try ring
  · show T2 M 0 0 + S3 M 0 1 * (S3 M 2 0 / S3 M 0 0) = S3 M 2 1
    rw [h21']
    try field_simp [hk]
    try ring
  · show T2 M 1 1 + S3 M 0 2 * (S3 M 2 0 / S3 M 0 0) = S3 M 2 2
    rw [h22']
    try field_simp [hk]
    try ring

/-! ## 5. The round trip -/

/-- **The `(1,1)` entry.**  `pX M - eX M · betaX M = M 1 1` — the normalization plus `S4_apply`. -/
theorem head_eq (M : Matrix5) (h00 : M 0 0 = 1) :
    pX M - eX M * betaX M = M 1 1 := by
  rw [pX, S4_apply_of M h00]
  simp [eX, betaX]
  ring

/-- **The `L` column.**  `pX M · xX M i - eX M · uX M i = M i⁺⁺ 1`. -/
theorem L_eq (M : Matrix5) (hp : pX M ≠ 0) (i : Fin 3) :
    pX M * xX M i - eX M * uX M i = M i.succ.succ 1 := by
  rw [xX]
  field_simp
  ring

/-- **The general-`w` round trip.**  Every matrix of the saturated-frame class is reconstructed by
its own reverse X22 point: `M (extractX M) = M`.  No `w = -r` substitution is used — `w` is read
back from `T2 M 1 1` and returned unchanged into the tail. -/
theorem reconstruct_extractX (M : Matrix5) (h : SatFrame M) :
    Rho5.Shared.V43ActualMatrix.M (extractX M) = M := by
  have h00 := h.h00
  have hp : pX M ≠ 0 := pX_ne_zero M h
  have hD := Dcore_extractX M h
  have hS3 : ∀ i j : Fin 3,
      S3 M i j = M i.succ.succ j.succ.succ - uX M i * vX M j - xX M i * qX M j :=
    fun i j => S3_block M h00 hp i j
  have e1 : pX M - eX M * betaX M = M 1 1 := head_eq M h00
  have e2 : ∀ i : Fin 3, pX M * xX M i - eX M * uX M i = M i.succ.succ 1 :=
    fun i => L_eq M hp i
  have e3 : ∀ i j : Fin 3, Rho5.Shared.V43ActualMatrix.Dcore (extractX M) i j
      + uX M i * vX M j + xX M i * qX M j = M i.succ.succ j.succ.succ := by
    intro i j
    rw [hD, hS3 i j]
    ring
  have e4 : ∀ j : Fin 3, betaX M * vX M j + qX M j = M 1 j.succ.succ := by
    intro j
    rw [qX]
    ring
  have e5 : ∀ i : Fin 3, uX M i = M i.succ.succ 0 := fun _ => rfl
  have e6 : ∀ j : Fin 3, vX M j = M 0 j.succ.succ := fun _ => rfl
  have e7 : -eX M = M 0 1 := by rw [eX]; ring
  have e8 : betaX M = M 1 0 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Ocore,
       Rho5.Shared.V43ActualMatrix.Pvec, Rho5.Shared.V43ActualMatrix.Lvec,
       Rho5.Shared.V43ActualMatrix.uOf, Rho5.Shared.V43ActualMatrix.xvOf,
       Rho5.Shared.V43ActualMatrix.vOf, Rho5.Shared.V43ActualMatrix.qOf,
       Rho5.Shared.V43ActualMatrix.pOf, Rho5.Shared.V43ActualMatrix.betaOf,
       Rho5.Shared.V43ActualMatrix.eOf, extractX]
     first
       | rfl
       | exact h00.symm
       | exact e1
       | exact e2 _
       | exact e3 _ _
       | exact e4 _
       | exact e7)

end

end Rho5.Shared.V43MatrixRoundTrip
