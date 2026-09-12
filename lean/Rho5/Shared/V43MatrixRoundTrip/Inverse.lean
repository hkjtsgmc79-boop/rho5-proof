/-
D119 — the inverse round trip and the two-way statement over the saturated subdomain
====================================================================================

The reverse map `extractX` is a genuine inverse of the accepted D103 reconstruction on the
saturated subdomain:

* `reconstruct_extractX` (in `Readings.lean`): every `SatFrame` matrix `M` satisfies
  `reconstruct (extractX M) = M` — the general-`w` round trip;
* `extractX_reconstruct` (here): every `V43.Physical` point `x` satisfies
  `extractX (reconstruct x) = x`;
* `satFrame_reconstruct` (here): the forward image of a `V43.Physical` point lies in `SatFrame`
  (this is where D103's four complete pivots, `matrixEntryMax = 1`, the positive pivots and
  `T2 (M x) = [[r, r], [r, w]]` supply the saturated tail `s = t = r`).

Scope, stated explicitly: the two-way statement covers the subdomain `s = t = r` of the actual
`Matrix5` class.  It does **not** claim that every global maximizer saturates, that every point
enters a cube, or anything about matrices outside `SatFrame`; and the reverse map reads the
*actual* Schur layers rather than substituting `w = -r` (the saturated `toXsat` route of D95 is not
used anywhere).
-/
import Rho5.Shared.V43MatrixRoundTrip.Height

namespace Rho5.Shared.V43MatrixRoundTrip

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

open Rho5.Shared.V43ActualMatrix (S3_eq_Dcore S4_eq_template S4template T2_eq_tail M_zero_zero
  matrixEntryMax_eq_one isCompletePivot_M isCompletePivot_S4 isCompletePivot_S3
  isCompletePivot_T2 p_M_pos k_M_pos r_M_pos)

/-- The accepted D103 reconstruction, re-exported under a distinct name so that this lane can keep
`M` for the arbitrary given matrix. -/
abbrev reconstruct (x : X) : Matrix5 := Rho5.Shared.V43ActualMatrix.M x

/-! ## 1. The 22 coordinate readings of `extractX (reconstruct x)` -/

/-- **Inverse round trip.**  Every `V43.Physical` X22 point is recovered from its own
reconstruction. -/
theorem extractX_reconstruct (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    extractX (reconstruct x) = x := by
  have h0 : extractX (reconstruct x) 0 = x 0 := by
    rw [extractX_0, kX, S3_eq_Dcore x hx]
    simp [Rho5.Shared.V43ActualMatrix.Dcore, Rho5.Shared.V43ActualMatrix.kOf]
  have h1 : extractX (reconstruct x) 1 = x 1 := by
    rw [extractX_1, rX, T2_eq_tail x hx]
    simp [Rho5.Shared.V43ActualMatrix.rOf]
  have h2 : extractX (reconstruct x) 2 = x 2 := by
    rw [extractX_2, wX, T2_eq_tail x hx]
    simp [Rho5.Shared.V43ActualMatrix.wOf]
  have h3 : extractX (reconstruct x) 3 = x 3 := by
    rw [extractX_3, aX, S3_eq_Dcore x hx]
    simp [Rho5.Shared.V43ActualMatrix.Dcore, Rho5.Shared.V43ActualMatrix.aOf]
  have h4 : extractX (reconstruct x) 4 = x 4 := by
    rw [extractX_4, bX, S3_eq_Dcore x hx]
    simp [Rho5.Shared.V43ActualMatrix.Dcore, Rho5.Shared.V43ActualMatrix.bOf]
  have h5 : extractX (reconstruct x) 5 = x 5 := by
    have hk : x 0 ≠ 0 := ne_of_gt hx.2.1
    rw [extractX_5, cX, S3_eq_Dcore x hx]
    simp [Rho5.Shared.V43ActualMatrix.Dcore, Rho5.Shared.V43ActualMatrix.kOf,
      Rho5.Shared.V43ActualMatrix.cOf]
    try field_simp
    try ring
  have h6 : extractX (reconstruct x) 6 = x 6 := by
    have hk : x 0 ≠ 0 := ne_of_gt hx.2.1
    rw [extractX_6, dX, S3_eq_Dcore x hx]
    simp [Rho5.Shared.V43ActualMatrix.Dcore, Rho5.Shared.V43ActualMatrix.kOf,
      Rho5.Shared.V43ActualMatrix.dOf]
    try field_simp
    try ring
  have hp7 : pX (reconstruct x) = x 7 := by
    rw [pX, S4_eq_template x]
    simp [S4template, Rho5.Shared.V43ActualMatrix.pOf]
  have h7 : extractX (reconstruct x) 7 = x 7 := by
    rw [extractX_7]
    exact hp7
  have h8 : extractX (reconstruct x) 8 = x 8 := by
    rw [extractX_8, eX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.eOf]
  have h9 : extractX (reconstruct x) 9 = x 9 := by
    rw [extractX_9, betaX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.betaOf]
  have h10 : extractX (reconstruct x) 10 = x 10 := by
    rw [extractX_10, uX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.uOf]
  have h11 : extractX (reconstruct x) 11 = x 11 := by
    rw [extractX_11, uX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.uOf]
  have h12 : extractX (reconstruct x) 12 = x 12 := by
    rw [extractX_12, uX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.uOf]
  have h13 : extractX (reconstruct x) 13 = x 13 := by
    have hp : x 7 ≠ 0 := ne_of_gt hx.2.2.2
    rw [extractX_13, xX, hp7]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Lvec,
      Rho5.Shared.V43ActualMatrix.uOf, Rho5.Shared.V43ActualMatrix.xvOf,
      Rho5.Shared.V43ActualMatrix.pOf, Rho5.Shared.V43ActualMatrix.eOf,
      eX, uX]
    try field_simp
    try ring
  have h14 : extractX (reconstruct x) 14 = x 14 := by
    have hp : x 7 ≠ 0 := ne_of_gt hx.2.2.2
    rw [extractX_14, xX, hp7]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Lvec,
      Rho5.Shared.V43ActualMatrix.uOf, Rho5.Shared.V43ActualMatrix.xvOf,
      Rho5.Shared.V43ActualMatrix.pOf, Rho5.Shared.V43ActualMatrix.eOf,
      eX, uX]
    try field_simp
    try ring
  have h15 : extractX (reconstruct x) 15 = x 15 := by
    have hp : x 7 ≠ 0 := ne_of_gt hx.2.2.2
    rw [extractX_15, xX, hp7]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Lvec,
      Rho5.Shared.V43ActualMatrix.uOf, Rho5.Shared.V43ActualMatrix.xvOf,
      Rho5.Shared.V43ActualMatrix.pOf, Rho5.Shared.V43ActualMatrix.eOf,
      eX, uX]
    try field_simp
    try ring
  have h16 : extractX (reconstruct x) 16 = x 16 := by
    rw [extractX_16, vX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.vOf]
  have h17 : extractX (reconstruct x) 17 = x 17 := by
    rw [extractX_17, vX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.vOf]
  have h18 : extractX (reconstruct x) 18 = x 18 := by
    rw [extractX_18, vX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.vOf]
  have h19 : extractX (reconstruct x) 19 = x 19 := by
    rw [extractX_19, qX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Pvec,
      Rho5.Shared.V43ActualMatrix.vOf, Rho5.Shared.V43ActualMatrix.qOf,
      Rho5.Shared.V43ActualMatrix.betaOf, betaX, vX]
    try ring
  have h20 : extractX (reconstruct x) 20 = x 20 := by
    rw [extractX_20, qX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Pvec,
      Rho5.Shared.V43ActualMatrix.vOf, Rho5.Shared.V43ActualMatrix.qOf,
      Rho5.Shared.V43ActualMatrix.betaOf, betaX, vX]
    try ring
  have h21 : extractX (reconstruct x) 21 = x 21 := by
    rw [extractX_21, qX]
    simp [Rho5.Shared.V43ActualMatrix.M, Rho5.Shared.V43ActualMatrix.Pvec,
      Rho5.Shared.V43ActualMatrix.vOf, Rho5.Shared.V43ActualMatrix.qOf,
      Rho5.Shared.V43ActualMatrix.betaOf, betaX, vX]
    try ring
  funext i
  fin_cases i <;>
    first
      | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 | exact h6
      | exact h7 | exact h8 | exact h9 | exact h10 | exact h11 | exact h12 | exact h13
      | exact h14 | exact h15 | exact h16 | exact h17 | exact h18 | exact h19 | exact h20
      | exact h21

/-! ## 2. The forward image lies in the saturated-frame class -/

/-- **The forward image is a saturated frame.**  Every field is an accepted D103 reading; the
saturated tail `s = t = r` is the content of `T2_eq_tail` (`T2 (M x) = [[r, r], [r, w]]`). -/
theorem satFrame_reconstruct (x : X) (hx : Rho5.LocalAnalysis.V43.Physical x) :
    SatFrame (reconstruct x) := by
  have hT := T2_eq_tail x hx
  have hs : s (reconstruct x) = r (reconstruct x) := by
    rw [Rho5.Certificate.B24Extraction.s, Rho5.Certificate.B24Extraction.r, hT]
    simp
  have ht : t (reconstruct x) = r (reconstruct x) := by
    rw [Rho5.Certificate.B24Extraction.t, Rho5.Certificate.B24Extraction.r, hT]
    simp
  exact ⟨M_zero_zero x, matrixEntryMax_eq_one x hx, isCompletePivot_M x hx,
    isCompletePivot_S4 x hx, isCompletePivot_S3 x hx, isCompletePivot_T2 x hx,
    p_M_pos x hx, k_M_pos x hx, r_M_pos x hx, hs, ht⟩

/-! ## 3. The two-way statement -/

/-- **Two-way round trip over the saturated subdomain.**  On `SatFrame` matrices `extractX` is a
left inverse of `reconstruct`, on `V43.Physical` points it is a right inverse, and the forward image
of a physical point is a saturated frame.  The statement is about this concrete `5 × 5`/X22 pair
only, and only about the subdomain `s = t = r`: no claim is made that every global maximizer is
saturated, that a cube is covered, or anything at another order. -/
theorem roundTrip_two_way :
    (∀ M : Matrix5, SatFrame M → reconstruct (extractX M) = M) ∧
      (∀ x : X, Rho5.LocalAnalysis.V43.Physical x → extractX (reconstruct x) = x) ∧
      (∀ x : X, Rho5.LocalAnalysis.V43.Physical x → SatFrame (reconstruct x)) :=
  ⟨fun _ h => reconstruct_extractX _ h, fun _ hx => extractX_reconstruct _ hx,
    fun _ hx => satFrame_reconstruct _ hx⟩

end

end Rho5.Shared.V43MatrixRoundTrip
