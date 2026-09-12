/-
D119 — stage A (1/2): the reverse X22 coordinates of an actual `5 × 5` matrix
============================================================================

The accepted D103 bridge goes forward: from a `V43.Physical` X22 point `x` it reconstructs the
`5 × 5` matrix `Rho5.Shared.V43ActualMatrix.M x` with tail `[[r, r], [r, w]]` and proves the four
complete pivots, the trace, the growth bound and `PolyCP`.  This lane builds the **reverse**
representation: from an actual matrix `M` in the class below it extracts an X22 point `extractX M`
in the *fixed* Model order `k, r, w, A, B, c, d, p, e, β, u0..2, x0..2, v0..2, q0..2`, and proves
the round trip.

`extractX` reads the *actual* Schur layers of `M` (never a saturation substitution):

* `k = S3 M 0 0`, `A = S3 M 0 1`, `B = S3 M 0 2`, `c = S3 M 1 0 / k`, `d = S3 M 2 0 / k` — so the
  coordinate `c`/`d` are the *scaled* entries of the actual `S3`, and the bordered-minor names
  `B`/`C` of the D52/D62 chain are **not** mixed into the coordinates `A`/`B`;
* `r = T2 M 0 0`, `w = T2 M 1 1` — `w` is free, no `w = -r` and no `toXsat` substitution;
* `p = S4 M 0 0`, `e = -M 0 1`, `β = M 1 0`;
* `u_i = M (i+2) 0`, `v_j = M 0 (j+2)`, `q_j = M 1 (j+2) - β v_j`;
* `x_i = (M (i+2) 1 + e u_i) / p`.

The class `SatFrame` is exactly the card's hypothesis list: `M 0 0 = 1`, `matrixEntryMax M = 1`,
the four leading complete pivots, `p, k, r > 0`, and the **saturated off-diagonal tail**
`s = t = r`.  Nothing else: no `d = -r`, no `HeadBand`, no `B24.Physical`, no `V43.Physical`.
-/
import Rho5.Shared.V43ActualMatrix

namespace Rho5.Shared.V43MatrixRoundTrip

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-- The fixed X22 coordinate space of the Model. -/
abbrev X := Rho5.LocalAnalysis.X
/-- The `5 × 5` real matrices of the pilot. -/
abbrev Matrix5 := Rho5.Matrix5

/-! ## 1. The class of matrices this lane inverts -/

/-- **The saturated-frame class.**  An actual `5 × 5` matrix with `M 0 0 = 1`, unit entry maximum,
the four leading complete pivots, strictly positive pivots `p, k, r`, and the actual tail with
`s = t = r` (the general `w = T2 M 1 1` stays free).  Every field is a genuine hypothesis of this
lane: no `d = -r`, no `HeadBand`, no `B24.Physical`, no `V43.Physical`. -/
structure SatFrame (M : Matrix5) : Prop where
  h00 : M 0 0 = 1
  hmax : Rho5.matrixEntryMax M = 1
  cp1 : Rho5.Pivot.IsCompletePivot M 0 0
  cp2 : Rho5.Pivot.IsCompletePivot (S4 M) 0 0
  cp3 : Rho5.Pivot.IsCompletePivot (S3 M) 0 0
  cp4 : Rho5.Pivot.IsCompletePivot (T2 M) 0 0
  hp : 0 < p M
  hk : 0 < k M
  hr : 0 < r M
  hs : s M = r M
  ht : t M = r M

/-! ## 2. The reverse coordinate readers -/

/-- `k`, read from the actual second Schur layer. -/
def kX (M : Matrix5) : ℝ := S3 M 0 0
/-- `r`, the tail pivot. -/
def rX (M : Matrix5) : ℝ := T2 M 0 0
/-- `w`, the free tail entry (`T2 M 1 1`). -/
def wX (M : Matrix5) : ℝ := T2 M 1 1
/-- the coordinate `A`: the `(0,1)` entry of the actual `S3`. -/
def aX (M : Matrix5) : ℝ := S3 M 0 1
/-- the coordinate `B`: the `(0,2)` entry of the actual `S3`. -/
def bX (M : Matrix5) : ℝ := S3 M 0 2
/-- the coordinate `c`: the scaled actual entry `S3 1 0 / k`. -/
def cX (M : Matrix5) : ℝ := S3 M 1 0 / S3 M 0 0
/-- the coordinate `d`: the scaled actual entry `S3 2 0 / k`. -/
def dX (M : Matrix5) : ℝ := S3 M 2 0 / S3 M 0 0
/-- `p`, the first Schur pivot. -/
def pX (M : Matrix5) : ℝ := S4 M 0 0
/-- `e`, read from the actual `(0,1)` entry. -/
def eX (M : Matrix5) : ℝ := -(M 0 1)
/-- `β`, the actual `(1,0)` entry. -/
def betaX (M : Matrix5) : ℝ := M 1 0
/-- `u_i = M (i+2) 0`, the actual first column below the first row.  Written with `Fin.succ` so the
reader is a genuine function of the index (no `Fin`-addition arithmetic in the statements). -/
def uX (M : Matrix5) (i : Fin 3) : ℝ := M i.succ.succ 0
/-- `v_j = M 0 (j+2)`, the actual first row right of the corner. -/
def vX (M : Matrix5) (j : Fin 3) : ℝ := M 0 j.succ.succ
/-- `q_j = M 1 (j+2) - β v_j`, the actual `P`-row residual. -/
def qX (M : Matrix5) (j : Fin 3) : ℝ := M 1 j.succ.succ - betaX M * vX M j
/-- `x_i = (M (i+2) 1 + e u_i) / p`, the normalised actual `L`-column. -/
def xX (M : Matrix5) (i : Fin 3) : ℝ := (M i.succ.succ 1 + eX M * uX M i) / pX M

/-- **The reverse X22 point**, in the fixed Model order
`k, r, w, A, B, c, d, p, e, β, u0..2, x0..2, v0..2, q0..2`. -/
def extractX (M : Matrix5) : X :=
  ![kX M, rX M, wX M, aX M, bX M, cX M, dX M, pX M, eX M, betaX M,
    uX M 0, uX M 1, uX M 2, xX M 0, xX M 1, xX M 2,
    vX M 0, vX M 1, vX M 2, qX M 0, qX M 1, qX M 2]

/-! ## 3. Coordinate readings of `extractX` (the 22 entries, by index) -/

@[simp] theorem extractX_0 (M : Matrix5) : extractX M 0 = kX M := rfl
@[simp] theorem extractX_1 (M : Matrix5) : extractX M 1 = rX M := rfl
@[simp] theorem extractX_2 (M : Matrix5) : extractX M 2 = wX M := rfl
@[simp] theorem extractX_3 (M : Matrix5) : extractX M 3 = aX M := rfl
@[simp] theorem extractX_4 (M : Matrix5) : extractX M 4 = bX M := rfl
@[simp] theorem extractX_5 (M : Matrix5) : extractX M 5 = cX M := rfl
@[simp] theorem extractX_6 (M : Matrix5) : extractX M 6 = dX M := rfl
@[simp] theorem extractX_7 (M : Matrix5) : extractX M 7 = pX M := rfl
@[simp] theorem extractX_8 (M : Matrix5) : extractX M 8 = eX M := rfl
@[simp] theorem extractX_9 (M : Matrix5) : extractX M 9 = betaX M := rfl
@[simp] theorem extractX_10 (M : Matrix5) : extractX M 10 = uX M 0 := rfl
@[simp] theorem extractX_11 (M : Matrix5) : extractX M 11 = uX M 1 := rfl
@[simp] theorem extractX_12 (M : Matrix5) : extractX M 12 = uX M 2 := rfl
@[simp] theorem extractX_13 (M : Matrix5) : extractX M 13 = xX M 0 := rfl
@[simp] theorem extractX_14 (M : Matrix5) : extractX M 14 = xX M 1 := rfl
@[simp] theorem extractX_15 (M : Matrix5) : extractX M 15 = xX M 2 := rfl
@[simp] theorem extractX_16 (M : Matrix5) : extractX M 16 = vX M 0 := rfl
@[simp] theorem extractX_17 (M : Matrix5) : extractX M 17 = vX M 1 := rfl
@[simp] theorem extractX_18 (M : Matrix5) : extractX M 18 = vX M 2 := rfl
@[simp] theorem extractX_19 (M : Matrix5) : extractX M 19 = qX M 0 := rfl
@[simp] theorem extractX_20 (M : Matrix5) : extractX M 20 = qX M 1 := rfl
@[simp] theorem extractX_21 (M : Matrix5) : extractX M 21 = qX M 2 := rfl

/-! ## 4. Immediate readings of the class -/

/-- `pX` is the frozen `p`. -/
theorem pX_eq_p (M : Matrix5) : pX M = p M := rfl
/-- `kX` is the frozen `k`. -/
theorem kX_eq_k (M : Matrix5) : kX M = k M := rfl
/-- `rX` is the frozen `r`. -/
theorem rX_eq_r (M : Matrix5) : rX M = r M := rfl
/-- `aX` is the frozen `S3 0 1`. -/
theorem aX_eq (M : Matrix5) : aX M = S3 M 0 1 := rfl
/-- `bX` is the frozen `S3 0 2`. -/
theorem bX_eq (M : Matrix5) : bX M = S3 M 0 2 := rfl

theorem pX_pos (M : Matrix5) (h : SatFrame M) : 0 < pX M := h.hp
theorem kX_pos (M : Matrix5) (h : SatFrame M) : 0 < kX M := h.hk
theorem rX_pos (M : Matrix5) (h : SatFrame M) : 0 < rX M := h.hr
theorem pX_ne_zero (M : Matrix5) (h : SatFrame M) : pX M ≠ 0 := ne_of_gt (pX_pos M h)
theorem kX_ne_zero (M : Matrix5) (h : SatFrame M) : kX M ≠ 0 := ne_of_gt (kX_pos M h)
theorem rX_ne_zero (M : Matrix5) (h : SatFrame M) : rX M ≠ 0 := ne_of_gt (rX_pos M h)
theorem zero_le_pX (M : Matrix5) (h : SatFrame M) : 0 ≤ pX M := (pX_pos M h).le
theorem zero_le_kX (M : Matrix5) (h : SatFrame M) : 0 ≤ kX M := (kX_pos M h).le
theorem zero_le_rX (M : Matrix5) (h : SatFrame M) : 0 ≤ rX M := (rX_pos M h).le

/-- **Normalization**: every entry of a `SatFrame` matrix is in `[-1, 1]`. -/
theorem SatFrame.entry_le_one (M : Matrix5) (h : SatFrame M) :
    ∀ (i j : Fin 5), |M i j| ≤ 1 := by
  intro i j
  have hle := Rho5.MatrixNormalization.abs_entry_le_matrixEntryMax M i j
  rwa [h.hmax] at hle

/-- `w` obeys `|w| ≤ r` through the tail complete pivot. -/
theorem abs_wX_le_rX (M : Matrix5) (h : SatFrame M) : |wX M| ≤ rX M := by
  have hbase : |T2 M 0 0| = rX M := abs_of_pos (rX_pos M h)
  have hle := h.cp4 1 1
  rwa [hbase] at hle

/-- `w ≤ r`, the orientation used by the height reading. -/
theorem wX_le_rX (M : Matrix5) (h : SatFrame M) : wX M ≤ rX M :=
  (abs_le.mp (abs_wX_le_rX M h)).2

theorem eX_eq (M : Matrix5) : eX M = -(M 0 1) := rfl
theorem betaX_eq (M : Matrix5) : betaX M = M 1 0 := rfl
/-- `uX`/`vX`/`qX`/`xX` are already functions of the index, so the only reading needed is the
`Fin.succ` normalisation of the concrete numerals. -/
theorem uX_zero (M : Matrix5) : uX M 0 = M 2 0 := rfl
theorem uX_one (M : Matrix5) : uX M 1 = M 3 0 := rfl
theorem uX_two (M : Matrix5) : uX M 2 = M 4 0 := rfl
theorem vX_zero (M : Matrix5) : vX M 0 = M 0 2 := rfl
theorem vX_one (M : Matrix5) : vX M 1 = M 0 3 := rfl
theorem vX_two (M : Matrix5) : vX M 2 = M 0 4 := rfl
theorem qX_zero (M : Matrix5) : qX M 0 = M 1 2 - betaX M * M 0 2 := by simp [qX, vX]
theorem qX_one (M : Matrix5) : qX M 1 = M 1 3 - betaX M * M 0 3 := by simp [qX, vX]
theorem qX_two (M : Matrix5) : qX M 2 = M 1 4 - betaX M * M 0 4 := by simp [qX, vX]
theorem xX_zero (M : Matrix5) : xX M 0 = (M 2 1 + eX M * M 2 0) / pX M := by simp [xX, uX]
theorem xX_one (M : Matrix5) : xX M 1 = (M 3 1 + eX M * M 3 0) / pX M := by simp [xX, uX]
theorem xX_two (M : Matrix5) : xX M 2 = (M 4 1 + eX M * M 4 0) / pX M := by simp [xX, uX]

end

end Rho5.Shared.V43MatrixRoundTrip
