import Rho5.Shared.BHeadSign.Action
import Rho5.Certificate.B24Reconstruction.Basic

/-!
# D137 — the reconstruction identity for the second row/column flip

`Rho5.Certificate.B24Reconstruction.reconstruct` is the one real `5 × 5` matrix
`[[1, -e, vᵀ], [β, p - eβ, (q + βv)ᵀ], [u, px - eu, O]]`.  This file proves, entry by entry
(all 25 entries through the nine emitted families), that conjugating it by
`S = diag(1,σ,1,1,1)` is exactly the reconstruction of the flipped frame with the two head
coordinates flipped:

`reconstruct (headEncode f t β p e σ) i j = sgOf σ i * reconstruct (encode f β p e t) i j * sgOf σ j`.

Combined with D120's `encode_decode` this is transported to an arbitrary `Qualified z` in
`Representative`, so the relation proved is the matrix relation of `z`'s own real matrix.

The head entries use only `p`, `e`, `β` of the encoded point (`p_headEncode`, `e_headEncode`,
`beta_headEncode`); `(0,2..4)` uses `v_encode`; `(1,2..4)` uses `P_encode` and
`Action.right_headFrame`; `(2..4,0)` uses `u_encode`; `(2..4,1)` uses `L_encode` and
`Action.left_headFrame`; the `3 × 3` block uses `O_encode` and `Action.original_headFrame`.
`Fin.cases` splits `Fin 5` into `0`, `1` and the block indices so every family lemma is applied
at its symbolic index.
-/

namespace Rho5.Shared.BHeadSign

open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail encode frameOf tailOf core original encode_decode)
open Rho5.Certificate.B24Reconstruction (reconstruct)

noncomputable section

/-! ## 1. The head coordinates of the flipped encoding -/

@[simp] theorem p_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.p (encode f b p e t) = p := rfl

@[simp] theorem e_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.e (encode f b p e t) = e := rfl

@[simp] theorem beta_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.beta (encode f b p e t) = b := rfl

@[simp] theorem p_headEncode (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.p (headEncode f t b p e sigma) = p := rfl

@[simp] theorem e_headEncode (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.e (headEncode f t b p e sigma) = sigma * e := rfl

@[simp] theorem beta_headEncode (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    Rho5.Certificate.B24Reconstruction.beta (headEncode f t b p e sigma) = sigma * b := rfl

/-! ## 2. The nine entry families -/

theorem conj2_00 (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    reconstruct (headEncode f t b p e sigma) 0 0
      = sgOf sigma 0 * reconstruct (encode f b p e t) 0 0 * sgOf sigma 0 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, sgOf]

theorem conj2_01 (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    reconstruct (headEncode f t b p e sigma) 0 1
      = sgOf sigma 0 * reconstruct (encode f b p e t) 0 1 * sgOf sigma 1 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, sgOf]
  ring

theorem conj2_0v (f : Frame) (t : Tail) (b p e sigma : ℝ) (j : Fin 3) :
    reconstruct (headEncode f t b p e sigma) 0 j.succ.succ
      = sgOf sigma 0 * reconstruct (encode f b p e t) 0 j.succ.succ
        * sgOf sigma j.succ.succ := by
  fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, headFrame, sgOf]

theorem conj2_10 (f : Frame) (t : Tail) (b p e sigma : ℝ) :
    reconstruct (headEncode f t b p e sigma) 1 0
      = sgOf sigma 1 * reconstruct (encode f b p e t) 1 0 * sgOf sigma 0 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, sgOf]

theorem conj2_11 (f : Frame) (t : Tail) (b p e sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) :
    reconstruct (headEncode f t b p e sigma) 1 1
      = sgOf sigma 1 * reconstruct (encode f b p e t) 1 1 * sgOf sigma 1 := by
  rcases hσ with rfl | rfl <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, sgOf]

theorem conj2_1P (f : Frame) (t : Tail) (b p e sigma : ℝ) (j : Fin 3) :
    reconstruct (headEncode f t b p e sigma) 1 j.succ.succ
      = sgOf sigma 1 * reconstruct (encode f b p e t) 1 j.succ.succ
        * sgOf sigma j.succ.succ := by
  fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, headFrame,
      Rho5.ExternalBFibreCapacity.P_encode, sgOf] <;> ring

theorem conj2_u0 (f : Frame) (t : Tail) (b p e sigma : ℝ) (i : Fin 3) :
    reconstruct (headEncode f t b p e sigma) i.succ.succ 0
      = sgOf sigma i.succ.succ * reconstruct (encode f b p e t) i.succ.succ 0
        * sgOf sigma 0 := by
  fin_cases i <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, headFrame, sgOf]

theorem conj2_u1 (f : Frame) (t : Tail) (b p e sigma : ℝ) (i : Fin 3) :
    reconstruct (headEncode f t b p e sigma) i.succ.succ 1
      = sgOf sigma i.succ.succ * reconstruct (encode f b p e t) i.succ.succ 1
        * sgOf sigma 1 := by
  fin_cases i <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, headFrame,
      sgOf] <;> ring

theorem conj2_OO (f : Frame) (t : Tail) (b p e sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) (i j : Fin 3) :
    reconstruct (headEncode f t b p e sigma) i.succ.succ j.succ.succ
      = sgOf sigma i.succ.succ * reconstruct (encode f b p e t) i.succ.succ j.succ.succ
        * sgOf sigma j.succ.succ := by
  rcases hσ with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, headEncode, headFrame,
      Rho5.ExternalBFibreCapacity.O_encode, original, core, sgOf]

/-! ## 3. The two exported matrix identities -/

/-- **The complete real matrix relation at the frame level.**  Conjugating the actual
reconstructed matrix by `diag(1,σ,1,1,1)` is exactly the reconstruction of the flipped frame. -/
theorem reconstruct_headEncode (f : Frame) (t : Tail) (b p e sigma : ℝ)
    (hσ : sigma = 1 ∨ sigma = -1) :
    ∀ i j, reconstruct (headEncode f t b p e sigma) i j
      = sgOf sigma i * reconstruct (encode f b p e t) i j * sgOf sigma j := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · exact conj2_00 f t b p e sigma
    · refine Fin.cases ?_ (fun j'' => ?_) j'
      · exact conj2_01 f t b p e sigma
      · exact conj2_0v f t b p e sigma j''
  · refine Fin.cases ?_ (fun i'' => ?_) i'
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact conj2_10 f t b p e sigma
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · exact conj2_11 f t b p e sigma hσ
        · exact conj2_1P f t b p e sigma j''
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact conj2_u0 f t b p e sigma i''
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · exact conj2_u1 f t b p e sigma i''
        · exact conj2_OO f t b p e sigma hσ i'' j''

/-- **The complete real matrix relation for the flipped point of `z`**: the conjugation is of
`z`'s own reconstructed matrix, using only `Qualified z` to rewrite `z` as the encoding of its
frame. -/
theorem reconstruct_headPointOf (z : Point) (hq : Rho5.Certificate.B24MinorBridge.Qualified z)
    (sigma : ℝ) (hσ : sigma = 1 ∨ sigma = -1) :
    ∀ i j, reconstruct (headPointOf z sigma) i j
      = sgOf sigma i * reconstruct z i j * sgOf sigma j := by
  intro i j
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z := encode_decode z hq.physical
  have hs := reconstruct_headEncode (frameOf z) (tailOf z) (z 10) (z 8) (z 9) sigma hσ i j
  have hz : reconstruct (encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z)) i j
      = reconstruct z i j := by
    rw [hdec]
  rw [hz] at hs
  simpa [headPointOf] using hs

end

end Rho5.Shared.BHeadSign
