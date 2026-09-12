import Rho5.Shared.PaperB17Signs.Action
import Rho5.Certificate.B24Reconstruction.Basic

/-!
# D133 — the complete reconstruction identity `reconstruct z' = S · reconstruct z · S`

`Rho5.Certificate.B24Reconstruction.reconstruct z` is the one real `5 × 5` matrix of the
frozen source, reconstructed from the same B24 coordinates:
`[[1, -e, vᵀ], [β, p - eβ, (q + βv)ᵀ], [u, px - eu, O]]`.  This file proves, entry by entry
(all 25 entries, through the nine families), that conjugating that matrix by
`S = diag(1,1,ε,εη,εη)` is exactly `reconstruct` of the signed frame:

`reconstruct (encode (signedFrame f ε η) β p e t) i j
   = sigma ε η i * reconstruct (encode f β p e t) i j * sigma ε η j`.

No coordinate is patched independently: the identity is the actual matrix relation, and
combined with `D120.encode_decode` it is transported to an arbitrary `NormalizedB z` in
`Representative`.

The proof strategy: the head entries use only `p`, `e`, `β` of the encoded point (the three
`@[simp]` lemmas below), the `(0,2..4)`/`(1,2..4)`/`(2..4,0)`/`(2..4,1)` families use
`v_encode`/`P_encode`/`u_encode`/`L_encode` (`L_encode` is the `px - eu` entry) together with
`Action`, and the `3 × 3` block uses `O_encode` with `Action.original_signedFrame`.
`Fin.cases` splits `Fin 5` into `0`, `1` and the block indices so that each family lemma is
applied at its symbolic index.
-/

namespace Rho5.Shared.PaperB17Signs

open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail encode core original)
open Rho5.Certificate.B24Reconstruction (reconstruct p e beta)

noncomputable section

/-! ## 1. The head coordinates of an encoded point -/

@[simp] theorem p_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.p (encode f b p e t) = p := rfl

@[simp] theorem e_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.e (encode f b p e t) = e := rfl

@[simp] theorem beta_encode (f : Frame) (b p e : ℝ) (t : Tail) :
    Rho5.Certificate.B24Reconstruction.beta (encode f b p e t) = b := rfl

/-! ## 2. The nine entry families -/

theorem conj_00 (f : Frame) (t : Tail) (b p e eps eta : ℝ) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 0 0
      = sigma eps eta 0 * reconstruct (encode f b p e t) 0 0 * sigma eps eta 0 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma]

theorem conj_01 (f : Frame) (t : Tail) (b p e eps eta : ℝ) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 0 1
      = sigma eps eta 0 * reconstruct (encode f b p e t) 0 1 * sigma eps eta 1 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma]

theorem conj_0v (f : Frame) (t : Tail) (b p e eps eta : ℝ) (j : Fin 3) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 0 j.succ.succ
      = sigma eps eta 0 * reconstruct (encode f b p e t) 0 j.succ.succ
        * sigma eps eta j.succ.succ := by
  fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma, signedFrame, tau] <;> ring

theorem conj_10 (f : Frame) (t : Tail) (b p e eps eta : ℝ) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 1 0
      = sigma eps eta 1 * reconstruct (encode f b p e t) 1 0 * sigma eps eta 0 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma]

theorem conj_11 (f : Frame) (t : Tail) (b p e eps eta : ℝ) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 1 1
      = sigma eps eta 1 * reconstruct (encode f b p e t) 1 1 * sigma eps eta 1 := by
  simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma]

theorem conj_1P (f : Frame) (t : Tail) (b p e eps eta : ℝ) (j : Fin 3) :
    reconstruct (encode (signedFrame f eps eta) b p e t) 1 j.succ.succ
      = sigma eps eta 1 * reconstruct (encode f b p e t) 1 j.succ.succ
        * sigma eps eta j.succ.succ := by
  fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, Rho5.ExternalBFibreCapacity.P_encode,
      right_signedFrame, sigma, tau] <;> ring

theorem conj_u0 (f : Frame) (t : Tail) (b p e eps eta : ℝ) (i : Fin 3) :
    reconstruct (encode (signedFrame f eps eta) b p e t) i.succ.succ 0
      = sigma eps eta i.succ.succ * reconstruct (encode f b p e t) i.succ.succ 0
        * sigma eps eta 0 := by
  fin_cases i <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, sigma, signedFrame, tau] <;> ring

theorem conj_u1 (f : Frame) (t : Tail) (b p e eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (i : Fin 3) :
    reconstruct (encode (signedFrame f eps eta) b p e t) i.succ.succ 1
      = sigma eps eta i.succ.succ * reconstruct (encode f b p e t) i.succ.succ 1
        * sigma eps eta 1 := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, left_signedFrame, sigma, tau] <;> ring

theorem conj_OO (f : Frame) (t : Tail) (b p e eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (i j : Fin 3) :
    reconstruct (encode (signedFrame f eps eta) b p e t) i.succ.succ j.succ.succ
      = sigma eps eta i.succ.succ * reconstruct (encode f b p e t) i.succ.succ j.succ.succ
        * sigma eps eta j.succ.succ := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    simp [Rho5.Certificate.B24Reconstruction.reconstruct, Rho5.ExternalBFibreCapacity.O_encode,
      original, core, signedFrame, tau, sigma] <;> ring

/-! ## 3. The matrix identity -/

/-- **The complete real matrix relation.**  Conjugating the actual reconstructed matrix by
`S = diag(1,1,ε,εη,εη)` is exactly the reconstruction of the signed frame. -/
theorem reconstruct_signedFrame (f : Frame) (t : Tail) (b p e eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) :
    ∀ i j : Fin 5,
      reconstruct (encode (signedFrame f eps eta) b p e t) i j
        = sigma eps eta i * reconstruct (encode f b p e t) i j * sigma eps eta j := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · exact conj_00 f t b p e eps eta
    · refine Fin.cases ?_ (fun j'' => ?_) j'
      · exact conj_01 f t b p e eps eta
      · exact conj_0v f t b p e eps eta j''
  · refine Fin.cases ?_ (fun i'' => ?_) i'
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact conj_10 f t b p e eps eta
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · exact conj_11 f t b p e eps eta
        · exact conj_1P f t b p e eps eta j''
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact conj_u0 f t b p e eps eta i''
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · exact conj_u1 f t b p e eps eta hε hη i''
        · exact conj_OO f t b p e eps eta hε hη i'' j''

end

end Rho5.Shared.PaperB17Signs
