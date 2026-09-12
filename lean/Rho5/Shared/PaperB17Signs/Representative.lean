import Rho5.Shared.PaperB17Signs.Matrix

/-!
# D133 — the sign representative of a normalized B point

This file transfers D120's actual predicate `NormalizedB` (equivalently `Admissible`, through
the frozen `admissible_iff_normalized`) along the signed frame, chooses the two signs from `z`
itself, and exports the card's fixed interface:

`normalizedB_has_sign_representative :`
for every `z` with `NormalizedB z` there are `z'` and `sg : Fin 5 → ℝ` with every `sg i = ±1`,
`reconstruct z' i j = sg i * reconstruct z i j * sg j` (the *actual* matrix relation), `NormalizedB z'`,
`z' 23 = z 23`, `z' 8 = z 8`, `z' 0 = z 0`, `z' 1 = z 1`, `z' 2 = z 2`, `z' 3 = z 3`,
`z' 9 = z 9`, `z' 10 = z 10`, `0 ≤ z' 14` and `z' 4 ≤ 0`.

The choice is the paper's own: `ε = 1` if `0 ≤ z 14` else `-1` (first flip, making `x0 ≥ 0`),
`η = 1` if `z 4 ≤ 0` else `-1` (second flip, making `A ≤ 0`).  Zero is decided to `+1`, and the
equality boundary is covered.  The stage-A theorem `normalizedB_has_x0_nonneg_representative`
is the first flip alone (`η = 1`), which keeps `A, B, c, d` and the whole head untouched.

No high-value hypothesis (`alpha < z 23`) and no feasibility, capacity or source conclusion is
used anywhere: the transfer consumes only `NormalizedB z` and the real reconstruction.
-/

namespace Rho5.Shared.PaperB17Signs

open Classical
open Rho5.Certificate.B16 (Point)
open Rho5.ExternalBFibreCapacity (Frame Tail NormalizedB encode frameOf tailOf Admissible
  FrameBounds PrefixBounds TailBounds core stage original tailHeight admissible_iff_normalized
  admissible_decode encode_decode)
open Rho5.Certificate.B24Reconstruction (reconstruct)

noncomputable section

/-! ## 1. `Admissible` and `NormalizedB` transfer -/

/-- **All coupling bands are preserved.**  Every field of `Admissible` (frame bounds, the six
prefix bands `1 ≤ p`, `0 ≤ e ≤ 1`, `0 ≤ β ≤ 1`, `|p - eβ| ≤ 1`, `|L_i| ≤ 1`, `|P_j| ≤ 1`,
`|q_j| ≤ p`, and the tail bounds `r > 0`, `0 ≤ s ≤ r`, `0 ≤ t ≤ r`, `|D| ≤ k`, `|S| ≤ p`,
`|O| ≤ 1`) is transported along `signedFrame`, using the block equivariance of `Action` and
`|tau ε η i| = 1`.  The tail `r, s, t` is untouched, so the height is preserved. -/
theorem admissible_signedFrame (f : Frame) (t : Tail) (b p e eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1) (h : Admissible f b p e t) :
    Admissible (signedFrame f eps eta) b p e t := by
  obtain ⟨hf, hp, ht⟩ := h
  refine ⟨⟨hf.k_pos, ?_, ?_, ?_⟩,
    ⟨hp.one_le_p, hp.e_nonneg, hp.e_le_one, hp.beta_nonneg, hp.beta_le_one, hp.head, ?_, ?_, ?_⟩,
    ⟨ht.r_pos, ht.s_nonneg, ht.s_le_r, ht.t_nonneg, ht.t_le_r, ?_, ?_, ?_⟩⟩
  · intro i
    have h1 : (signedFrame f eps eta).u i = tau eps eta i * f.u i := rfl
    rw [h1, abs_mul, abs_tau eps eta hε hη i, one_mul]
    exact hf.u_bound i
  · intro i
    have h1 : (signedFrame f eps eta).x i = tau eps eta i * f.x i := rfl
    rw [h1, abs_mul, abs_tau eps eta hε hη i, one_mul]
    exact hf.x_bound i
  · intro i
    have h1 : (signedFrame f eps eta).v i = tau eps eta i * f.v i := rfl
    rw [h1, abs_mul, abs_tau eps eta hε hη i, one_mul]
    exact hf.v_bound i
  · intro i
    rw [left_signedFrame f eps eta p e i, abs_mul, abs_tau eps eta hε hη i, one_mul]
    exact hp.left i
  · intro j
    rw [right_signedFrame f eps eta b j, abs_mul, abs_tau eps eta hε hη j, one_mul]
    exact hp.right j
  · intro j
    have h1 : (signedFrame f eps eta).q j = tau eps eta j * f.q j := rfl
    rw [h1, abs_mul, abs_tau eps eta hε hη j, one_mul]
    exact hp.q_stage j
  · intro i j
    rw [core_signedFrame f t eps eta hε hη i j, abs_mul, abs_mul,
      abs_tau eps eta hε hη i, abs_tau eps eta hε hη j]
    simp only [signedFrame, one_mul]
    exact ht.core i j
  · intro i j
    rw [stage_signedFrame f t eps eta hε hη i j, abs_mul, abs_mul,
      abs_tau eps eta hε hη i, abs_tau eps eta hε hη j]
    simp only [signedFrame, one_mul]
    exact ht.stage i j
  · intro i j
    rw [original_signedFrame f t eps eta hε hη i j, abs_mul, abs_mul,
      abs_tau eps eta hε hη i, abs_tau eps eta hε hη j]
    simp only [signedFrame, one_mul]
    exact ht.original i j

/-- The actual predicate `NormalizedB` is preserved by both flips. -/
theorem normalizedB_signedFrame (f : Frame) (t : Tail) (b p e eps eta : ℝ)
    (hε : eps = 1 ∨ eps = -1) (hη : eta = 1 ∨ eta = -1)
    (h : NormalizedB (encode f b p e t)) :
    NormalizedB (encode (signedFrame f eps eta) b p e t) :=
  (admissible_iff_normalized (signedFrame f eps eta) b p e t).mp
    (admissible_signedFrame f t b p e eps eta hε hη
      ((admissible_iff_normalized f b p e t).mpr h))

/-! ## 2. The two sign choices -/

/-- The first flip `ε`: chosen so that `x0 ≥ 0` (zero goes to `+1`). -/
def epsOf (z : Point) : ℝ := if 0 ≤ z 14 then 1 else -1

/-- The second flip `η`: chosen so that `A ≤ 0` (zero goes to `+1`). -/
def etaOf (z : Point) : ℝ := if z 4 ≤ 0 then 1 else -1

theorem epsOf_eq_one_or_neg_one (z : Point) : epsOf z = 1 ∨ epsOf z = -1 := by
  unfold epsOf
  by_cases h : 0 ≤ z 14
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem etaOf_eq_one_or_neg_one (z : Point) : etaOf z = 1 ∨ etaOf z = -1 := by
  unfold etaOf
  by_cases h : z 4 ≤ 0
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- The first flip makes the `x0` coordinate nonnegative, equality included. -/
theorem epsOf_mul_nonneg (z : Point) : 0 ≤ epsOf z * z 14 := by
  unfold epsOf
  by_cases h : 0 ≤ z 14
  · rw [if_pos h]; simpa using h
  · rw [if_neg h]
    have h' : z 14 ≤ 0 := le_of_not_ge h
    nlinarith

/-- The second flip makes the `A` coordinate nonpositive, equality included. -/
theorem etaOf_mul_nonpos (z : Point) : etaOf z * z 4 ≤ 0 := by
  unfold etaOf
  by_cases h : z 4 ≤ 0
  · rw [if_pos h]; simpa using h
  · rw [if_neg h]
    have h' : 0 < z 4 := lt_of_not_ge h
    nlinarith

/-! ## 3. The normalized point (both flips) -/

/-- Both flips: `diag(1,1,ε,εη,εη)` applied to the frame of `z`. -/
def signFrame (z : Point) : Frame := signedFrame (frameOf z) (epsOf z) (etaOf z)

/-- Both flips, as an actual point of the same B24 model. -/
def signPoint (z : Point) : Point := encode (signFrame z) (z 10) (z 8) (z 9) (tailOf z)

/-- The composed sign vector `diag(1,1,ε,εη,εη)`. -/
def signVector (z : Point) : Fin 5 → ℝ := sigma (epsOf z) (etaOf z)

@[simp] theorem signPoint_apply_zero (z : Point) : signPoint z 0 = z 0 := rfl

@[simp] theorem signPoint_apply_one (z : Point) : signPoint z 1 = z 1 := rfl

@[simp] theorem signPoint_apply_two (z : Point) : signPoint z 2 = z 2 := rfl

@[simp] theorem signPoint_apply_three (z : Point) : signPoint z 3 = z 3 := rfl

@[simp] theorem signPoint_apply_four (z : Point) : signPoint z 4 = etaOf z * z 4 := rfl

@[simp] theorem signPoint_apply_eight (z : Point) : signPoint z 8 = z 8 := rfl

@[simp] theorem signPoint_apply_nine (z : Point) : signPoint z 9 = z 9 := rfl

@[simp] theorem signPoint_apply_ten (z : Point) : signPoint z 10 = z 10 := rfl

@[simp] theorem signPoint_apply_fourteen (z : Point) : signPoint z 14 = epsOf z * z 14 := rfl

/-- The height is preserved: the tail `r, s, t` is untouched by both flips, and the `23`-th
coordinate of the encoding is the computed height `r + s t / r`. -/
theorem signPoint_apply_height (z : Point) (h : NormalizedB z) : signPoint z 23 = z 23 := by
  rw [h.1.physical.height]
  rfl

/-- `NormalizedB` survives both flips. -/
theorem normalizedB_signPoint (z : Point) (h : NormalizedB z) : NormalizedB (signPoint z) := by
  have hnew := admissible_signedFrame (frameOf z) (tailOf z) (z 10) (z 8) (z 9)
    (epsOf z) (etaOf z) (epsOf_eq_one_or_neg_one z) (etaOf_eq_one_or_neg_one z)
    (admissible_decode z h)
  have hfin := (admissible_iff_normalized (signedFrame (frameOf z) (epsOf z) (etaOf z))
    (z 10) (z 8) (z 9) (tailOf z)).mp hnew
  simpa [signPoint, signFrame] using hfin

/-! ## 4. The first flip alone (stage A) -/

/-- The first paper flip alone: `diag(1,1,ε,ε,ε)`. -/
def flipFrame (z : Point) : Frame := signedFrame (frameOf z) (epsOf z) 1

/-- The first flip alone, as a point. -/
def flipPoint (z : Point) : Point := encode (flipFrame z) (z 10) (z 8) (z 9) (tailOf z)

/-- The sign vector of the first flip alone: `diag(1,1,ε,ε,ε)`. -/
def flipVector (z : Point) : Fin 5 → ℝ := sigma (epsOf z) 1

theorem flipPoint_apply_four (z : Point) : flipPoint z 4 = z 4 := by
  show (1 : ℝ) * z 4 = z 4
  rw [one_mul]

theorem flipPoint_apply_five (z : Point) : flipPoint z 5 = z 5 := by
  show (1 : ℝ) * z 5 = z 5
  rw [one_mul]

theorem flipPoint_apply_six (z : Point) : flipPoint z 6 = z 6 := by
  show (1 : ℝ) * z 6 = z 6
  rw [one_mul]

theorem flipPoint_apply_seven (z : Point) : flipPoint z 7 = z 7 := by
  show (1 : ℝ) * z 7 = z 7
  rw [one_mul]

@[simp] theorem flipPoint_apply_fourteen (z : Point) : flipPoint z 14 = epsOf z * z 14 := rfl

/-- The height is preserved by the first flip alone. -/
theorem flipPoint_apply_height (z : Point) (h : NormalizedB z) : flipPoint z 23 = z 23 := by
  rw [h.1.physical.height]
  rfl

/-- `NormalizedB` survives the first flip alone. -/
theorem normalizedB_flipPoint (z : Point) (h : NormalizedB z) : NormalizedB (flipPoint z) := by
  have hnew := admissible_signedFrame (frameOf z) (tailOf z) (z 10) (z 8) (z 9)
    (epsOf z) 1 (epsOf_eq_one_or_neg_one z) (Or.inl rfl) (admissible_decode z h)
  have hfin := (admissible_iff_normalized (signedFrame (frameOf z) (epsOf z) 1)
    (z 10) (z 8) (z 9) (tailOf z)).mp hnew
  simpa [flipPoint, flipFrame] using hfin

/-! ## 5. The coupling bands for the normalized point, in the original coordinates -/

/-- The real `3 × 3` block `D` of the normalized point is the signed conjugate of `D z`. -/
theorem D_signPoint (z : Point) (h : NormalizedB z) (i j : Fin 3) :
    Rho5.Certificate.B16.D (signPoint z) i j
      = tau (epsOf z) (etaOf z) i * tau (epsOf z) (etaOf z) j * Rho5.Certificate.B16.D z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  have hc := core_signedFrame (frameOf z) (tailOf z) (epsOf z) (etaOf z)
    (epsOf_eq_one_or_neg_one z) (etaOf_eq_one_or_neg_one z) i j
  rw [← hdec]
  simpa [signPoint, signFrame] using hc

/-- The stage block `S = D + x qᵀ` of the normalized point is the signed conjugate. -/
theorem S_signPoint (z : Point) (h : NormalizedB z) (i j : Fin 3) :
    Rho5.Certificate.B16.S (signPoint z) i j
      = tau (epsOf z) (etaOf z) i * tau (epsOf z) (etaOf z) j * Rho5.Certificate.B16.S z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  have hc := stage_signedFrame (frameOf z) (tailOf z) (epsOf z) (etaOf z)
    (epsOf_eq_one_or_neg_one z) (etaOf_eq_one_or_neg_one z) i j
  rw [← hdec]
  simpa [signPoint, signFrame] using hc

/-- The original block `O = D + x qᵀ + u vᵀ` of the normalized point is the signed conjugate. -/
theorem O_signPoint (z : Point) (h : NormalizedB z) (i j : Fin 3) :
    Rho5.Certificate.B16.O (signPoint z) i j
      = tau (epsOf z) (etaOf z) i * tau (epsOf z) (etaOf z) j * Rho5.Certificate.B16.O z i j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  have hc := original_signedFrame (frameOf z) (tailOf z) (epsOf z) (etaOf z)
    (epsOf_eq_one_or_neg_one z) (etaOf_eq_one_or_neg_one z) i j
  rw [← hdec]
  simpa [signPoint, signFrame] using hc

/-- The left head band `L_i = p x_i - e u_i` of the normalized point is the signed conjugate. -/
theorem L_signPoint (z : Point) (h : NormalizedB z) (i : Fin 3) :
    Rho5.Certificate.B16.L (signPoint z) i
      = tau (epsOf z) (etaOf z) i * Rho5.Certificate.B16.L z i := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  have hc := left_signedFrame (frameOf z) (epsOf z) (etaOf z) (z 8) (z 9) i
  rw [← hdec]
  simpa [signPoint, signFrame] using hc

/-- The right head band `P_j = β v_j + q_j` of the normalized point is the signed conjugate. -/
theorem P_signPoint (z : Point) (h : NormalizedB z) (j : Fin 3) :
    Rho5.Certificate.B16.P (signPoint z) j
      = tau (epsOf z) (etaOf z) j * Rho5.Certificate.B16.P z j := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  have hc := right_signedFrame (frameOf z) (epsOf z) (etaOf z) (z 10) j
  rw [← hdec]
  simpa [signPoint, signFrame] using hc

/-! ## 6. The exported theorems -/

/-- **Stage A — the first paper flip.**  Simultaneously flipping the last three rows and
columns of the real reconstructed matrix (equivalently `u, x, v, q ↦ ε·`, everything else
untouched) makes `x0` nonnegative and preserves `NormalizedB`, the height, `k, r, s, t, p, e, β`
and `A, B, c, d`, with the complete matrix identity. -/
theorem normalizedB_has_x0_nonneg_representative (z : Point) (h : NormalizedB z) :
    ∃ (z' : Point) (sg : Fin 5 → ℝ),
      (∀ i, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j, reconstruct z' i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB z' ∧ z' 23 = z 23 ∧ z' 8 = z 8 ∧ z' 0 = z 0 ∧ z' 1 = z 1 ∧ z' 2 = z 2 ∧
      z' 3 = z 3 ∧ z' 4 = z 4 ∧ z' 5 = z 5 ∧ z' 6 = z 6 ∧ z' 7 = z 7 ∧ z' 9 = z 9 ∧
      z' 10 = z 10 ∧ 0 ≤ z' 14 := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  refine ⟨flipPoint z, flipVector z, ?_, ?_, normalizedB_flipPoint z h,
    flipPoint_apply_height z h, rfl, rfl, rfl, rfl, rfl, flipPoint_apply_four z,
    flipPoint_apply_five z, flipPoint_apply_six z, flipPoint_apply_seven z, rfl, rfl, ?_⟩
  · intro i
    exact sigma_eq_one_or_neg_one (epsOf z) 1 (epsOf_eq_one_or_neg_one z) (Or.inl rfl) i
  · intro i j
    have hs := reconstruct_signedFrame (frameOf z) (tailOf z) (z 10) (z 8) (z 9) (epsOf z) 1
      (epsOf_eq_one_or_neg_one z) (Or.inl rfl) i j
    rw [hdec] at hs
    simpa [flipPoint, flipFrame, flipVector] using hs
  · show (0 : ℝ) ≤ epsOf z * z 14
    exact epsOf_mul_nonneg z

/-- **The card's fixed interface — both paper flips.**  For every `NormalizedB z` there are
`z'` and `sg : Fin 5 → ℝ`, each `sg i = ±1`, such that `z'` is the actual legal row/column sign
conjugate `reconstruct z' = diag(sg) · reconstruct z · diag(sg)` of the one real reconstructed
matrix, `NormalizedB z'` holds, the height and the head/tail coordinates
`z 23, z 8, z 0, z 1, z 2, z 3, z 9, z 10` are preserved, and `0 ≤ z' 14`, `z' 4 ≤ 0`. -/
theorem normalizedB_has_sign_representative (z : Point) (h : NormalizedB z) :
    ∃ (z' : Point) (sg : Fin 5 → ℝ),
      (∀ i, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j, reconstruct z' i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB z' ∧ z' 23 = z 23 ∧ z' 8 = z 8 ∧ z' 0 = z 0 ∧ z' 1 = z 1 ∧ z' 2 = z 2 ∧
      z' 3 = z 3 ∧ z' 9 = z 9 ∧ z' 10 = z 10 ∧ 0 ≤ z' 14 ∧ z' 4 ≤ 0 := by
  have hdec : encode (frameOf z) (z 10) (z 8) (z 9) (tailOf z) = z :=
    encode_decode z h.1.physical
  refine ⟨signPoint z, signVector z, ?_, ?_, normalizedB_signPoint z h, signPoint_apply_height z h,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i
    exact sigma_eq_one_or_neg_one (epsOf z) (etaOf z) (epsOf_eq_one_or_neg_one z)
      (etaOf_eq_one_or_neg_one z) i
  · intro i j
    have hs := reconstruct_signedFrame (frameOf z) (tailOf z) (z 10) (z 8) (z 9) (epsOf z)
      (etaOf z) (epsOf_eq_one_or_neg_one z) (etaOf_eq_one_or_neg_one z) i j
    rw [hdec] at hs
    simpa [signPoint, signFrame, signVector] using hs
  · show (0 : ℝ) ≤ epsOf z * z 14
    exact epsOf_mul_nonneg z
  · show etaOf z * z 4 ≤ 0
    exact etaOf_mul_nonpos z

end

end Rho5.Shared.PaperB17Signs
