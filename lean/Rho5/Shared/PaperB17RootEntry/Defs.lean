/-
D134 — the B17 root predicate and the paper's isolated endpoint
==============================================================

Fixed interfaces of this lane:

* `gamma = 4132517 / 1000000` — the paper's explicit lower endpoint constant, kept as an exact
  rational (no decimal approximation anywhere);
* `gamma_lt_alpha : gamma < Rho5.Algebraic.AlphaRoot.alpha` — taken from the *actual* isolated
  endpoint `Rho5.Algebraic.AlphaRoot.alphaLower` (itself defined by the explicit rational of
  `AlphaRoot/Data.lean`) and the accepted interval theorem
  `Rho5.Algebraic.AlphaRoot.alpha_in_exact_interval`; nothing is assumed about `alpha`;
* `B17RootVector v` — the complete 17-dimensional closed root, indexed by `Fin 17` in the exact
  `frameVector` order `(k, A, B, c, d, u0, u1, u2, x0, x1, x2, v0, v1, v2, q0, q1, q2)`, with the
  paper's endpoints slot by slot:
  `4γ/9 ≤ k ≤ 9/4`, `-9/4 ≤ A ≤ 0`, `|B| ≤ 9/4`, `|c|, |d| ≤ 1`, `|u_i| ≤ 1`,
  `0 ≤ x0 ≤ 1`, `|x1|, |x2| ≤ 1`, `|v_i| ≤ 1`, `|q_i| ≤ 2`;
* `B17Root f := B17RootVector (frameVector f)` — so the 17 slots are definitionally the
  `frameVector` coordinates, and `b17Root_endpoint_table` records the slot-by-slot correspondence
  with the paper's table as a theorem (not a numeric check or a hash).

The predicate deliberately contains **no** feasibility, capacity, RootMembership or maximum
conclusion: it is the closed root only.
-/
import Rho5.ExternalBFibreCapacity.Model
import Rho5.Algebraic.AlphaRoot.Root

namespace Rho5.Shared.PaperB17RootEntry

noncomputable section
set_option maxHeartbeats 800000

open Rho5.ExternalBFibreCapacity (Frame frameOf frameVector frameOfVector)

/-- The paper's isolated endpoint constant, exactly as a rational. -/
def gamma : ℝ := 4132517 / 1000000

/-- **`γ < alpha` from the actual isolated endpoint.**  The comparison is made against the exact
rational `Rho5.Algebraic.AlphaRoot.alphaLower` and then transported through the accepted interval
theorem; no decimal approximation and no new root hypothesis is used. -/
theorem gamma_lt_alpha : gamma < Rho5.Algebraic.AlphaRoot.alpha := by
  have h : gamma < Rho5.Algebraic.AlphaRoot.alphaLower := by
    norm_num [gamma, Rho5.Algebraic.AlphaRoot.alphaLower]
  exact lt_trans h Rho5.Algebraic.AlphaRoot.alpha_in_exact_interval.1

/-- `γ` is positive. -/
theorem gamma_pos : 0 < gamma := by norm_num [gamma]

/-- **The complete 17-dimensional closed B-root**, slot by slot in the `frameVector` order
`(k, A, B, c, d, u0, u1, u2, x0, x1, x2, v0, v1, v2, q0, q1, q2)`. -/
def B17RootVector (v : Fin 17 → ℝ) : Prop :=
  (4 * gamma / 9 ≤ v 0 ∧ v 0 ≤ 9 / 4) ∧
    (-(9 / 4) ≤ v 1 ∧ v 1 ≤ 0) ∧
    (|v 2| ≤ 9 / 4) ∧
    (|v 3| ≤ 1 ∧ |v 4| ≤ 1) ∧
    (|v 5| ≤ 1 ∧ |v 6| ≤ 1 ∧ |v 7| ≤ 1) ∧
    (0 ≤ v 8 ∧ v 8 ≤ 1) ∧
    (|v 9| ≤ 1 ∧ |v 10| ≤ 1) ∧
    (|v 11| ≤ 1 ∧ |v 12| ≤ 1 ∧ |v 13| ≤ 1) ∧
    (|v 14| ≤ 2 ∧ |v 15| ≤ 2 ∧ |v 16| ≤ 2)

/-- **The root predicate on a frame**, in the fixed `frameVector` order. -/
def B17Root (f : Frame) : Prop := B17RootVector (frameVector f)

/-- The predicate unfolds to the `frameVector` coordinates definitionally. -/
theorem b17Root_iff_vector (f : Frame) : B17Root f ↔ B17RootVector (frameVector f) := Iff.rfl

/-- The predicate in terms of `frameOfVector`, i.e. the same 17 slots read off from a vector. -/
theorem b17Root_frameOfVector (v : Fin 17 → ℝ) :
    B17Root (frameOfVector v) ↔ B17RootVector v := by
  rw [B17Root, Rho5.ExternalBFibreCapacity.frameVector_frameOfVector]

/-! ## The slot-by-slot endpoint table -/

/-- **The paper's endpoint table, slot by slot.**  Each `frameVector` slot carries exactly the
endpoint of the original formula: slot `0 = k`, `1 = A`, `2 = B`, `3 = c`, `4 = d`, `5..7 = u0..u2`,
`8..10 = x0..x2`, `11..13 = v0..v2`, `14..16 = q0..q2`, with the bounds
`[4γ/9, 9/4]`, `[-9/4, 0]`, `[-9/4, 9/4]`, `[-1,1]`, `[-1,1]`, `[-1,1]³`, `[0,1]×[-1,1]²`,
`[-1,1]³`, `[-2,2]³` in that order. -/
theorem b17Root_endpoint_table (f : Frame) :
    (frameVector f 0 = f.k ∧ frameVector f 1 = f.A ∧ frameVector f 2 = f.B ∧
      frameVector f 3 = f.c ∧ frameVector f 4 = f.d) ∧
    (frameVector f 5 = f.u 0 ∧ frameVector f 6 = f.u 1 ∧ frameVector f 7 = f.u 2) ∧
    (frameVector f 8 = f.x 0 ∧ frameVector f 9 = f.x 1 ∧ frameVector f 10 = f.x 2) ∧
    (frameVector f 11 = f.v 0 ∧ frameVector f 12 = f.v 1 ∧ frameVector f 13 = f.v 2) ∧
    (frameVector f 14 = f.q 0 ∧ frameVector f 15 = f.q 1 ∧ frameVector f 16 = f.q 2) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩⟩

/-- The same table in `frameOf z` coordinates: the root slots are the actual B24 coordinates
`z 0, z 4, z 5, z 6, z 7, z 11..13, z 14..16, z 17..19, z 20..22`. -/
theorem b17Root_frameOf_slots (z : Rho5.Certificate.B16.Point) :
    (frameVector (frameOf z) 0 = z 0 ∧ frameVector (frameOf z) 1 = z 4 ∧
      frameVector (frameOf z) 2 = z 5 ∧ frameVector (frameOf z) 3 = z 6 ∧
      frameVector (frameOf z) 4 = z 7) ∧
    (frameVector (frameOf z) 5 = z 11 ∧ frameVector (frameOf z) 6 = z 12 ∧
      frameVector (frameOf z) 7 = z 13) ∧
    (frameVector (frameOf z) 8 = z 14 ∧ frameVector (frameOf z) 9 = z 15 ∧
      frameVector (frameOf z) 10 = z 16) ∧
    (frameVector (frameOf z) 11 = z 17 ∧ frameVector (frameOf z) 12 = z 18 ∧
      frameVector (frameOf z) 13 = z 19) ∧
    (frameVector (frameOf z) 14 = z 20 ∧ frameVector (frameOf z) 15 = z 21 ∧
      frameVector (frameOf z) 16 = z 22) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩⟩

end

end Rho5.Shared.PaperB17RootEntry
