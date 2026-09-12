/-
D70 stage 2 — each disjunct, and the whole four-disjunct predicate, is equivalent to the
actual Schur faces `M 4 4 = -1`, `S4 M 3 3 = -p M`, `S3 M 2 2 = -k M`, `T2 M 1 1 = -r M`.

The transports are the accepted D61/D62 identities, used as paid:

* `m2 M i j = S4 M i j`                       (D61 `m2_eq_S4`, needs `M 0 0 = 1`);
* `m3 M i j = p M * S3 M i j`                 (D61 `m3_eq_p_mul_S3`, needs `M 0 0 = 1`, `p M ≠ 0`);
* `m4 M 1 1 = p M * k M * T2 M 1 1`           (D62 `m4_11_eq`, needs `0 < p M`, `0 < k M`);
* `A M = p M`, `B M = p M * k M`, `C M = p M * k M * r M` (D62).

Face 1 is the same formula on both sides.  Faces 2–4 cancel only the **proved positive**
factors `p M` and `p M * k M` (`mul_left_cancel₀`, no division, no assumed conclusion), so
the equivalence carries exactly the hypotheses the paid identities need.  The `PolyCP`
versions derive that positivity from D62's `polyCP_iff_frame` instead of asking for it.
-/
import Rho5.Shared.MinorBoundaryFaces.Defs

namespace Rho5.MinorBoundaryFaces

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)
open Rho5.MinorCPDomain (A B C PolyCP m4)

/-! ## 1. Each disjunct on its own -/

/-- Face 1 is literally the first Schur face. -/
theorem face1_iff (M : Matrix5) : face1 M ↔ M 4 4 = -1 := Iff.rfl

/-- Face 2: `m2 3 3 = -A` is `S4 M 3 3 = -p M`, by D61's pointwise `m2 = S4` and
`A = p`.  No positivity is needed, only `M 0 0 = 1`. -/
theorem face2_iff (M : Matrix5) (h00 : M 0 0 = 1) : face2 M ↔ S4 M 3 3 = -p M := by
  show Rho5.PrefixBorderedMinors.m2 M 3 3 = -A M ↔ S4 M 3 3 = -p M
  rw [Rho5.PrefixBorderedMinors.m2_eq_S4 M h00 3 3, Rho5.MinorCPDomain.A_eq M h00]

/-- Face 3: `m3 2 2 = -B` is `S3 M 2 2 = -k M`, cancelling the proved positive `p M`
from D61's `m3 = p * S3` and D62's `B = p * k`. -/
theorem face3_iff (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) :
    face3 M ↔ S3 M 2 2 = -k M := by
  show Rho5.PrefixBorderedMinors.m3 M 2 2 = -B M ↔ S3 M 2 2 = -k M
  rw [Rho5.PrefixBorderedMinors.m3_eq_p_mul_S3 M h00 (ne_of_gt hp) 2 2,
    Rho5.MinorCPDomain.B_eq M h00 (ne_of_gt hp)]
  constructor
  · intro h
    rw [← mul_neg] at h
    exact mul_left_cancel₀ (ne_of_gt hp) h
  · intro h
    rw [h, mul_neg]

/-- Face 4: `m4 1 1 = -C` is `T2 M 1 1 = -r M`, cancelling the proved positive product
`p M * k M` from D62's `m4 1 1 = p * k * T2 M 1 1` and `C = p * k * r`. -/
theorem face4_iff (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    face4 M ↔ T2 M 1 1 = -r M := by
  have hck : p M * k M ≠ 0 := ne_of_gt (mul_pos hp hk)
  show m4 M 1 1 = -C M ↔ T2 M 1 1 = -r M
  rw [Rho5.MinorCPDomain.m4_11_eq M h00 hp hk, Rho5.MinorCPDomain.C_eq M h00 hp hk]
  constructor
  · intro h
    rw [← mul_neg] at h
    exact mul_left_cancel₀ hck h
  · intro h
    rw [h, mul_neg]

/-- The four equivalences together, in the card's order. -/
theorem face_equivs (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M) (hk : 0 < k M) :
    (face1 M ↔ M 4 4 = -1) ∧ (face2 M ↔ S4 M 3 3 = -p M) ∧
      (face3 M ↔ S3 M 2 2 = -k M) ∧ (face4 M ↔ T2 M 1 1 = -r M) :=
  ⟨face1_iff M, face2_iff M h00, face3_iff M h00 hp, face4_iff M h00 hp hk⟩

/-! ## 2. The whole four-disjunct predicate -/

/-- **The card's equivalence.**  The four-disjunct predicate in original entries/minors is
equivalent to the actual four Schur faces, disjunct by disjunct: the four way structure is
preserved on both sides, no face is dropped, merged or added. -/
theorem boundaryFace_iff_schurFaces (M : Matrix5) (h00 : M 0 0 = 1) (hp : 0 < p M)
    (hk : 0 < k M) : BoundaryFace M ↔ SchurFaces M := by
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl ((face1_iff M).mp h)
    · exact Or.inr (Or.inl ((face2_iff M h00).mp h))
    · exact Or.inr (Or.inr (Or.inl ((face3_iff M h00 hp).mp h)))
    · exact Or.inr (Or.inr (Or.inr ((face4_iff M h00 hp hk).mp h)))
  · rintro (h | h | h | h)
    · exact Or.inl ((face1_iff M).mpr h)
    · exact Or.inr (Or.inl ((face2_iff M h00).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((face3_iff M h00 hp).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((face4_iff M h00 hp hk).mpr h)))

/-- The same equivalence with the positivity taken from the card's polynomial domain
`PolyCP` instead of being assumed: `p > 0` and `k > 0` are derived in D62's order. -/
theorem boundaryFace_iff_schurFaces_of_polyCP (M : Matrix5) (h00 : M 0 0 = 1) (hP : PolyCP M) :
    BoundaryFace M ↔ SchurFaces M := by
  obtain ⟨-, -, -, -, -, hp, hk, -⟩ := (Rho5.MinorCPDomain.polyCP_iff_frame M h00).mp hP
  exact boundaryFace_iff_schurFaces M h00 hp hk

end Rho5.MinorBoundaryFaces
