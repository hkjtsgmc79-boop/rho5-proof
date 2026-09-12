/-
D70 stage 1 — the four boundary faces written **only** in original entries and minors.

For an actual `M : Matrix5` the card fixes the four-disjunct predicate

`M 4 4 = -1  ∨  m2 M 3 3 = -A M  ∨  m3 M 2 2 = -B M  ∨  m4 M 1 1 = -C M`

with `A = m2 M 0 0`, `B = m3 M 0 0`, `C = m4 M 0 0`.  Every ingredient is an original
entry or a determinant of the fixed ordered bordered minor families of the accepted
deliveries: `m2`/`m3` are D61 `Rho5.PrefixBorderedMinors` (16 + 9 minors) and `m4`/`A`/`B`/`C`
are D62 `Rho5.MinorCPDomain` (4 bordered minors).  **No family is redefined here**, and no
`S4`/`S3`/`T2`, no Schur update, no quotient coordinate occurs in `BoundaryFace`: the
polynomial side never hides a Schur face inside its own definition.  The Schur reading is
kept in the separate `SchurFaces` predicate so that stage 2 can prove the two equivalent.

This is a fixed finite family of five indices (`(4,4)`, `(3,3)`, `(2,2)`, `(1,1)`, `(0,1)`,
`(1,0)`), not a generic minor symmetry framework.
-/
import Rho5.Shared.MinorCPDomain

namespace Rho5.MinorBoundaryFaces

open Rho5 (Matrix5)
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t)

/-! ## 1. The four faces, one disjunct each -/

/-- **Face 1**: the original corner entry itself, unchanged by any minor. -/
def face1 (M : Matrix5) : Prop := M 4 4 = -1

/-- **Face 2**: the ordered `2 × 2` bordered minor `m2 3 3` equals `-A`, `A = m2 0 0`. -/
def face2 (M : Matrix5) : Prop := Rho5.PrefixBorderedMinors.m2 M 3 3 = -Rho5.MinorCPDomain.A M

/-- **Face 3**: the ordered `3 × 3` bordered minor `m3 2 2` equals `-B`, `B = m3 0 0`. -/
def face3 (M : Matrix5) : Prop := Rho5.PrefixBorderedMinors.m3 M 2 2 = -Rho5.MinorCPDomain.B M

/-- **Face 4**: the bordered `4 × 4` minor `m4 1 1` equals `-C`, `C = m4 0 0`. -/
def face4 (M : Matrix5) : Prop := Rho5.MinorCPDomain.m4 M 1 1 = -Rho5.MinorCPDomain.C M

/-- **The card's four-disjunct boundary predicate**, written only from the original
entries and the three frozen minor families (`A`, `B`, `C` are their leading corners as
defined in D62). -/
def BoundaryFace (M : Matrix5) : Prop := face1 M ∨ face2 M ∨ face3 M ∨ face4 M

/-- The same four faces read in the actual Schur coordinates; the equivalence with
`BoundaryFace` is proved in `MinorBoundaryFaces.Equiv`, never assumed here. -/
def SchurFaces (M : Matrix5) : Prop :=
  M 4 4 = -1 ∨ S4 M 3 3 = -p M ∨ S3 M 2 2 = -k M ∨ T2 M 1 1 = -r M

/-! ## 2. The definitions read back (definitional, no expansion of any determinant) -/

theorem boundaryFace_iff_list (M : Matrix5) :
    BoundaryFace M ↔ (face1 M ∨ face2 M ∨ face3 M ∨ face4 M) := Iff.rfl

theorem schurFaces_iff_list (M : Matrix5) :
    SchurFaces M ↔ (M 4 4 = -1 ∨ S4 M 3 3 = -p M ∨ S3 M 2 2 = -k M ∨ T2 M 1 1 = -r M) :=
  Iff.rfl

/-! ## 3. Each face is one disjunct of the four-disjunct predicate

These four constructors are the only way a face enters `BoundaryFace`; in particular the
later determinant work on face 4 leaves the other three disjuncts untouched. -/

theorem boundaryFace_of_face1 (M : Matrix5) (h : face1 M) : BoundaryFace M := Or.inl h

theorem boundaryFace_of_face2 (M : Matrix5) (h : face2 M) : BoundaryFace M :=
  Or.inr (Or.inl h)

theorem boundaryFace_of_face3 (M : Matrix5) (h : face3 M) : BoundaryFace M :=
  Or.inr (Or.inr (Or.inl h))

theorem boundaryFace_of_face4 (M : Matrix5) (h : face4 M) : BoundaryFace M :=
  Or.inr (Or.inr (Or.inr h))

end Rho5.MinorBoundaryFaces
