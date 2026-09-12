/-
D65 — the balanced branch enters B24 at the same height
========================================================

**Item 1 of the card.**  For an actual `Matrix5 M` whose tail satisfies the *explicit balanced
condition* `T2 M 1 1 = -r M`, the B24 height read off the tail,

    `F M = r M + s M * t M / r M`      (D37 `B24Extraction.F`)

is the negative of D48's `delta`,

    `delta M = T2 M 1 1 - t M * s M / r M`   (D48 `CanonicalTail.delta`),

so under `T2 M 1 1 = -r M` we get `F M = -delta M`.  With `0 < r M` and `0 ≤ s M * t M` this
gives `F M ≥ r M ≥ 0`, hence `|delta M| = F M`.

The four shifted-endpoint branches are `M44 = -1`, `S4_33 = -p`, `S3_22 = -k`, `T2_11 = -r`
(D55/D57).  **This module consumes only the last one**; the other three stay open.  Nothing here
assumes `s` or `t` strictly positive — only nonnegativity, as the card requires.
-/
import Rho5.Certificate.B24Extraction
import Rho5.Shared.CanonicalTail

namespace Rho5.Certificate.BalancedMaximizer

open Rho5
open Rho5.Certificate.B24Extraction (S4 S3 T2 p k r s t F)

/-- **Item 1a.**  On the balanced branch the tail height is the negative of `delta`. -/
theorem F_eq_neg_delta (M : Matrix5) (htail : T2 M 1 1 = -r M) :
    F M = -Rho5.CanonicalTail.delta M := by
  have hdelta : Rho5.CanonicalTail.delta M = T2 M 1 1 - t M * s M / r M := rfl
  rw [hdelta, htail, F]
  ring

/-- The reading of `delta` on the balanced branch, in the direction the rest of the file uses. -/
theorem delta_eq_neg_F (M : Matrix5) (htail : T2 M 1 1 = -r M) :
    Rho5.CanonicalTail.delta M = -F M := by
  rw [F_eq_neg_delta M htail, neg_neg]

/-- **Item 1b.**  `F` dominates the leading entry `r` of the tail: `r M ≤ F M`.
Only `0 < r M` and `0 ≤ s M * t M` are used. -/
theorem r_le_F (M : Matrix5) (hrpos : 0 < r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    r M ≤ F M := by
  have hst : 0 ≤ s M * t M := mul_nonneg hs ht
  have hdiv : 0 ≤ s M * t M / r M := div_nonneg hst hrpos.le
  have : F M = r M + s M * t M / r M := rfl
  rw [this]; linarith

/-- `F M` is nonnegative on the balanced branch. -/
theorem F_nonneg (M : Matrix5) (hrpos : 0 < r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    0 ≤ F M :=
  le_trans hrpos.le (r_le_F M hrpos hs ht)

/-- **Item 1c.**  On the balanced branch the fifth trace value is the height itself:
`|delta M| = F M`. -/
theorem abs_delta_eq_F (M : Matrix5) (htail : T2 M 1 1 = -r M)
    (hrpos : 0 < r M) (hs : 0 ≤ s M) (ht : 0 ≤ t M) :
    |Rho5.CanonicalTail.delta M| = F M := by
  rw [delta_eq_neg_F M htail, abs_neg, abs_of_nonneg (F_nonneg M hrpos hs ht)]

end Rho5.Certificate.BalancedMaximizer
