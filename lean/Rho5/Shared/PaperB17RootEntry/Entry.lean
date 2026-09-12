/-
D134 — stage B: the canonical root representative and the final G05 entry
=======================================================================

Stage B consumes the accepted D133 sign representative
`Rho5.Shared.PaperB17Signs.normalizedB_has_sign_representative` (its receipt
`B17_SIGN_REPRESENTATIVE_READY`, olean hashes verified before linking) and nothing else new.

Given `NormalizedB z` with `alpha < z 23`, D133 supplies the *same-height* real sign representative
`z'` together with

* the actual matrix relation `reconstruct z' i j = sg i * reconstruct z i j * sg j` for every `i j`
  and `sg i = ±1` — a genuine legal row/column sign operation, not an independent coordinate patch;
* `NormalizedB z'`, i.e. all coupled bands (`Qualified` + `1 ≤ z' 8` + `0 ≤ z' 9` + `0 ≤ z' 10`)
  together with the actual tail and height;
* the preserved readings `z' 23 = z 23` (height), `z' 8 = z 8` (p), `z' 0 = z 0` (k),
  `z' 1 = z 1` (r), `z' 2 = z 2` (s), `z' 3 = z 3` (t), `z' 9 = z 9` (e), `z' 10 = z 10` (β);
* the two sign conclusions `0 ≤ z' 14` (x0) and `z' 4 ≤ 0` (A).

Stage A's `root_of_normalizedB_high` then gives the complete 17-dimensional closed root at
`frameOf z'`, with `alpha < z' 23` transported through `z' 23 = z 23`.  This is the whole G05 entry:
no `RootMembership`, no capacity or maximum conclusion, no general source existence and no
whole-root safety claim is made here.
-/
import Rho5.Shared.PaperB17RootEntry.Bounds
import Rho5.Shared.PaperB17Signs

namespace Rho5.Shared.PaperB17RootEntry

noncomputable section
set_option maxHeartbeats 800000

open Rho5.Certificate.B16 (Point)
open Rho5.Certificate.B24Reconstruction (reconstruct)
open Rho5.ExternalBFibreCapacity (NormalizedB frameOf)

/-- **`high_normalizedB_has_canonical_root_representative` (the G05 entry).**  A normalized,
high-valued B source has a *same-height* real sign representative whose `frameVector` lies in the
complete 17-dimensional closed B-root; the signed matrix relation, all coupled bands, the actual
tail and the preserved readings are all returned. -/
theorem high_normalizedB_has_canonical_root_representative (z : Point) (h : NormalizedB z)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < z 23) :
    ∃ z' : Point, ∃ sg : Fin 5 → ℝ, (∀ i : Fin 5, sg i = 1 ∨ sg i = -1) ∧
      (∀ i j : Fin 5, reconstruct z' i j = sg i * reconstruct z i j * sg j) ∧
      NormalizedB z' ∧ B17Root (frameOf z') ∧
      z' 23 = z 23 ∧ z' 8 = z 8 ∧ z' 0 = z 0 ∧ z' 1 = z 1 ∧ z' 2 = z 2 ∧ z' 3 = z 3 ∧
      z' 9 = z 9 ∧ z' 10 = z 10 := by
  obtain ⟨z', sg, hsg, hmat, hnorm, h23, h8, h0, h1, h2, h3, h9, h10, hx0, hA⟩ :=
    Rho5.Shared.PaperB17Signs.normalizedB_has_sign_representative z h
  refine ⟨z', sg, hsg, hmat, hnorm, ?_, h23, h8, h0, h1, h2, h3, h9, h10⟩
  exact root_of_normalizedB_high z' hnorm hx0 hA (by rw [h23]; exact hhigh)

/-- The representative's root, stated on its own (stage B's essential output). -/
theorem exists_root_representative (z : Point) (h : NormalizedB z)
    (hhigh : Rho5.Algebraic.AlphaRoot.alpha < z 23) :
    ∃ z' : Point, NormalizedB z' ∧ B17Root (frameOf z') ∧ z' 23 = z 23 := by
  obtain ⟨z', sg, -, -, hnorm, hroot, h23, -⟩ :=
    high_normalizedB_has_canonical_root_representative z h hhigh
  exact ⟨z', hnorm, hroot, h23⟩

end

end Rho5.Shared.PaperB17RootEntry
