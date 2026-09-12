/-
D74 — `Rho5.Shared.BoundaryUpperReduction`, the entry module.

The sharp upper certificate reduced to the sorted four-boundary matrices, for every
threshold `T ≥ 4`:

    rho5Trace ≤ T  ↔
      ∀ M, M 0 0 = 1 → PolyCP M →
        0 ≤ m4 M 0 1 → m4 M 0 1 ≤ m4 M 1 0 →        -- D70 sorted non-negative tail, minor form
          BoundaryFace M →                           -- D70 four-boundary predicate
            (D67.C M ≤ T * D67.B M ∧ |M.det| ≤ T * D67.C M)

* `Forward.lean` — the restricted forward direction (a restriction of D69's global
  reduction; the two extra hypotheses are unused);
* `Main.lean` — the reverse direction through D68's accepted stage-A four-faces existence
  and D70's two paid bridges, the equivalence, the strict-violation form, and the
  four-obligation certificate corollary (`rho5Trace_le_of_four_face_bounds`).

This keeps all four faces and reuses D70's own predicate — no second four-face framework,
no balanced-maximum assumption, no extra full-rank premise.  It reduces the external work
to four concrete families; it does **not** assert any of the four face inequalities, any
alpha equality, `4 < rho5Trace`, or the vanishing of the first three faces.
-/
import Rho5.Shared.BoundaryUpperReduction.Forward
import Rho5.Shared.BoundaryUpperReduction.Main

namespace Rho5.BoundaryUpperReduction

end Rho5.BoundaryUpperReduction
