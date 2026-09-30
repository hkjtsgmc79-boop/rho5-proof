import Rho5.Shared.MainlineTreeCover.V31Batch.Scaling
import Rho5.Shared.CertificateContraction.QuadraticLift

/-!
# M02: explicit source-row selection into a rational terminal

Only representation transport is proved here. The terminal bounds and every
selected coefficient/right-hand side must be supplied as exact equalities.
There is no assumption that an external row index, parser, or numerical check
has already established those identities. The source point is real throughout.

Authored source; compilation and axiom checks await owner integration.
-/

namespace Rho5.Shared.MainlineTreeCover.V31Batch

open Rho5.Shared.CertificateRules
open scoped BigOperators

/-- Exact bounds and selected rows transport a real source point to D135. -/
theorem ratFeasibleR_of_source_rows {n m t : ℕ}
    (b : CertificateContraction.Box n) (rows : CertificateContraction.Rows n m)
    (terminal : Rational.RatSystem (Fin t) (Fin n)) (pick : Fin t → Fin m)
    (hlo : ∀ j, terminal.lo j = b.lo j)
    (hhi : ∀ j, terminal.hi j = b.hi j)
    (ha : ∀ i j, terminal.rows i j = rows.a (pick i) j)
    (hrhs : ∀ i, terminal.rhs i = rows.rhs (pick i))
    (y : Fin n → ℝ) (hb : b.Contains y) (hrows : rows.Holds y) :
    Rational.FeasibleR terminal y := by
  refine ⟨?_, ?_⟩
  · intro j
    rw [hlo j, hhi j]
    exact hb j
  · intro i
    simp only [ha, hrhs]
    exact hrows (pick i)

/-- A previously proved real terminal exclusion rules out the matched source. -/
theorem source_empty_of_rat_terminal_empty {n m t : ℕ}
    (b : CertificateContraction.Box n) (rows : CertificateContraction.Rows n m)
    (terminal : Rational.RatSystem (Fin t) (Fin n)) (pick : Fin t → Fin m)
    (hlo : ∀ j, terminal.lo j = b.lo j)
    (hhi : ∀ j, terminal.hi j = b.hi j)
    (ha : ∀ i j, terminal.rows i j = rows.a (pick i) j)
    (hrhs : ∀ i, terminal.rhs i = rows.rhs (pick i))
    (hempty : ∀ y : Fin n → ℝ, ¬ Rational.FeasibleR terminal y) :
    ∀ y : Fin n → ℝ, b.Contains y → rows.Holds y → False := by
  intro y hb hrows
  exact hempty y
    (ratFeasibleR_of_source_rows b rows terminal pick hlo hhi ha hrhs y hb hrows)

/-- Direct checker form; nonnegative weights and the exact check are explicit. -/
theorem source_empty_of_rat_check {n m t : ℕ}
    (b : CertificateContraction.Box n) (rows : CertificateContraction.Rows n m)
    (terminal : Rational.RatSystem (Fin t) (Fin n)) (pick : Fin t → Fin m)
    (hlo : ∀ j, terminal.lo j = b.lo j)
    (hhi : ∀ j, terminal.hi j = b.hi j)
    (ha : ∀ i j, terminal.rows i j = rows.a (pick i) j)
    (hrhs : ∀ i, terminal.rhs i = rows.rhs (pick i))
    (w : Fin t → ℚ) (hw : ∀ i, 0 ≤ w i)
    (hc : Rational.check terminal w = true) :
    ∀ y : Fin n → ℝ, b.Contains y → rows.Holds y → False := by
  exact source_empty_of_rat_terminal_empty b rows terminal pick hlo hhi ha hrhs
    (Rational.check_sound_real terminal w hw hc)

end Rho5.Shared.MainlineTreeCover.V31Batch
