/-
D69 — `Rho5.Shared.GlobalMinorReduction`, the entry module.

The global coverage-to-finite-domain reduction, for every real threshold `T ≥ 4`:

    rho5Trace ≤ T  ↔  ∀ M, M 0 0 = 1 → Rho5.MinorCPDomain.PolyCP M →
                        (D67.C M ≤ T * D67.B M ∧ |M.det| ≤ T * D67.C M)

together with the strict-violation form

    T < rho5Trace ↔ ∃ M, M 0 0 = 1 ∧ PolyCP M ∧
                        (T * B M < C M ∨ T * C M < |M.det|).

* `Basic.lean` — the forward direction and the actual `LegalTrace` a `PolyCP` matrix
  carries (D62 frame → D55 trace at shift `0` → D17 `GrowthValues`);
* `Main.lean` — the reverse direction through D48's paid canonical witness, the
  equivalence, and the strict form.

D62's `PolyCP` is the one finite domain (no second domain is defined); the minors are
D67's, with explicit bridges to D62's same-letter abbreviations.  This closes the global
reduction only: it does **not** claim the underlying inequalities at alpha, a sharp
bound, or any certificate.
-/
import Rho5.Shared.GlobalMinorReduction.Basic
import Rho5.Shared.GlobalMinorReduction.Main

namespace Rho5.GlobalMinorReduction

end Rho5.GlobalMinorReduction
