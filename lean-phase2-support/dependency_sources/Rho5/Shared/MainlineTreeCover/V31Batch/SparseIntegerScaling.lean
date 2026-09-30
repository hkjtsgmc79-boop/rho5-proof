import Rho5.Shared.MainlineTreeCover.V31Batch.Scaling
import Rho5.Shared.CertificateContraction.QuadraticSyntax

/-!
# M02: sparse integer rows and diagonal rational scaling

The integer representation uses the same additive convention as C03's
`sparseCoeff`: repeated columns accumulate. Dense integer equality and the
short scaled-term equality remain explicit input obligations. Neither this
adapter nor its term lists provide a source-feasibility or checker axiom.

No positivity or nonzero premise is needed for these algebraic identities,
including when the common denominator is zero. Compilation is pending owner
integration; upstream C03 and D135 definitions are unchanged.
-/

namespace Rho5.Shared.MainlineTreeCover.V31Batch

open Rho5.Shared.CertificateContraction

/-- Integer counterpart of C03's additive sparse coefficient interpreter. -/
def sparseIntCoeff {n : ℕ} : List (Fin n × ℤ) → Fin n → ℤ
  | [], _ => 0
  | (i, c) :: ts, j => (if j = i then c else 0) + sparseIntCoeff ts j

/-- Coordinate scaling commutes with accumulation, including duplicate columns. -/
theorem sparseCoeff_scaled_integer {n : ℕ} (ts : List (Fin n × ℤ))
    (s : Fin n → ℚ) (b : ℚ) (j : Fin n) :
    sparseCoeff (ts.map (fun t => (t.1, (t.2 : ℚ) * s t.1 / b))) j =
      (sparseIntCoeff ts j : ℚ) * s j / b := by
  induction ts with
  | nil => simp [sparseCoeff, sparseIntCoeff]
  | cons t ts ih =>
    rcases t with ⟨i, c⟩
    by_cases h : j = i
    · subst j
      simp [sparseCoeff, sparseIntCoeff, ih, add_mul, add_div]
    · simp only [List.map_cons, sparseCoeff, sparseIntCoeff, if_neg h,
        zero_add, ih]

/-- Dense matching can be discharged over integers; only the sparse terms
need their rational scaling identity checked by the concrete consumer. -/
theorem scaled_dense_eq_sparse {n : ℕ}
    (row : List ℤ) (ts : List (Fin n × ℤ))
    (s : Fin n → ℚ) (b : ℚ) (actualTerms : List (Fin n × ℚ))
    (hdense : ∀ j : Fin n, row.getD j.val 0 = sparseIntCoeff ts j)
    (hterms : ts.map (fun t => (t.1, (t.2 : ℚ) * s t.1 / b)) = actualTerms) :
    ∀ j : Fin n, ((row.getD j.val 0 : ℚ) * s j) / b =
      sparseCoeff actualTerms j := by
  intro j
  rw [hdense j, ← hterms]
  exact (sparseCoeff_scaled_integer ts s b j).symm

end Rho5.Shared.MainlineTreeCover.V31Batch
