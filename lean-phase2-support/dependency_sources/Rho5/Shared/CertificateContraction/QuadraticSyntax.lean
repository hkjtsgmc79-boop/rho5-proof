import Rho5.Shared.CertificateContraction.IntervalArithmetic
import Mathlib.Algebra.BigOperators.Fin

namespace Rho5.Shared.CertificateContraction
open scoped BigOperators

/-- Fixed original coordinates and shared product slots. Slot q has the actual
value z (pairs q).1 * z (pairs q).2, also when both indices are equal. -/
abbrev ProductPairs (n k : ℕ) := Fin k → Fin n × Fin n

inductive QAtom (n k : ℕ) where
  | constant
  | linear (i : Fin n)
  | product (q : Fin k)
  deriving DecidableEq, Repr

abbrev QPolynomial (n k : ℕ) := List (ℚ × QAtom n k)

def QAtom.eval {n k : ℕ} (pairs : ProductPairs n k) (z : Fin n → ℝ) : QAtom n k → ℝ
  | .constant => 1
  | .linear i => z i
  | .product q => z (pairs q).1 * z (pairs q).2

def QPolynomial.eval {n k : ℕ} (pairs : ProductPairs n k) (z : Fin n → ℝ) :
    QPolynomial n k → ℝ
  | [] => 0
  | (c,a)::ps => (c : ℝ)*a.eval pairs z + QPolynomial.eval pairs z ps

def liftPoint {n k : ℕ} (pairs : ProductPairs n k) (z : Fin n → ℝ) : Fin (n+k) → ℝ :=
  Fin.addCases z (fun q => z (pairs q).1 * z (pairs q).2)

def projectPoint {n k : ℕ} (y : Fin (n+k) → ℝ) : Fin n → ℝ := fun i => y (Fin.castAdd k i)

@[simp] theorem project_lift {n k : ℕ} (pairs : ProductPairs n k) (z : Fin n → ℝ) :
    projectPoint (liftPoint pairs z) = z := by funext i; simp [projectPoint,liftPoint]

def QAtom.column {n k : ℕ} : QAtom n k → Option (Fin (n+k))
  | .constant => none
  | .linear i => some (Fin.castAdd k i)
  | .product q => some (Fin.natAdd n q)

/-- Dense coefficients are obtained by summing *all* sparse contributions, not
overwriting a coefficient when two entries target the same column. -/
def sparseCoeff {N : ℕ} : List (Fin N × ℚ) → Fin N → ℚ
  | [], _ => 0
  | (i,c)::ts, h => (if h=i then c else 0) + sparseCoeff ts h

def sparseEval {N : ℕ} (z : Fin N → ℝ) : List (Fin N × ℚ) → ℝ
  | [] => 0
  | (i,c)::ts => (c : ℝ)*z i + sparseEval z ts

theorem sparse_dot {N : ℕ} (ts : List (Fin N × ℚ)) (z : Fin N → ℝ) :
    ∑ h, (sparseCoeff ts h : ℝ)*z h = sparseEval z ts := by
  induction ts with
  | nil => simp [sparseCoeff,sparseEval]
  | cons t ts ih =>
    rcases t with ⟨i,c⟩
    simp only [sparseCoeff,sparseEval]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib, ih]
    simp [apply_ite,ite_mul]

structure SparseRow (N : ℕ) where
  terms : List (Fin N × ℚ)
  rhs : ℚ

def SparseRow.Holds {N : ℕ} (r : SparseRow N) (z : Fin N → ℝ) : Prop :=
  sparseEval z r.terms ≤ (r.rhs : ℝ)

def QPolynomial.toRow {n k : ℕ} : QPolynomial n k → SparseRow (n+k)
  | [] => ⟨[],0⟩
  | (c,.constant)::ps => ⟨(toRow ps).terms, c+(toRow ps).rhs⟩
  | (c,.linear i)::ps => ⟨(Fin.castAdd k i,-c)::(toRow ps).terms,(toRow ps).rhs⟩
  | (c,.product q)::ps => ⟨(Fin.natAdd n q,-c)::(toRow ps).terms,(toRow ps).rhs⟩

theorem quadratic_row_identity {n k : ℕ} (pairs : ProductPairs n k)
    (p : QPolynomial n k) (z : Fin n → ℝ) :
    sparseEval (liftPoint pairs z) p.toRow.terms = (p.toRow.rhs : ℝ) - p.eval pairs z := by
  induction p with
  | nil => simp [QPolynomial.toRow,sparseEval,QPolynomial.eval]
  | cons t ps ih =>
    rcases t with ⟨c,a⟩
    cases a <;> simp [QPolynomial.toRow,sparseEval,QPolynomial.eval,QAtom.eval,liftPoint,ih] <;> ring

theorem quadratic_row_sound {n k : ℕ} (pairs : ProductPairs n k)
    (p : QPolynomial n k) (z : Fin n → ℝ) (hp : 0 ≤ p.eval pairs z) :
    p.toRow.Holds (liftPoint pairs z) := by
  unfold SparseRow.Holds
  rw [quadratic_row_identity]
  linarith

def rowsFromList {N : ℕ} (rs : List (SparseRow N)) : Rows N rs.length where
  a := fun j => sparseCoeff (rs.get j).terms
  rhs := fun j => (rs.get j).rhs

theorem rowsFromList_sound {N : ℕ} (rs : List (SparseRow N)) (z : Fin N → ℝ)
    (h : ∀ r ∈ rs, r.Holds z) : (rowsFromList rs).Holds z := by
  intro j
  change (∑ h, (sparseCoeff (rs.get j).terms h : ℝ)*z h) ≤ _
  rw [sparse_dot]
  exact h _ (List.get_mem _ _)

end Rho5.Shared.CertificateContraction
