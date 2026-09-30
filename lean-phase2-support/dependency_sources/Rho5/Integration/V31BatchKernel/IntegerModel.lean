import Rho5.Integration.V31BatchKernel.IntegerSyntax

namespace Rho5.Integration.V31BatchKernel
open Rho5.Shared.CertificateContraction

abbrev IPoly (n k : ℕ) := List (ℤ × QAtom n k)
def IPoly.toQ {n k : ℕ} (p : IPoly n k) : QPolynomial n k :=
  p.map (fun t => ((t.1 : ℚ), t.2))
def IPoly.toRow {n k : ℕ} : IPoly n k → IRow (n+k)
  | [] => ⟨[],0⟩
  | (c,.constant)::ps => ⟨(toRow ps).terms, c+(toRow ps).rhs⟩
  | (c,.linear i)::ps => ⟨(Fin.castAdd k i,-c)::(toRow ps).terms,(toRow ps).rhs⟩
  | (c,.product q)::ps => ⟨(Fin.natAdd n q,-c)::(toRow ps).terms,(toRow ps).rhs⟩

theorem IPoly.row_identity {n k : ℕ} (pairs : ProductPairs n k) (p : IPoly n k) (v : Fin n → ℝ) :
    iEval (liftPoint pairs v) p.toRow.terms = (p.toRow.rhs : ℝ) - p.toQ.eval pairs v := by
  induction p with
  | nil => simp [toRow, iEval, toQ, QPolynomial.eval]
  | cons t ps ih =>
    rcases t with ⟨c,a⟩
    cases a <;> simp [toRow, iEval, toQ, QPolynomial.eval, QAtom.eval, liftPoint, toQ] at * <;> linarith

theorem IPoly.row_sound {n k : ℕ} (pairs : ProductPairs n k) (p : IPoly n k) (v : Fin n → ℝ)
    (hp : 0 ≤ p.toQ.eval pairs v) : p.toRow.Holds (liftPoint pairs v) := by
  unfold IRow.Holds
  rw [row_identity]
  linarith

def IPoly.scalePoly {n k : ℕ} (T : ℤ) : IPoly n k → IPoly n k
  | [] => []
  | (c,a)::ps =>
    ((match a with | .constant => c*T^2 | .linear _ => c*T | .product _ => c), a)::scalePoly T ps

theorem IPoly.scale_eval {n k : ℕ} (T : ℤ) (p : IPoly n k) (pairs : ProductPairs n k) (v : Fin n → ℝ) :
    (p.scalePoly T).toQ.eval pairs (fun j => (T : ℝ)*v j) = (T : ℝ)^2 * p.toQ.eval pairs v := by
  induction p with
  | nil => simp [scalePoly, toQ, QPolynomial.eval]
  | cons t ps ih =>
    rcases t with ⟨c,a⟩
    cases a <;> simp [scalePoly, toQ, QPolynomial.eval, QAtom.eval, toQ] at * <;> rw [ih] <;> ring

structure IntModel (n k r : ℕ) where
  pairs : ProductPairs n k
  ps : Fin r → IPoly n k

def IntModel.Source {n k r : ℕ} (m : IntModel n k r) (v : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ (m.ps j).toQ.eval m.pairs v
def IntModel.scaled {n k r : ℕ} (T : ℤ) (m : IntModel n k r) : IntModel n k r :=
  ⟨m.pairs, fun j => (m.ps j).scalePoly T⟩
theorem IntModel.scaled_source {n k r : ℕ} (T : ℤ) (m : IntModel n k r) (v : Fin n → ℝ)
    (hv : m.Source v) : (m.scaled T).Source (fun j => (T : ℝ)*v j) := by
  intro j
  change 0 ≤ ((m.ps j).scalePoly T).toQ.eval m.pairs _
  rw [IPoly.scale_eval]
  exact mul_nonneg (sq_nonneg _) (hv j)

end Rho5.Integration.V31BatchKernel
