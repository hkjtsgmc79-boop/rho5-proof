import Rho5.Shared.CertificateContraction.QuadraticLift
import Rho5.Shared.MainlineTreeCover.Box

/-! Integer sparse arithmetic is interpreted at arbitrary real points.
Indices are typed: no modulo coercions and no last-write-wins coefficients. -/
namespace Rho5.Integration.V31BatchKernel
open Rho5.Shared.CertificateContraction (QAtom QPolynomial ProductPairs)

abbrev ITerms (N : ℕ) := List (Fin N × ℤ)
def iEval {N : ℕ} (y : Fin N → ℝ) : ITerms N → ℝ
  | [] => 0
  | (j,c)::ts => (c : ℝ) * y j + iEval y ts

structure IRow (N : ℕ) where
  terms : ITerms N
  rhs : ℤ
  deriving DecidableEq, Repr

def IRow.Holds {N : ℕ} (r : IRow N) (y : Fin N → ℝ) : Prop := iEval y r.terms ≤ (r.rhs : ℝ)
def IRow.toRat {N : ℕ} (r : IRow N) : Rho5.Shared.CertificateContraction.SparseRow N :=
  ⟨r.terms.map (fun t => (t.1, (t.2 : ℚ))), (r.rhs : ℚ)⟩

theorem iEval_eq_sparseEval {N : ℕ} (ts : ITerms N) (y : Fin N → ℝ) :
    iEval y ts = Rho5.Shared.CertificateContraction.sparseEval y
      (ts.map (fun t => (t.1, (t.2 : ℚ)))) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨i,c⟩
    simp [iEval, Rho5.Shared.CertificateContraction.sparseEval, ih]

theorem IRow.holds_iff_toRat {N : ℕ} (r : IRow N) (y : Fin N → ℝ) :
    r.Holds y ↔ r.toRat.Holds y := by
  simp [Holds, toRat, Rho5.Shared.CertificateContraction.SparseRow.Holds, iEval_eq_sparseEval]

structure IBox (N : ℕ) where
  lo : Fin N → ℤ
  hi : Fin N → ℤ

def IBox.Contains {N : ℕ} (b : IBox N) (y : Fin N → ℝ) : Prop :=
  ∀ j, (b.lo j : ℝ) ≤ y j ∧ y j ≤ (b.hi j : ℝ)
def IBox.toRat {N : ℕ} (b : IBox N) : Rho5.Shared.CertificateContraction.Box N :=
  ⟨fun j => (b.lo j : ℚ), fun j => (b.hi j : ℚ)⟩
def IBox.decode {N : ℕ} (b : IBox N) (T : ℤ) : Rho5.Shared.MainlineTreeCover.Box N :=
  ⟨fun j => (b.lo j : ℚ) / (T : ℚ), fun j => (b.hi j : ℚ) / (T : ℚ)⟩
def IBox.ordered {N : ℕ} (b : IBox N) : Bool := decide (∀ j, b.lo j ≤ b.hi j)
def IBox.left {N : ℕ} (b : IBox N) (j : Fin N) (c : ℤ) : IBox N :=
  ⟨b.lo, Function.update b.hi j c⟩
def IBox.right {N : ℕ} (b : IBox N) (j : Fin N) (c : ℤ) : IBox N :=
  ⟨Function.update b.lo j c, b.hi⟩

theorem IBox.contains_iff_toRat {N : ℕ} (b : IBox N) (y : Fin N → ℝ) :
    b.Contains y ↔ b.toRat.Contains y := by
  simp [Contains, toRat, Rho5.Shared.CertificateContraction.Box.Contains]

theorem IBox.scaled_contains_of_decode {N : ℕ} (b : IBox N) (T : ℤ) (hT : 0 < T)
    (x : Fin N → ℝ) (hx : x ∈ (b.decode T).denote) :
    b.Contains (fun j => (T : ℝ) * x j) := by
  have ht : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  intro j
  have h := hx j
  change (((b.lo j : ℚ) / (T : ℚ) : ℚ) : ℝ) ≤ x j ∧
    x j ≤ (((b.hi j : ℚ) / (T : ℚ) : ℚ) : ℝ) at h
  push_cast at h
  constructor
  · simpa only [mul_comm] using (div_le_iff₀ ht).mp h.1
  · simpa only [mul_comm] using (le_div_iff₀ ht).mp h.2

theorem IBox.split_cover {N : ℕ} (b : IBox N) (j : Fin N) (c : ℤ)
    (y : Fin N → ℝ) (hy : b.Contains y) :
    (b.left j c).Contains y ∨ (b.right j c).Contains y := by
  rcases le_total (y j) (c : ℝ) with hc | hc
  · left
    intro i
    by_cases hi : i = j
    · subst i; simpa [IBox.left] using And.intro (hy j).1 hc
    · simpa [IBox.left, Function.update_of_ne hi] using hy i
  · right
    intro i
    by_cases hi : i = j
    · subst i; simpa [IBox.right] using And.intro hc (hy j).2
    · simpa [IBox.right, Function.update_of_ne hi] using hy i

end Rho5.Integration.V31BatchKernel
