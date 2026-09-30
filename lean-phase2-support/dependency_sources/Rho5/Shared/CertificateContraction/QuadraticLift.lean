import Rho5.Shared.CertificateContraction.QuadraticSyntax
import Rho5.Shared.XSmallKBranch.Sound
import Mathlib.Tactic.FinCases

namespace Rho5.Shared.CertificateContraction

def liftBox {n k : ℕ} (pairs : ProductPairs n k) (b : Box n) : Box (n+k) where
  lo := Fin.addCases b.lo (fun q => ((b.interval (pairs q).1).mul (b.interval (pairs q).2)).lo)
  hi := Fin.addCases b.hi (fun q => ((b.interval (pairs q).1).mul (b.interval (pairs q).2)).hi)

def projectBox {n k : ℕ} (b : Box (n+k)) : Box n where
  lo := fun i => b.lo (Fin.castAdd k i)
  hi := fun i => b.hi (Fin.castAdd k i)

theorem liftBox_contains {n k : ℕ} (pairs : ProductPairs n k) (b : Box n)
    (z : Fin n → ℝ) (hb : b.Contains z) : (liftBox pairs b).Contains (liftPoint pairs z) := by
  apply Fin.addCases
  · intro i
    simpa [liftBox,liftPoint] using hb i
  · intro q
    simpa [liftBox,liftPoint] using QInterval.mul_contains (b.interval (pairs q).1) (b.interval (pairs q).2) (z (pairs q).1) (z (pairs q).2) (hb (pairs q).1) (hb (pairs q).2)

theorem projectBox_contains {n k : ℕ} (b : Box (n+k)) (y : Fin (n+k) → ℝ)
    (hb : b.Contains y) : (projectBox b).Contains (projectPoint y) :=
  fun i => hb (Fin.castAdd k i)

/-- Three contributions are kept as a list. If i=j, the first two accumulate
in sparseCoeff, precisely as the runtime dictionary updates do. -/
def mccRow {n k : ℕ} (pairs : ProductPairs n k) (b : Box n)
    (q : Fin k) : Fin 4 → SparseRow (n+k)
  | 0 => ⟨[(Fin.castAdd k (pairs q).1,b.lo (pairs q).2),
      (Fin.castAdd k (pairs q).2,b.lo (pairs q).1),(Fin.natAdd n q,-1)],
      b.lo (pairs q).1 * b.lo (pairs q).2⟩
  | 1 => ⟨[(Fin.castAdd k (pairs q).1,b.hi (pairs q).2),
      (Fin.castAdd k (pairs q).2,b.hi (pairs q).1),(Fin.natAdd n q,-1)],
      b.hi (pairs q).1 * b.hi (pairs q).2⟩
  | 2 => ⟨[(Fin.castAdd k (pairs q).1,-b.hi (pairs q).2),
      (Fin.castAdd k (pairs q).2,-b.lo (pairs q).1),(Fin.natAdd n q,1)],
      -b.lo (pairs q).1 * b.hi (pairs q).2⟩
  | 3 => ⟨[(Fin.castAdd k (pairs q).1,-b.lo (pairs q).2),
      (Fin.castAdd k (pairs q).2,-b.hi (pairs q).1),(Fin.natAdd n q,1)],
      -b.hi (pairs q).1 * b.lo (pairs q).2⟩

theorem mccRow_sound {n k : ℕ} (pairs : ProductPairs n k) (b : Box n)
    (z : Fin n → ℝ) (hb : b.Contains z) (q : Fin k) (f : Fin 4) :
    (mccRow pairs b q f).Holds (liftPoint pairs z) := by
  have h := Rho5.Shared.XSmallKBranch.mccormick_of_bounds
    (hb (pairs q).1).1 (hb (pairs q).1).2 (hb (pairs q).2).1 (hb (pairs q).2).2
  fin_cases f <;> dsimp [mccRow,SparseRow.Holds,sparseEval,liftPoint] <;> push_cast <;>
    simp only [Fin.addCases_left,Fin.addCases_right,neg_one_mul,one_mul,add_zero] <;>
    linarith [h.ll,h.uu,h.ul,h.lu]

def generatedRow {n k r : ℕ} (pairs : ProductPairs n k) (ps : Fin r → QPolynomial n k)
    (b : Box n) : Fin (r+k*4) → SparseRow (n+k) :=
  Fin.addCases (fun j => (ps j).toRow) (fun j => mccRow pairs b j.divNat j.modNat)

def generatedRows {n k r : ℕ} (pairs : ProductPairs n k) (ps : Fin r → QPolynomial n k)
    (b : Box n) : Rows (n+k) (r+k*4) where
  a := fun j => sparseCoeff (generatedRow pairs ps b j).terms
  rhs := fun j => (generatedRow pairs ps b j).rhs

theorem generatedRows_sound {n k r : ℕ} (pairs : ProductPairs n k)
    (ps : Fin r → QPolynomial n k) (b : Box n) (z : Fin n → ℝ)
    (hb : b.Contains z) (hp : ∀ j, 0 ≤ (ps j).eval pairs z) :
    (generatedRows pairs ps b).Holds (liftPoint pairs z) := by
  intro j
  change (∑ h, (sparseCoeff (generatedRow pairs ps b j).terms h : ℝ)*liftPoint pairs z h) ≤ _
  rw [sparse_dot]
  change (generatedRow pairs ps b j).Holds (liftPoint pairs z)
  refine Fin.addCases ?_ ?_ j
  · intro i
    simpa [generatedRow] using quadratic_row_sound pairs (ps i) z (hp i)
  · intro i
    simpa [generatedRow] using mccRow_sound pairs b z hb i.divNat i.modNat

theorem quadratic_lift_source {n k r : ℕ} (pairs : ProductPairs n k)
    (ps : Fin r → QPolynomial n k) (b : Box n) (z : Fin n → ℝ)
    (hb : b.Contains z) (hp : ∀ j, 0 ≤ (ps j).eval pairs z) :
    (liftBox pairs b).Contains (liftPoint pairs z) ∧
      (generatedRows pairs ps b).Holds (liftPoint pairs z) :=
  ⟨liftBox_contains pairs b z hb,generatedRows_sound pairs ps b z hb hp⟩

def LiftSource {n k r : ℕ} (pairs : ProductPairs n k) (ps : Fin r → QPolynomial n k)
    (y : Fin (n+k) → ℝ) : Prop :=
  ∃ z, y = liftPoint pairs z ∧ ∀ j, 0 ≤ (ps j).eval pairs z

/-- On any current lifted box, regenerate rows from this very box's original
coordinate projection. No parent/root endpoints are substituted. -/
theorem generatedRows_SourceRowsOn {n k r : ℕ} (pairs : ProductPairs n k)
    (ps : Fin r → QPolynomial n k) :
    SourceRowsOn (LiftSource pairs ps) (fun b => generatedRows pairs ps (projectBox b)) := by
  intro y hy b hb
  obtain ⟨z,rfl,hp⟩ := hy
  have ho := projectBox_contains b (liftPoint pairs z) hb
  rw [project_lift] at ho
  exact generatedRows_sound pairs ps (projectBox b) z ho hp

end Rho5.Shared.CertificateContraction
